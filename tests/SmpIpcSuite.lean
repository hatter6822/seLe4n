-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n - A Lean Microkernel
  Copyright (C) 2026 Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.EndpointCall
import SeLe4n.Kernel.IPC.CrossCore.EndpointReply
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallDispatch
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyDispatch
import SeLe4n.Kernel.IPC.CrossCore.Cancellation
import SeLe4n.Kernel.IPC.Invariant.PerCoreBundlePreservation
import SeLe4n.Kernel.Scheduler.Operations.PerCoreWcrt
import SeLe4n.Kernel.API
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
  footprints, hierarchical kinds, exact resolved footprint sizes, SM5.J WCRT
  bound);
* **§3.8** live-dispatch coherence: `determineExecutingCore` + the full
  `endpointCallCrossCoreDispatch` agree with the bare transition;
* **§3.9** SchedContext **donation** round trip: a bound-SC client calls a
  passive (unbound-SC) server homed on a remote core — the SC donates to the
  server (`applyCallDonation`), the server's donated-priority boost migrates
  its run-queue bucket on its home core (cross-core PIP), and the reply
  returns the SC to the client (`applyReplyDonationOnCore`);
* **§3.10** **capability transfer** across cores: a Call carrying a capability
  installs it into the receiver's CSpace via `ipcUnwrapCaps` (grant-right
  gated — denied without `.grant`), plus the `ipcMessageTooManyCaps` bound;
* **§3.11** **info-flow-checked** cross-core dispatch: `…CrossCoreDispatchChecked`
  runs the transition when the flow is permitted and fails closed with
  `.flowDenied` (state unchanged) when it is not — for both the call
  (caller→endpoint) and the reply (replier→target) gates;
* **§3.12** the **live API dispatch** path (`dispatchSyscall` `.call`): the
  full CSpace capability resolution + authority gate + cross-core dispatch
  composition (authorized call succeeds; no-cap / read-only-cap / wrong-kind
  fail closed), plus the checked (`dispatchSyscallChecked`) info-flow variant;
* **§3.13** **cancellation × IPC** composition: suspending / cancelling a
  client blocked awaiting a reply severs its reply linkage, so the server's
  later cross-core reply fails closed (`.replyCapInvalid`);
* **§3.14** **scheduler contention** on the handler path: a woken server does
  NOT preempt a strictly higher-priority current thread on its home core;
* **§9** the deterministic **4-core IPC golden trace** (SM6.F.4), verified
  byte-for-byte against `tests/fixtures/smp_ipc_4core.expected`.

`lake exe smp_ipc_suite` runs all scenarios; an IPC-logic regression flips a
decidable check or diverges the golden trace.

**Coverage note.** There is deliberately no cross-core `.replyRecv` dispatch
wrapper to exercise: the raw-thread `endpointReplyRecvCrossCoreDispatch{,Checked}`
were removed (they exposed a reply-without-reply-cap surface); the live
`.replyRecv` routes through `API.replyRecvBody`, and the below-API building block
`endpointReplyRecvOnCore` is exercised in §3.5.
-/

namespace SeLe4n.Testing.SmpIpc

open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Concurrency
open SeLe4n.Testing

-- ============================================================================
-- §1 Surface anchors (elaboration-time: rename/removal breaks this suite)
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
-- SchedContext donation (SM6.A.5 / SM6.C.3) + cross-core PIP (production):
#check @applyCallDonation
#check @applyReplyDonationOnCore
#check @SeLe4n.Kernel.PriorityInheritance.propagatePipChainCrossCore
-- Capability transfer across cores (SM6.A.8, production):
#check @ipcUnwrapCaps
#check @lookupCspaceRoot
-- Info-flow-checked cross-core dispatch + its flow theorems (production):
#check @endpointCallCrossCoreDispatchChecked_flow_denied
#check @endpointCallCrossCoreDispatchChecked_flow_allowed
#check @endpointReplyCrossCoreDispatchChecked_flow_denied
#check @endpointReplyCrossCoreDispatchChecked_flow_allowed
#check @securityFlowsTo
#check @LabelingContext.threadLabelOf
-- Live API dispatch (`.call` through CSpace cap resolution, production):
#check @dispatchSyscall
#check @dispatchSyscallChecked
-- Cancellation × IPC composition (SM6.E, production):
#check @cancelIpcBlockingOnCore
#check @Lifecycle.Suspend.suspendThreadOnCore

-- ============================================================================
-- §2 Elaboration-time witnesses (headline theorems applied to typed inputs)
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

/-- SM6.A info-flow gate: a disallowed caller→endpoint flow rejects the checked
cross-core call before any state change (fail-closed). -/
example (ctx : LabelingContext) (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState)
    (hDeny : securityFlowsTo (ctx.threadLabelOf caller) (ctx.endpointLabelOf endpointId) = false) :
    endpointCallCrossCoreDispatchChecked ctx endpointId caller msg endpointRights
        receiverSlotBase executingCore st = (st, .error .flowDenied) :=
  endpointCallCrossCoreDispatchChecked_flow_denied ctx endpointId caller msg endpointRights
    receiverSlotBase executingCore st hDeny

/-- SM6.C info-flow gate: when the replier→target flow is permitted, the checked
cross-core reply is exactly the unchecked one (the guard is a pure precondition). -/
example (ctx : LabelingContext) (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState)
    (hAllow : securityFlowsTo (ctx.threadLabelOf replier) (ctx.threadLabelOf target) = true) :
    endpointReplyCrossCoreDispatchChecked ctx replier target msg executingCore st
      = endpointReplyCrossCoreDispatch replier target msg executingCore st :=
  endpointReplyCrossCoreDispatchChecked_flow_allowed ctx replier target msg executingCore st hAllow

-- ============================================================================
-- §3 Runtime scenarios — the deterministic 4-thread / 4-core IPC fixture
-- ============================================================================

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then IO.println s!" PASS: {name}"
  else
    IO.println s!" FAIL: {name}"
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
`Recv`, each thread runnable on its **own** core's run queue. Client A is
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

-- Labelled plumbing: a failed step names itself, so a pipeline break reports the
-- exact failing transition instead of a blanket "pipeline succeeded: FAIL".
private def stepPair {α : Type} (label : String)
    (r : SystemState × Except KernelError α) : Except String (SystemState × α) :=
  match r with
  | (st, .ok a) => .ok (st, a)
  | (_, .error _) => .error label

private def stepExcept {α : Type} (label : String) (r : Except KernelError α) :
    Except String α :=
  match r with
  | .ok a => .ok a
  | .error _ => .error label

/-- The full interleaved 4-thread round-trip pipeline (every intermediate state
+ every surfaced SGI). Both servers block on their endpoints from their own
cores; both clients call cross-core; each SGI is handled on its target core;
both servers reply cross-core; each reply SGI is handled on its target core. -/
private structure RoundTrip where
  afterRecv : SystemState
  afterCallA : SystemState
  sgiCallA : Option (CoreId × SgiKind)
  afterSgiB : SystemState
  afterCallC : SystemState
  sgiCallC : Option (CoreId × SgiKind)
  afterSgiD : SystemState
  afterReplyB : SystemState
  sgiReplyB : Option (CoreId × SgiKind)
  afterSgiA : SystemState
  afterReplyD : SystemState
  sgiReplyD : Option (CoreId × SgiKind)
  afterSgiC : SystemState

/-- The full interleaved 4-thread round trip, computed once with **step
attribution** — each step names itself, so a break reports the exact failing
transition (`.error "<step>"`) rather than a blanket pipeline failure. -/
private def roundTripE : Except String RoundTrip := do
  let (st1, _) ← stepPair "step1: server B recv on core 1"
    (endpointReceiveDualOnCore epAB serverB (some replyB) c1 stFourCore)
  let (afterRecv, _) ← stepPair "step2: server D recv on core 3"
    (endpointReceiveDualOnCore epCD serverD (some replyD) c3 st1)
  let (afterCallA, sgiCallA) ← stepPair "step3: client A call on core 0"
    (endpointCallOnCore epAB clientA callMsgA c0 afterRecv)
  let afterSgiB ← stepExcept "step4: core 1 SGI handler" (handleRescheduleSgiOnCore afterCallA c1)
  let (afterCallC, sgiCallC) ← stepPair "step5: client C call on core 2"
    (endpointCallOnCore epCD clientC callMsgC c2 afterSgiB)
  let afterSgiD ← stepExcept "step6: core 3 SGI handler" (handleRescheduleSgiOnCore afterCallC c3)
  let (afterReplyB, sgiReplyB) ← stepPair "step7: server B reply on core 1"
    (endpointReplyOnCore serverB clientA replyMsgB c1 afterSgiD)
  let afterSgiA ← stepExcept "step8: core 0 SGI handler" (handleRescheduleSgiOnCore afterReplyB c0)
  let (afterReplyD, sgiReplyD) ← stepPair "step9: server D reply on core 3"
    (endpointReplyOnCore serverD clientC replyMsgD c3 afterSgiA)
  let afterSgiC ← stepExcept "step10: core 2 SGI handler" (handleRescheduleSgiOnCore afterReplyD c2)
  pure { afterRecv := afterRecv, afterCallA := afterCallA, sgiCallA := sgiCallA,
         afterSgiB := afterSgiB, afterCallC := afterCallC, sgiCallC := sgiCallC,
         afterSgiD := afterSgiD, afterReplyB := afterReplyB, sgiReplyB := sgiReplyB,
         afterSgiA := afterSgiA, afterReplyD := afterReplyD, sgiReplyD := sgiReplyD,
         afterSgiC := afterSgiC }

/-- The round trip as an `Option` (for the §9 golden-trace emitters). -/
private def roundTrip? : Option RoundTrip := roundTripE.toOption

/-- The cross-core send/receive rendezvous: blocked sender E (homed core 2) is
woken by a receive executing on core 1. Returns (post-state, popped sender,
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
-- §3.1 The 2-thread cross-core IPC round trip (acceptance gate)
-- ============================================================================

private def runTwoThreadRoundTripChecks : IO Unit := do
  IO.println "--- §3.1 two-thread cross-core IPC round trip (client A core 0 ↔ server B core 1) ---"
  match roundTripE with
  | .error step => assertBool s!"round-trip pipeline succeeded ({step} failed)" false
  | .ok rt =>
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
-- §3.2 The 4-thread SMP rendezvous (acceptance gate)
-- ============================================================================

private def runFourThreadRendezvousChecks : IO Unit := do
  IO.println "--- §3.2 four-thread SMP rendezvous (pairs 0↔1 and 2↔3, interleaved) ---"
  match roundTripE with
  | .error step => assertBool s!"rendezvous pipeline succeeded ({step} failed)" false
  | .ok rt =>
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
    -- Read ALL FOUR currents from the FINAL rendezvous state (`afterSgiC`), not
    -- from each core's earlier snapshot: a later cross-core step accidentally
    -- clearing or switching another core's current slot must fail this gate.
    assertBool "terminal placement: every thread current on its own core (final state afterSgiC)"
      (rt.afterSgiC.scheduler.currentOnCore c0 == some clientA
        && rt.afterSgiC.scheduler.currentOnCore c1 == some serverB
        && rt.afterSgiC.scheduler.currentOnCore c2 == some clientC
        && rt.afterSgiC.scheduler.currentOnCore c3 == some serverD)

-- ============================================================================
-- §3.3 Cross-core send/receive rendezvous (sender woken to its home core)
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
-- §3.4 Client-first ordering (blockedOnCall, then the server's receive)
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
-- §3.5 Server steady-state: replyRecv (reply leg + receive leg, SGI union)
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
-- §3.6 Fail-closed error paths (pre-state returned on every error)
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
-- §3.7 2PL lock-set discipline on the live pipeline states
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
    -- Exact resolved footprint size: on this rendezvous state the footprint is
    -- exactly the five declared locks — caller TCB (W), sender CNode (R),
    -- endpoint (W), woken-receiver TCB (W), server-first reply (W); no donated
    -- SC (the client is `.unbound`). Pinning the exact size catches a regression
    -- that silently adds or drops a lock, which a `≤` bound would not.
    assertBool "state-resolved call footprint has exactly 5 locks (caller/cnode/ep/receiver/reply)"
      (decide (callLs.pairs.length = 5))
    assertBool "call lock-set size within maxLockSetSize"
      (decide (callLs.pairs.length ≤ maxLockSetSize))
    -- SM5.J (plan §4.1): an IPC op's lock WCRT is |lockSet| · 3 · tCs (tCs = 60µs).
    -- The 5-lock call footprint is 5·3·60 = 900µs, which genuinely fits the 1 ms
    -- (1000µs) per-core timer-tick budget — a real timing property (a 6th lock
    -- would be 1080µs and blow the budget), not the trivially-true `≤ max · c`.
    assertBool "call lock-set WCRT (900µs) fits the 1 ms timer-tick budget"
      (decide (callLs.pairs.length * (3 * 60) < 1000))
    assertBool "call lock-set WCRT equals |footprint| · 3 · tCs exactly (= 900µs)"
      (decide (callLs.pairs.length * (3 * 60) = 900))
    -- The reply footprint covers the caller-TCB write (the reply-state lifecycle).
    let replyLs := lockSet_endpointReplyOnCore stWait serverB cnRoot clientA
    assertBool "state-resolved reply lock-set kinds all permitted"
      (decide (∀ p ∈ replyLs.pairs, p.fst.kind ∈ permittedKinds .reply))
    assertBool "the reply target's TCB write lock is in the reply footprint"
      (decide ((tcbLock clientA, AccessMode.write) ∈ replyLs.pairs))

-- ============================================================================
-- §3.8 Live-dispatch coherence (determineExecutingCore + full dispatch)
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
      AccessRightSet.empty (SeLe4n.Slot.ofNat 0) c0 stWait
    assertBool "cross-core dispatch rendezvous fires the remote reschedule SGI"
      (match resDisp with
       | .ok (_, some (tgt, kind)) => decide (tgt = c1 ∧ kind = SgiKind.reschedule)
       | _ => false)
    assertBool "cross-core dispatch wakes the server with the request payload"
      (ipcStateIs stDisp serverB .ready && pendingMessageIs stDisp serverB (some callMsgA))
    assertBool "cross-core dispatch blocks the caller as blockedOnReply"
      (ipcStateIs stDisp clientA (.blockedOnReply epAB (some serverB)))

-- ============================================================================
-- §3.9 SchedContext donation round trip (call donates, reply returns)
-- ============================================================================

private def scClient : SeLe4n.SchedContextId := SchedContextId.ofNat 840
private def donClient : SeLe4n.ThreadId := ⟨841⟩ -- active, bound-SC, home boot core
private def donServer : SeLe4n.ThreadId := ⟨842⟩ -- passive (.unbound), home core 1
private def donEp : SeLe4n.ObjId := ⟨843⟩
private def donReply : SeLe4n.ReplyId := ⟨844⟩

/-- The client's own SchedContext (priority 60, above the passive server's base). -/
private def donClientSc : SchedContext :=
  { scId := scClient, budget := ⟨100⟩, period := ⟨1000⟩, priority := ⟨60⟩, deadline := ⟨0⟩,
    domain := ⟨0⟩, budgetRemaining := ⟨50⟩, boundThread := some donClient, isActive := true }

/-- A bound-SC client (prio 60) and a passive `.unbound` server homed on core 1. -/
private def stDonBase : SystemState :=
  (BootstrapBuilder.empty
    |>.withObject donEp (.endpoint {})
    |>.withObject scClient.toObjId (.schedContext donClientSc)
    |>.withObject donClient.toObjId
        (.tcb { mkTcb 841 60 none with schedContextBinding := .bound scClient })
    |>.withObject donServer.toObjId
        (.tcb { mkTcb 842 20 (some c1) with schedContextBinding := .unbound })
    |>.withObject donReply.toObjId (.reply { replyId := donReply })
    |>.withRunnable [donClient]
    |>.build)

private def runDonationChecks : IO Unit := do
  IO.println "--- §3.9 SchedContext donation round trip (call donates SC, reply returns it) ---"
  -- Pre-state: the client holds its own SC; the server is passive.
  assertBool "pre: client holds its bound SchedContext"
    (match stDonBase.getTcb? donClient with
     | some t => decide (t.schedContextBinding = .bound scClient) | none => false)
  assertBool "pre: server is passive (.unbound)"
    (match stDonBase.getTcb? donServer with
     | some t => decide (t.schedContextBinding = SchedContextBinding.unbound) | none => false)
  -- The server blocks on the endpoint; then the client calls cross-core (donating).
  match okPair (endpointReceiveDualOnCore donEp donServer (some donReply) c1 stDonBase) with
  | none => assertBool "donation setup (server recv) succeeded" false
  | some (stRecv, _) =>
    let (stCall, resCall) := endpointCallCrossCoreDispatch donEp donClient IpcMessage.empty
      AccessRightSet.empty (SeLe4n.Slot.ofNat 0) c0 stRecv
    assertBool "donating call succeeds and fires the remote reschedule SGI to core 1"
      (match resCall with
       | .ok (_, some (tgt, kind)) => decide (tgt = c1 ∧ kind = SgiKind.reschedule)
       | _ => false)
    -- Donation: the SC rebinds from the client to the passive server.
    assertBool "call donates the SC to the server (server binding = .donated scClient donClient)"
      (match stCall.getTcb? donServer with
       | some t => decide (t.schedContextBinding = .donated scClient donClient) | none => false)
    assertBool "call leaves the client SC-less (.unbound) after donating"
      (match stCall.getTcb? donClient with
       | some t => decide (t.schedContextBinding = SchedContextBinding.unbound) | none => false)
    assertBool "the donated SchedContext's boundThread moves to the server"
      (match stCall.getSchedContext? scClient with
       | some sc => decide (sc.boundThread = some donServer) | none => false)
    -- Cross-core PIP: the donated priority (60) boosts the server on its home core.
    assertBool "the server inherits the client's donated priority (pipBoost = 60)"
      (match stCall.getTcb? donServer with
       | some t => decide (t.pipBoost = some ⟨60⟩) | none => false)
    assertBool "the boosted server is enqueued on its home core 1"
      ((stCall.scheduler.runQueueOnCore c1).contains donServer)
    -- The scheduler resolves the server's EFFECTIVE priority to the donated 60
    -- (via the donated SchedContext's priority ⊔ the PIP boost) — the run-queue
    -- bucket key is the stale enqueue-time base, but selection reads the resolver.
    assertBool "the server's effective scheduling priority is the donated 60 (was base 20)"
      (match stCall.getTcb? donServer with
       | some t => decide ((resolveEffectivePrioDeadline stCall t).1 = ⟨60⟩) | none => false)
    -- Dispatch the woken donated server on its HOME core (core 1) so it is CURRENT
    -- there before the reply: `endpointReplyCrossCoreDispatch` derives the
    -- donation-return cleanup core from `determineExecutingCore st server`, so a
    -- non-current server would fall back to the boot core and never be descheduled
    -- on core 1 (leaving the now-passive server runnable there).
    match okExcept (handleRescheduleSgiOnCore stCall c1) with
    | none => assertBool "donation: core 1 handles the call wake SGI" false
    | some stDispatched =>
      assertBool "core 1's handler dispatches the woken donated server (current = server)"
        (stDispatched.scheduler.currentOnCore c1 == some donServer)
      -- The reply returns the SC to the client and descheds the now-passive server.
      let (stReply, resReply) := endpointReplyCrossCoreDispatch donServer donClient IpcMessage.empty c1 stDispatched
      assertBool "reply succeeds and wakes the client back on the boot core"
        (match resReply with | .ok _ => true | .error _ => false)
      assertBool "reply returns the SC: server passive again (.unbound)"
        (match stReply.getTcb? donServer with
         | some t => decide (t.schedContextBinding = SchedContextBinding.unbound) | none => false)
      assertBool "reply returns the SC: client bound to its own SC again (.bound scClient)"
        (match stReply.getTcb? donClient with
         | some t => decide (t.schedContextBinding = .bound scClient) | none => false)
      assertBool "the returned SchedContext's boundThread is the client again"
        (match stReply.getSchedContext? scClient with
         | some sc => decide (sc.boundThread = some donClient) | none => false)
      -- Donation-return deschedule: the now-passive server is removed from core 1
      -- (no longer current, not runnable there) via the SC return's home-core
      -- `removeRunnableOnCore` — the very thing the non-current fixture would miss.
      assertBool "donation return descheds the now-passive server from core 1"
        (stReply.scheduler.currentOnCore c1 != some donServer
          && !(stReply.scheduler.runQueueOnCore c1).contains donServer)
      -- **WS-OD OD4**: the reply-stack fields are *live* since the push landed.
      -- At OD2 this check read the other way -- the three fields stayed `none`
      -- through a whole donating call and its return, which is what made
      -- `donationChainWellFormed` vacuously true of every reachable state -- and
      -- the comment there said this is the check that fails the day the push
      -- lands.  It did, and the push landed with its chain preservation
      -- (`donateSchedContext_preserves_donationChainWellFormed`), so the
      -- assertion is inverted rather than deleted: a *depth-1* call now pushes
      -- one frame, and its return pops that frame back off.
      assertBool "OD4: the donating call pushes the caller's Reply as the stack head"
        (match stCall.getReply? donReply, stCall.getSchedContext? scClient with
         | some r, some sc =>
             decide (r.next = some (.head scClient)) && decide (r.prev = none) &&
             decide (sc.scReply = some donReply)
         | _, _ => false)
      assertBool "OD4: the donation return pops it back off, clearing the frame"
        (match stReply.getReply? donReply, stReply.getSchedContext? scClient with
         | some r, some sc =>
             decide (r.next = none) && decide (r.prev = none) &&
             decide (sc.scReply = none)
         | _, _ => false)

-- ============================================================================
-- §3.9b WS-RR RR2.19 — the donation's replenish-queue migration
-- ============================================================================
-- RR2.2 / RR2.8 / RR2.20 made all three live donation paths carry the
-- SchedContext's pending CBS replenishments across cores with it. §3.9 above
-- proves the *binding* moves; these checks prove the **replenish queue entries**
-- move with it, which is the half the SM5.H affinity invariant reads and the
-- half that was missing on the live path. Without the migration the entries sit
-- on the donor's core, where nothing drains them for a SchedContext the donee
-- now runs on.
--
-- The three paths are the cross-core `.call` (RR2.2), the `.reply` return
-- (RR2.8), and `.replyRecv`'s return-and-re-donate pair (RR2.20) — the last of
-- which the pre-SM10 audit's blocker 2 did not name.

/-- `stDonBase`'s threads with an explicit live `threadState`. `mkTcb` leaves the
field at its `.Inactive` default, which `suspendThreadOnCore` rejects outright
(`illegalState`) — so the suspend-arm fixture has to say the threads are running,
which is the state the live dispatch entry suspends from. -/
private def donClientTcbRunning : TCB :=
  { mkTcb 841 60 none with
      schedContextBinding := .bound scClient
      threadState := ThreadState.Running }

private def donServerTcbReady : TCB :=
  { mkTcb 842 20 (some c1) with threadState := ThreadState.Ready }

private def stDonRunning : SystemState :=
  { stDonBase with objects :=
      ((stDonBase.objects.insert donClient.toObjId (.tcb donClientTcbRunning)).insert
        donServer.toObjId (.tcb donServerTcbReady)) }

/-- `stDonBase` with two pending replenishments for the client's SchedContext
already on the client's home core (the boot core), and one unrelated
SchedContext's entry on the *server's* home core — the bystander that must not
move. Two entries rather than one so a migration that moves only the first is
visible. -/
private def scBystander : SeLe4n.SchedContextId := SchedContextId.ofNat 845

private def stDonWithReplenishments : SystemState :=
  { stDonRunning with scheduler :=
      ((stDonRunning.scheduler.setReplenishQueueOnCore c0
          (((ReplenishQueue.empty.insert scClient 100).insert scClient 200))).setReplenishQueueOnCore
        c1 (ReplenishQueue.empty.insert scBystander 300)) }

/-- The delegated receiver of the RR2.20 `.replyRecv` rendezvous check: a passive
thread homed on a **third** core, so the return hop (core 1 → core 0) and the
re-donation hop (core 0 → core 2) land in distinguishable places. -/
private def donDelegate : SeLe4n.ThreadId := ⟨846⟩

private def donDelegateTcb : TCB :=
  { mkTcb 846 30 (some c2) with threadState := ThreadState.Ready }

/-- WS-RR RR2.20 (PR #885 review round 1): the **distinct queued caller**.

The rendezvous arm below re-donates *this* thread's SchedContext rather than the
one being replied to. That matters because `replyRecvPostReceiveDonation` branches on
`nextThread`'s `.blockedOnReply` — and the thread being replied to is *already*
`.blockedOnReply` from its own outgoing call, so passing it as `nextThread` lets
the branch fire for a reason the live `.replyRecv` ordering would not produce
(there the reply leg unblocks that thread before the receive leg dequeues the
next request). With a distinct caller the two hops move **two different
SchedContexts**, so neither can stand in for the other: the return hop is
`scClient` core 1 → core 0, and the re-donation hop is `scCaller2` core 3 →
core 2.

Homed on core 3 so its hop is distinguishable from every other core in play. -/
private def scCaller2 : SeLe4n.SchedContextId := SchedContextId.ofNat 847
private def donCaller2 : SeLe4n.ThreadId := ⟨848⟩

private def donCaller2Sc : SchedContext :=
  { scId := scCaller2, budget := ⟨100⟩, period := ⟨1000⟩, priority := ⟨40⟩, deadline := ⟨0⟩,
    domain := ⟨0⟩, budgetRemaining := ⟨50⟩, boundThread := some donCaller2, isActive := true }

/-- The queued caller's own reply object -- the frame **WS-OD OD4.1**'s push
mounts on its context's stack when the receive leg hands that context on.  A
`Call` caller always holds one (the rendezvous linked it), and since OD4 the
donation refuses a donor that does not: a donation with no stack frame is what
lets a later pop clear an outer caller's frame. -/
private def donCaller2Reply : SeLe4n.ReplyId := ⟨849⟩

/-- The queued caller as the endpoint left it: blocked awaiting a reply from the
server, still holding its own SchedContext, and linked to its own Reply. -/
private def donCaller2Tcb : TCB :=
  { mkTcb 848 40 (some c3) with
      schedContextBinding := .bound scCaller2
      ipcState := .blockedOnReply donEp (some donServer)
      replyObject := some donCaller2Reply
      threadState := ThreadState.Ready }

/-- **WS-RM (`v0.35.6`)**: the two donation steps `replyRecvBody` performs, run
back to back with the receive leg elided.

`replyRecvBody` sequences `replyRecvPopDonation` (between the two legs, which is
seL4-MCS's own `doReplyTransfer` -> `reply_remove` -> `receiveIPC` order) and
`replyRecvPostReceiveDonation` (after the receive leg), passing the popped
context from the first to the second.  The migration facts below are about that
pair, and this driver runs them exactly as the arm does; the receive leg is
elided because these checks supply `nextThread` directly rather than dequeuing
it, which is the same elision the pre-WS-RM fused step allowed.

**WS-HP HP4.5**: the pop is keyed on the reply capability's frame (`rid`) and the
caller it answers (`prevCaller`), as the arm keys it, rather than on the recorded
server's `.donated` binding.  The parameters mirror `replyRecvBody`'s own, because
a driver that re-derives what the arm is handed is testing its own derivation. -/
private def runReplyRecvDonationSteps (tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (prevCaller recordedServer nextThread : SeLe4n.ThreadId)
    (serverCore : CoreId) (st : SystemState) : Except KernelError SystemState :=
  match replyRecvPopDonation rid prevCaller st with
  | .error e => .error e
  | .ok (returned?, st1) =>
      match replyRecvPostReceiveDonation tid recordedServer nextThread serverCore returned?
          st1 with
      | .error e => .error e
      | .ok ((), st2) => .ok st2

private def replenishEntriesOn (st : SystemState) (c : CoreId) :
    List (SeLe4n.SchedContextId × Nat) :=
  (st.scheduler.replenishQueueOnCore c).entries

private def replenishCountFor (st : SystemState) (c : CoreId)
    (scId : SeLe4n.SchedContextId) : Nat :=
  ((replenishEntriesOn st c).filter (fun e => e.1 == scId)).length

private def runDonationMigrationChecks : IO Unit := do
  IO.println "--- §3.9b WS-RR RR2.19 / RR2.20: the donation migrates the CBS replenish queue ---"
  assertBool "pre: both of the client SC's replenishments sit on its home core 0"
    (decide (replenishCountFor stDonWithReplenishments c0 scClient = 2))
  assertBool "pre: the server's home core 1 holds only the bystander SC's entry"
    (decide (replenishCountFor stDonWithReplenishments c1 scClient = 0)
      && decide (replenishCountFor stDonWithReplenishments c1 scBystander = 1))
  match okPair (endpointReceiveDualOnCore donEp donServer (some donReply) c1
      stDonWithReplenishments) with
  | none => assertBool "migration setup (server recv) succeeded" false
  | some (stRecv, _) =>
    assertBool "the receive leaves the replenish queues alone"
      (decide (replenishCountFor stRecv c0 scClient = 2)
        && decide (replenishCountFor stRecv c1 scClient = 0))
    let (stCall, resCall) := endpointCallCrossCoreDispatch donEp donClient IpcMessage.empty
      AccessRightSet.empty (SeLe4n.Slot.ofNat 0) c0 stRecv
    assertBool "the donating call succeeds"
      (match resCall with | .ok _ => true | .error _ => false)
    -- RR2.2: donor home (core 0) → donee home (core 1).
    assertBool "the call drains the donated SC's replenishments off the donor's core 0"
      (decide (replenishCountFor stCall c0 scClient = 0))
    assertBool "the call lands BOTH replenishments on the donee's home core 1"
      (decide (replenishCountFor stCall c1 scClient = 2))
    assertBool "the migration leaves the bystander SchedContext's entry where it was"
      (decide (replenishCountFor stCall c1 scBystander = 1))
    assertBool "the migration preserves each replenishment's eligibility time"
      (decide (((replenishEntriesOn stCall c1).filter (fun e => e.1 == scClient)).map (·.2)
        = [100, 200]))
    match okExcept (handleRescheduleSgiOnCore stCall c1) with
    | none => assertBool "migration: core 1 handles the call wake SGI" false
    | some stDispatched =>
      let (stReply, resReply) :=
        endpointReplyCrossCoreDispatch donServer donClient IpcMessage.empty c1 stDispatched
      assertBool "the returning reply succeeds"
        (match resReply with | .ok _ => true | .error _ => false)
      -- RR2.8: the mirror — replier home (core 1) → original-owner home (core 0).
      assertBool "the reply drains the returned SC's replenishments off the server's core 1"
        (decide (replenishCountFor stReply c1 scClient = 0))
      assertBool "the reply lands both replenishments back on the owner's home core 0"
        (decide (replenishCountFor stReply c0 scClient = 2))
      assertBool "the round trip leaves the bystander entry untouched throughout"
        (decide (replenishCountFor stReply c1 scBystander = 1))
      assertBool "the round trip restores the original eligibility times"
        (decide (((replenishEntriesOn stReply c0).filter (fun e => e.1 == scClient)).map (·.2)
          = [100, 200]))
    -- RR2.20: the THIRD live donation path. `.replyRecv` returns the recorded
    -- server's donated context and, when the receive rendezvoused with a queued
    -- `Call`, immediately re-donates the next caller's — two hand-offs, neither
    -- of which migrated before RR2.20. Both arms are exercised, because the
    -- round-trip arm alone cannot tell "both migrations ran" from "neither did":
    -- returning to the owner and re-donating to the same server lands the entries
    -- back where they started.
    -- **WS-HP HP4.5**: the driver's pop is keyed on the frame, so assert the
    -- resolver answers before relying on it -- a pop that silently found no head
    -- would be the identity, and every migration check below would then pass by
    -- measuring nothing.  The binding-driven reading coincides here (the recorded
    -- server *is* the holder on this state), which is why the two arms agreed
    -- before HP4 and why a witness has to name which one it exercises.
    assertBool "HP4.5: the answered frame names the holder and the donated context"
      (replyFrameHeadHolder? stCall donReply == some (scClient, donServer))
    assertBool "HP4.5: ...and the binding-driven reading agrees on this state"
      (replyDonationReturn? stCall donServer == some (scClient, donClient))
    match runReplyRecvDonationSteps donServer donReply donClient donServer donServer c1
        stCall with
    | .error _ => assertBool "the .replyRecv return-only arm succeeds" false
    | .ok stRet =>
      assertBool "the .replyRecv return-only arm succeeds" true
      assertBool "the .replyRecv return drains the SC's replenishments off the server's core 1"
        (decide (replenishCountFor stRet c1 scClient = 0))
      assertBool "the .replyRecv return lands them on the original owner's home core 0"
        (decide (replenishCountFor stRet c0 scClient = 2))
      assertBool "the .replyRecv return leaves the bystander SchedContext alone"
        (decide (replenishCountFor stRet c1 scBystander = 1))
      assertBool "the .replyRecv return preserves each replenishment's eligibility time"
        (decide (((replenishEntriesOn stRet c0).filter (fun e => e.1 == scClient)).map (·.2)
          = [100, 200]))
    -- The rendezvous arm: a *delegated* reply cap, so the next caller's context
    -- is re-donated to a receiver on a third core. Two migrations in one
    -- transition — core 1 → core 0 on the return, core 0 → core 2 on the
    -- re-donation — and the third core is what makes them distinguishable.
    let stCallD : SystemState :=
      { stCall with objects := stCall.objects.insert donDelegate.toObjId (.tcb donDelegateTcb) }
    match runReplyRecvDonationSteps donDelegate donReply donClient donServer donClient c1
        stCallD with
    | .error _ => assertBool "the .replyRecv rendezvous arm succeeds" false
    | .ok stRr =>
      assertBool "the .replyRecv rendezvous arm succeeds" true
      assertBool "the re-donated SC's replenishments leave the replier's core 1"
        (decide (replenishCountFor stRr c1 scClient = 0))
      assertBool "they do not stay parked on the original owner's core 0 either"
        (decide (replenishCountFor stRr c0 scClient = 0))
      assertBool "they land on the delegated receiver's home core 2"
        (decide (replenishCountFor stRr c2 scClient = 2))
      assertBool "the two-hop migration leaves the bystander SchedContext alone"
        (decide (replenishCountFor stRr c1 scBystander = 1))
      assertBool "the two-hop migration preserves each replenishment's eligibility time"
        (decide (((replenishEntriesOn stRr c2).filter (fun e => e.1 == scClient)).map (·.2)
          = [100, 200]))
    -- RR2.20 (PR #885 review round 1): the same rendezvous with a **distinct**
    -- queued caller. The arm above re-donates the replied-to thread's own
    -- context, so it cannot tell "the re-donation branch fired because a new
    -- request was dequeued" from "it fired because that thread's outgoing call
    -- was still parked `.blockedOnReply`". Here the returned context
    -- (`scClient`) and the re-donated one (`scCaller2`) are different
    -- SchedContexts homed on different cores, so each hop is pinned
    -- independently and neither can stand in for the other.
    let stCallQ : SystemState :=
      { stCall with
          objects := (((stCall.objects.insert donDelegate.toObjId (.tcb donDelegateTcb)).insert
            donCaller2.toObjId (.tcb donCaller2Tcb)).insert scCaller2.toObjId
              (.schedContext donCaller2Sc)).insert donCaller2Reply.toObjId
              (.reply { replyId := donCaller2Reply, caller := some donCaller2 })
          scheduler := stCall.scheduler.setReplenishQueueOnCore c3
            ((ReplenishQueue.empty.insert scCaller2 400).insert scCaller2 500) }
    assertBool "pre: the queued caller's SC holds both replenishments on its home core 3"
      (decide (replenishCountFor stCallQ c3 scCaller2 = 2))
    match runReplyRecvDonationSteps donDelegate donReply donClient donServer donCaller2 c1
        stCallQ with
    | .error _ => assertBool "the .replyRecv distinct-caller rendezvous arm succeeds" false
    | .ok stQ =>
      assertBool "the .replyRecv distinct-caller rendezvous arm succeeds" true
      -- The return hop, on the replied-to thread's context.
      assertBool "return hop: the returned SC leaves the server's core 1"
        (decide (replenishCountFor stQ c1 scClient = 0))
      assertBool "return hop: the returned SC lands on its owner's home core 0"
        (decide (replenishCountFor stQ c0 scClient = 2))
      -- The re-donation hop, on the *queued caller's* context — a SchedContext
      -- that took no part in the return.
      assertBool "re-donation hop: the queued caller's SC leaves its home core 3"
        (decide (replenishCountFor stQ c3 scCaller2 = 0))
      assertBool "re-donation hop: it lands on the delegated receiver's home core 2"
        (decide (replenishCountFor stQ c2 scCaller2 = 2))
      assertBool "the delegate holds the QUEUED CALLER's context, owner recorded"
        (match stQ.getTcb? donDelegate with
         | some t => decide (t.schedContextBinding = .donated scCaller2 donCaller2)
         | none => false)
      assertBool "the two contexts never cross: the returned SC does not reach core 2"
        (decide (replenishCountFor stQ c2 scClient = 0))
      assertBool "the distinct-caller hops leave the bystander SchedContext alone"
        (decide (replenishCountFor stQ c1 scBystander = 1))
      assertBool "the distinct-caller hops preserve each replenishment's eligibility time"
        (decide (((replenishEntriesOn stQ c2).filter (fun e => e.1 == scCaller2)).map (·.2)
          = [400, 500]))
      -- **PR #895 review round 8**: the recorded server is DESCHEDULED here.
      -- `tid` is the delegate, so the queued caller's context went to *it* and
      -- the recorded server received nothing — while the pop had already made
      -- the server `.unbound`.  Left on its run queue it would be selected at
      -- its legacy TCB priority and charged to no reservation, which is WS-OD
      -- OD3.6's defect on the delegated path.  `passiveServerIdle` structurally
      -- cannot see it: that conjunct is conditioned on the thread already being
      -- descheduled, so an unbound thread still queued satisfies it vacuously.
      assertBool "pre: the recorded server is queued on its own core 1"
        ((stCallQ.scheduler.runQueueOnCore c1).contains donServer)
      -- **PR #895 review round 10**: and it is QUEUED rather than current, which
      -- is the shape round 9's fix could not actually handle.  That cut took the
      -- core from the caller's `serverCore`, which production computes as
      -- `determineExecutingCore st recordedServer` — a core the server is
      -- *current* on, else `bootCoreId` — so a preempted server was descheduled
      -- on core 0's queue while it sat on core 1's.
      --
      -- This witness did not catch it because the harness passes `serverCore`
      -- BY HAND, supplying the very answer production was getting wrong.  The
      -- deschedule resolves its own core now (`placedCoreOf?`), so there is no
      -- parameter left for a test to supply and this assertion exercises the
      -- resolver rather than the fixture's opinion of it.
      assertBool "pre: ...and NOT current there — genuinely preempted"
        (stCallQ.scheduler.currentOnCore c1 != some donServer)
      assertBool "pre: ...so the retired proxy would have answered the boot core"
        (decide (determineExecutingCore stCallQ donServer = Concurrency.bootCoreId)
          && decide (c1 != Concurrency.bootCoreId))
      assertBool "pre: ...while the resolver answers core 1"
        (decide (placedCoreOf? stCallQ donServer = some c1))
      assertBool "the delegated rendezvous deschedules the recorded server"
        (!(stQ.scheduler.runQueueOnCore c1).contains donServer)
      assertBool "...and it is not left as core 1's current thread either"
        (stQ.scheduler.currentOnCore c1 != some donServer)
      assertBool "...which matters because the pop left it `.unbound`"
        (match stQ.getTcb? donServer with
         | some t => decide (t.schedContextBinding = SchedContextBinding.unbound)
         | none => false)
    -- ...and the CONTRAST, which is what stops the fix from over-descheduling:
    -- the same rendezvous NOT delegated.  `tid` is the recorded server, so the
    -- queued caller's context is donated to it and it must keep running — the
    -- passive-server steady state.  An unconditional deschedule passes the
    -- delegated case above and fails this one.
    match runReplyRecvDonationSteps donServer donReply donClient donServer donCaller2 c1
        stCallQ with
    | .error _ => assertBool "the .replyRecv non-delegated rendezvous arm succeeds" false
    | .ok stN =>
      assertBool "the .replyRecv non-delegated rendezvous arm succeeds" true
      assertBool "the non-delegated server KEEPS its place on core 1"
        ((stN.scheduler.runQueueOnCore c1).contains donServer)
      assertBool "...because it received the queued caller's context itself"
        (match stN.getTcb? donServer with
         | some t => decide (t.schedContextBinding = .donated scCaller2 donCaller2)
         | none => false)

-- ============================================================================
-- §3.10 Capability transfer across cores (ipcUnwrapCaps, grant-gated)
-- ============================================================================

private def capCallerCn : SeLe4n.ObjId := ⟨850⟩ -- the caller's own CSpace root
private def capEp : SeLe4n.ObjId := ⟨851⟩
private def capCaller : SeLe4n.ThreadId := ⟨852⟩
private def capServer : SeLe4n.ThreadId := ⟨853⟩ -- home core 1
private def capReply : SeLe4n.ReplyId := ⟨854⟩
private def capServerCn : SeLe4n.ObjId := ⟨855⟩ -- the server's DISTINCT CSpace root
private def capMarkerObj : SeLe4n.ObjId := ⟨856⟩ -- the object the transferred cap targets
private def recvSlot : SeLe4n.Slot := SeLe4n.Slot.ofNat 1
/-- The capability the Call transfers — a distinctive **read** cap on a marker
object (not the endpoint), so it is uniquely identifiable in whichever CSpace it
lands, letting the test prove it reaches the *receiver's* root and only there. -/
private def payloadCap : Capability :=
  { target := .object capMarkerObj, rights := AccessRightSet.ofList [.read] }
/-- The caller's slot the payload capability is resolved from. The transfer
records its edge against that slot's derivation node, so revoking the slot is
what must reach the copy installed in the server's CSpace — and the slot has to
be a real one, since a node no slot points at is the orphan shape the transfer
declines. -/
private def payloadSrcSlot : SeLe4n.Slot := SeLe4n.Slot.ofNat 2
/-- 4 caps > maxExtraCaps (3): rejected at the send boundary, before any source
is resolved, so a bare node id is the honest fixture here. -/
private def tooManyCapsMsg : IpcMessage :=
  { registers := #[], caps := Array.replicate (maxExtraCaps + 1)
      (TransferCap.fromNode Capability.null 0), badge := none }

/-- **Distinct** single-level CNodes (`depth=4, radixWidth=4, guard=0`) for the
caller (`capCallerCn`) and the server (`capServerCn`), both empty at the receive
slot. Separate roots are what let the test prove the transferred cap lands in
the **server's** CSpace — not a shared/caller root — exercising the receiver-root
plumbing in `endpointCallWithCapsOnCore` / `ipcUnwrapCaps`.

The caller holds the payload at `payloadSrcSlot` (2), away from `recvSlot` (1)
and slot 0, so the no-leak-back assertions still read slots the transfer must
leave empty. -/
private def stCapBase : SystemState :=
  (BootstrapBuilder.empty
    |>.withObject capEp (.endpoint {})
    |>.withObject capCallerCn (.cnode
        { depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
          slots := SeLe4n.UniqueSlotMap.ofListWF [(payloadSrcSlot, payloadCap)] })
    |>.withObject capServerCn (.cnode
        { depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
          slots := SeLe4n.UniqueSlotMap.ofListWF [] })
    |>.withObject capCaller.toObjId (.tcb { mkTcb 852 40 none with cspaceRoot := capCallerCn })
    |>.withObject capServer.toObjId (.tcb { mkTcb 853 50 (some c1) with cspaceRoot := capServerCn })
    |>.withObject capReply.toObjId (.reply { replyId := capReply })
    |>.withRunnable [capCaller]
    |>.build)

/-- Mint the payload slot's derivation node exactly as `resolveExtraCaps` does,
and keep the state that binding lives in: the message names the NODE, and the
transfer installs only while some slot still points at it. -/
private def capSourceMint : SeLe4n.Model.CdtNodeId × SystemState :=
  SystemState.ensureCdtNodeForSlot stCapBase { cnode := capCallerCn, slot := payloadSrcSlot }
/-- The base state with the payload slot's derivation node bound. -/
private def stCapBound : SystemState := capSourceMint.2
private def capMsg : IpcMessage :=
  { registers := #[],
    caps := #[{ cap := payloadCap, srcNode := capSourceMint.1 }],
    badge := none }

/-- `true` iff a transfer summary reports a cap installed into CNode `cn` — the
receiver-root check (the `.installed` result carries the *receiver's* CSpace root
per `ipcTransferSingleCap`). -/
private def summaryInstalledInto (s : CapTransferSummary) (cn : SeLe4n.ObjId) : Bool :=
  s.results.any (fun r => match r with | .installed c _ => c == cn | _ => false)
/-- `true` iff every result in a transfer summary is grant-denied. -/
private def summaryAllGrantDenied (s : CapTransferSummary) : Bool :=
  !s.results.isEmpty && s.results.all (fun r => match r with | .grantDenied => true | _ => false)
/-- Read the capability in slot `slot` of CNode `cn` (if it holds one). -/
private def cnodeSlotCap (st : SystemState) (cn : SeLe4n.ObjId) (slot : SeLe4n.Slot) :
    Option Capability :=
  match st.objects[cn]? with
  | some (.cnode c) => c.slots[slot]?
  | _ => none
/-- `true` iff CNode `cn`'s slot `slot` holds the transferred payload cap
**intact** — full value equality (target AND rights AND badge), so a transfer
that widened the rights (e.g. added `.write`/`.grant`) or otherwise mutated the
cap while preserving the target is caught, not just target-equality. -/
private def slotHoldsPayload (st : SystemState) (cn : SeLe4n.ObjId) (slot : SeLe4n.Slot) : Bool :=
  match cnodeSlotCap st cn slot with
  | some c => decide (c = payloadCap)
  | none => false

private def runCapTransferChecks : IO Unit := do
  IO.println "--- §3.10 capability transfer across cores (ipcUnwrapCaps, receiver-root, grant-gated) ---"
  match okPair (endpointReceiveDualOnCore capEp capServer (some capReply) c1 stCapBound) with
  | none => assertBool "cap-transfer setup (server recv) succeeded" false
  | some (stRecv, _) =>
    -- WITH grant: the carried cap is installed into the SERVER's CSpace root.
    let (stGrant, resGrant) := endpointCallWithCapsOnCore capEp capCaller capMsg
      (AccessRightSet.ofList [.write, .grant]) recvSlot c0 stRecv
    assertBool "a granted cross-core Call installs the transferred cap into the SERVER's CSpace root"
      (match resGrant with
       | .ok (summary, _) => summaryInstalledInto summary capServerCn
       | .error _ => false)
    assertBool "the transferred cap actually lands in the server's receive slot"
      (slotHoldsPayload stGrant capServerCn recvSlot)
    -- Receiver-root plumbing: the cap does NOT land in the CALLER's CSpace
    -- (a regression writing back to the caller/shared root would fail here).
    assertBool "the transferred cap does NOT land in the caller's CSpace (no leak-back)"
      (!slotHoldsPayload stGrant capCallerCn recvSlot
        && !slotHoldsPayload stGrant capCallerCn (SeLe4n.Slot.ofNat 0))
    -- WITHOUT grant: the transfer is denied and the server's CSpace is untouched.
    let (stNoGrant, resNoGrant) := endpointCallWithCapsOnCore capEp capCaller capMsg
      (AccessRightSet.ofList [.write]) recvSlot c0 stRecv
    assertBool "an ungranted cross-core Call denies the transfer (summary = grantDenied)"
      (match resNoGrant with
       | .ok (summary, _) => summaryAllGrantDenied summary
       | .error _ => false)
    assertBool "an ungranted Call leaves the server's receive slot empty (nothing installed)"
      ((cnodeSlotCap stNoGrant capServerCn recvSlot).isNone)
    -- The grant gate is exactly the endpoint cap's `.grant` right.
    assertBool "the grant gate reads the endpoint cap's `.grant` right"
      ((AccessRightSet.ofList [.write, .grant]).mem .grant
        && !(AccessRightSet.ofList [.write]).mem .grant)
  -- Oversized cap payload (4 > maxExtraCaps): rejected at the send boundary.
  assertBool "a 4-cap message exceeds maxExtraCaps"
    (decide (tooManyCapsMsg.caps.size > maxExtraCaps))
  assertBool "an over-capped cross-core call fails with ipcMessageTooManyCaps"
    (match (endpointCallOnCore capEp capCaller tooManyCapsMsg c0 stCapBase).2 with
     | .error .ipcMessageTooManyCaps => true | _ => false)

-- ============================================================================
-- §3.11 Info-flow-checked cross-core dispatch (flow-allowed vs flow-denied)
-- ============================================================================

private def lowLabel : SecurityLabel := { confidentiality := .low, integrity := .untrusted }
private def highLabel : SecurityLabel := { confidentiality := .high, integrity := .trusted }

/-- Call gate is `caller → endpoint`; DENY = HIGH caller (client A) → LOW endpoint. -/
private def callDeniedCtx : LabelingContext :=
  { objectLabelOf := fun _ => lowLabel
    threadLabelOf := fun t => if t == clientA then highLabel else lowLabel
    endpointLabelOf := fun _ => lowLabel
    serviceLabelOf := fun _ => lowLabel }
/-- Everything public ⇒ every flow permitted (reflexive `securityFlowsTo`). -/
private def allPublicCtx : LabelingContext :=
  { objectLabelOf := fun _ => lowLabel, threadLabelOf := fun _ => lowLabel,
    endpointLabelOf := fun _ => lowLabel, serviceLabelOf := fun _ => lowLabel }
/-- Reply gate is `replier → target`; DENY = HIGH replier (server B) → LOW target. -/
private def replyDeniedCtx : LabelingContext :=
  { objectLabelOf := fun _ => lowLabel
    threadLabelOf := fun t => if t == serverB then highLabel else lowLabel
    endpointLabelOf := fun _ => lowLabel
    serviceLabelOf := fun _ => lowLabel }

private def runFlowCheckedChecks : IO Unit := do
  IO.println "--- §3.11 info-flow-checked cross-core dispatch (allowed vs flowDenied) ---"
  match roundTripE with
  | .error step => assertBool s!"info-flow fixture ({step} failed)" false
  | .ok rt =>
    -- (a) Call gate. Fixture: rt.afterRecv (server B waiting on epAB).
    -- DENIED (high client A → low endpoint): fail-closed — the WHOLE affected
    -- footprint (endpoint, waiting server, caller, reply object) and the two
    -- involved cores' run queues are unchanged from the pre-state `rt.afterRecv`,
    -- so a regression that dequeues the server or mutates state before returning
    -- `.flowDenied` fails here, not just an endpoint-object check.
    let (stDenied, resDenied) := endpointCallCrossCoreDispatchChecked callDeniedCtx epAB clientA
      callMsgA AccessRightSet.empty (SeLe4n.Slot.ofNat 0) c0 rt.afterRecv
    assertBool "a high→low call is denied with .flowDenied"
      (match resDenied with | .error .flowDenied => true | _ => false)
    assertBool "the denied call leaves the whole footprint unchanged (endpoint/server/caller/reply)"
      (stDenied.objects[epAB]? == rt.afterRecv.objects[epAB]?
        && stDenied.objects[serverB.toObjId]? == rt.afterRecv.objects[serverB.toObjId]?
        && stDenied.objects[clientA.toObjId]? == rt.afterRecv.objects[clientA.toObjId]?
        && stDenied.objects[replyB.toObjId]? == rt.afterRecv.objects[replyB.toObjId]?)
    assertBool "the denied call leaves cores 0/1 run queues unchanged"
      ((stDenied.scheduler.runQueueOnCore c0).toList == (rt.afterRecv.scheduler.runQueueOnCore c0).toList
        && (stDenied.scheduler.runQueueOnCore c1).toList == (rt.afterRecv.scheduler.runQueueOnCore c1).toList)
    assertBool "the denied call does NOT block the client (still ready)"
      (ipcStateIs stDenied clientA .ready)
    -- ALLOWED (all public): the checked dispatch equals the unchecked one — compare
    -- the SGI, the woken server, the blocked caller, the linked reply object, and the
    -- two cores' run queues (parity with the reply-side check), not just the server.
    let checkedAllowed := endpointCallCrossCoreDispatchChecked allPublicCtx epAB clientA
      callMsgA AccessRightSet.empty (SeLe4n.Slot.ofNat 0) c0 rt.afterRecv
    let uncheckedCall := endpointCallCrossCoreDispatch epAB clientA callMsgA
      AccessRightSet.empty (SeLe4n.Slot.ofNat 0) c0 rt.afterRecv
    assertBool "an allowed checked call equals the unchecked cross-core call (SGI + server/caller/reply/queues)"
      ((match checkedAllowed.2, uncheckedCall.2 with
        | .ok (_, s1), .ok (_, s2) => s1 == s2 | _, _ => false)
        && checkedAllowed.1.objects[serverB.toObjId]? == uncheckedCall.1.objects[serverB.toObjId]?
        && checkedAllowed.1.objects[clientA.toObjId]? == uncheckedCall.1.objects[clientA.toObjId]?
        && checkedAllowed.1.objects[replyB.toObjId]? == uncheckedCall.1.objects[replyB.toObjId]?
        && checkedAllowed.1.objects[epAB]? == uncheckedCall.1.objects[epAB]?
        && (checkedAllowed.1.scheduler.runQueueOnCore c0).toList
            == (uncheckedCall.1.scheduler.runQueueOnCore c0).toList
        && (checkedAllowed.1.scheduler.runQueueOnCore c1).toList
            == (uncheckedCall.1.scheduler.runQueueOnCore c1).toList)
    -- (b) Reply gate. Fixture: rt.afterCallA (client A blockedOnReply, server B ready).
    -- DENIED (high server B → low client A): fail-closed — the whole affected
    -- footprint (caller, replier, reply object, endpoint) and cores 0/1 run queues
    -- are unchanged from `rt.afterCallA`, so a regression that delivers/relinks
    -- before returning `.flowDenied` fails here, not just the caller-ipcState check.
    let (stRDenied, resRDenied) :=
      endpointReplyCrossCoreDispatchChecked replyDeniedCtx serverB clientA replyMsgB c1 rt.afterCallA
    assertBool "a high→low reply is denied with .flowDenied"
      (match resRDenied with | .error .flowDenied => true | _ => false)
    assertBool "the denied reply leaves the client still blockedOnReply (undelivered)"
      (ipcStateIs stRDenied clientA (.blockedOnReply epAB (some serverB)))
    assertBool "the denied reply leaves the whole footprint unchanged (caller/replier/reply/endpoint)"
      (stRDenied.objects[clientA.toObjId]? == rt.afterCallA.objects[clientA.toObjId]?
        && stRDenied.objects[serverB.toObjId]? == rt.afterCallA.objects[serverB.toObjId]?
        && stRDenied.objects[replyB.toObjId]? == rt.afterCallA.objects[replyB.toObjId]?
        && stRDenied.objects[epAB]? == rt.afterCallA.objects[epAB]?)
    assertBool "the denied reply leaves cores 0/1 run queues unchanged"
      ((stRDenied.scheduler.runQueueOnCore c0).toList == (rt.afterCallA.scheduler.runQueueOnCore c0).toList
        && (stRDenied.scheduler.runQueueOnCore c1).toList == (rt.afterCallA.scheduler.runQueueOnCore c1).toList)
    -- ALLOWED (all public): the checked reply equals the unchecked one — compare
    -- the surfaced SGI (a dropped remote-wake would diverge here), the woken
    -- caller's object (payload delivery), the consumed reply object, AND the
    -- caller's home-core run queue (the wake's scheduler effect), not just the
    -- caller TCB — so the "equals unchecked" claim is actually gated.
    let checkedRAllowed := endpointReplyCrossCoreDispatchChecked allPublicCtx serverB clientA replyMsgB c1 rt.afterCallA
    let uncheckedReply := endpointReplyCrossCoreDispatch serverB clientA replyMsgB c1 rt.afterCallA
    assertBool "an allowed checked reply equals the unchecked cross-core reply (SGI + caller + reply + queue)"
      ((match checkedRAllowed.2, uncheckedReply.2 with
        | .ok s1, .ok s2 => s1 == s2
        | _, _ => false)
        && checkedRAllowed.1.objects[clientA.toObjId]? == uncheckedReply.1.objects[clientA.toObjId]?
        && checkedRAllowed.1.objects[replyB.toObjId]? == uncheckedReply.1.objects[replyB.toObjId]?
        && (checkedRAllowed.1.scheduler.runQueueOnCore c0).toList
            == (uncheckedReply.1.scheduler.runQueueOnCore c0).toList)

-- ============================================================================
-- §3.12 Live API dispatch (`dispatchSyscall` .call through CSpace resolution)
-- ============================================================================

private def apiCn : SeLe4n.ObjId := ⟨860⟩
private def apiEp : SeLe4n.ObjId := ⟨861⟩
private def apiCaller : SeLe4n.ThreadId := ⟨862⟩
private def apiServer : SeLe4n.ThreadId := ⟨863⟩ -- home core 1
private def apiReply : SeLe4n.ReplyId := ⟨864⟩
private def apiEpCap : Capability := { target := .object apiEp, rights := AccessRightSet.ofList [.write] }
private def apiEpCapRO : Capability := { target := .object apiEp, rights := AccessRightSet.ofList [.read] }
/-- A cap whose target is a TCB, not an endpoint — resolves, but the `.call` arm
rejects it (the transition finds a wrong-kinded object). -/
private def apiWrongKindCap : Capability :=
  { target := .object apiServer.toObjId, rights := AccessRightSet.ofList [.write] }

/-- A `.call` syscall decode whose primary cap sits at CPtr `capSlot`. -/
private def apiCallDecoded (capSlot : Nat) : SyscallDecodeResult :=
  { capAddr := SeLe4n.CPtr.ofNat capSlot,
    msgInfo := { length := 0, extraCaps := 0, label := 0 },
    syscallId := .call, msgRegs := #[] }

private def stApi (slots : List (SeLe4n.Slot × Capability)) : SystemState :=
  (BootstrapBuilder.empty
    |>.withObject apiEp (.endpoint {})
    |>.withObject apiCn (.cnode
        { depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
          slots := SeLe4n.UniqueSlotMap.ofListWF slots })
    |>.withObject apiCaller.toObjId (.tcb { mkTcb 862 40 none with cspaceRoot := apiCn })
    |>.withObject apiServer.toObjId (.tcb { mkTcb 863 50 (some c1) with cspaceRoot := apiCn })
    |>.withObject apiReply.toObjId (.reply { replyId := apiReply })
    |>.withRunnable [apiCaller]
    |>.build)

/-- Block the server on the endpoint, then dispatch the caller's `.call` syscall
through the full public entry (`dispatchSyscall` → CSpace lookup → cross-core). -/
private def apiDispatch (slots : List (SeLe4n.Slot × Capability)) (capSlot : Nat) :
    Except KernelError (Unit × SystemState) :=
  match endpointReceiveDual apiEp apiServer (some apiReply) (stApi slots) with
  | .error e => .error e
  | .ok (_, stRecv) => dispatchSyscall (apiCallDecoded capSlot) apiCaller stRecv

private def runLiveApiChecks : IO Unit := do
  IO.println "--- §3.12 live API dispatch (dispatchSyscall .call: CSpace lookup + authority + cross-core) ---"
  -- AUTHORIZED: an endpoint cap with `.write` at slot 0 → the call rendezvouses.
  match apiDispatch [(SeLe4n.Slot.ofNat 0, apiEpCap)] 0 with
  | .error _ => assertBool "authorized live .call succeeds" false
  | .ok ((), st') =>
    assertBool "authorized live .call rendezvouses: server B receives (.ready)"
      (ipcStateIs st' apiServer .ready)
    assertBool "authorized live .call blocks the caller as blockedOnReply"
      (ipcStateIs st' apiCaller (.blockedOnReply apiEp (some apiServer)))
    assertBool "authorized live .call wakes the server on its home core 1"
      ((st'.scheduler.runQueueOnCore c1).contains apiServer)
  -- NO CAP (empty slot 0): the CSpace lookup fails closed.
  assertBool "live .call with no cap at the CPtr fails with invalidCapability"
    (match apiDispatch [] 0 with | .error .invalidCapability => true | _ => false)
  -- READ-ONLY cap (no `.write`): the authority gate rejects (syscallRequiredRight .call = .write).
  assertBool "live .call with a read-only endpoint cap fails with illegalAuthority"
    (match apiDispatch [(SeLe4n.Slot.ofNat 0, apiEpCapRO)] 0 with
     | .error .illegalAuthority => true | _ => false)
  -- WRONG-KIND cap (targets a TCB): the `.call` transition rejects it.
  assertBool "live .call resolving a non-endpoint cap fails with invalidCapability"
    (match apiDispatch [(SeLe4n.Slot.ofNat 0, apiWrongKindCap)] 0 with
     | .error .invalidCapability => true | _ => false)
  -- Checked entry (dispatchSyscallChecked): a high→low policy denies the call.
  match endpointReceiveDual apiEp apiServer (some apiReply) (stApi [(SeLe4n.Slot.ofNat 0, apiEpCap)]) with
  | .error _ => assertBool "checked-dispatch setup (server recv) succeeded" false
  | .ok (_, stRecv) =>
    let apiDeniedCtx : LabelingContext :=
      { objectLabelOf := fun _ => lowLabel
        threadLabelOf := fun t => if t == apiCaller then highLabel else lowLabel
        endpointLabelOf := fun _ => lowLabel
        serviceLabelOf := fun _ => lowLabel }
    assertBool "live checked .call under a high→low policy fails with flowDenied"
      (match dispatchSyscallChecked apiDeniedCtx (apiCallDecoded 0) apiCaller stRecv with
       | .error .flowDenied => true | _ => false)
    assertBool "live checked .call under an all-public policy succeeds"
      (match dispatchSyscallChecked allPublicCtx (apiCallDecoded 0) apiCaller stRecv with
       | .ok _ => true | _ => false)

-- ============================================================================
-- §3.13 Cancellation × IPC composition (cancel a reply-blocked client)
-- ============================================================================

private def runCancellationCompositionChecks : IO Unit := do
  IO.println "--- §3.13 cancellation × IPC (cancel a reply-blocked client ⇒ server's reply fails closed) ---"
  match roundTripE with
  | .error step => assertBool s!"cancellation×IPC fixture ({step} failed)" false
  | .ok rt =>
    -- rt.afterCallA: client A is blockedOnReply(server B), linked to reply B.
    assertBool "pre: client A is blockedOnReply and linked to its reply object"
      (ipcStateIs rt.afterCallA clientA (.blockedOnReply epAB (some serverB))
        && (match rt.afterCallA.getReply? replyB with
            | some r => decide (r.caller = some clientA) | none => false))
    -- Cancel the client's blocked IPC (the suspend pipeline's teardown slice).
    match rt.afterCallA.getTcb? clientA with
    | none => assertBool "client A TCB resolves for cancellation" false
    | some tcbA =>
      let (stCancelled, _) := cancelIpcBlockingOnCore clientA tcbA c0 rt.afterCallA
      assertBool "cancellation makes the client .ready and clears its reply forward link"
        (ipcStateIs stCancelled clientA .ready
          && (match stCancelled.getTcb? clientA with
              | some t => decide (t.replyObject = none) | none => false))
      assertBool "cancellation severs the reply object's caller back-link"
        (match stCancelled.getReply? replyB with
         | some r => decide (r.caller = none) | none => false)
      -- The composition: the server's later cross-core reply now fails closed
      -- (the client is `.ready`, not `.blockedOnReply` — the SM6.C replay barrier).
      assertBool "the server's reply to the cancelled client fails closed with replyCapInvalid"
        (match (endpointReplyOnCore serverB clientA replyMsgB c1 stCancelled).2 with
         | .error .replyCapInvalid => true | _ => false)

-- ============================================================================
-- §3.13b WS-RR RR2.19 — the live `.tcbSuspend` operation, end to end
-- ============================================================================
-- RR2.17 extended the cancellation's `ipcInvariant` closure from the teardown
-- composite to `suspendThreadOnCore`, which is what the dispatch entry's
-- `.tcbSuspend` arm actually calls. These checks exercise that operation on the
-- state the donation round trip produces — a passive server holding a donated
-- SchedContext, current on its own core — which is the arm where the five
-- post-teardown stages (PIP revert, two deschedules, pending-state clear,
-- `.Inactive` store, local scheduling point) all do something.

private def runSuspendArmChecks : IO Unit := do
  IO.println "--- §3.13b WS-RR RR2.19: the live `.tcbSuspend` arm (suspendThreadOnCore) ---"
  match okPair (endpointReceiveDualOnCore donEp donServer (some donReply) c1
      stDonWithReplenishments) with
  | none => assertBool "suspend-arm setup (server recv) succeeded" false
  | some (stRecv, _) =>
    let (stCall, _) := endpointCallCrossCoreDispatch donEp donClient IpcMessage.empty
      AccessRightSet.empty (SeLe4n.Slot.ofNat 0) c0 stRecv
    match okExcept (handleRescheduleSgiOnCore stCall c1) with
    | none => assertBool "suspend-arm setup: core 1 handles the call wake SGI" false
    | some stDispatched =>
      assertBool "pre: the donated server is current on its home core 1"
        (stDispatched.scheduler.currentOnCore c1 == some donServer)
      assertBool "pre: the server holds the donated SchedContext"
        (match stDispatched.getTcb? donServer with
         | some t => decide (t.schedContextBinding = .donated scClient donClient) | none => false)
      match SeLe4n.ThreadId.toValid? donServer with
      | none => assertBool "the server id promotes to a ValidThreadId" false
      | some serverV =>
        match okExcept (Lifecycle.Suspend.suspendThreadOnCore stDispatched serverV c1) with
        | none => assertBool "suspending the donated server succeeds" false
        | some (stSusp, _) =>
          assertBool "the suspended server is .Inactive"
            (match stSusp.getTcb? donServer with
             | some t => decide (t.threadState = ThreadState.Inactive) | none => false)
          assertBool "the suspend returns the donated SchedContext to its original owner"
            (match stSusp.getTcb? donClient with
             | some t => decide (t.schedContextBinding = .bound scClient) | none => false)
          assertBool "the suspend leaves the server SC-less (.unbound)"
            (match stSusp.getTcb? donServer with
             | some t => decide (t.schedContextBinding = SchedContextBinding.unbound) | none => false)
          assertBool "the suspend descheds the victim from its home core 1"
            (stSusp.scheduler.currentOnCore c1 != some donServer
              && !(stSusp.scheduler.runQueueOnCore c1).contains donServer)
          assertBool "the suspend clears the victim's IPC state and queue links"
            (match stSusp.getTcb? donServer with
             | some t => decide (t.ipcState = ThreadIpcState.ready)
                 && decide (t.queueNext = none) && decide (t.queuePrev = none)
             | none => false)
          -- RR2.17's subject: the suspend's five extra stages write TCBs and
          -- scheduler slots only, so no notification object moves. The donated
          -- SC's replenishments follow the binding home, exactly as on the reply.
          assertBool "the suspend migrates the returned SC's replenishments back to core 0"
            (decide (replenishCountFor stSusp c0 scClient = 2)
              && decide (replenishCountFor stSusp c1 scClient = 0))
          assertBool "the suspend leaves the bystander SchedContext's entry alone"
            (decide (replenishCountFor stSusp c1 scBystander = 1))
    -- Self-migration is a definitional no-op: donor and donee on one core (every
    -- single-core configuration) must leave both replenish queues untouched.
    let stSelf := migrateSchedContextReplenishment stCall scClient c1 c1
    assertBool "a same-core migration leaves every replenish queue exactly as it was"
      (decide (replenishEntriesOn stSelf c0 = replenishEntriesOn stCall c0)
        && decide (replenishEntriesOn stSelf c1 = replenishEntriesOn stCall c1))

-- ============================================================================
-- §3.14 Scheduler contention on the handler path (no wrongful preemption)
-- ============================================================================

private def highPrioT : SeLe4n.ThreadId := ⟨870⟩

/-- A core-1 current thread of priority `curPrio`, with the endpoint's server
(priority 50) about to be woken onto core 1 by a cross-core call from the client.
`highPrioT` is CURRENT on core 1 and **not** in its run queue — the scheduler's
dequeue-on-dispatch discipline (`queueCurrentConsistentOnCore`: the current thread
is not in its own run queue). This matters: with the current left in the queue,
the woken server would simply lose the reselection to a still-queued higher-prio
thread, so the no-preemption gate would pass without actually protecting a
*dispatched* current. Here the woken server B is the **only** entry in core 1's
queue, so the gate passes iff the current genuinely outranks the candidate. -/
private def stContention (curPrio : Nat) : SystemState :=
  let base :=
    (BootstrapBuilder.empty
      |>.withObject epAB (.endpoint {})
      |>.withObject serverB.toObjId (.tcb (mkTcb 822 50 (some c1)))
      |>.withObject highPrioT.toObjId (.tcb (mkTcb 870 curPrio (some c1)))
      |>.withObject clientA.toObjId (.tcb (mkTcb 821 40 none))
      |>.withObject replyB.toObjId (.reply { replyId := replyB })
      |>.withRunnable [clientA]
      |>.build)
  { base with scheduler := base.scheduler.setCurrentOnCore c1 (some highPrioT) }

/-- Drive: server B receives on core 1, then client A calls cross-core (waking B
onto core 1), then core 1 handles the reschedule SGI. -/
private def contentionAfterHandle (curPrio : Nat) : Option SystemState := do
  let (stRecv, _) ← okPair (endpointReceiveDualOnCore epAB serverB (some replyB) c1 (stContention curPrio))
  let (stCall, _) ← okPair (endpointCallOnCore epAB clientA IpcMessage.empty c0 stRecv)
  okExcept (handleRescheduleSgiOnCore stCall c1)

private def runHandlerContentionChecks : IO Unit := do
  IO.println "--- §3.14 scheduler contention (woken server does not preempt a higher-prio current) ---"
  -- (a) HIGH current (prio 90 > server 50): the woken server does NOT preempt.
  match contentionAfterHandle 90 with
  | none => assertBool "contention pipeline (high current) succeeded" false
  | some st =>
    assertBool "the woken server (prio 50) is enqueued on core 1"
      ((st.scheduler.runQueueOnCore c1).contains serverB)
    assertBool "core 1's handler keeps the higher-priority current (no wrongful preemption)"
      (st.scheduler.currentOnCore c1 == some highPrioT)
  -- (b) LOW current (prio 10 < server 50): the woken server DOES preempt (control).
  match contentionAfterHandle 10 with
  | none => assertBool "contention pipeline (low current) succeeded" false
  | some st =>
    assertBool "core 1's handler preempts a lower-priority current (server B dispatched)"
      (st.scheduler.currentOnCore c1 == some serverB)

-- ============================================================================
-- §9 The deterministic 4-core IPC trace (SM6.F.4 golden fixture)
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
IPC-logic regression diverges the golden fixture. Every line carries the
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
against the golden fixture. The lines print before the (strict) verification,
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
    IO.println s!" FAIL: golden fixture {fixturePath} not found"
    IO.println s!" regenerate: lake exe smp_ipc_suite | grep '^\\[smp-ipc-4core\\]' > {fixturePath}"
    throw (IO.userError s!"missing fixture {fixturePath}")
  let actual ← IO.FS.readFile fixturePath
  if actual == expectedContent then
    IO.println s!" PASS: 4-core IPC trace matches golden fixture {fixturePath}"
  else
    IO.println s!" FAIL: 4-core IPC trace differs from golden fixture {fixturePath}"
    IO.println s!" the live trace is printed above; regenerate the golden fixture with:"
    IO.println s!" lake exe smp_ipc_suite | grep '^\\[smp-ipc-4core\\]' > {fixturePath}"
    IO.println s!" (then refresh {fixturePath}.sha256 — see tests/fixtures/README.md)"
    throw (IO.userError "4-core IPC trace fixture mismatch")

-- ============================================================================
-- §3.15 the SchedContext donation chain's structure (WS-OD OD2 — inert)
-- ============================================================================

/-! The reply stack a depth-2 Call chain leaves, exercised as a store.  `chainSc`
heads the inner call's Reply (`next = .head chainSc`), which links **down** to
the outer call's through `prev`; the outer frame links **up** to the inner one
(`next = .frame chainHeadReply`) and names no context at all.  The context is
recorded at the head alone, which is what makes taking a frame out of the middle
an `O(1)` repair of its two neighbours rather than a walk clearing a per-frame
context field below the cut.

The negatives are the mutation this project asks for — they **keep the link and
break the relation** rather than deleting it.  In each, the head still carries a
`prev`; what changes is what that link leads to: a live Reply whose upward link
names a *different* frame, one that heads a *different* context, one carrying no
upward link at all, the head itself (a cycle), or a `ReplyId` no object answers.
Deleting the link would be caught by the positive above; the first three are what
a re-linked (reused) Reply object actually looks like, which is the confused
deputy the walk's reciprocity test exists to refuse. -/

private def chainSc : SeLe4n.SchedContextId := ⟨71⟩
private def chainOtherSc : SeLe4n.SchedContextId := ⟨74⟩
private def chainHeadReply : SeLe4n.ReplyId := ⟨72⟩
private def chainOuterReply : SeLe4n.ReplyId := ⟨73⟩
private def chainAbsentReply : SeLe4n.ReplyId := ⟨75⟩

/-- A caller for the literal `Reply.wellFormed` checks below: the predicate is
`caller = none → prev = none ∧ next = none`, so every *positive* shape it admits
carries a caller. -/
private def chainCaller : SeLe4n.ThreadId := ⟨76⟩

/-- A donation-chain store, parameterised by the two things the negatives vary:
what the head links down to, and what the frame below it links back **up** to.
`caller` is left at `none` throughout: the walk validates a `prev` by the
target's own upward link and never by who is blocked on it — the decision that
refuses a re-linked Reply — so the fixture exercising it carries no callers. -/
private def chainStore (headPrev : Option SeLe4n.ReplyId)
    (outerUp : Option ReplyStackLink) : SystemState :=
  (BootstrapBuilder.empty
    |>.withObject chainSc.toObjId
        (.schedContext { SchedContext.empty chainSc with scReply := some chainHeadReply })
    |>.withObject chainOtherSc.toObjId (.schedContext (SchedContext.empty chainOtherSc))
    |>.withObject chainHeadReply.toObjId
        (.reply { replyId := chainHeadReply, next := some (.head chainSc), prev := headPrev })
    |>.withObject chainOuterReply.toObjId
        (.reply { replyId := chainOuterReply, next := outerUp })
    |>.build)

/-- The well-formed depth-2 chain. -/
private def stChain : SystemState :=
  chainStore (some chainOuterReply) (some (.frame chainHeadReply))

private def runDonationChainStructureChecks : IO Unit := do
  IO.println "--- §3.15 the SchedContext donation chain's structure (WS-OD OD2, inert) ---"
  -- `Reply.wellFormed`: a stack link only on a reply that is itself on a stack.
  assertBool "an inert Reply is well formed"
    (decide (Reply.empty chainHeadReply).wellFormed)
  assertBool "a Reply with a caller may carry both stack links"
    (decide ({ replyId := chainHeadReply, caller := some chainCaller,
               next := some (.head chainSc),
               prev := some chainOuterReply } : Reply).wellFormed)
  assertBool "NEGATIVE: a Reply off every stack may not carry a prev link"
    (!decide ({ replyId := chainHeadReply, prev := some chainOuterReply } : Reply).wellFormed)
  -- The `next` half of the same predicate: the doubly-linked stack made the
  -- upward link a second way to pin an object, so it is refused on the same
  -- terms.  Without this check the head link could be left behind by a pop and
  -- `Reply.wellFormed` would still pass.
  assertBool "NEGATIVE: a Reply off every stack may not head a context either"
    (!decide ({ replyId := chainHeadReply, next := some (.head chainSc) } : Reply).wellFormed)
  assertBool "NEGATIVE: a Reply off every stack may not carry an upward frame link"
    (!decide ({ replyId := chainHeadReply,
                next := some (.frame chainOuterReply) } : Reply).wellFormed)
  -- The walk: the head's chain is the two replies, innermost first.
  assertBool "the context's head walks the whole depth-2 chain"
    (donationChainFrom stChain chainSc 2 (some chainHeadReply)
       == some [chainHeadReply, chainOuterReply])
  assertBool "walking from the context's own scReply gives the same chain"
    (match stChain.getSchedContext? chainSc with
     | some sc => donationChainFrom stChain chainSc 2 sc.scReply
                    == some [chainHeadReply, chainOuterReply]
     | none => false)
  assertBool "the walk is fuel-bounded: one step short returns none"
    (donationChainFrom stChain chainSc 1 (some chainHeadReply) == none)
  assertBool "more fuel than the chain needs returns the same chain"
    (donationChainFrom stChain chainSc 8 (some chainHeadReply)
       == some [chainHeadReply, chainOuterReply])
  -- NEGATIVE: the link is still there and still names a LIVE Reply — but that
  -- reply's upward link does not answer the frame that reached it, which is what
  -- a re-linked (reused) Reply looks like.  Following it would hand this context
  -- to the other stack's caller.
  assertBool "NEGATIVE: a prev whose target links up to a different frame is refused"
    (donationChainFrom (chainStore (some chainOuterReply) (some (.frame chainAbsentReply)))
       chainSc 8 (some chainHeadReply) == none)
  assertBool "NEGATIVE: a prev whose target heads another context is refused"
    (donationChainFrom (chainStore (some chainOuterReply) (some (.head chainOtherSc)))
       chainSc 8 (some chainHeadReply) == none)
  assertBool "NEGATIVE: a prev whose target heads THIS context is refused"
    (donationChainFrom (chainStore (some chainOuterReply) (some (.head chainSc)))
       chainSc 8 (some chainHeadReply) == none)
  assertBool "NEGATIVE: a prev whose target carries no upward link is refused"
    (donationChainFrom (chainStore (some chainOuterReply) none)
       chainSc 8 (some chainHeadReply) == none)
  assertBool "NEGATIVE: a self-linked head (a cycle) is refused at every fuel"
    ((List.range 12).all (fun f =>
      donationChainFrom (chainStore (some chainHeadReply) (some (.frame chainHeadReply)))
        chainSc f (some chainHeadReply) == none))
  assertBool "NEGATIVE: a prev naming no object at all is refused"
    (donationChainFrom (chainStore (some chainAbsentReply) (some (.frame chainHeadReply)))
       chainSc 8 (some chainHeadReply) == none)
  -- One chain per context: the second context's stack is empty and does not
  -- pick up a chain whose members name the first.
  assertBool "a second context's stack is empty and does not pick up this chain"
    (donationChainFrom stChain chainOtherSc 8 none == some [] &&
     donationChainFrom stChain chainOtherSc 8 (some chainHeadReply) == none)
  -- The head is erased by the NI projection, in the same class as `boundThread`.
  -- The second check is the discriminating control: without it the first would
  -- pass for a comparator that cannot see the field at all.
  let obs : IfObserver := { clearance := lowLabel }
  assertBool "the reply-stack head is erased by the NI projection"
    (projectKernelObject allPublicCtx obs
        (.schedContext { SchedContext.empty chainSc with scReply := some chainHeadReply })
      == projectKernelObject allPublicCtx obs (.schedContext (SchedContext.empty chainSc)))
  assertBool "...and the structural comparator does distinguish the head"
    (!(KernelObject.schedContext { SchedContext.empty chainSc with scReply := some chainHeadReply }
        == KernelObject.schedContext (SchedContext.empty chainSc)))


/-! §3.16 — the donation return as a reply-stack pop (WS-OD OD3, inert).

The pop is the transition that *reads* the structure §3.15 exercises, and this
section runs it on both shapes it can meet: the bottom of the stack, where it
must be the pre-OD3 return character for character, and one level up, where it
pops the head and hands the context back `.donated`.

The depth-≥ 2 case was deliberately exercised before any transition in the tree
produced it.  A pop that is only ever run at depth 1 is a pop whose
generalisation nothing has evaluated — and the arm OD4.1 (`v0.35.2`) made
reachable would then have arrived untested. -/

private def popServer : SeLe4n.ThreadId := ⟨81⟩
private def popClient : SeLe4n.ThreadId := ⟨82⟩
private def popOuter : SeLe4n.ThreadId := ⟨83⟩

/-- The donor shape the pop requires of an outer caller: a thread that has given
up its binding and waits on a reply.  Named so the negatives can vary one clause
at a time rather than deleting the caller outright. -/
private def popWaitingDonor : TCB :=
  { mkTcb 83 40 none with
      ipcState := .blockedOnReply (SeLe4n.ObjId.ofNat 76) (some popClient) }

/-- A donation return's pre-state: the context is bound to the server, which
holds it `.donated` from the client.  `head?` says whether the context heads a
reply stack, `prev?` what that head links down to, and `outerReply` is the frame
below the head as the resolver will find it — one builder for every shape the
checks below vary, so the negatives differ from the well-formed fixture in
exactly the field each one names. -/
private def popStoreShaped (outerTcb : TCB) (head? : Option SeLe4n.ReplyId)
    (prev? : Option SeLe4n.ReplyId) (outerReply : Reply) : SystemState :=
  (BootstrapBuilder.empty
    |>.withObject chainSc.toObjId
        (.schedContext { SchedContext.empty chainSc with
                           boundThread := some popServer, scReply := head? })
    |>.withObject chainHeadReply.toObjId
        (.reply { replyId := chainHeadReply, caller := some popClient,
                  next := some (.head chainSc), prev := prev? })
    |>.withObject chainOuterReply.toObjId (.reply outerReply)
    |>.withObject popServer.toObjId
        (.tcb { mkTcb 81 50 none with schedContextBinding := .donated chainSc popClient })
    |>.withObject popClient.toObjId (.tcb (mkTcb 82 40 none))
    -- WS-OD OD4.4: the outer caller must be a *waiting donor*, because the pop
    -- validates it before handing it the context.  A fixture that made it merely
    -- `.ready` was modelling a state the kernel now refuses — the guard doing its
    -- job — so the shape is a parameter and the negatives below vary it.
    |>.withObject popOuter.toObjId (.tcb outerTcb)
    |>.build)

/-- The frame below the head as a live depth-2 chain leaves it: linking **up**
to the head, with the outer caller still waiting on it.  It names no context —
only the head does — which is what makes the pop's lookahead one frame deep. -/
private def popOuterFrame : Reply :=
  { replyId := chainOuterReply, caller := some popOuter,
    next := some (.frame chainHeadReply) }

/-- The pre-state with the outer caller's TCB varied and the frame below the
head well formed. -/
private def popStoreWith (outerTcb : TCB) (head? : Option SeLe4n.ReplyId)
    (prev? : Option SeLe4n.ReplyId) : SystemState :=
  popStoreShaped outerTcb head? prev? popOuterFrame

/-- The well-formed depth-≥ 2 fixture: a waiting-donor outer caller. -/
private def popStore (head? : Option SeLe4n.ReplyId)
    (prev? : Option SeLe4n.ReplyId) : SystemState :=
  popStoreWith popWaitingDonor head? prev?

/-- ...and the same store with the frame *below* the head carrying some other
upward link — what a re-linked (reused) Reply looks like from the resolver's
side.  A reused Reply keeps its `caller`; what it loses is the link back up to
the frame that named it, and that is the reciprocity the resolver refuses to
read past. -/
private def popStoreOuterLinkedTo (up : Option ReplyStackLink) : SystemState :=
  popStoreShaped popWaitingDonor (some chainHeadReply) (some chainOuterReply)
    { popOuterFrame with next := up }

/-- ...and the store with the *head* itself carrying some other upward link.
The context still points at it, so the mutation keeps the head and breaks the
relation `donationHeadOf?` reads: a head that heads a different context, one
that heads none, or one claiming a frame above it. -/
private def popHeadLinkedTo (up : Option ReplyStackLink) : SystemState :=
  (BootstrapBuilder.empty
    |>.withObject chainSc.toObjId
        (.schedContext { SchedContext.empty chainSc with
                           boundThread := some popServer,
                           scReply := some chainHeadReply })
    |>.withObject chainHeadReply.toObjId
        (.reply { replyId := chainHeadReply, caller := some popClient, next := up })
    |>.withObject chainOuterReply.toObjId (.reply popOuterFrame)
    |>.withObject popServer.toObjId
        (.tcb { mkTcb 81 50 none with schedContextBinding := .donated chainSc popClient })
    |>.withObject popClient.toObjId (.tcb (mkTcb 82 40 none))
    |>.withObject popOuter.toObjId (.tcb popWaitingDonor)
    |>.build)

/-- ...and with the frame below the head *validated* but its caller consumed —
the shape the pre-`v0.35.4` single-linked stack left behind when a middle caller
was cancelled and nothing could remove its frame.  The outer caller's TCB is
still present, so the resolver's verdict here is decided by the frame and not by
a missing thread. -/
private def popStoreOuterConsumed : SystemState :=
  popStoreShaped popWaitingDonor (some chainHeadReply) (some chainOuterReply)
    { popOuterFrame with caller := none }

private def popBindingOf (st : SystemState) (tid : SeLe4n.ThreadId) :
    Option SchedContextBinding :=
  (st.getTcb? tid).map (·.schedContextBinding)

private def popHeadOf (st : SystemState) : Option (Option SeLe4n.ReplyId) :=
  (st.getSchedContext? chainSc).map (·.scReply)

private def popReplyLinks (st : SystemState) :
    Option (Option SeLe4n.ReplyId × Option ReplyStackLink) :=
  match st.objects[chainHeadReply.toObjId]? with
  | some (.reply r) => some (r.prev, r.next)
  | _ => none

private def runDonationReturnPopChecks : IO Unit := do
  IO.println "--- §3.16 the donation return as a reply-stack pop (WS-OD OD3, inert) ---"
  -- The bottom of the stack: no head, `newOwner? = none`.  This is the shape
  -- every call site in the tree produces today, and it must be the pre-OD3
  -- return exactly — the context back to its owner, the server unbound.
  match returnDonatedSchedContext (popStore none none) popServer chainSc popClient none with
  | .error e => assertBool s!"depth-1 pop must succeed (got {reprStr e})" false
  | .ok st' =>
    assertBool "depth-1: the owner is rebound `.bound`, not `.donated`"
      (popBindingOf st' popClient == some (.bound chainSc))
    assertBool "depth-1: the server is unbound"
      (popBindingOf st' popServer == some .unbound)
    assertBool "depth-1: the context points back at the owner"
      ((st'.getSchedContext? chainSc).map (·.boundThread) == some (some popClient))
    assertBool "depth-1: the context still heads no stack"
      (popHeadOf st' == some none)
  -- One level up: the context heads a stack whose head links down to the outer
  -- call's reply.  The pop must consume exactly one frame.
  match returnDonatedSchedContext (popStore (some chainHeadReply) (some chainOuterReply))
      popServer chainSc popClient (some popOuter) with
  | .error e => assertBool s!"depth-2 pop must succeed (got {reprStr e})" false
  | .ok st' =>
    assertBool "depth-2: the head is popped to the reply below it"
      (popHeadOf st' == some (some chainOuterReply))
    assertBool "depth-2: the consumed head's stack links are cleared, both ways"
      (popReplyLinks st' == some (none, none))
    assertBool "depth-2: the owner comes back `.donated` at the outer caller"
      (popBindingOf st' popClient == some (.donated chainSc popOuter))
    assertBool "depth-2: the server is still unbound"
      (popBindingOf st' popServer == some .unbound)
  -- ...and the frame below the head is untouched: the pop consumes ONE frame,
  -- which is the discriminating control for "popped to `prev`" above.
  match returnDonatedSchedContext (popStore (some chainHeadReply) (some chainOuterReply))
      popServer chainSc popClient (some popOuter) with
  | .error _ => assertBool "depth-2 pop must succeed (control)" false
  | .ok st' =>
    assertBool "depth-2: the frame below the head becomes the head, caller intact"
      (match st'.objects[chainOuterReply.toObjId]? with
       | some (.reply r) =>
           r.next == some (.head chainSc) && r.prev == none && r.caller == some popOuter
       | _ => false)
  -- NEGATIVE: the head validation is fail-closed, and the mutations keep the
  -- head and break the relation.  A head whose upward link names a *different*
  -- context, or none at all, is what a re-linked (reused) Reply looks like; a
  -- head naming no object at all is a dangling link.  Each must refuse rather
  -- than read as an empty stack, or the pop would clear a Reply belonging to
  -- someone else and leave this context's own head dangling.
  assertBool "NEGATIVE: a head that heads another context is refused"
    (match returnDonatedSchedContext (popHeadLinkedTo (some (.head chainOtherSc)))
        popServer chainSc popClient none with
     | .error e => e == KernelError.invalidArgument
     | .ok _ => false)
  assertBool "NEGATIVE: a head carrying no upward link is refused"
    (match returnDonatedSchedContext (popHeadLinkedTo none)
        popServer chainSc popClient none with
     | .error e => e == KernelError.invalidArgument
     | .ok _ => false)
  assertBool "NEGATIVE: a head whose upward link names a frame above it is refused"
    (match returnDonatedSchedContext (popHeadLinkedTo (some (.frame chainOuterReply)))
        popServer chainSc popClient none with
     | .error e => e == KernelError.invalidArgument
     | .ok _ => false)
  assertBool "NEGATIVE: a head naming no object is refused"
    (match returnDonatedSchedContext (popStore (some chainAbsentReply) none)
        popServer chainSc popClient none with
     | .error e => e == KernelError.objectNotFound
     | .ok _ => false)
  -- WS-OD OD4.4 NEGATIVE: **the outer caller is validated, not trusted.**  The
  -- pop mints a `.donated` binding, so it checks its donee the way
  -- `donateSchedContext` checks its donor.  Each mutation below keeps the whole
  -- depth-2 chain intact and breaks exactly one clause of the donor shape, so a
  -- check that merely looked for "an outer caller exists" would pass all three.
  assertBool "NEGATIVE: an outer caller that is not blocked on a reply is refused"
    (match returnDonatedSchedContext
        (popStoreWith (mkTcb 83 40 none) (some chainHeadReply) (some chainOuterReply))
        popServer chainSc popClient (some popOuter) with
     | .error e => e == KernelError.invalidArgument
     | .ok _ => false)
  assertBool "NEGATIVE: an outer caller that still holds a binding is refused"
    (match returnDonatedSchedContext
        (popStoreWith { popWaitingDonor with schedContextBinding := .bound chainOtherSc }
          (some chainHeadReply) (some chainOuterReply))
        popServer chainSc popClient (some popOuter) with
     | .error e => e == KernelError.invalidArgument
     | .ok _ => false)
  assertBool "NEGATIVE: an outer caller naming no TCB is refused"
    (match returnDonatedSchedContext (popStore (some chainHeadReply) (some chainOuterReply))
        popServer chainSc popClient (some ⟨99⟩) with
     | .error e => e == KernelError.invalidArgument
     | .ok _ => false)
  -- ...and the two self-reference clauses: the pop rewrites both of these
  -- threads, so a claim about their pre-state shape would not survive the step.
  assertBool "NEGATIVE: an outer caller that IS the rebound thread is refused"
    (match returnDonatedSchedContext (popStore (some chainHeadReply) (some chainOuterReply))
        popServer chainSc popClient (some popClient) with
     | .error e => e == KernelError.invalidArgument
     | .ok _ => false)
  assertBool "NEGATIVE: an outer caller that IS the server is refused"
    (match returnDonatedSchedContext (popStore (some chainHeadReply) (some chainOuterReply))
        popServer chainSc popClient (some popServer) with
     | .error e => e == KernelError.invalidArgument
     | .ok _ => false)
  -- WS-OD OD3.4: the resolver reads the *frame below the head*, and answers
  -- `none` at the bottom.  Both readings are exercised, because a resolver only
  -- ever run on an empty stack is one nothing has evaluated.
  assertBool "the resolver answers the caller of the frame below the head"
    (match replyStackOuterCaller? (popStore (some chainHeadReply) (some chainOuterReply))
        chainSc with
     | .ok (some t) => t == popOuter
     | _ => false)
  assertBool "the resolver answers `none` at the bottom of the stack"
    (match replyStackOuterCaller? (popStore (some chainHeadReply) none) chainSc with
     | .ok none => true | _ => false)
  assertBool "the resolver answers `none` for a context heading no stack"
    (match replyStackOuterCaller? (popStore none none) chainSc with
     | .ok none => true | _ => false)
  -- The fourth state — a frame below the head that validates but whose caller
  -- has been consumed.  Before `v0.35.4` the resolver read it as the bottom of
  -- the stack: the pop bound the target outright and left that dead frame
  -- heading the context forever, pinning both objects against every retype and
  -- against ever linking the Reply again.  `severAtCut` is now implemented by
  -- the *splice* at the cancellation (`spliceReplyFrameOut`), so a linked
  -- frame always has a blocked caller (`Reply.wellFormed`) and this shape is an
  -- invariant violation — refused, never settled.  Pinned in three halves: the
  -- resolver's verdict, the declared below-head read (which is on the link
  -- alone, so it still answers), and the resolved pop the call sites run.
  assertBool "NEGATIVE: a validated frame whose caller was consumed is refused, not read as the bottom"
    (match replyStackOuterCaller? popStoreOuterConsumed chainSc with
     | .error e => e == KernelError.illegalState
     | .ok _ => false)
  assertBool "...and the below-head Reply read is still declared on that frame"
    (replyStackBelowHead? popStoreOuterConsumed chainSc == (some chainOuterReply, none))
  assertBool "...and the resolved pop refuses rather than settling the context on nobody"
    (match returnDonatedSchedContextResolved popStoreOuterConsumed popServer chainSc
        popClient with
     | .error e => e == KernelError.illegalState
     | .ok _ => false)
  -- NEGATIVE: the frame below is validated too — the confused deputy of §3.4.
  -- A reused Reply keeps its `caller`; what it loses is the link back up to the
  -- frame that named it, and that is what the resolver refuses to read past.
  assertBool "NEGATIVE: a frame below the head linking up to a different frame is refused"
    (match replyStackOuterCaller?
        (popStoreOuterLinkedTo (some (.frame chainAbsentReply))) chainSc with
     | .error e => e == KernelError.invalidArgument
     | .ok _ => false)
  assertBool "NEGATIVE: a frame below the head that heads a context is refused"
    (match replyStackOuterCaller?
        (popStoreOuterLinkedTo (some (.head chainOtherSc))) chainSc with
     | .error e => e == KernelError.invalidArgument
     | .ok _ => false)
  assertBool "NEGATIVE: a frame below the head carrying no upward link is refused"
    (match replyStackOuterCaller? (popStoreOuterLinkedTo none) chainSc with
     | .error e => e == KernelError.invalidArgument
     | .ok _ => false)
  -- The RR2.8 guard is unchanged by the widening: a context bound to someone
  -- else is still refused before anything is read or written.
  assertBool "NEGATIVE: a context not bound to the server is still refused"
    (match returnDonatedSchedContext (popStore none none) popOuter chainSc popClient none with
     | .error e => e == KernelError.invalidArgument
     | .ok _ => false)

-- ============================================================================
-- WS-OD OD4/OD5/OD6 — the donation PUSH, and the chain it builds
-- ============================================================================

/-- **OD6.3: the push at call depth ≥ 2, and the freshening barrier that keeps
it honest.**

The dual of the pop fixtures above, and the case the workstream exists for: a
caller that is *itself* holding a donation calls a passive server and passes the
context on, leaving the stack one frame deeper.  Exercised operationally, so the
push's four stores are evaluated rather than only proved about. -/
private def pushDonor : SeLe4n.ThreadId := ⟨91⟩
private def pushServer : SeLe4n.ThreadId := ⟨92⟩
private def pushOuter : SeLe4n.ThreadId := ⟨93⟩
private def pushDonorReply : SeLe4n.ReplyId := ⟨94⟩
private def pushOuterReply : SeLe4n.ReplyId := ⟨95⟩
private def pushSc : SeLe4n.SchedContextId := ⟨96⟩

/-- The pre-state a depth-2 push runs on: `pushSc` is bound to `pushDonor`, which
holds it `.donated` from `pushOuter`, and the stack already carries the outer
call's frame.  `donorBinding` and `donorReply?` are parameters so the negatives
vary one field at a time. -/
private def pushStoreShaped (donorBinding : SchedContextBinding)
    (donorReply? : Option SeLe4n.ReplyId) (headReply : Reply) : SystemState :=
  (BootstrapBuilder.empty
    |>.withObject pushSc.toObjId
        (.schedContext { SchedContext.empty pushSc with
                           boundThread := some pushDonor, scReply := some pushOuterReply })
    |>.withObject pushOuterReply.toObjId
        (.reply { replyId := pushOuterReply, caller := some pushOuter,
                  next := some (.head pushSc) })
    |>.withObject pushDonorReply.toObjId (.reply headReply)
    |>.withObject pushDonor.toObjId
        (.tcb { mkTcb 91 40 none with
                  schedContextBinding := donorBinding, replyObject := donorReply? })
    |>.withObject pushServer.toObjId (.tcb (mkTcb 92 30 none))
    -- **WS-HP HP5 (fixture correction)**: the outer caller names the reply object it
    -- is blocked on.  `pushOuterReply.caller` has always named it back, so the store
    -- was one `replyCallerLinkage` forbids; and since HP5.1 the cancellation
    -- reclaim's trigger reads exactly this field, so the omission made the OD5.2
    -- checks below pass for the wrong reason.  Two local re-spellings of this TCB
    -- collapse onto `pushOuterBlockedTcb` with it.
    |>.withObject pushOuter.toObjId
        (.tcb { mkTcb 93 50 none with
                  ipcState := .blockedOnReply (SeLe4n.ObjId.ofNat 97) (some pushDonor),
                  replyObject := some pushOuterReply })
    |>.build)

/-- The donor's own reply object, fresh: linked to the donor, on no stack —
neither link set, which is what `donationPushFrame?` requires of a frame. -/
private def pushFreshHead : Reply :=
  { replyId := pushDonorReply, caller := some pushDonor }

/-- The well-formed depth-2 pre-state. -/
private def pushStore : SystemState :=
  pushStoreShaped (.donated pushSc pushOuter) (some pushDonorReply) pushFreshHead

/-- The outer caller's TCB exactly as `pushStoreShaped` holds it: reply-blocked on
the donor and naming the reply object that blocking is about.

One definition, because three checks below need it and two of them used to spell it
again locally — and one of those spellings carried a note saying no assertion read
the `replyObject`, which WS-HP HP5.1 made false by keying the cancellation reclaim's
trigger on that very field. -/
private def pushOuterBlockedTcb : TCB :=
  { mkTcb 93 50 none with
      ipcState := .blockedOnReply (SeLe4n.ObjId.ofNat 97) (some pushDonor),
      replyObject := some pushOuterReply }

private def pushBindingOf (st : SystemState) (tid : SeLe4n.ThreadId) :
    Option SchedContextBinding :=
  (st.getTcb? tid).map (·.schedContextBinding)

private def pushHeadOf (st : SystemState) : Option (Option SeLe4n.ReplyId) :=
  (st.getSchedContext? pushSc).map (·.scReply)

private def pushLinksOf (st : SystemState) (rid : SeLe4n.ReplyId) :
    Option (Option SeLe4n.ReplyId × Option ReplyStackLink) :=
  match st.objects[rid.toObjId]? with
  | some (.reply r) => some (r.prev, r.next)
  | _ => none

/-- The whole of what a splice can write: the frames' links and the context's
head.  `SystemState` has no `BEq`, and comparing this rather than asserting a
single field is what lets "the step is the identity" be checked instead of
described. -/
private def pushStackShape (st : SystemState) :
    Option (Option SeLe4n.ReplyId × Option ReplyStackLink) ×
      Option (Option SeLe4n.ReplyId × Option ReplyStackLink) ×
      Option (Option SeLe4n.ReplyId) :=
  (pushLinksOf st pushDonorReply, pushLinksOf st pushOuterReply, pushHeadOf st)

private def runDonationPushChecks : IO Unit := do
  IO.println "--- §3.18 the donation push at call depth ≥ 2 (WS-OD OD4/OD5/OD6) ---"
  -- OD4.1/OD4.2: a `.donated` donor passes the context on, and the push writes a
  -- new stack frame whose `prev` is the old head.
  match donateSchedContext pushStore pushDonor pushServer pushSc with
  | .error e => assertBool s!"depth-2 push must succeed (got {reprStr e})" false
  | .ok st' =>
    assertBool "depth-2 push: the server holds the context, donated from the donor"
      (pushBindingOf st' pushServer == some (.donated pushSc pushDonor))
    assertBool "depth-2 push: the intermediate donor is unbound"
      (pushBindingOf st' pushDonor == some .unbound)
    assertBool "depth-2 push: the context is bound to the server"
      ((st'.getSchedContext? pushSc).map (·.boundThread) == some (some pushServer))
    assertBool "depth-2 push: the donor's own reply is now the stack head"
      (pushHeadOf st' == some (some pushDonorReply))
    assertBool "depth-2 push: the new frame heads the context and links down to the old head"
      (pushLinksOf st' pushDonorReply == some (some pushOuterReply, some (.head pushSc)))
    -- The fifth store: the old head stops heading the context and links **up**
    -- to the frame pushed above it.  Under the single-linked stack this object
    -- was untouched, which is precisely what left a middle frame unreachable
    -- from above and so unremovable in `O(1)`.
    assertBool "depth-2 push: the old head now links up to the new frame, heading nothing"
      (pushLinksOf st' pushOuterReply == some (none, some (.frame pushDonorReply)))
    -- OD4.5: the chain the push leaves is the two frames, in order.
    assertBool "depth-2 push: the chain walks head-then-outer"
      (donationChainFrom st' pushSc 4 (some pushDonorReply)
         == some [pushDonorReply, pushOuterReply])
  -- OD6.1: the payoff, read off the widened guard through the whole `.call`
  -- donation rather than the raw push.
  match pushDonor.toValid?, pushServer.toValid? with
  | some donorV, some serverV =>
    assertBool "OD4.2: the guard names the donor's EFFECTIVE context"
      (callDonationSchedContext? pushStore pushDonor pushServer == some pushSc)
    match applyCallDonation pushStore donorV serverV with
    | .error e => assertBool s!"depth-2 call donation must succeed (got {reprStr e})" false
    | .ok st' =>
      assertBool "OD6.1: the passive server holds the donated context"
        (pushBindingOf st' pushServer == some (.donated pushSc pushDonor))
      assertBool "OD6.1: ...and the context's bound thread is that server"
        ((st'.getSchedContext? pushSc).map (·.boundThread) == some (some pushServer))
  | _, _ => assertBool "push fixture ids must be valid thread ids" false
  -- NEGATIVE: the guard is the *effective* context, so an `.unbound` donor
  -- donates nothing.  The token stays (the donor is still there); what changes
  -- is the relation the guard reads.
  assertBool "NEGATIVE: an unbound donor donates nothing"
    (callDonationSchedContext?
       (pushStoreShaped .unbound (some pushDonorReply) pushFreshHead)
       pushDonor pushServer == none)
  -- OD4.1 NEGATIVE: the push is FAIL-CLOSED on its frame.  Each mutation keeps
  -- the whole depth-2 chain and breaks exactly one clause of the frame's shape.
  assertBool "NEGATIVE: a donor holding no reply object cannot push"
    (match donateSchedContext
        (pushStoreShaped (.donated pushSc pushOuter) none pushFreshHead)
        pushDonor pushServer pushSc with
     | .error e => e == KernelError.replyCapInvalid
     | .ok _ => false)
  assertBool "NEGATIVE: a donor whose reply object names no Reply cannot push"
    (match donateSchedContext
        (pushStoreShaped (.donated pushSc pushOuter) (some ⟨98⟩) pushFreshHead)
        pushDonor pushServer pushSc with
     | .error e => e == KernelError.objectNotFound
     | .ok _ => false)
  assertBool "NEGATIVE: a donor whose reply already heads a stack cannot push"
    (match donateSchedContext
        (pushStoreShaped (.donated pushSc pushOuter) (some pushDonorReply)
          { pushFreshHead with next := some (.head pushSc) })
        pushDonor pushServer pushSc with
     | .error e => e == KernelError.invalidArgument
     | .ok _ => false)
  assertBool "NEGATIVE: a donor whose reply already sits on a stack cannot push"
    (match donateSchedContext
        (pushStoreShaped (.donated pushSc pushOuter) (some pushDonorReply)
          { pushFreshHead with prev := some pushOuterReply })
        pushDonor pushServer pushSc with
     | .error e => e == KernelError.invalidArgument
     | .ok _ => false)
  -- ...and a *consumed* frame is refused too, with its own error: pushing one
  -- would build a stack whose pop cannot resolve an outer caller, which is the
  -- dead frame this cut exists to make impossible.
  assertBool "NEGATIVE: a donor whose reply has no caller cannot push"
    (match donateSchedContext
        (pushStoreShaped (.donated pushSc pushOuter) (some pushDonorReply)
          { pushFreshHead with caller := none })
        pushDonor pushServer pushSc with
     | .error e => e == KernelError.illegalState
     | .ok _ => false)
  -- OD5.1: the freshening barrier.  A Reply still carrying a stack link is a
  -- live frame; re-linking it to a new caller is the confused deputy of plan
  -- §3.4, and it is refused rather than cleared.  The three shapes below are one
  -- predicate (`Reply.isFree`) read three ways: no link, an upward link, a
  -- downward one.
  assertBool "OD5.1: an unlinked Reply with no caller may be linked to a new caller"
    (match SystemState.linkReply pushDonorReply pushServer
        (pushStoreShaped (.donated pushSc pushOuter) (some pushDonorReply)
          { pushFreshHead with caller := none }) with
     | .ok _ => true | .error _ => false)
  assertBool "OD5.1 NEGATIVE: a caller-free Reply that still heads a stack is refused"
    (match SystemState.linkReply pushDonorReply pushServer
        (pushStoreShaped (.donated pushSc pushOuter) (some pushDonorReply)
          { pushFreshHead with caller := none, next := some (.head pushSc) }) with
     | .error e => e == KernelError.replyCapInvalid
     | .ok _ => false)
  assertBool "OD5.1 NEGATIVE: ...and one that still links down to a frame below"
    (match SystemState.linkReply pushDonorReply pushServer
        (pushStoreShaped (.donated pushSc pushOuter) (some pushDonorReply)
          { pushFreshHead with caller := none, prev := some pushOuterReply }) with
     | .error e => e == KernelError.replyCapInvalid
     | .ok _ => false)
  assertBool "OD5.1: ...and the link never CLEARS the stack links instead"
    (match SystemState.linkReply pushOuterReply pushServer
        (pushStoreShaped (.donated pushSc pushOuter) (some pushDonorReply)
          { pushFreshHead with caller := none }) with
     | .error e => e == KernelError.replyCapInvalid
     | .ok _ => false)
  -- OD5.4: retype refuses both halves of a live stack -- the frame and the head.
  -- Both mutations keep the Reply caller-free — the clause the pre-OD5.4 guard
  -- read — and add exactly one stack link, so a guard reading `caller` and the
  -- stash alone would pass both.
  assertBool "OD5.4 NEGATIVE: a Reply that still heads a stack cannot be retyped"
    (match lifecyclePreRetypeCleanup pushStore pushOuterReply.toObjId
        (.reply { replyId := pushOuterReply, next := some (.head pushSc) })
        (.reply (Reply.empty pushOuterReply)) with
     | .error e => e == KernelError.revocationRequired
     | .ok _ => false)
  assertBool "OD5.4 NEGATIVE: ...and one linked only downward, the top of a cut-off part"
    (match lifecyclePreRetypeCleanup pushStore pushOuterReply.toObjId
        (.reply { replyId := pushOuterReply, prev := some pushDonorReply })
        (.reply (Reply.empty pushOuterReply)) with
     | .error e => e == KernelError.revocationRequired
     | .ok _ => false)
  assertBool "OD5.4 NEGATIVE: a context heading a reply stack cannot be retyped"
    (match lifecyclePreRetypeCleanup pushStore pushSc.toObjId
        (.schedContext { SchedContext.empty pushSc with scReply := some pushOuterReply })
        (.schedContext (SchedContext.empty pushSc)) with
     | .error e => e == KernelError.revocationRequired
     | .ok _ => false)
  assertBool "OD5.4: ...and a free Reply heading no stack still retypes"
    (match lifecyclePreRetypeCleanup pushStore pushDonorReply.toObjId
        (.reply (Reply.empty pushDonorReply)) (.reply (Reply.empty pushDonorReply)) with
     | .ok _ => true | .error _ => false)
  assertBool "OD5.4: ...and a context heading no stack still retypes"
    (match lifecyclePreRetypeCleanup pushStore pushSc.toObjId
        (.schedContext (SchedContext.empty pushSc))
        (.schedContext (SchedContext.empty pushSc)) with
     | .ok _ => true | .error _ => false)
  -- OD5.2: the middle-caller policy, from the cancellation end.  The reclaim
  -- fires for the immediate donor and declines below the cut; both are the
  -- chosen `severAtCut` policy rather than an omission.
  -- **WS-HP HP5.3**: both restated on the STACK, which is what the trigger reads
  -- since HP5.1.  The first fires because the victim's own frame heads the context;
  -- the second declines because a frame sits above it — and that state is now the
  -- one the **live push** produces, rather than a hand-shaped `.unbound` donor.
  -- Before this correction both passed for the same wrong reason: the TCB they
  -- passed carried no `replyObject` at all, so the trigger declined on the first
  -- too and the pair discriminated nothing.
  assertBool "OD5.2: the reclaim fires when the victim's own frame heads the context"
    (Lifecycle.Suspend.cancelledCallerDonation? pushStore pushOuter pushOuterBlockedTcb
       == some (pushSc, pushDonor))
  assertBool "OD5.2: the reclaim declines below the cut (a frame sits above the victim's)"
    (match donateSchedContext pushStore pushDonor pushServer pushSc with
     | .ok pushed =>
         Lifecycle.Suspend.cancelledCallerDonation? pushed pushOuter pushOuterBlockedTcb == none
     | .error _ => false)
  assertBool "HP6.8: the policy this kernel implements is `spliceOutTheCut`"
    (cancelledMiddleCallerPolicy == CancelledMiddleCallerPolicy.spliceOutTheCut)
  -- OD4.7: the `.call` footprint already declares every object the push writes.
  assertBool "OD4.7: the resolved `.call` footprint declares the donated context"
    (((lockSet_endpointCallOnCore pushStore (SeLe4n.ObjId.ofNat 97) pushDonor
        (SeLe4n.ObjId.ofNat 0)).pairs.any
        (fun p => p.1 == schedContextLock pushSc && p.2 == AccessMode.write)))

/-- **`v0.35.4`: the middle-caller removal, and the wedge it removes.**

Its own runner rather than a tail of the push checks: the C code generator
nests a `do`-block's statements, and a helper past roughly 150 Lean lines
compiles to an `if`-tree that can exceed clang's bracket limit.  The boundary
resets the nesting, and the concern is distinct anyway -- the push builds the
stack these checks then cut. -/
private def runMiddleCallerRemovalChecks : IO Unit := do
  IO.println "--- §3.19 the middle-caller removal, and the wedge it removes (`v0.35.4`; spliced since HP6.3) ---"
  -- The state a depth-2 push leaves is exactly the one the pinning defect
  -- needed: two frames, the outer caller's below the donor's.  Cancelling the
  -- *outer* caller consumes a frame that is not the head, and before this cut
  -- the head went on linking down to it.  Both directions are exercised below,
  -- because a witness that ran only the repaired path would pass before the fix
  -- and after it.
  match donateSchedContext pushStore pushDonor pushServer pushSc with
  | .error e =>
    assertBool s!"the removal witness needs a depth-2 push (got {reprStr e})" false
  | .ok pushed =>
    -- The outer caller, exactly as the store holds it (WS-HP HP5: one definition,
    -- since the reclaim's trigger now reads its `replyObject`).
    let outerTcb : TCB := pushOuterBlockedTcb
    -- Step one: the splice's WRITING arm.  Every `spliceReplyFrameOut` result
    -- proved elsewhere is discharged on a state whose frame has nothing above
    -- it, where the step is the identity; this is the arm that stores.
    let detached := spliceThreadReplyFrameOut pushed outerTcb
    assertBool "the removal clears the `prev` of the frame ABOVE the cancelled one (a bottom frame: the splice's sever arm)"
      (pushLinksOf detached pushDonorReply == some (none, some (.head pushSc)))
    assertBool "...and writes nothing on the cancelled frame itself — the consume does that"
      (pushLinksOf detached pushOuterReply == some (none, some (.frame pushDonorReply)))
    assertBool "...and the context still heads the same frame"
      (pushHeadOf detached == some (some pushDonorReply))
    -- Step two: the consume, in the order the cancellation arm runs them.
    let severed := Lifecycle.Suspend.consumeReplyLink detached pushOuter outerTcb
    assertBool "the consumed frame leaves the structure entirely"
      (pushLinksOf severed pushOuterReply == some (none, none))
    assertBool "...with its caller gone, so `Reply.wellFormed` holds of it"
      (match severed.getReply? pushOuterReply with
       | some r => r.caller == none && r.isFree
       | none => false)
    -- The payoff: the later pop SUCCEEDS.  The head is now the bottom of its own
    -- stack, so the outer-caller resolution answers `none` and the context
    -- settles on the original owner.
    assertBool "the pop resolves the severed stack to its bottom"
      (match replyStackOuterCaller? severed pushSc with
       | .ok none => true | _ => false)
    assertBool "PAYOFF: the pop after a severed middle caller succeeds"
      (match returnDonatedSchedContextResolved severed pushServer pushSc pushDonor with
       | .ok _ => true | .error _ => false)
    assertBool "...and hands the context back to the original owner"
      (match returnDonatedSchedContextResolved severed pushServer pushSc pushDonor with
       | .ok st' => pushBindingOf st' pushDonor == some (.bound pushSc)
       | .error _ => false)
    assertBool "...leaving no frame on the context's stack but the head"
      (match returnDonatedSchedContextResolved severed pushServer pushSc pushDonor with
       | .ok st' => pushHeadOf st' == some none
       | .error _ => false)
    -- NEGATIVE, and the reason this witness exists: the SAME consume with the
    -- splice omitted.  Every object is still there and every field the consume
    -- writes is identical; what changes is the relation between the head and the
    -- frame below it.  That state is what wedged the chain — the pop refuses and
    -- the context can never leave the server.
    let wedged := Lifecycle.Suspend.consumeReplyLink pushed pushOuter outerTcb
    assertBool "NEGATIVE: without the splice the head still links down to the consumed frame"
      (pushLinksOf wedged pushDonorReply == some (some pushOuterReply, some (.head pushSc)))
    assertBool "NEGATIVE: ...and the outer-caller resolution refuses it"
      (match replyStackOuterCaller? wedged pushSc with
       | .error e => e == KernelError.invalidArgument
       | .ok _ => false)
    assertBool "NEGATIVE: ...so the pop wedges, writing nothing"
      (match returnDonatedSchedContextResolved wedged pushServer pushSc pushDonor with
       | .error e => e == KernelError.invalidArgument
       | .ok _ => false)
    -- The splice is FAIL-CLOSED and the wrapper is TOTAL: a frame above that
    -- does not link back is refused by the primitive, and the cancellation still
    -- runs rather than failing — which is what keeps a severed stack's lower
    -- frames cancellable.  Both halves, since the primitive's refusal and the
    -- wrapper's fold are different facts.
    -- The severed state is itself the shape that must be refused: the frame
    -- below still links UP to the head, and the head no longer links down to it.
    -- That is the state a second cancellation — of the caller below the cut —
    -- meets, so the refusal and the wrapper's fold together are what keep a
    -- severed stack's lower frames cancellable rather than wedged in turn.
    assertBool "the splice refuses a frame above that does not link back"
      (match spliceReplyFrameOut detached pushOuterReply with
       | .error e => e == KernelError.invalidArgument
       | .ok _ => false)
    assertBool "...and the cancellation wrapper folds that refusal to the identity"
      (pushStackShape (spliceThreadReplyFrameOut detached outerTcb)
         == pushStackShape detached)
    assertBool "...so the caller below a cut can still be cancelled, and leaves cleanly"
      (match (Lifecycle.Suspend.consumeReplyLink
                (spliceThreadReplyFrameOut detached outerTcb)
                pushOuter outerTcb).getReply? pushOuterReply with
       | some r => r.isFree
       | none => false)
    -- ...and a frame above that names no Reply at all is a different refusal,
    -- so the two fail-closed arms are told apart rather than merged.
    assertBool "the splice refuses a frame above that resolves to no Reply"
      (match spliceReplyFrameOut
          (pushStoreShaped (.donated pushSc pushOuter) (some pushDonorReply)
            { pushFreshHead with next := some (.frame ⟨98⟩) })
          pushDonorReply with
       | .error e => e == KernelError.objectNotFound
       | .ok _ => false)
    assertBool "the splice is the identity for a frame with nothing above it"
      (pushStackShape (spliceThreadReplyFrameOut pushed
         { outerTcb with replyObject := some pushDonorReply }) == pushStackShape pushed)
    assertBool "...and for a thread holding no reply object at all"
      (pushStackShape (spliceThreadReplyFrameOut pushed
         { outerTcb with replyObject := none }) == pushStackShape pushed)

-- ============================================================================
-- WS-RM — seL4's `reply_remove` on the reply path (`v0.35.6`)
-- ============================================================================

/-- **WS-RM**: the depth-2 chain's outer caller, carrying the reply object it is
blocked on.

`§3.19`'s removal witness builds the same TCB for the *cancellation* path; the
reply path answers the very same frame, which is the point — one removal step,
two callers of it. -/
private def replyRemovalOuterTcb : TCB := pushOuterBlockedTcb

/-- **WS-RM**: a thread holding a *copy* of the outer caller's reply capability,
homed on core 1 -- a **delegated** replier.

`endpointReplyOnCore` deliberately does not gate on the replier being the thread
the call recorded (PR #822 review): authority flows from holding the reply
capability, and a copied or minted one held by another server is legitimate
seL4-MCS delegation.  That is what lets this witness answer the outer caller
**out of order** -- `pushDonor`, the thread the outer call recorded, has a call
of its own still outstanding, so the frame the delegate answers is *not* the
head of its stack. -/
private def replyRemovalDelegate : SeLe4n.ThreadId := ⟨99⟩

/-- **WS-HP HP10.9**: the state a depth-2 donating chain is built *from* — the
reservation's **owner** still holds it, `.bound`.

`pushStore` is that state's successor with the first push already applied by hand,
which is why nothing in this tree had ever measured the field HP10 turns on:
`SchedContext.donationOrigin` is written by `donateSchedContext` on a **first**
push (`donationFirstPush` — the donor's binding still *owns* the context it is
lending), and every fixture that carried an origin set it directly.  A witness
whose field is supplied by its fixture asserts nothing about the production write
that is supposed to supply it.

So this is `pushStore` with the first push undone: the context is bound to
`pushOuter` and heads no stack, `pushOuterReply` is free (both links clear, its
caller set), and `pushOuter` is `.bound pushSc`.  It is `.blockedOnReply` on
`pushDonor` already, which is not a liberty — `endpointCall` blocks the caller and
links its reply object *before* `applyCallDonation` runs, so `.bound` **and**
`.blockedOnReply` is exactly the state the live `.call` hands the donation. -/
private def pushOwnerStore : SystemState :=
  (BootstrapBuilder.empty
    |>.withObject pushSc.toObjId
        (.schedContext { SchedContext.empty pushSc with boundThread := some pushOuter })
    |>.withObject pushOuterReply.toObjId
        (.reply { replyId := pushOuterReply, caller := some pushOuter })
    |>.withObject pushDonorReply.toObjId (.reply pushFreshHead)
    |>.withObject pushDonor.toObjId
        (.tcb { mkTcb 91 40 none with replyObject := some pushDonorReply })
    |>.withObject pushServer.toObjId (.tcb (mkTcb 92 30 none))
    |>.withObject pushOuter.toObjId
        (.tcb { pushOuterBlockedTcb with schedContextBinding := .bound pushSc })
    |>.build)

/-- **WS-HP HP10.9**: the depth-2 chain, built by the live push **twice** — so the
reservation's origin is recorded by production rather than by this fixture.

`pushOuter` lends to `pushDonor` (a **first** push: the donor owns what it lends,
so the origin is recorded), and `pushDonor` lends on to `pushServer` (an
**onward** push: the donor holds a `.donated` binding, `ownScId?` is `none`, and
the field is left alone — which is what makes it the *origin* rather than the
immediate donor).  The result is `pushStore`'s own post-push shape plus that one
field, and §3.20 asserts the agreement, so the hand-built fixture is known to be a
state the kernel reaches rather than assumed to be. -/
private def replyRemovalChain : Except KernelError SystemState :=
  match donateSchedContext pushOwnerStore pushOuter pushDonor pushSc with
  | .error e => .error e
  | .ok depth1 => donateSchedContext depth1 pushDonor pushServer pushSc

/-- **WS-RM**: the intermediate caller of a live depth-2 chain, blocked on its own
reply to `pushServer`.

One definition, because the in-order contrast, the in-order reply and the
depth-two accounting differential all need it and three of them used to spell it
again locally. -/
private def replyRemovalInOrderDonorTcb : TCB :=
  { mkTcb 91 40 none with
      schedContextBinding := SchedContextBinding.unbound,
      ipcState := ThreadIpcState.blockedOnReply (SeLe4n.ObjId.ofNat 97) (some pushServer),
      replyObject := some pushDonorReply }

/-- **WS-RM**: the removal witness's state, from a pushed depth-2 chain: the outer
caller reply-blocked on the intermediate one, plus the **delegate** that holds a
copy of its reply capability. -/
private def replyRemovalStateOf (pushed : SystemState) : SystemState :=
  { pushed with
      objects := (pushed.objects.insert pushOuter.toObjId (.tcb replyRemovalOuterTcb)).insert
        replyRemovalDelegate.toObjId (.tcb (mkTcb 99 45 (some c1))) }

/-- **WS-HP HP10.9**: the whole depth-2 sequence, from a pushed chain to the
bindings the live `.reply` spine leaves — `(pushOuter's, pushDonor's)`.

A delegate answers the owner **out of order**, whose frame is the stack's bottom
and so leaves the stack; then the intermediate caller's own server replies **in
order**, through `endpointReplyCrossCoreDispatch` — the live `.reply` arm, leg and
pop and reversion and migration together, because the pop is inside it and the pop
is where the redirect lives.

Taking the chain as a *parameter* is what makes this witness decisive without a
mutation.  A mutation of the production code fails to **elaborate** rather than
failing this suite — the origin write, the resolver and the three pops are each
pinned as theorems, which is the situation §3.23 recorded for the splice's store
shape — so what discriminates is a differential *within* the suite: this function
applied to a chain whose first push recorded an origin, and to `pushStore`'s,
which predates HP10.4 and records none.  The two chains differ in exactly one
field and the reservation ends on a different thread. -/
private def replyRemovalOutcome (pushed : SystemState) :
    Option (Option SchedContextBinding × Option SchedContextBinding) :=
  match endpointReplyOnCore replyRemovalDelegate pushOuter IpcMessage.empty bootCoreId
      (replyRemovalStateOf pushed) with
  | (_, .error _) => none
  | (postOoO, .ok _) =>
    let stInOrderPre : SystemState :=
      { postOoO with
          objects := postOoO.objects.insert pushDonor.toObjId (.tcb replyRemovalInOrderDonorTcb) }
    match endpointReplyCrossCoreDispatch pushServer pushDonor IpcMessage.empty bootCoreId
        stInOrderPre with
    | (_, .error _) => none
    | (stFinal, .ok _) => some (pushBindingOf stFinal pushOuter, pushBindingOf stFinal pushDonor)

private def runReplyFrameRemovalChecks : IO Unit := do
  IO.println "--- §3.20 WS-RM: the reply path takes the answered frame off its stack ---"
  -- **WS-HP HP10.9**: the first push, measured on its own, because it is the step
  -- that records the reservation's origin and nothing in the tree had run it.
  match donateSchedContext pushOwnerStore pushOuter pushDonor pushSc with
  | .error e =>
    assertBool s!"the depth-1 push from the OWNER must succeed (got {reprStr e})" false
  | .ok depth1 =>
    assertBool "PRE: a FIRST push records the reservation's origin"
      ((depth1.getSchedContext? pushSc).bind (·.donationOrigin) == some pushOuter)
    -- ...and it reproduces the hand-built depth-1 fixture exactly, which is what
    -- makes `pushStore` a state the kernel reaches rather than one this suite
    -- asserts about.  The origin is the single field that differs, and it differs
    -- because `pushStore` predates HP10.4.
    assertBool "...and otherwise reproduces `pushStore`'s stack shape"
      (pushStackShape depth1 == pushStackShape pushStore)
    assertBool "...and `pushStore`'s bindings"
      (pushBindingOf depth1 pushOuter == some .unbound
        && pushBindingOf depth1 pushDonor == some (.donated pushSc pushOuter)
        && pushBindingOf depth1 pushServer == pushBindingOf pushStore pushServer)
    assertBool "...while `pushStore` itself records no origin, being older than HP10.4"
      ((pushStore.getSchedContext? pushSc).bind (·.donationOrigin) == none)
  match replyRemovalChain with
  | .error e =>
    assertBool s!"the removal witness needs a depth-2 push (got {reprStr e})" false
  | .ok pushed =>
    -- **WS-HP HP10.9**: the ONWARD push leaves the origin alone.  A field that
    -- tracked the immediate donor would read `pushDonor` here, and the immediate
    -- donor is already recoverable from `.donated scId owner` — so this assertion
    -- is what distinguishes an *origin* from a duplicate of the binding.
    assertBool "PRE: an ONWARD push preserves the origin — it is not the immediate donor"
      ((pushed.getSchedContext? pushSc).bind (·.donationOrigin) == some pushOuter)
    assertBool "...and the onward push's own donor is recorded in the BINDING, not the field"
      (pushBindingOf pushed pushServer == some (.donated pushSc pushDonor))
    -- The stack a depth-2 `Call` chain leaves: `pushDonorReply` heads the
    -- context and links down to `pushOuterReply`, which links back up.  Built
    -- through the same `replyRemovalStateOf` the accounting differential below
    -- drives, so the shape the step assertions measure is the shape it measures.
    let stChain : SystemState := replyRemovalStateOf pushed
    assertBool "pre: the donor's frame heads the context and links down to the outer one"
      (pushLinksOf stChain pushDonorReply == some (some pushOuterReply, some (.head pushSc)))
    assertBool "pre: the outer frame links up to the head, heading nothing"
      (pushLinksOf stChain pushOuterReply == some (none, some (.frame pushDonorReply)))
    -- The in-order contrast's own pre-state: `pushDonor` blocked on its own
    -- reply to `pushServer`, which is what a live depth-2 chain looks like.
    let stChainInOrder : SystemState :=
      { stChain with
          objects := stChain.objects.insert pushDonor.toObjId
            (.tcb replyRemovalInOrderDonorTcb) }
    -- The footprint declares the frame the removal writes, resolved from the
    -- answered thread's own reply object.
    assertBool "the footprint resolves the frame ABOVE the answered one"
      (answeredReplyFrameAbove? stChain pushOuter == some pushDonorReply)
    -- **Out of order**: the answered caller is the one BELOW the head, because
    -- the recorded replier `pushDonor` has a call of its own still outstanding.
    assertBool "pre: the outer caller records `pushDonor` as its replier"
      (match stChain.getTcb? pushOuter with
       | some t => t.ipcState == .blockedOnReply (SeLe4n.ObjId.ofNat 97) (some pushDonor)
       | none => false)
    -- Through the DELEGATE, which is what makes the reply out of order: the
    -- recorded replier `pushDonor` has a call of its own still outstanding, so
    -- the frame this answers sits below the head rather than being it.
    let (postOoO, resOoO) :=
      endpointReplyOnCore replyRemovalDelegate pushOuter IpcMessage.empty bootCoreId stChain
    assertBool "the out-of-order reply through a DELEGATED reply capability succeeds"
      (match resOoO with | .ok _ => true | .error _ => false)
    assertBool "the frame ABOVE the answered one has its `prev` cleared"
      (pushLinksOf postOoO pushDonorReply == some (none, some (.head pushSc)))
    assertBool "...and the answered frame is off the stack entirely (`Reply.isFree`)"
      (match postOoO.getReply? pushOuterReply with
       | some r => r.isFree
       | none => false)
    assertBool "...and the context still heads the donor's frame"
      (pushHeadOf postOoO == some (some pushDonorReply))
    -- **PAYOFF**: the in-order reply that follows now succeeds.  Before WS-RM
    -- the out-of-order reply left `pushDonorReply.prev` naming a consumed frame,
    -- the walk's reciprocity test refused it, and this call returned
    -- `.invalidArgument` — a wedged call chain reached from an ordinary reply.
    --
    -- **WS-HP HP10.9**: this reply is now run through the **live `.reply` spine**
    -- rather than through `endpointReplyOnCore` alone, because the spine is what
    -- performs the pop, and the pop is where the redirect lives.  The accounting
    -- assertions below used to measure `returnDonatedSchedContextResolved`
    -- directly, which was an accurate proxy for the pop while nothing redirected
    -- and is a proxy that omits the redirect now — *a proxy is not the fact*.
    let stInOrderPre : SystemState :=
      { postOoO with
          objects := postOoO.objects.insert pushDonor.toObjId
            (.tcb replyRemovalInOrderDonorTcb) }
    let (stInOrderLeg, resInOrderLeg) :=
      endpointReplyOnCore pushServer pushDonor IpcMessage.empty bootCoreId stInOrderPre
    assertBool "PAYOFF: the in-order reply that follows succeeds — the wedge is gone"
      (match resInOrderLeg with | .ok _ => true | .error _ => false)
    -- ...and the pop the reply chain runs after it resolves, rather than
    -- refusing a stale link.  **This is the answer that names the WRONG thread**:
    -- the owner's own frame has left the stack, so reachability reports the
    -- surviving frame as the bottom and the pop's reachability recipient is the
    -- thread that answered it.  HP10.7's redirect is what overrides it.
    assertBool "PAYOFF: the pop resolves the remaining stack to its bottom"
      (match replyStackOuterCaller? postOoO pushSc with
       | .ok none => true | _ => false)
    -- **WS-HP HP10.9 — THE PAYOFF, WHERE THIS ROW USED TO CARRY A COST.**
    --
    -- Up to `v0.35.52` these three assertions measured the loss: taking a caller
    -- out of the middle of a chain is destructive to the donation accounting, the
    -- removal moves no scheduling context, and the later pop donated to whatever
    -- the remaining stack said was outermost — so the reservation settled `.bound`
    -- on `pushDonor`, a thread strictly *inside* the chain, and `pushOuter`, which
    -- owned it, was left `.unbound` for good.  Reachable from an ordinary
    -- delegated reply.  seL4-MCS has the same loss: `reply_pop` donates to the
    -- answered frame's own `replyTCB`.
    --
    -- **This is a TWO-frame stack, so HP6's splice provably could not reach it**:
    -- `pushOuterReply` is the bottom, nothing sits below it to reconnect, and
    -- `severAtCut` and `spliceOutTheCut` write the same `none` into the frame
    -- above.  The sentence that explains why this witness cannot *measure* the
    -- depth-≥ 3 defect is the reason the depth-2 defect survived the fix for it.
    -- What closes it is the reservation's recorded **origin**
    -- (`SchedContext.donationOrigin`, written by the first push above) read in
    -- place of stack reachability — `donationAccountingPreserved_atCallDepthTwo`.
    assertBool "PAYOFF: the live reply spine settles the reservation on its OWNER, not the intermediate caller"
      (replyRemovalOutcome pushed == some (some (.bound pushSc), some .unbound))
    -- **NEGATIVE — the decisive differential, and it needs no mutation.**  A
    -- mutation of the production code here fails to *elaborate* rather than
    -- failing this suite: the origin write, the resolver and the three reply-path
    -- pops are each pinned as theorems, which is the situation §3.23 recorded for
    -- the splice's store shape.  So what makes the payoff above discriminate is
    -- the same function applied to `pushStore`'s own chain, which predates HP10.4
    -- and records **no** origin: one field differs, and the reservation ends on a
    -- different thread.  These are the values this row asserted up to `v0.35.52`,
    -- and the outcome every state this tree reached before HP10.4 still has.
    assertBool "NEGATIVE: with NO origin recorded the same spine settles it on the INTERMEDIATE caller"
      (match donateSchedContext pushStore pushDonor pushServer pushSc with
       | .ok noOrigin => replyRemovalOutcome noOrigin == some (some .unbound, some (.bound pushSc))
       | .error _ => false)
    assertBool "PAYOFF: ...which is a DIFFERENT thread, so the redirect is not vacuous"
      (!(pushOuter == pushDonor))
    -- **NEGATIVE — the retired reachability reading, spelled out beside the live
    -- one.**  `returnDonatedSchedContextResolved` at the answered caller is what
    -- the pop did before HP10.7, and it is still the identity everywhere the
    -- redirect declines, so it cannot be deleted; what it must not be is the
    -- recipient at the bottom of a stack whose owner's frame was removed.  These
    -- two assertions are the values this row asserted up to `v0.35.52`, so a
    -- revert of the flip does not merely fail the payoff above — it makes these
    -- pass, which is what makes the pair known to discriminate rather than merely
    -- to pass (the lesson HP5.5 and HP7 recorded on this same surface).
    assertBool "NEGATIVE: the retired reachability recipient would settle it on the INTERMEDIATE caller"
      (match returnDonatedSchedContextResolved stInOrderLeg pushServer pushSc pushDonor with
       | .ok st' => pushBindingOf st' pushDonor == some (.bound pushSc)
       | .error _ => false)
    assertBool "NEGATIVE: ...leaving the original owner unbound, having lost its reservation"
      (match returnDonatedSchedContextResolved stInOrderLeg pushServer pushSc pushDonor with
       | .ok st' => pushBindingOf st' pushOuter == some .unbound
       | .error _ => false)
    -- ...and the live pop's own recipient is the origin rather than that thread,
    -- read at the state the pop runs on.  The two readings computed side by side
    -- is what makes the flip a measurement.
    assertBool "PAYOFF: the live pop's recipient is the recorded ORIGIN, not the answered caller"
      (replyDonationRecipient stInOrderLeg pushSc pushDonor == pushOuter)
    -- **AGREEMENT, where this row used to carry a contrast.**  An IN-ORDER unwind
    -- never lost the reservation, and HP10.9 leaves it byte for byte: the pop is
    -- at a `some` arm (the surviving stack still names an outer caller), where
    -- `donationOriginRecipient?` is silent by construction
    -- (`replyDonationRecipient_eq_of_outer_some`), so the intermediate caller
    -- receives it `.donated … pushOuter` — still owed outward — exactly as before.
    -- That the two routes now *agree* on where the reservation ends up is the
    -- closure of the defect, which is why this reads as an agreement rather than
    -- as a contrast.
    assertBool "AGREEMENT: an IN-ORDER unwind still leaves it owed outward, not owned"
      (match endpointReplyOnCore pushServer pushDonor IpcMessage.empty bootCoreId
                stChainInOrder with
       | (stIn, .ok _) =>
           (match returnDonatedSchedContextResolved stIn pushServer pushSc pushDonor with
            | .ok st' => pushBindingOf st' pushDonor == some (.donated pushSc pushOuter)
            | .error _ => false)
       | (_, .error _) => false)
    -- ...and the SECOND pop of that unwind delivers it home, so "reaches its
    -- owner" is measured on both routes rather than asserted for one.  The
    -- redirect is the identity here too: at the bottom of this stack reachability
    -- and the recorded origin name the same thread, which is what "inert wherever
    -- it was already right" means operationally.
    assertBool "AGREEMENT: ...and the second pop of that unwind delivers it to the owner"
      (match endpointReplyCrossCoreDispatch pushServer pushDonor IpcMessage.empty
                bootCoreId stChainInOrder with
       | (stAfterFirst, .ok _) =>
           (match endpointReplyCrossCoreDispatch pushDonor pushOuter IpcMessage.empty
                     bootCoreId stAfterFirst with
            | (stAfterSecond, .ok _) =>
                pushBindingOf stAfterSecond pushOuter == some (.bound pushSc)
            | (_, .error _) => false)
       | (_, .error _) => false)
    -- NEGATIVE, and the reason this witness exists: the SAME reply with the
    -- splice omitted.  Every object is present and every field the consume
    -- writes is identical; what changes is the head's link down to a frame whose
    -- caller is gone.  A fixture that exercised only the in-order path would
    -- pass before this cut and after it.
    let wedged := SystemState.consumeCallerReply pushOuter pushOuterReply stChain
    assertBool "NEGATIVE: without the splice the head still links down to the answered frame"
      (match wedged with
       | .ok ((), st') => pushLinksOf st' pushDonorReply == some (some pushOuterReply,
           some (.head pushSc))
       | .error _ => false)
    assertBool "NEGATIVE: ...and the outer-caller resolution refuses that stack"
      (match wedged with
       | .ok ((), st') =>
           (match replyStackOuterCaller? st' pushSc with
            | .error e => e == KernelError.invalidArgument
            | .ok _ => false)
       | .error _ => false)
    assertBool "NEGATIVE: ...so the donation return wedges, writing nothing"
      (match wedged with
       | .ok ((), st') =>
           (match returnDonatedSchedContextResolved st' pushServer pushSc pushDonor with
            | .error e => e == KernelError.invalidArgument
            | .ok _ => false)
       | .error _ => false)
    -- The in-order path is unchanged: the head has nothing above it, so the
    -- removal is the bare consume and every pre-WS-RM result holds verbatim.
    assertBool "the in-order reply's answered frame has nothing above it"
      (answeredReplyFrameAbove? stChain pushDonor == none)

/-- **WS-RM**: a second client for the passive server's steady state, with its
own scheduling context — the request the `seL4_ReplyRecv` loop takes after
answering the first. -/
private def loopCaller2 : SeLe4n.ThreadId := ⟨861⟩
private def loopCaller2Sc : SeLe4n.SchedContextId := SchedContextId.ofNat 862
private def loopCaller2Reply : SeLe4n.ReplyId := ⟨863⟩

private def loopCaller2SchedContext : SchedContext :=
  { scId := loopCaller2Sc, budget := ⟨100⟩, period := ⟨1000⟩, priority := ⟨55⟩,
    deadline := ⟨0⟩, domain := ⟨0⟩, budgetRemaining := ⟨50⟩,
    boundThread := some loopCaller2, isActive := true }

/-- `stDonBase` plus a second, ready client holding its own context and its own
free Reply object. -/
private def stLoopBase : SystemState :=
  { stDonBase with
      objects := ((stDonBase.objects.insert loopCaller2Sc.toObjId
          (.schedContext loopCaller2SchedContext)).insert loopCaller2.toObjId
          (.tcb { mkTcb 861 55 none with schedContextBinding := .bound loopCaller2Sc })).insert
          loopCaller2Reply.toObjId (.reply { replyId := loopCaller2Reply }) }

private def runReplyRecvLoopCompletionChecks : IO Unit := do
  IO.println "--- §3.21 WS-RM: the passive server's `seL4_ReplyRecv` loop completes ---"
  -- The MCS passive-server steady state, built the way a real one arrives at it:
  -- the server blocks on `Recv`, the first client `Call`s (donating its
  -- context), the server's home core dispatches it, and a second client `Call`s
  -- and queues behind the busy server.
  match okPair (endpointReceiveDualOnCore donEp donServer (some donReply) c1 stLoopBase) with
  | none => assertBool "loop setup: the server's first `Recv` succeeds" false
  | some (stRecv, _) =>
    let (stCall, resCall) := endpointCallCrossCoreDispatch donEp donClient IpcMessage.empty
      AccessRightSet.empty (SeLe4n.Slot.ofNat 0) c0 stRecv
    assertBool "loop setup: the first client's donating `Call` succeeds"
      (match resCall with | .ok _ => true | .error _ => false)
    match okExcept (handleRescheduleSgiOnCore stCall c1) with
    | none => assertBool "loop setup: core 1 handles the call wake SGI" false
    | some stDispatched =>
      let (stQueued, resQueued) := endpointCallCrossCoreDispatch donEp loopCaller2
        IpcMessage.empty AccessRightSet.empty (SeLe4n.Slot.ofNat 0) c0 stDispatched
      assertBool "loop setup: the second client's `Call` queues behind the busy server"
        (match resQueued with | .ok _ => true | .error _ => false)
      -- The fact that makes the ORDER of the legs load-bearing: the answered
      -- caller's Reply **heads** its scheduling context, and `Reply.consumed`
      -- keeps a head's links deliberately (the pop validates the head by them).
      assertBool "pre: the answered caller's Reply heads the donated context"
        (match stQueued.getReply? donReply with
         | some r => r.next == some (.head scClient)
         | none => false)
      -- **The chain payoff's own condition, exhibited on this state.**
      -- `endpointReplyCrossCoreDispatch_preserves_donationChainWellFormed` used to
      -- hold under `answeredHeadContextIsServerDonation`, a pre-state fact neither
      -- `ipcInvariantFull` nor `donationChainWellFormed` entails (the bundle
      -- relates a caller's recorded reply target to no donation, and the chain
      -- invariant carries no binding clause at all).  A hypothesis nothing exhibits
      -- is indistinguishable from one that cannot hold, so the two rows below are
      -- its premise and its conclusion at the only quadruple that satisfies them,
      -- on a state a real MCS chain reaches through the live operations.
      --
      -- **WS-HP HP4.4 and HP7 (`v0.35.46`).**  HP4.4 replaced that condition in the
      -- composite with the strictly weaker `replyFrameHeadIsBound`, and HP7 deleted
      -- it -- so these two rows now exhibit the **retired** reading, kept because
      -- they are what shows the retired and live conditions coincide on this shape,
      -- and the row after them exhibits what the composite actually carries.  Both
      -- are worth having: a cut that changed only the live condition would leave
      -- the first two passing, and a cut that changed only the trigger would leave
      -- the third passing.
      assertBool "the RETIRED chain condition's premise: the answered caller records the server"
        (recordedReplyServer? stQueued donClient == some donServer)
      assertBool "...and its conclusion: that server holds the context that frame heads"
        (replyDonationReturn? stQueued donServer == some (scClient, donClient))
      -- ...and the LIVE condition, which is what
      -- `endpointReplyCrossCoreDispatch_preserves_donationChainWellFormed` carries:
      -- the context the answered frame heads is bound to *some* thread.  Weaker by
      -- construction -- it names no particular server -- and here the holder it
      -- names is the recorded server, which is the coincidence HP6.8's splice can
      -- break at an orphan head.
      assertBool "the LIVE chain condition: the head context is bound, and here to that server"
        (replyFrameHeadContext? stQueued donReply == some scClient
         && replyFrameHeadHolder? stQueued donReply == some (scClient, donServer))
      -- Leg one alone: the caller is answered and the Reply is NOT free, because
      -- it still heads the context.  `Reply.isFree` reads both links, so the
      -- receive leg below cannot re-link this object yet.
      let (stAfterReply, resAfterReply) :=
        endpointReplyOnCore donServer donClient IpcMessage.empty c1 stQueued
      assertBool "the reply leg succeeds"
        (match resAfterReply with | .ok _ => true | .error _ => false)
      assertBool "...and the answered Reply is NOT free: it still heads the context"
        (match stAfterReply.getReply? donReply with
         | some r => r.caller == none && !r.isFree && r.next == some (.head scClient)
         | none => false)
      -- **NEGATIVE — the defect.**  The pre-WS-RM order ran the receive leg
      -- here, on exactly this state, and `linkCallerReply` refused the
      -- still-heading Reply.  Every token is present: the reply leg ran, the
      -- receive leg ran, the same Reply object was supplied.  What was wrong was
      -- the order of the pop, and the consequence was that no passive server
      -- whose client had donated could ever complete a `seL4_ReplyRecv`.
      assertBool "NEGATIVE: the receive leg on the un-popped state refuses `.replyCapInvalid`"
        (match (endpointReceiveDualWithCapsOnCore donEp donServer (some donReply) cnRoot
                  (SeLe4n.Slot.ofNat 0) c1 stAfterReply).2 with
         | .error e => e == KernelError.replyCapInvalid
         | .ok _ => false)
      -- Leg two, in the live order: the donation pop runs between the legs, and
      -- it is what frees the Reply.
      --
      -- **WS-HP HP4.5: and this is the state that forces the pop's key.**  The
      -- reply leg ran `consumeCallerReply`, so the answered caller no longer
      -- holds a reply object and nothing keyed on *the caller* can find the
      -- frame any more -- which is why `.reply`'s pop reads `answeredReplyObject?`
      -- on its PRE-state and this arm takes `rid` from the reply capability it
      -- was invoked with.  Both assertions below are about this state, after the
      -- leg: the caller-keyed route is gone and the frame-keyed one still answers.
      assertBool "HP4.5: the reply leg has consumed the caller's reply object"
        (answeredReplyObject? stAfterReply donClient == none)
      assertBool "HP4.5: ...while the frame still names the holder and the context"
        (replyFrameHeadHolder? stAfterReply donReply == some (scClient, donServer))
      match replyRecvPopDonation donReply donClient stAfterReply with
      | .error e => assertBool s!"the donation pop must succeed (got {reprStr e})" false
      | .ok (returned?, stPopped) =>
        -- **PR #897 review**: the pop answers the context AND the thread it
        -- unbound, so the post-receive half deschedules that thread rather than
        -- `recordedReplyServer?` — which HP6.8's splice makes a different thread.
        assertBool "the pop hands the context back to its original owner, naming the holder"
          (returned? == some (scClient, donServer))
        assertBool "...and the answered Reply is free once its frame comes off the stack"
          (match stPopped.getReply? donReply with
           | some r => r.isFree
           | none => false)
        assertBool "...so the receive leg on the POPPED state succeeds"
          (match (endpointReceiveDualWithCapsOnCore donEp donServer (some donReply) cnRoot
                    (SeLe4n.Slot.ofNat 0) c1 stPopped).2 with
           | .ok _ => true
           | .error _ => false)
      -- **PAYOFF**: the whole arm, in the live order, end to end.
      match replyRecvBody donEp donServer donReply donClient IpcMessage.empty cnRoot
          (SeLe4n.Slot.ofNat 0) c1 stQueued with
      | .error e =>
        assertBool s!"PAYOFF: the `ReplyRecv` loop must complete (got {reprStr e})" false
      | .ok (_, stLoop) =>
        assertBool "PAYOFF: the passive server's `seL4_ReplyRecv` completes" true
        assertBool "PAYOFF: the first client is answered and holds its own context again"
          (match stLoop.getTcb? donClient with
           | some t => t.ipcState == .ready && t.schedContextBinding == .bound scClient
           | none => false)
        assertBool "PAYOFF: the queued second client is now the one awaiting a reply"
          (match stLoop.getTcb? loopCaller2 with
           | some t => match t.ipcState with
                       | .blockedOnReply _ _ => true
                       | _ => false
           | none => false)
        assertBool "PAYOFF: ...linked to the SAME Reply object (faithful one-object reuse)"
          (match stLoop.getReply? donReply with
           | some r => r.caller == some loopCaller2
           | none => false)
        assertBool "PAYOFF: ...and the server runs on the new request's donated context"
          (match stLoop.getTcb? donServer with
           | some t => t.schedContextBinding == .donated loopCaller2Sc loopCaller2
           | none => false)


-- ============================================================================
-- WS-OD OD3.14 — the receive rendezvous' PRIORITY hand-off
-- ============================================================================

/-- OD3.14: the **active** server's own scheduling context, priority 20 — well
below the queued caller's 60.

With it bound, `applyCallDonation` is the identity (it donates only to an
`.unbound` receiver), which is the case the inversion bites hardest: no
donation fires at all, so the receiver's `pipBoost` is the *only* channel the
queued caller's priority has. -/
private def scHandoffServer : SeLe4n.SchedContextId := SchedContextId.ofNat 845

private def handoffServerSc : SchedContext :=
  { scId := scHandoffServer, budget := ⟨100⟩, period := ⟨1000⟩, priority := ⟨20⟩,
    deadline := ⟨0⟩, domain := ⟨0⟩, budgetRemaining := ⟨50⟩,
    boundThread := some donServer, isActive := true }

/-- `stDonBase` with the server holding its own budget rather than passive. -/
private def stHandoffActiveBase : SystemState :=
  { stDonBase with
      objects :=
        (stDonBase.objects.insert scHandoffServer.toObjId
            (.schedContext handoffServerSc)).insert donServer.toObjId
          (.tcb { mkTcb 842 20 (some c1) with
                    schedContextBinding := .bound scHandoffServer }) }

/-- WS-OD OD3.14: the client-first rendezvous, at runtime.

The caller parks a `Call` on an endpoint with no receiver; the server then takes
it with `seL4_Recv`.  That is the shape `.call` never reaches — there the
receiver is already waiting and the call arm propagates the chain itself — and
it is the shape the `.receive` arm handled without any propagation at all until
OD3.14, so a chain blocked behind the caller stopped dead at it. -/


private def runReceivePriorityHandoffChecks : IO Unit := do
  IO.println "--- WS-OD OD3.14 the receive rendezvous' priority hand-off ---"
  match okPair (endpointCallOnCore donEp donClient IpcMessage.empty c0 stHandoffActiveBase) with
  | none => assertBool "OD3.14 setup: the no-receiver call parks the caller" false
  | some (stParked, _) =>
    assertBool "the caller parks on the endpoint (.blockedOnCall)"
      (ipcStateIs stParked donClient (.blockedOnCall donEp))
    match okPair (endpointReceiveDualOnCore donEp donServer (some donReply) c1 stParked) with
    | none => assertBool "OD3.14 setup: the server's receive completes the rendezvous" false
    | some (stRecv, (sender, _)) =>
      assertBool "the receive dequeues the parked caller" (sender == donClient)
      assertBool "the dequeued caller is blocked on reply to THIS receiver"
        (ipcStateIs stRecv donClient (.blockedOnReply donEp (some donServer)))
      assertBool "the rendezvous guard fires on the dequeued caller"
        (decide (rendezvousDequeuedCall stRecv donClient = true))
      match applyReceiveRendezvousDonation stRecv donServer donClient,
            applyReceiveRendezvousHandoff stRecv donServer donClient c1 with
      | .ok stDonOnly, .ok stHandoff =>
          -- The superseded shape, kept as the witness that the assertions below
          -- track the WALK and not the donation: with an active receiver the
          -- donation is the identity, so this state is the rendezvous' own.
          assertBool "NEGATIVE (the defect): the donation alone installs no boost"
            (match stDonOnly.getTcb? donServer with
             | some t => decide (t.pipBoost = none) | none => false)
          assertBool "NEGATIVE (the defect): ...so the receiver still resolves to its own 20"
            (match stDonOnly.getTcb? donServer with
             | some t => decide ((resolveEffectivePrioDeadline stDonOnly t).1 = ⟨20⟩)
             | none => false)
          -- ...and the hand-off carries the queued caller's 60 across.
          assertBool "the hand-off boosts the receiver to the queued caller's priority (60)"
            (match stHandoff.getTcb? donServer with
             | some t => decide (t.pipBoost = some ⟨60⟩) | none => false)
          assertBool "...so the receiver's effective scheduling priority becomes 60"
            (match stHandoff.getTcb? donServer with
             | some t => decide ((resolveEffectivePrioDeadline stHandoff t).1 = ⟨60⟩)
             | none => false)
          assertBool "the active receiver keeps its OWN SchedContext (no donation fired)"
            (match stHandoff.getTcb? donServer with
             | some t => decide (t.schedContextBinding = .bound scHandoffServer) | none => false)
          -- The sibling step, both ways.  `.replyRecv`'s reply leg already walks
          -- from the recorded server, so the receive leg's hand-off must be the
          -- identity exactly when that walk started at the receiver.
          assertBool "the receive leg's hand-off is inert when the earlier walk covered the receiver"
            (match (applyReceiveLegPipHandoff stRecv donServer donClient donServer
                      c1).getTcb? donServer with
             | some t => decide (t.pipBoost = none) | none => false)
          assertBool "...and boosts the receiver on a DELEGATED reply, where it did not"
            (match (applyReceiveLegPipHandoff stRecv donServer donClient donClient
                      c1).getTcb? donServer with
             | some t => decide (t.pipBoost = some ⟨60⟩) | none => false)
      | _, _ => assertBool "OD3.14: both hand-off shapes succeed on the rendezvous" false
  -- NEGATIVE: a receive that BLOCKS dequeues nobody, so the guard is false and
  -- neither half of the hand-off runs.  This is the arm that keeps every result
  -- taken before OD3.14 true on the states it held for.
  match okPair (endpointReceiveDualOnCore donEp donServer (some donReply) c1
      stHandoffActiveBase) with
  | none => assertBool "OD3.14 setup: a receive with no sender blocks" false
  | some (stBlocked, (sender, _)) =>
    assertBool "NEGATIVE: a receive that blocks returns the receiver's own id"
      (sender == donServer)
    assertBool "NEGATIVE: ...so the rendezvous guard is false"
      (decide (rendezvousDequeuedCall stBlocked donServer = false))
    match applyReceiveRendezvousHandoff stBlocked donServer donServer c1 with
    | .ok stNoop =>
        assertBool "NEGATIVE: ...and the hand-off installs no boost"
          (match stNoop.getTcb? donServer with
           | some t => decide (t.pipBoost = none) | none => false)
    | .error _ => assertBool "OD3.14: the inert hand-off succeeds" false
  -- NEGATIVE: a plain `Send` rendezvous wakes its sender `.ready` rather than
  -- leaving it reply-blocked, so it lends the receiver nothing and the guard is
  -- false there too.
  match okPair (endpointSendDualOnCore donEp donClient IpcMessage.empty c0
      stHandoffActiveBase) with
  | none => assertBool "OD3.14 setup: a plain send with no receiver parks the sender" false
  | some (stSend, _) =>
    match okPair (endpointReceiveDualOnCore donEp donServer (some donReply) c1 stSend) with
    | none => assertBool "OD3.14 setup: the receive completes the send rendezvous" false
    | some (stSendRdv, (sender, _)) =>
      assertBool "NEGATIVE: the plain-send rendezvous wakes its sender .ready"
        (sender == donClient && ipcStateIs stSendRdv donClient .ready)
      assertBool "NEGATIVE: ...so the rendezvous guard is false"
        (decide (rendezvousDequeuedCall stSendRdv donClient = false))
      match applyReceiveRendezvousHandoff stSendRdv donServer donClient c1 with
      | .ok stNoop2 =>
          assertBool "NEGATIVE: ...and the hand-off installs no boost"
            (match stNoop2.getTcb? donServer with
             | some t => decide (t.pipBoost = none) | none => false)
      | .error _ => assertBool "OD3.14: the plain-send hand-off succeeds" false

-- ============================================================================
-- WS-RM — what a middle removal costs at stack depth three
-- ============================================================================

/-- **The innermost server of a three-frame chain, and its own reply frame.**

`§3.20` removes the *bottom* frame of a two-frame stack.  A bottom frame has
nothing below it, so "take the frame above off this frame's stack" and "splice
this frame out of the list" write the same value -- `none` -- into the frame
above, and the two readings of a middle removal cannot be told apart there.
**Three frames is the shallowest stack on which they differ**, and that is what
makes `cancelledMiddleCallerPolicy` measurable rather than described.

Up to `v0.35.44` this witness measured the sever's **cost**: the frames below the
cut left the context's stack, so the reservation settled on the thread *above* the
cut and its owner was left `.unbound` for good -- a callee that delegated its
caller's reply capability to a confederate could capture that caller's CBS
reservation.  Since WS-HP HP6.8 (`v0.35.45`) it measures the splice's **payoff**:
the frame above the cut is re-pointed at the frame below, so the reservation
travels outward and the pop that answers the bottom frame delivers it home.  The
retired sever's values are spelled out in the negatives below, which is what makes
the assertions known to discriminate rather than merely to pass.

The depth-**two** loss the splice provably cannot reach -- both policies write
`none` into the frame above a bottom frame -- is WS-HP HP10's, and §3.20 is
deliberately left asserting the depth-two outcome unchanged: that is the
measurement that this cut is confined to depth ≥ 3.

Reachable with no more authority than `§3.20` needs -- three nested donating
`Call`s (which the transitive chain makes ordinary since OD4) and one delegated
reply capability. -/
private def depth3Server : SeLe4n.ThreadId := ⟨101⟩
private def depth3Reply : SeLe4n.ReplyId := ⟨102⟩

/-- The three-frame stack, built by pushing twice: `pushOuter` lends to
`pushDonor`, `pushDonor` lends on to `pushServer`, `pushServer` lends on to
`depth3Server`.  Both pushes are the live `donateSchedContext`, so the shape
this witness measures is the shape the kernel produces. -/
private def depth3Chain : Except KernelError SystemState :=
  match donateSchedContext pushStore pushDonor pushServer pushSc with
  | .error e => .error e
  | .ok depth2 =>
      let stReady : SystemState :=
        { depth2 with
            objects := ((depth2.objects.insert depth3Reply.toObjId
                (.reply { replyId := depth3Reply, caller := some pushServer })).insert
                depth3Server.toObjId (.tcb (mkTcb 101 25 none))).insert
                pushServer.toObjId
                (.tcb { mkTcb 92 30 none with
                          schedContextBinding := .donated pushSc pushDonor,
                          ipcState := .blockedOnReply (SeLe4n.ObjId.ofNat 97)
                            (some depth3Server),
                          replyObject := some depth3Reply }) }
      match donateSchedContext stReady pushServer depth3Server pushSc with
      | .error e => .error e
      | .ok depth3 =>
          -- Every intermediate caller of a live chain is blocked on its own
          -- reply; `pushDonor` is left `.ready` by the fixture's first push, and
          -- a state in which it is not blocked is one the pop's outer-caller
          -- validation refuses (`outerCallerAcceptable`).  Patched here, so the
          -- removal and the in-order contrast below run on the same live shape.
          .ok { depth3 with
                  objects := depth3.objects.insert pushDonor.toObjId
                    (.tcb { mkTcb 91 40 none with
                              schedContextBinding := .unbound,
                              ipcState := .blockedOnReply (SeLe4n.ObjId.ofNat 97)
                                (some pushServer),
                              replyObject := some pushDonorReply }) }

private def runMiddleRemovalDepthThreeChecks : IO Unit := do
  IO.println "--- §3.22 WS-RM: a middle removal at stack depth three ---"
  match depth3Chain with
  | .error e =>
    assertBool s!"the witness needs a depth-3 chain (got {reprStr e})" false
  | .ok chain =>
    -- The stack, bottom to top: `pushOuterReply` → `pushDonorReply` → `depth3Reply`.
    assertBool "pre: the innermost frame heads the context and links down to the middle one"
      (pushLinksOf chain depth3Reply == some (some pushDonorReply, some (.head pushSc)))
    assertBool "pre: the middle frame links both ways"
      (pushLinksOf chain pushDonorReply
        == some (some pushOuterReply, some (.frame depth3Reply)))
    assertBool "pre: the bottom frame links up only"
      (pushLinksOf chain pushOuterReply == some (none, some (.frame pushDonorReply)))
    assertBool "pre: the context is held by the innermost server, owed to the one before it"
      (pushBindingOf chain depth3Server == some (.donated pushSc pushServer))
    -- The middle caller is blocked on its own call, which is what makes the
    -- frame a delegate answers a MIDDLE frame rather than the head.
    assertBool "pre: the middle caller is blocked on its own call"
      (match chain.getTcb? pushDonor with
       | some t => t.ipcState == .blockedOnReply (SeLe4n.ObjId.ofNat 97) (some pushServer)
       | none => false)
    assertBool "the footprint resolves the frame ABOVE the middle one"
      (answeredReplyFrameAbove? chain pushDonor == some depth3Reply)
    -- **The middle removal**, through a delegated reply capability.
    let (post, res) :=
      endpointReplyOnCore replyRemovalDelegate pushDonor IpcMessage.empty bootCoreId chain
    assertBool "the out-of-order reply to the MIDDLE caller succeeds"
      (match res with | .ok _ => true | .error _ => false)
    assertBool "the answered frame leaves the structure entirely (`Reply.isFree`)"
      (match post.getReply? pushDonorReply with | some r => r.isFree | none => false)
    -- **THE PAYOFF, MEASURED.**  The head's link down is **re-pointed** at the
    -- frame below the cut rather than cleared, and that frame links back up at the
    -- head, so the bottom frame -- whose caller `pushOuter` owns the reservation --
    -- stays on the context's stack.  Under `severAtCut`, which this kernel
    -- implemented up to `v0.35.44` and which seL4-MCS still implements, the first
    -- of these was `(none, some (.head pushSc))` and every assertion below it
    -- failed the other way.
    assertBool "PAYOFF: the head's link down is RE-POINTED at the frame below the cut"
      (pushLinksOf post depth3Reply == some (some pushOuterReply, some (.head pushSc)))
    assertBool "PAYOFF: ...and the frame below links back up at the head"
      (pushLinksOf post pushOuterReply == some (none, some (.frame depth3Reply)))
    -- NEGATIVE, and the reason the two assertions above discriminate: the
    -- **retired** `severAtCut` values, spelled here and nowhere else.  A revert of
    -- the splice makes each of these hold and each assertion above fail.
    assertBool "NEGATIVE: the head does NOT read as a severed cut"
      (!(pushLinksOf post depth3Reply == some (none, some (.head pushSc))))
    assertBool "NEGATIVE: ...and the frame below does NOT keep a stale upward link"
      (!(pushLinksOf post pushOuterReply == some (none, some (.frame pushDonorReply))))
    -- ...so the pop resolves the remaining stack to the reservation's OWNER,
    -- where the sever left it reading as bottomed out.
    assertBool "PAYOFF: the pop resolves the remaining stack to the reservation's owner"
      (match replyStackOuterCaller? post pushSc with
       | .ok (some outer) => outer == pushOuter
       | _ => false)
    assertBool "PAYOFF: ...so the reservation leaves the cut owed OUTWARD"
      (match returnDonatedSchedContextResolved post depth3Server pushSc pushServer with
       | .ok st' => pushBindingOf st' pushServer == some (.donated pushSc pushOuter)
       | .error _ => false)
    assertBool "PAYOFF: ...and its owner is still unbound, waiting rather than abandoned"
      (match returnDonatedSchedContextResolved post depth3Server pushSc pushServer with
       | .ok st' => pushBindingOf st' pushOuter == some .unbound
       | .error _ => false)
    -- **AND IT ARRIVES.**  One pop leaves the reservation owed; the pop that
    -- answers the bottom frame delivers it home.  The sever could not reach this
    -- state at all -- the bottom frame had left the stack, so no later pop carried
    -- the context below the cut and `.bound pushSc` on the thread ABOVE the cut was
    -- terminal.
    assertBool "PAYOFF: ...and the next pop delivers it home `.bound` to its owner"
      (match returnDonatedSchedContextResolved post depth3Server pushSc pushServer with
       | .ok st' =>
           (match returnDonatedSchedContextResolved st' pushServer pushSc pushOuter with
            | .ok st'' => pushBindingOf st'' pushOuter == some (.bound pushSc)
            | .error _ => false)
       | .error _ => false)
    assertBool "PAYOFF: ...leaving the intermediate caller unbound, owing nothing"
      (match returnDonatedSchedContextResolved post depth3Server pushSc pushServer with
       | .ok st' =>
           (match returnDonatedSchedContextResolved st' pushServer pushSc pushOuter with
            | .ok st'' => pushBindingOf st'' pushServer == some .unbound
            | .error _ => false)
       | .error _ => false)
    -- **AGREEMENT**: the same three-frame stack unwound IN ORDER reaches the same
    -- binding.  Under the sever these two disagreed -- that disagreement was the
    -- defect -- and the contrast half is kept because a witness that only checked
    -- the out-of-order path could not say the two now coincide.
    assertBool "AGREEMENT: an IN-ORDER pop on the same stack owes the context outward too"
      (match returnDonatedSchedContextResolved chain depth3Server pushSc pushServer with
       | .ok st' => pushBindingOf st' pushServer == some (.donated pushSc pushDonor)
       | .error _ => false)
    -- **NOTHING IS PINNED BY A REMOVAL**, at either policy: a frame whose own
    -- caller is consumed while it heads no context is cleared outright
    -- (`Reply.consumed`'s non-head branch), and since HP6.3 the removal clears the
    -- cut frame's downward link itself -- seL4's `reply_unlink` downward half -- so
    -- `donationChainWellFormed` survives the removal rather than being transiently
    -- broken.
    assertBool "PAYOFF: the cut frame's own downward link is cleared by the removal"
      (pushLinksOf post pushDonorReply == some (none, none))
    let stBottom : SystemState :=
      { post with
          objects := post.objects.insert pushOuter.toObjId (.tcb replyRemovalOuterTcb) }
    let (postBottom, resBottom) :=
      endpointReplyOnCore replyRemovalDelegate pushOuter IpcMessage.empty bootCoreId stBottom
    assertBool "PAYOFF: the bottom frame's own caller can still be answered"
      (match resBottom with | .ok _ => true | .error _ => false)
    assertBool "PAYOFF: ...and that frees it, so nothing is pinned by the cut"
      (match postBottom.getReply? pushOuterReply with | some r => r.isFree | none => false)
    assertBool "PAYOFF: ...leaving no consumed frame heading the context"
      (pushHeadOf postBottom == some (some depth3Reply))

/-! ### §3.23 WS-HP HP9.1: a middle removal at stack depth FOUR

**Why depth 3 is not enough**, and this is the whole reason for the sub-task.
The splice writes `above.prev := some below`, where `below` is the *cut frame's own*
`prev` — and `below`'s own `prev` is **not touched**.  At depth 3 a middle cut
leaves exactly one frame below it, so "the stack stays connected" and "the frame
immediately beneath the reconnection survives" are the same statement, and §3.22
cannot tell them apart.  Four frames is the shallowest stack on which **two** frames
sit below a cut, which makes the splice's *transitivity* measurable: the chain has
to remain walkable past the reconnection, and the reservation has to reach the
bottom-most owner through **three** successive pops rather than two.

A splice that re-pointed the frame above at its new neighbour while disturbing that
neighbour's own downward link would pass §3.22 and fail here.  So would one that
re-headed the context at the wrong frame: under `severAtCut` the head's `prev` is
cleared, and pop one would then read the remaining stack as bottomed out and settle
the reservation `.bound` on a thread **two** hops inside the chain rather than on
its owner.

The cut is the *third* frame from the bottom, not the second: cutting the second
would leave one frame below and measure §3.22 again.

**What this witness does and does not catch, measured.**  A code mutation of the
splice's *stores* never reaches it: `spliceReplyFrameStores_cases` states the three
stores exactly, so both candidate mutations — the full sever, and one that
reconnects the pair while clobbering the frame below's own downward link — fail to
**elaborate**, four errors each, before any suite runs.  That is the stronger
guarantee and it is where the store shape is pinned.  What this scenario measures
is therefore the **composition**, which no theorem states and which §3.22 cannot
reach: that the reconnected chain is walkable past its reconnection, and that three
successive pops carry the reservation from the innermost holder to its owner.
§3.22 does two pops over a two-frame remainder; three frames below a head is a
different proposition, and it is the one HP10 kept true when the recipient
stopped being derived from stack reachability: at depth ≥ 3 every pop sits at a
`some` arm, where the redirect is the identity by theorem
(`replyDonationRecipient_eq_of_outer_some`), and this scenario is byte-identical
across HP10.7.

Non-vacuous by construction: every pop assertion reads `.error _ => false`, so a
refused pop fails the row rather than passing it. -/
private def depth4Server : SeLe4n.ThreadId := ⟨103⟩
private def depth4Reply : SeLe4n.ReplyId := ⟨104⟩

/-- The four-frame stack, built by pushing a third time: `depth3Server` lends the
context on to `depth4Server`.  Every push is the live `donateSchedContext`, so the
shape is the one the kernel produces rather than one assembled by hand. -/
private def depth4Chain : Except KernelError SystemState :=
  match depth3Chain with
  | .error e => .error e
  | .ok depth3 =>
      let stReady : SystemState :=
        { depth3 with
            objects := ((depth3.objects.insert depth4Reply.toObjId
                (.reply { replyId := depth4Reply, caller := some depth3Server })).insert
                depth4Server.toObjId (.tcb (mkTcb 103 20 none))).insert
                depth3Server.toObjId
                (.tcb { mkTcb 101 25 none with
                          schedContextBinding := .donated pushSc pushServer,
                          ipcState := .blockedOnReply (SeLe4n.ObjId.ofNat 97)
                            (some depth4Server),
                          replyObject := some depth4Reply }) }
      donateSchedContext stReady depth3Server depth4Server pushSc

/-- **WS-HP HP10.5: the reservation origin cannot outlive the thread it names.**

`SchedContext.donationOrigin` is history the kernel validates rather than an
invariant, and that is sound only while the `ThreadId` it holds still means the
thread that lent the reservation.  A `ThreadId` is an index, so destroying the
origin thread and allocating at its id would leave a later pop handing a
reservation to an unrelated thread — with `donationRecipientAcceptable` satisfied,
because that guard asks whether the *recipient* may take a context, never whether
the recorded origin is still the lender.

So the destroy path scrubs it (`clearDonationOriginReferences`, reached from
`cleanupTcbReferences` and thence `lifecyclePreRetypeCleanup`), and this witness is
the measurement: a context recording `pushOuter` as its origin, after a reference
scrub of `pushOuter`, records nothing.  The **negative** beside it is the same
scrub of a *different* thread, which must leave the origin alone — a sweep that
cleared unconditionally would pass the first assertion and destroy the field's
whole purpose. -/
private def runDonationOriginIdReuseChecks : IO Unit := do
  IO.println "--- §3.24 WS-HP HP10.5: a recorded origin does not outlive its thread ---"
  let stOrigin : SystemState :=
    { pushStore with
        objects := pushStore.objects.insert pushSc.toObjId
          (.schedContext { SchedContext.empty pushSc with
                             boundThread := some pushServer,
                             scReply := some pushOuterReply,
                             donationOrigin := some pushOuter }) }
  let originOf (st : SystemState) : Option (Option SeLe4n.ThreadId) :=
    (st.getSchedContext? pushSc).map (·.donationOrigin)
  assertBool "pre: the context records `pushOuter` as the reservation's origin"
    (originOf stOrigin == some (some pushOuter))
  -- **THE SCRUB.**  `cleanupTcbReferences` is what `lifecyclePreRetypeCleanup` runs
  -- before a TCB is destroyed; the origin clear is its fourth sweep.
  assertBool "PAYOFF: a reference scrub of that thread clears the origin"
    (originOf (cleanupTcbReferences stOrigin pushOuter) == some none)
  -- ...and the primitive on its own, so the sweep is known to be what does it
  -- rather than one of the three sweeps beside it.
  assertBool "PAYOFF: ...and the primitive alone is what does it"
    (originOf (clearDonationOriginReferences stOrigin pushOuter) == some none)
  -- NEGATIVE: scrubbing a DIFFERENT thread must leave the origin standing.  A
  -- sweep that cleared unconditionally would satisfy both payoffs above and
  -- silently destroy the only thing the field is for.
  assertBool "NEGATIVE: scrubbing a different thread leaves the origin recorded"
    (originOf (clearDonationOriginReferences stOrigin pushServer)
      == some (some pushOuter))
  assertBool "NEGATIVE: ...and so does the composed scrub of a different thread"
    (originOf (cleanupTcbReferences stOrigin pushServer)
      == some (some pushOuter))
  -- ...and the scrub is the identity on a context recording no origin at all,
  -- which is every state before a first donation.
  assertBool "the scrub is the identity when nothing records an origin"
    (originOf (clearDonationOriginReferences pushStore pushOuter) == some none)

/-- **`v0.35.61`** (the post-landing audit): a recorded origin naming a thread the
store does not hold.  Reachable only through a stale field, which
`clearDonationOriginReferences` prevents; what §3.25's last negative measures is
the resolver's *contract* -- a candidate resolves -- not the field's reachability. -/
private def staleOrigin : SeLe4n.ThreadId := ⟨89⟩

/-- The re-called client's fresh frame, the surviving bottom frame, and the shapes
the `v0.35.157` guard refuses -- ids outside `pushStoreShaped`'s 91..97. -/
private def redirectHeadReply : SeLe4n.ReplyId := ⟨98⟩
private def redirectSc2 : SeLe4n.SchedContextId := ⟨99⟩
private def redirectSc2Holder : SeLe4n.ThreadId := ⟨100⟩
private def redirectFrameAbove : SeLe4n.ReplyId := ⟨101⟩

/-- The retired reading of `donationOriginRebindable` (`v0.35.51` .. `v0.35.156`):
refuse an origin that is `.blockedOnReply`.  Computed beside the live guard so the
assertions below are known to DISCRIMINATE -- a re-called client is reply-blocked
and on no stack, which is the one input on which the two readings differ. -/
private def retiredProxyRebindable (st : SystemState) (origin : SeLe4n.ThreadId) : Bool :=
  match st.getTcb? origin with
  | none => true
  | some tcb =>
    match tcb.ipcState with
    | .blockedOnReply _ _ => false
    | _ => true

/-- **WS-HP HP10.7 / `v0.35.157`: the redirect computes a DIFFERENT recipient, and
the guard is the bind's own admissibility.**

The measurement this phase owes.  Every state the tree reached before HP10.7
either records no origin or records one that *is* the answered caller, so on all
of them the redirect is the identity and a suite that only exercised those would
pass with the whole flip reverted.  The shape that separates them is the
out-of-order removal of plan §3.2: a client answered by a delegate is woken
`.ready`, its frame leaves the stack, and the surviving bottom frame names the
*intermediate* caller — so reachability says one thread and the recorded origin
says another.

**The PAYOFF group drives the re-called client** (PR #897's review, `v0.35.141`;
closed `v0.35.157`).  Until `v0.35.157` the rebindability guard read the origin's
`ipcState` — a PROXY for "some live binding names it" — so a client that was
answered out of order and simply issued its next Call was refused: it is
`.unbound`, so that Call donated nothing and pushed no frame, and no binding names
it, yet it is `.blockedOnReply` again.  The pop then fell back and *transferred*
the reservation to the answered caller, erasing the origin with it.  The guard now
asks `schedContextBind`'s question — is the origin's reply frame on a **live**
stack — which admits that client: its new frame is on no stack.  The retired
reading is computed beside the live one (`retiredProxyRebindable`) so the group is
known to decide the guard rather than the fixture.

**The NEGATIVE groups are the two shapes the proxy could not tell apart from it**,
and each carries the CONTROL that the recipient guard alone admits the thread, so
the decline is attributable to rebindability: an origin whose frame **heads** a
context — a live owner, and the fixture plants the binding that names it — and an
origin whose frame sits **inside** a live stack, owed a pop that a binding made here
would make refuse.  Both decline to the reachability answer rather than refusing
the pop.  The three remaining negatives are unchanged from HP10.7: a bound origin
(the recipient guard's own case), no origin recorded, and a stale origin. -/
private def runDonationOriginRedirectChecks : IO Unit := do
  IO.println "--- §3.25 WS-HP HP10.7: the reply pop's recipient is the recorded origin ---"
  -- **The depth-2 out-of-order shape, coherently.**  The chain was
  -- `pushOuter → pushServer → pushDonor` (client, intermediate caller, holder).  A
  -- delegate answered `pushOuter` out of order: its frame left the stack, so the
  -- surviving frame (`redirectHeadReply`, the intermediate caller's) is both the
  -- head and the BOTTOM of `pushSc`'s stack, `pushDonor` holds the reservation
  -- `.donated` from `pushServer`, and the context records `pushOuter` as the
  -- origin.  `outerTcb` is the client's TCB, varied by the groups below.
  let redirectStore (outerTcb : TCB) : SystemState :=
    { pushStore with
        objects := (((pushStore.objects.insert pushSc.toObjId
          (.schedContext { SchedContext.empty pushSc with
                             boundThread := some pushDonor,
                             scReply := some redirectHeadReply,
                             donationOrigin := some pushOuter })).insert
            redirectHeadReply.toObjId
            (.reply { replyId := redirectHeadReply, caller := some pushServer,
                      next := some (.head pushSc) })).insert
            pushServer.toObjId
            (.tcb { mkTcb 92 30 none with
                      ipcState := .blockedOnReply (SeLe4n.ObjId.ofNat 97) (some pushDonor),
                      replyObject := some redirectHeadReply })).insert
            pushDonor.toObjId
            (.tcb { mkTcb 91 40 none with
                      schedContextBinding := .donated pushSc pushServer,
                      replyObject := some pushDonorReply })
          |>.insert pushOuter.toObjId (.tcb outerTcb) }
  -- The re-called client: `.unbound`, reply-blocked on its NEXT call, whose frame
  -- is `pushOuterReply` re-linked fresh -- the removal cleared its links and the
  -- re-Call donated nothing, so it pushed none.  Homed on core 1, where nothing
  -- else in the chain is.
  let recalledClient : TCB :=
    { mkTcb 93 50 (some c1) with
        ipcState := .blockedOnReply (SeLe4n.ObjId.ofNat 97) (some pushServer),
        replyObject := some pushOuterReply }
  let withFreshFrame (st : SystemState) : SystemState :=
    { st with
        objects := st.objects.insert pushOuterReply.toObjId
          (.reply { replyId := pushOuterReply, caller := some pushOuter }) }
  let stRedirect : SystemState := withFreshFrame (redirectStore recalledClient)
  let poppedFrom (st : SystemState) : Option SystemState :=
    (returnDonatedSchedContextResolved st pushDonor pushSc
      (replyDonationRecipient st pushSc pushServer)).toOption
  assertBool "pre: the pop is at the BOTTOM of the stack (nothing further out)"
    (match replyStackOuterCaller? stRedirect pushSc with
     | .ok none => true
     | _ => false)
  assertBool "pre: ...and the context records `pushOuter` as the origin"
    ((stRedirect.getSchedContext? pushSc).bind (·.donationOrigin) == some pushOuter)
  assertBool "pre: the reservation is held by a THIRD thread, the server"
    ((stRedirect.getSchedContext? pushSc).bind (·.boundThread) == some pushDonor)
  assertBool "pre: ...whose binding records it as owed to the intermediate caller"
    (pushBindingOf stRedirect pushDonor == some (.donated pushSc pushServer))
  assertBool "pre: the origin is reply-blocked on its NEXT call, `.unbound`"
    ((stRedirect.getTcb? pushOuter).map (fun t =>
      t.schedContextBinding == .unbound
        && (match t.ipcState with | .blockedOnReply _ _ => true | _ => false)) == some true)
  assertBool "pre: ...and its frame is on NO stack -- that Call donated nothing"
    ((stRedirect.getTcb? pushOuter).map (fun t => replyFrameOnLiveStack stRedirect t)
      == some false)
  -- **PAYOFF**: the retired proxy refused this client and the live guard admits it
  -- -- the one input on which the two readings differ.
  assertBool "PAYOFF: the retired `.blockedOnReply` proxy REFUSES the re-called client"
    (retiredProxyRebindable stRedirect pushOuter == false)
  assertBool "PAYOFF: ...and the live guard, the bind's own admissibility, ADMITS it"
    (donationOriginRebindable stRedirect pushOuter == true)
  assertBool "PAYOFF: the resolver answers the recorded origin"
    (donationOriginRecipient? stRedirect pushSc == some pushOuter)
  assertBool "PAYOFF: ...and the pop's recipient is that origin, NOT the answered caller"
    (replyDonationRecipient stRedirect pushSc pushServer == pushOuter)
  assertBool "PAYOFF: ...which is a DIFFERENT thread, so the redirect is not vacuous"
    (!(pushOuter == pushServer))
  -- **PAYOFF, driven through the live pop**: the reservation goes HOME.  This is
  -- the assertion the retired proxy failed -- under it the same pop bound the
  -- reservation to `pushServer` and erased the origin.
  assertBool "PAYOFF: the pop succeeds"
    (poppedFrom stRedirect).isSome
  assertBool "PAYOFF: ...and binds the reservation to the ORIGIN, the client that owned it"
    ((poppedFrom stRedirect).bind
      (fun st' => (st'.getSchedContext? pushSc).bind (·.boundThread)) == some pushOuter)
  assertBool "PAYOFF: ...which now holds it outright, as its own"
    ((poppedFrom stRedirect).bind (fun st' => pushBindingOf st' pushOuter)
      == some (.bound pushSc))
  assertBool "PAYOFF: ...while the intermediate caller ends holding nothing"
    ((poppedFrom stRedirect).bind (fun st' => pushBindingOf st' pushServer)
      == some .unbound)
  assertBool "PAYOFF: ...and so does the server that held it"
    ((poppedFrom stRedirect).bind (fun st' => pushBindingOf st' pushDonor)
      == some .unbound)
  -- **PAYOFF**: and the replenishment migration's DESTINATION follows it too.  A
  -- redirect that moved the reservation without moving the queue would leave
  -- `replenishQueueAffinityConsistentOnCore` false from the instant it committed.
  assertBool "PAYOFF: the migration's destination home is the ORIGIN's core"
    (replyDonationRecipientHome stRedirect redirectHeadReply pushServer
      == determineTargetCore stRedirect pushOuter)
  assertBool "PAYOFF: ...and that is core 1, not the answered caller's"
    (replyDonationRecipientHome stRedirect redirectHeadReply pushServer == c1)
  -- **NEGATIVE: a live OWNER.**  The origin was bound a second reservation and
  -- Called with it: its frame now HEADS `redirectSc2`, whose holder's binding
  -- names it as owner.  Binding `pushSc` to it would falsify that binding's owner
  -- clause, so the guard refuses -- and this is the shape the proxy refused too,
  -- for the wrong reason (its `ipcState`) rather than the right one (its frame).
  let liveOwnerStore : SystemState :=
    { redirectStore recalledClient with
        objects := ((redirectStore recalledClient).objects.insert pushOuterReply.toObjId
          (.reply { replyId := pushOuterReply, caller := some pushOuter,
                    next := some (.head redirectSc2) })).insert
            redirectSc2.toObjId
            (.schedContext { SchedContext.empty redirectSc2 with
                               boundThread := some redirectSc2Holder,
                               scReply := some pushOuterReply })
          |>.insert redirectSc2Holder.toObjId
            (.tcb { mkTcb 100 20 none with
                      schedContextBinding := .donated redirectSc2 pushOuter }) }
  assertBool "NEGATIVE (live owner): a binding NAMES the origin as owner"
    (pushBindingOf liveOwnerStore redirectSc2Holder == some (.donated redirectSc2 pushOuter))
  assertBool "NEGATIVE (live owner): ...its frame heads that context, so it is on a live stack"
    ((liveOwnerStore.getTcb? pushOuter).map (fun t => replyFrameOnLiveStack liveOwnerStore t)
      == some true)
  assertBool "NEGATIVE (live owner): ...and the guard refuses it"
    (donationOriginRebindable liveOwnerStore pushOuter == false)
  -- CONTROL: the *recipient* guard admits it, so the decline is attributable to
  -- rebindability alone.  Without this the negative would pass under a resolver
  -- that declined for the other reason.
  assertBool "CONTROL (live owner): ...while the recipient guard ALONE admits it"
    (donationRecipientAcceptable liveOwnerStore pushOuter == true)
  assertBool "NEGATIVE (live owner): ...so the resolver declines it"
    (donationOriginRecipient? liveOwnerStore pushSc == none)
  assertBool "NEGATIVE (live owner): ...and the pop FALLS BACK to the answered caller, never refuses"
    (replyDonationRecipient liveOwnerStore pushSc pushServer == pushServer)
  -- **NEGATIVE: an INTERIOR frame.**  The origin's frame sits below another on a
  -- live stack (`redirectFrameAbove` reciprocates its upward link), so the origin
  -- is owed a context by the pop that reaches its frame -- binding one here would
  -- make that pop refuse.  The proxy could not tell this shape from the re-called
  -- client's: both are `.blockedOnReply`.
  let interiorStore : SystemState :=
    { redirectStore recalledClient with
        objects := ((redirectStore recalledClient).objects.insert pushOuterReply.toObjId
          (.reply { replyId := pushOuterReply, caller := some pushOuter,
                    next := some (.frame redirectFrameAbove) })).insert
            redirectFrameAbove.toObjId
            (.reply { replyId := redirectFrameAbove, caller := some pushServer,
                      prev := some pushOuterReply, next := some (.head redirectSc2) }) }
  assertBool "NEGATIVE (interior frame): the origin's frame is inside a live stack"
    ((interiorStore.getTcb? pushOuter).map (fun t => replyFrameOnLiveStack interiorStore t)
      == some true)
  assertBool "NEGATIVE (interior frame): ...and the guard refuses it"
    (donationOriginRebindable interiorStore pushOuter == false)
  assertBool "CONTROL (interior frame): ...while the recipient guard ALONE admits it"
    (donationRecipientAcceptable interiorStore pushOuter == true)
  assertBool "NEGATIVE (interior frame): ...so the resolver declines it"
    (donationOriginRecipient? interiorStore pushSc == none)
  assertBool "NEGATIVE (interior frame): ...and the pop FALLS BACK to the answered caller"
    (replyDonationRecipient interiorStore pushSc pushServer == pushServer)
  -- NEGATIVE: an origin that already holds a reservation of its own is the case
  -- `donationRecipientAcceptable` has always covered.
  let stBoundOrigin : SystemState :=
    redirectStore { mkTcb 93 50 none with schedContextBinding := .bound pushSc }
  assertBool "NEGATIVE: a bound origin fails the recipient guard"
    (donationRecipientAcceptable stBoundOrigin pushOuter == false)
  -- CONTROL: and rebindability admits *it*, so the two guards are known to be
  -- independent rather than two spellings of one test.
  assertBool "CONTROL: ...while the rebindability guard ALONE admits it"
    (donationOriginRebindable stBoundOrigin pushOuter == true)
  assertBool "NEGATIVE: ...so the resolver declines that too"
    (donationOriginRecipient? stBoundOrigin pushSc == none)
  -- NEGATIVE: and with NO origin recorded the redirect is the identity, which is
  -- every state this tree reached before HP10.4.
  assertBool "NEGATIVE: no origin recorded — the recipient is the answered caller"
    (replyDonationRecipient pushStore pushSc pushServer == pushServer)
  assertBool "NEGATIVE: ...and the destination home is the answered caller's"
    (replyDonationRecipientHome pushStore pushOuterReply pushServer
      == determineTargetCore pushStore pushServer)
  -- NEGATIVE (`v0.35.61`, the post-landing audit): an origin that no longer
  -- RESOLVES is not a candidate.  Both guards pass a thread with no TCB (their
  -- `_of_none` arms), so before the resolver resolved the origin itself the pop's
  -- own `lookupTcb` was what met a stale origin -- as `.objectNotFound`, a
  -- refusal on the one shape the redirect exists to make a fallback.  The two
  -- CONTROLs are what make the last assertion attributable: with both guards
  -- admitting the thread, only the resolution check can be what declines it,
  -- and deleting that check answers `some staleOrigin` here.
  let stStaleOrigin : SystemState :=
    { pushStore with
        objects := pushStore.objects.insert pushSc.toObjId
          (.schedContext { SchedContext.empty pushSc with
                             boundThread := some pushServer,
                             scReply := some pushOuterReply,
                             donationOrigin := some staleOrigin }) }
  assertBool "CONTROL: the stale origin resolves to no thread"
    (lookupTcb stStaleOrigin staleOrigin).isNone
  assertBool "CONTROL: ...and BOTH guards admit it, vacuously"
    (donationRecipientAcceptable stStaleOrigin staleOrigin == true
      && donationOriginRebindable stStaleOrigin staleOrigin == true)
  assertBool "NEGATIVE: so only the resolution check can decline it, and it does"
    (donationOriginRecipient? stStaleOrigin pushSc == none)
  assertBool "NEGATIVE: ...and the pop FALLS BACK to the answered caller, never refuses"
    (replyDonationRecipient stStaleOrigin pushSc pushServer == pushServer)

private def runMiddleRemovalDepthFourChecks : IO Unit := do
  IO.println "--- §3.23 WS-HP HP9.1: a middle removal at stack depth four ---"
  match depth4Chain with
  | .error e =>
    assertBool s!"the witness needs a depth-4 chain (got {reprStr e})" false
  | .ok chain =>
    -- The stack, bottom to top: `pushOuterReply` → `pushDonorReply` → `depth3Reply`
    -- → `depth4Reply`.  All four links asserted, because the point of the scenario
    -- is what survives beneath a cut and a missing pre-state link would make that
    -- vacuous.
    assertBool "pre: the head frame links down to the third one"
      (pushLinksOf chain depth4Reply == some (some depth3Reply, some (.head pushSc)))
    assertBool "pre: the third frame links both ways"
      (pushLinksOf chain depth3Reply
        == some (some pushDonorReply, some (.frame depth4Reply)))
    assertBool "pre: the second frame links both ways"
      (pushLinksOf chain pushDonorReply
        == some (some pushOuterReply, some (.frame depth3Reply)))
    assertBool "pre: the bottom frame links up only"
      (pushLinksOf chain pushOuterReply == some (none, some (.frame pushDonorReply)))
    assertBool "pre: the context is held by the innermost server, owed to the one before it"
      (pushBindingOf chain depth4Server == some (.donated pushSc depth3Server))
    -- The frame the delegate answers is `depth3Reply`, whose caller is `pushServer`:
    -- the THIRD frame from the bottom, so two frames remain below the cut.
    assertBool "pre: the cut frame's caller is blocked on its own call"
      (match chain.getTcb? pushServer with
       | some t => t.ipcState == .blockedOnReply (SeLe4n.ObjId.ofNat 97) (some depth3Server)
       | none => false)
    assertBool "the footprint resolves the frame ABOVE the cut"
      (answeredReplyFrameAbove? chain pushServer == some depth4Reply)
    -- **The middle removal**, through a delegated reply capability.
    let (post, res) :=
      endpointReplyOnCore replyRemovalDelegate pushServer IpcMessage.empty bootCoreId chain
    assertBool "the out-of-order reply to the third frame's caller succeeds"
      (match res with | .ok _ => true | .error _ => false)
    assertBool "the answered frame leaves the structure entirely (`Reply.isFree`)"
      (match post.getReply? depth3Reply with | some r => r.isFree | none => false)
    -- **THE TRANSITIVITY, MEASURED.**  The head is re-pointed at the frame below the
    -- cut, that frame links back up at the head — and the frame below *it* is
    -- untouched, which is the half depth 3 cannot see.
    assertBool "PAYOFF: the head's link down is RE-POINTED at the frame below the cut"
      (pushLinksOf post depth4Reply == some (some pushDonorReply, some (.head pushSc)))
    assertBool "PAYOFF: ...and that frame links back up at the head"
      (pushLinksOf post pushDonorReply == some (some pushOuterReply, some (.frame depth4Reply)))
    assertBool "PAYOFF: ...while the frame BELOW it is untouched — the transitive half"
      (pushLinksOf post pushOuterReply == some (none, some (.frame pushDonorReply)))
    -- NEGATIVE: the retired `severAtCut` values, spelled here and nowhere else, so
    -- the three assertions above are known to discriminate.
    assertBool "NEGATIVE: the head does NOT read as a severed cut"
      (!(pushLinksOf post depth4Reply == some (none, some (.head pushSc))))
    -- ...and the whole remaining stack is walkable, bottom-most owner included.
    assertBool "PAYOFF: the pop resolves the remaining stack one frame down, not to the bottom"
      (match replyStackOuterCaller? post pushSc with
       | .ok (some outer) => outer == pushDonor
       | _ => false)
    -- **THREE POPS, AND IT ARRIVES.**  Depth 3 needed two; the third is the one a
    -- sever at this depth could never reach, because both frames below the cut had
    -- left the stack.
    --
    -- Each pop's *recipient* is the previous pop's **production-resolved** owner:
    -- `returnDonatedSchedContextResolved` reads `replyStackOuterCaller?` of its own
    -- state, so the `.donated pushSc X` this row asserts is where the kernel says
    -- the reservation is still owed, and the next row then pops at that same `X`.
    -- The witness follows that answer rather than supplying it — which is the only
    -- reason the chain measures the composition instead of the fixture.
    assertBool "PAYOFF: pop one owes the context outward to the second frame's caller"
      (match returnDonatedSchedContextResolved post depth4Server pushSc depth3Server with
       | .ok st' => pushBindingOf st' depth3Server == some (.donated pushSc pushDonor)
       | .error _ => false)
    assertBool "PAYOFF: pop two owes it outward again, to the bottom frame's caller"
      (match returnDonatedSchedContextResolved post depth4Server pushSc depth3Server with
       | .ok st' =>
           (match returnDonatedSchedContextResolved st' depth3Server pushSc pushDonor with
            | .ok st'' => pushBindingOf st'' pushDonor == some (.donated pushSc pushOuter)
            | .error _ => false)
       | .error _ => false)
    assertBool "PAYOFF: pop three delivers it HOME `.bound` to its owner"
      (match returnDonatedSchedContextResolved post depth4Server pushSc depth3Server with
       | .ok st' =>
           (match returnDonatedSchedContextResolved st' depth3Server pushSc pushDonor with
            | .ok st'' =>
                (match returnDonatedSchedContextResolved st'' pushDonor pushSc pushOuter with
                 | .ok st''' => pushBindingOf st''' pushOuter == some (.bound pushSc)
                 | .error _ => false)
            | .error _ => false)
       | .error _ => false)
    -- ...and nothing between the cut and the owner is left holding it.
    assertBool "PAYOFF: ...leaving every intermediate caller unbound, owing nothing"
      (match returnDonatedSchedContextResolved post depth4Server pushSc depth3Server with
       | .ok st' =>
           (match returnDonatedSchedContextResolved st' depth3Server pushSc pushDonor with
            | .ok st'' =>
                (match returnDonatedSchedContextResolved st'' pushDonor pushSc pushOuter with
                 | .ok st''' =>
                     pushBindingOf st''' depth3Server == some .unbound &&
                     pushBindingOf st''' pushDonor == some .unbound
                 | .error _ => false)
            | .error _ => false)
       | .error _ => false)
    -- The cut frame's own downward link is cleared by the removal, as at depth 3.
    assertBool "PAYOFF: the cut frame's own downward link is cleared by the removal"
      (pushLinksOf post depth3Reply == some (none, none))

-- ============================================================================
-- §3.26 the `.receive` replenish segment is keyed on the donation's own guard
--        (WS-RR RR8.12, PR #897 Codex review; the resolver half is Cut C1,
--        register row 55)
-- ============================================================================

/-! The narrowing is pinned definitionally — reverting the segment breaks
`endpointReceiveHandoffReplenishCores_of_blockedOnSend` and
`endpointReceiveHandoffReplenishCores_of_no_donation` at elaboration — so what no
theorem states is that **every shape is reachable by the live operations and the
segment differs between them**.  That is this section's whole subject.

The two retired readings live here, `private`, and nowhere else: computed beside the
live one on every shape, so the assertions are known to discriminate rather than
merely to pass.  Three shapes, and each retired reading is wrong on exactly one of
them: the sender-keyed segment declares two cores on a plain `Send`, the `Call`-keyed
one on a `Call` whose donation the resolver declines. -/

/-- The first superseded segment (`v0.35.107`): keyed on *is there a queued sender at
all*, which named both cores on every rendezvous including a plain `Send`. -/
private def senderKeyedReplenishCores (st : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) : List CoreId :=
  match receiveRendezvousSender? st endpointId with
  | some sender => [determineTargetCore st sender, determineTargetCore st receiver]
  | none        => []

/-- The second superseded segment (`v0.35.112`): keyed on the queued sender carrying a
`Call`, which named both cores on every `Call` — including one whose donation
`callDonationSchedContext?` declines because the receiver already holds a context of
its own, where the donation step is the identity. -/
private def callKeyedReplenishCores (st : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) : List CoreId :=
  match receiveRendezvousCallSender? st endpointId with
  | some sender => [determineTargetCore st sender, determineTargetCore st receiver]
  | none        => []

private def runReceiveReplenishSegmentChecks : IO Unit := do
  IO.println "--- §3.26 WS-RR RR8.12: the `.receive` replenish segment follows the donation ---"
  -- (a) a `Call` rendezvous the donation CARRIES OUT: the server is passive, so the
  --     resolver answers `some` and both cores are declared.
  match okPair (endpointCallOnCore donEp donClient IpcMessage.empty c0 stDonBase) with
  | none => assertBool "RR8.12 setup: the no-receiver call parks the caller" false
  | some (stCall, _) =>
    assertBool "the caller parks `.blockedOnCall`" (ipcStateIs stCall donClient (.blockedOnCall donEp))
    assertBool "the pre-state Call guard fires on a queued Call"
      (decide (rendezvousSenderIsCall stCall donClient = true))
    assertBool "...so the `Call`-narrowed resolver names the queued caller"
      (decide (receiveRendezvousCallSender? stCall donEp = some donClient))
    assertBool "...the donation resolver would hand the caller's context to the passive server"
      (decide (callDonationSchedContext? stCall donClient donServer = some scClient))
    assertBool "...so the donation-keyed resolver names the caller too"
      (decide (receiveRendezvousDonatingSender? stCall donEp donServer = some donClient))
    assertBool "...and the segment declares the donor's and the receiver's homes"
      (decide (endpointReceiveHandoffReplenishCores stCall donEp donServer
                 = [determineTargetCore stCall donClient,
                    determineTargetCore stCall donServer]))
    assertBool "CONTROL: both retired readings agree here — each names two cores"
      (decide (senderKeyedReplenishCores stCall donEp donServer
                 = endpointReceiveHandoffReplenishCores stCall donEp donServer
               ∧ callKeyedReplenishCores stCall donEp donServer
                 = endpointReceiveHandoffReplenishCores stCall donEp donServer))
    -- ...and the reason both cores are needed: at the state the donation runs on the
    -- resolver still answers `some` (the binding frame, measured) and the step donates.
    match okPair (endpointReceiveDualOnCore donEp donServer (some donReply) c1 stCall) with
    | none => assertBool "RR8.12: the passive server's receive completes the Call rendezvous" false
    | some (stRecv, (sender, _)) =>
      assertBool "the receive dequeues the parked caller" (sender == donClient)
      assertBool "the post-state Call guard fires"
        (decide (rendezvousDequeuedCall stRecv donClient = true))
      assertBool "the resolver's answer survives the receive leg"
        (decide (callDonationSchedContext? stRecv donClient donServer = some scClient))
      assertBool "...and the donation step hands the context over"
        (match applyReceiveRendezvousDonation stRecv donServer donClient with
         | .ok stDon =>
             (match stDon.getTcb? donServer with
              | some t => t.schedContextBinding == .donated scClient donClient
              | none => false)
         | .error _ => false)
  -- (b) a plain `Send` rendezvous: the donation is the identity, so NO replenish
  --     lock is declared.  This is the shape the sender-keyed segment over-declared.
  match okPair (endpointSendDualOnCore donEp donClient IpcMessage.empty c0
      stHandoffActiveBase) with
  | none => assertBool "RR8.12 setup: the no-receiver send parks the sender" false
  | some (stSend, _) =>
    assertBool "the sender parks `.blockedOnSend`" (ipcStateIs stSend donClient (.blockedOnSend donEp))
    assertBool "the pre-state guard is false on a queued plain Send"
      (decide (rendezvousSenderIsCall stSend donClient = false))
    assertBool "...so the `Call`-narrowed resolver names nobody"
      (decide (receiveRendezvousCallSender? stSend donEp = none))
    assertBool "...and so does the donation-keyed one"
      (decide (receiveRendezvousDonatingSender? stSend donEp donServer = none))
    assertBool "PAYOFF: the segment declares NO replenish-queue lock"
      (decide (endpointReceiveHandoffReplenishCores stSend donEp donServer = []))
    -- The decisive comparison: same state, same endpoint, same receiver; the
    -- sender-keyed reading declares two cores for a migration that does not happen.
    assertBool "NEGATIVE (the defect): the sender-keyed retired reading declared TWO cores here"
      (decide ((senderKeyedReplenishCores stSend donEp donServer).length = 2))
    assertBool "CONTROL: the `Call`-keyed retired reading already agreed here"
      (decide (callKeyedReplenishCores stSend donEp donServer = []))
    -- ...and the reason it is sound to declare none: the donation step is the
    -- identity, because the receive leg leaves the dequeued sender `.ready`.
    match okPair (endpointReceiveDualOnCore donEp donServer (some donReply) c1 stSend) with
    | none => assertBool "RR8.12: the receive completes the plain-Send rendezvous" false
    | some (stRecv, (sender, _)) =>
      assertBool "the receive dequeues the parked sender" (sender == donClient)
      assertBool "the dequeued sender is woken `.ready`, not `.blockedOnReply`"
        (ipcStateIs stRecv donClient .ready)
      assertBool "...so the post-state donation guard is false"
        (decide (rendezvousDequeuedCall stRecv donClient = false))
      -- Asserted on the replenish queues themselves rather than on state equality:
      -- what the footprint claims is that no replenishment moves, and that is the
      -- proposition, not "the states are equal" (which `SystemState` cannot decide).
      assertBool "...and the donation step moves NO replenishment on either core"
        (match applyReceiveRendezvousDonation stRecv donServer donClient with
         | .ok stDon =>
             (replenishEntriesOn stDon (determineTargetCore stRecv donClient)
                == replenishEntriesOn stRecv (determineTargetCore stRecv donClient))
             && (replenishEntriesOn stDon (determineTargetCore stRecv donServer)
                == replenishEntriesOn stRecv (determineTargetCore stRecv donServer))
         | .error _ => false)
  -- (c) a `Call` rendezvous the resolver DECLINES: the receiver already holds a context
  --     of its own (`stHandoffActiveBase`'s active server), so the donation is the
  --     identity and NO replenish lock is declared.  This is the shape the
  --     `Call`-keyed segment still over-declared, and the one Cut C1 closes.
  match okPair (endpointCallOnCore donEp donClient IpcMessage.empty c0 stHandoffActiveBase) with
  | none => assertBool "RR8.12 setup: the no-receiver call parks the caller" false
  | some (stCallActive, _) =>
    assertBool "the caller parks `.blockedOnCall`"
      (ipcStateIs stCallActive donClient (.blockedOnCall donEp))
    assertBool "the pre-state Call guard fires"
      (decide (rendezvousSenderIsCall stCallActive donClient = true))
    assertBool "CONTROL: the `Call`-narrowed resolver admits this shape — the decline is the donation resolver's"
      (decide (receiveRendezvousCallSender? stCallActive donEp = some donClient))
    assertBool "...but the donation resolver declines: the receiver holds a context of its own"
      (decide (callDonationSchedContext? stCallActive donClient donServer = none))
    assertBool "...so the donation-keyed resolver names nobody"
      (decide (receiveRendezvousDonatingSender? stCallActive donEp donServer = none))
    assertBool "PAYOFF: the segment declares NO replenish-queue lock"
      (decide (endpointReceiveHandoffReplenishCores stCallActive donEp donServer = []))
    assertBool "NEGATIVE (the defect): the `Call`-keyed retired reading declared TWO cores here"
      (decide ((callKeyedReplenishCores stCallActive donEp donServer).length = 2))
    match okPair (endpointReceiveDualOnCore donEp donServer (some donReply) c1 stCallActive) with
    | none => assertBool "RR8.12: the active server's receive completes the Call rendezvous" false
    | some (stRecvActive, (sender, _)) =>
      assertBool "the receive dequeues the parked caller" (sender == donClient)
      assertBool "the dequeued caller IS `.blockedOnReply`: the post-state Call guard fires"
        (decide (rendezvousDequeuedCall stRecvActive donClient = true))
      assertBool "...and the resolver still declines at the state the donation runs on (the licence, measured)"
        (decide (callDonationSchedContext? stRecvActive donClient donServer = none))
      assertBool "...so the donation step moves NO replenishment on either core"
        (match applyReceiveRendezvousDonation stRecvActive donServer donClient with
         | .ok stDon =>
             (replenishEntriesOn stDon (determineTargetCore stRecvActive donClient)
                == replenishEntriesOn stRecvActive (determineTargetCore stRecvActive donClient))
             && (replenishEntriesOn stDon (determineTargetCore stRecvActive donServer)
                == replenishEntriesOn stRecvActive (determineTargetCore stRecvActive donServer))
         | .error _ => false)
      assertBool "...and hands no context over: the server keeps its own reservation"
        (match applyReceiveRendezvousDonation stRecvActive donServer donClient with
         | .ok stDon =>
             (match stDon.getTcb? donServer with
              | some t => t.schedContextBinding == .bound scHandoffServer
              | none => false)
         | .error _ => false)

-- ============================================================================
-- §3.27 the `.replyRecv` deschedule names the thread the pop unbound
--        (WS-RR RR8.12, PR #897 review)
-- ============================================================================

/-! The post-receive half used to deschedule `recordedReplyServer?` — the server
the answered caller recorded when it **Called** — while the thread the pop makes
`.unbound` is the answered frame's head context's own `boundThread`.  HP4
(`v0.35.38`) repointed the pop's *trigger* onto the frame and left the
*deschedule* on the binding-era proxy; HP6.8 (`v0.35.45`) made the splice live,
which is what puts the two readings in disagreement — a spliced middle caller
leaves an **orphan head**, and there the context's bound thread is not the thread
the caller recorded.

Two-sided, and the suite measures both sides: the holder stayed runnable while
`.unbound` (`hasSufficientBudget` is unconditionally `true` there, so it runs at
its legacy TCB band charged to no reservation — PR #895 round 8's defect on the
sibling site that round did not sweep), and an unrelated thread still holding its
own reservation was taken off its run queue and left `.ready`, which WS-OD OD1.7
enumerates as unrecoverable (`.tcbResume` demands `.Inactive`, `schedContextBind`
re-buckets only an already-queued thread, and `chooseThreadOnCore` never scans
ready TCBs).

The retired reading lives here, `private`, and nowhere else. -/

/-- The superseded deschedule target: the server the answered caller recorded at
Call time, which is the holder only while nothing has re-headed the stack. -/
private def recordedServerDescheduleTarget (st : SystemState) (prevCaller receiver : SeLe4n.ThreadId) :
    SeLe4n.ThreadId :=
  (recordedReplyServer? st prevCaller).getD receiver

private def orphanS1 : SeLe4n.ThreadId := ⟨861⟩
private def orphanClient : SeLe4n.ThreadId := ⟨862⟩
private def orphanHolder : SeLe4n.ThreadId := ⟨863⟩
private def orphanSender : SeLe4n.ThreadId := ⟨864⟩
private def orphanDelegate : SeLe4n.ThreadId := ⟨865⟩
private def orphanEp : SeLe4n.ObjId := ⟨866⟩
private def orphanReply : SeLe4n.ReplyId := ⟨867⟩
private def orphanSc : SeLe4n.SchedContextId := ⟨868⟩
private def orphanS1Sc : SeLe4n.SchedContextId := ⟨869⟩

/-- **The orphan head**: `orphanReply` heads `orphanSc`, whose `boundThread` is
`orphanHolder`, while `orphanClient` recorded `orphanS1` as its server.  A plain
`Send` waits on the endpoint so the receive leg takes the **non-rendezvous** arm,
which is the arm that deschedules unconditionally.  `orphanS1` carries a
reservation of its own, so descheduling it is a measurable strand rather than a
no-op. -/
private def stOrphanHeadReplyRecv : SystemState :=
  (BootstrapBuilder.empty
    |>.withObject cnRoot (.cnode
        { depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
          slots := SeLe4n.UniqueSlotMap.ofListWF [] })
    |>.withObject orphanEp (.endpoint
        { sendQ := ({ head := some orphanSender, tail := some orphanSender } : IntrusiveQueue) })
    |>.withObject orphanReply.toObjId (.reply
        { replyId := orphanReply, caller := some orphanClient,
          next := some (.head orphanSc) })
    |>.withObject orphanClient.toObjId (.tcb { mkTcb 862 30 (some c1) with
        ipcState := .blockedOnReply orphanEp (some orphanS1),
        threadState := .BlockedReply,
        replyObject := some orphanReply,
        schedContextBinding := SchedContextBinding.unbound })
    |>.withObject orphanS1.toObjId (.tcb { mkTcb 861 40 (some c2) with
        schedContextBinding := .bound orphanS1Sc })
    |>.withObject orphanHolder.toObjId (.tcb { mkTcb 863 50 (some c3) with
        schedContextBinding := .donated orphanSc orphanClient })
    |>.withObject orphanSender.toObjId (.tcb { mkTcb 864 20 (some c0) with
        ipcState := .blockedOnSend orphanEp,
        threadState := .BlockedSend,
        queuePPrev := some .endpointHead,
        pendingMessage := some IpcMessage.empty })
    |>.withObject orphanDelegate.toObjId (.tcb { mkTcb 865 25 (some c0) with
        schedContextBinding := SchedContextBinding.unbound })
    |>.withObject orphanSc.toObjId (.schedContext { SchedContext.empty orphanSc with
        boundThread := some orphanHolder, scReply := some orphanReply })
    |>.withObject orphanS1Sc.toObjId (.schedContext { SchedContext.empty orphanS1Sc with
        boundThread := some orphanS1 })
    |>.withRunnable [orphanS1, orphanHolder, orphanDelegate]
    |>.build)

/-- The CONTROL: `stOrphanHeadReplyRecv` with the answered caller recording the
**holder** — one field different, and the two readings then coincide, which is
the ordinary non-delegated steady state. -/
private def stAgreeingHeadReplyRecv : SystemState :=
  match stOrphanHeadReplyRecv.getTcb? orphanClient with
  | none => stOrphanHeadReplyRecv
  | some t =>
      { stOrphanHeadReplyRecv with
          objects := stOrphanHeadReplyRecv.objects.insert orphanClient.toObjId
            (.tcb { t with ipcState := .blockedOnReply orphanEp (some orphanHolder) }) }

private def runReplyRecvHolderDescheduleChecks : IO Unit := do
  IO.println "--- §3.27 WS-RR RR8.12: the `.replyRecv` deschedule names the pop's holder ---"
  let st := stOrphanHeadReplyRecv
  -- (i) Setup: the two readings DISAGREE on this state, which is the whole point.
  assertBool "setup: the answered frame heads the context, whose bound thread is the holder"
    (replyFrameHeadHolder? st orphanReply == some (orphanSc, orphanHolder))
  assertBool "setup: ...while the caller recorded a DIFFERENT server"
    (decide (recordedServerDescheduleTarget st orphanClient orphanDelegate = orphanS1)
      && decide (orphanS1 ≠ orphanHolder))
  assertBool "setup: both are runnable, and the recorded server holds its own reservation"
    (runnableOnSomeCore st orphanHolder && runnableOnSomeCore st orphanS1
      && decide ((st.getTcb? orphanS1).map (·.schedContextBinding)
          = some (SchedContextBinding.bound orphanS1Sc)))
  -- (ii) The live arm, end to end.
  match replyRecvBody orphanEp orphanDelegate orphanReply orphanClient IpcMessage.empty
      cnRoot (SeLe4n.Slot.ofNat 0) c0 st with
  | .error e => assertBool s!"the live `.replyRecv` must succeed (got {reprStr e})" false
  | .ok (_, stOut) =>
      -- The pop unbound the holder...
      assertBool "the pop unbinds the holder"
        (decide ((stOut.getTcb? orphanHolder).map (·.schedContextBinding)
          = some SchedContextBinding.unbound))
      -- ...and the deschedule takes THAT thread off its run queue.
      assertBool "...and the deschedule takes the HOLDER off its core: no unbudgeted runnable"
        (!runnableOnSomeCore stOut orphanHolder && !runningOnSomeCore stOut orphanHolder)
      -- ...while the recorded server, which lost nothing, keeps its placement.
      assertBool "...while the recorded server keeps its reservation AND its placement"
        (decide ((stOut.getTcb? orphanS1).map (·.schedContextBinding)
            = some (SchedContextBinding.bound orphanS1Sc))
          && threadPlacedOnSomeCore stOut orphanS1)
      -- The retired reading, computed beside the live one: it names the thread
      -- the fix stopped descheduling, so the assertions above discriminate.
      assertBool "NEGATIVE: the RETIRED target is the recorded server, not the holder"
        (decide (recordedServerDescheduleTarget st orphanClient orphanDelegate ≠ orphanHolder))
  -- (iii) The CONTROL: the same fixture with the caller recording the holder --
  -- one field different, the two readings agreeing, which is the non-delegated
  -- steady state.  There the fix is the identity, so an implementation that
  -- descheduled `recordedReplyServer?` passes (iii) and fails (ii): that is what
  -- makes (ii) a measurement of the DIVERGENCE rather than of the deschedule.
  let stAgree := stAgreeingHeadReplyRecv
  assertBool "CONTROL setup: here the recorded server IS the holder"
    (decide (recordedServerDescheduleTarget stAgree orphanClient orphanDelegate = orphanHolder))
  match replyRecvBody orphanEp orphanDelegate orphanReply orphanClient IpcMessage.empty
      cnRoot (SeLe4n.Slot.ofNat 0) c0 stAgree with
  | .error e => assertBool s!"the control `.replyRecv` must succeed (got {reprStr e})" false
  | .ok (_, stOut) =>
      assertBool "CONTROL: the holder is descheduled here too -- the fix is the identity"
        (!runnableOnSomeCore stOut orphanHolder && !runningOnSomeCore stOut orphanHolder)
      assertBool "CONTROL: ...and the bystander is untouched, as it is on the divergent shape"
        (threadPlacedOnSomeCore stOut orphanS1)

-- ============================================================================
-- §3.28 the pre-receive donation return migrates its replenishments
--        (register row 57, `v0.35.161`)
-- ============================================================================

/-! The block arm of the cross-core receive leg returns a `.donated` receiver's
context to its owner before the receiver parks, and until `v0.35.161` it ran the
pop bare: `boundThread` moved to the owner and the reservation's replenishments
stayed on the receiver's home core, so `replenishQueueAffinityConsistent_smp` was
false on a state three ordinary operations reach.  What the theorems now say
(`cleanupPreReceiveDonationMigrated_preserves_replenishQueueAffinityConsistent_smp`,
`endpointReceiveDualOnCore_preserves_replenishQueueAffinityConsistent_smp`) is that
the migrated return preserves the invariant; what no theorem states is that the
invariant is *falsifiable* by the bare pop on a reachable state — which is the
whole content of the defect, and this section's subject.

The retired reading is not a private copy here, because the bare pop is still a
live definition (`cleanupPreReceiveDonationChecked`, the migrated return's own first
half): it is computed beside the migrated one on the same state, so the assertions
are known to discriminate.  Two controls bound the claim: a receiver holding no
loan, where the migrated return is the identity, and an owner homed on the
receiver's own core, where the migration is. -/

/-- The decidable reading of `replenishQueueAffinityConsistent_smp`, clause for
clause: every entry of every core's replenish queue names a context that is either
unresolvable, unbound, or bound to a thread homed on that core. -/
private def replenishAffinityConsistentB (st : SystemState) : Bool :=
  Concurrency.allCores.all fun c =>
    (replenishEntriesOn st c).all fun e =>
      match st.getSchedContext? e.1 with
      | some sc =>
          match sc.boundThread with
          | some t => decide (determineTargetCore st t = c)
          | none => true
      | none => true

/-- `stDonBase` with one replenishment for the client's context on the client's
home core — the shape the invariant is about, since a queue holding no entry for the
context satisfies it vacuously and could witness no migration. -/
private def stPreReturnBase : SystemState :=
  { stDonBase with scheduler :=
      stDonBase.scheduler.setReplenishQueueOnCore c0 (ReplenishQueue.empty.insert scClient 100) }

/-- The same-core CONTROL: the client pinned to the server's own core, its
replenishment there too, so the return's migration is the identity. -/
private def stPreReturnSameCore : SystemState :=
  { stDonBase with
      objects := stDonBase.objects.insert donClient.toObjId
        (.tcb { mkTcb 841 60 (some c1) with schedContextBinding := .bound scClient }),
      scheduler :=
        stDonBase.scheduler.setReplenishQueueOnCore c1 (ReplenishQueue.empty.insert scClient 100) }

/-- The three-operation prefix the defect needs: the client `Call`s with nobody
waiting and parks; the passive server takes it with a `Recv`, whose hand-off donates
the client's context and migrates its replenishment to the server's home; the state
returned is the one the server then abandons the call from. -/
private def preReturnHandoffState (base : SystemState) : Option SystemState := do
  let (stCall, _) ← okPair (endpointCallOnCore donEp donClient IpcMessage.empty c0 base)
  let (stRecv, (dequeued, _)) ← okPair (endpointReceiveDualOnCore donEp donServer (some donReply) c1 stCall)
  okExcept (applyReceiveRendezvousHandoff stRecv donServer dequeued c1)

private def runPreReceiveReturnMigrationChecks : IO Unit := do
  IO.println "--- §3.28 register row 57: the pre-receive donation return migrates its replenishments ---"
  match preReturnHandoffState stPreReturnBase with
  | none => assertBool "row 57 setup: call, rendezvous and hand-off succeed" false
  | some stDon =>
    -- (i) the hand-off left the shape the defect needs: the server holds the loan,
    --     the context is bound to it, and the replenishment sits on ITS home core.
    assertBool "setup: the server holds the client's context on loan"
      (match stDon.getTcb? donServer with
       | some t => t.schedContextBinding == .donated scClient donClient | none => false)
    assertBool "setup: the context is bound to the server"
      (match stDon.getSchedContext? scClient with
       | some sc => sc.boundThread == some donServer | none => false)
    assertBool "setup: the hand-off migrated the replenishment to the server's home (core 1)"
      (replenishCountFor stDon c1 scClient == 1 && replenishCountFor stDon c0 scClient == 0)
    assertBool "setup: the invariant holds at the hand-off's post-state (the hand-off migrates)"
      (replenishAffinityConsistentB stDon)
    assertBool "setup: the pop's own guard resolves the loan and its owner"
      (decide (preReceiveDonation? stDon donServer = some (scClient, donClient)))
    -- (ii) NEGATIVE (the defect): the bare pop rebinds the context to the client,
    --      homed on core 0, and leaves the replenishment on core 1.
    match okExcept (cleanupPreReceiveDonationChecked stDon donServer) with
    | none => assertBool "row 57: the bare pop succeeds" false
    | some stBare =>
      assertBool "NEGATIVE: the bare pop binds the context back to the client..."
        (match stBare.getSchedContext? scClient with
         | some sc => sc.boundThread == some donClient | none => false)
      assertBool "NEGATIVE: ...whose home is core 0..."
        (decide (determineTargetCore stBare donClient = c0))
      assertBool "NEGATIVE: ...while the replenishment stays on core 1"
        (replenishCountFor stBare c1 scClient == 1 && replenishCountFor stBare c0 scClient == 0)
      assertBool "NEGATIVE (the defect): the bare pop FALSIFIES the affinity invariant"
        (!replenishAffinityConsistentB stBare)
      -- The destination the migrated return reads off the post-pop state IS the
      -- owner's home (`preReceiveReturnMigration_destination`, measured).
      assertBool "the post-pop home of the context is the client's home"
        (decide (replenishHomeOfSchedContext stBare scClient (determineTargetCore stDon donServer)
                   = determineTargetCore stDon donClient))
    -- (iii) PAYOFF: the migrated return moves the replenishment with the binding.
    match okExcept (cleanupPreReceiveDonationMigrated stDon donServer) with
    | none => assertBool "row 57: the migrated return succeeds" false
    | some stMig =>
      assertBool "PAYOFF: the migrated return binds the context back to the client too"
        (match stMig.getSchedContext? scClient with
         | some sc => sc.boundThread == some donClient | none => false)
      assertBool "PAYOFF: ...and the replenishment now sits on the client's home (core 0)"
        (replenishCountFor stMig c0 scClient == 1 && replenishCountFor stMig c1 scClient == 0)
      assertBool "PAYOFF: the affinity invariant holds after the migrated return"
        (replenishAffinityConsistentB stMig)
      assertBool "the two returns agree on every object: the migration is scheduler-only"
        (match stMig.getTcb? donServer, stMig.getTcb? donClient with
         | some s, some c =>
             s.schedContextBinding == SchedContextBinding.unbound
               && c.schedContextBinding == .bound scClient
         | _, _ => false)
    -- (iv) ...and the LIVE leg runs the migrated one: the server's plain `Recv` on
    --      the empty endpoint blocks it, and the state it parks in is affinity-consistent.
    match okPair (endpointReceiveDualOnCore donEp donServer none c1 stDon) with
    | none => assertBool "row 57: the abandoning receive blocks" false
    | some (stBlock, (who, _)) =>
      assertBool "the receive parks the server itself" (who == donServer)
      assertBool "...`.blockedOnReceive`, holding no context"
        (ipcStateIs stBlock donServer (.blockedOnReceive donEp)
          && (match stBlock.getTcb? donServer with
              | some t => t.schedContextBinding == SchedContextBinding.unbound | none => false))
      assertBool "PAYOFF: the live leg leaves the replenishment on the client's home"
        (replenishCountFor stBlock c0 scClient == 1 && replenishCountFor stBlock c1 scClient == 0)
      assertBool "PAYOFF: the live leg's post-state is affinity-consistent"
        (replenishAffinityConsistentB stBlock)
    -- (v) the footprint the object domain and the scheduler domain both read: on this
    --     block the segment names the receiver's home and the owner's, in that order.
    assertBool "the block path's replenish segment names the receiver's home and the owner's"
      (decide (endpointReceiveHandoffReplenishCores stDon donEp donServer
                 = [determineTargetCore stDon donServer, determineTargetCore stDon donClient]))
    assertBool "...which are two different cores"
      (decide (determineTargetCore stDon donServer ≠ determineTargetCore stDon donClient))
  -- (vi) CONTROL: a receiver holding no loan — the migrated return is the identity
  --      and the segment is empty, so the payoff above is attributable to the loan.
  assertBool "CONTROL: the passive server of `stDonBase` holds no loan"
    (decide (preReceiveDonation? stDonBase donServer = none))
  assertBool "CONTROL: ...so the migrated return is the identity on it"
    (match okExcept (cleanupPreReceiveDonationMigrated stDonBase donServer) with
     | some stOut =>
         Concurrency.allCores.all fun c =>
           replenishEntriesOn stOut c == replenishEntriesOn stDonBase c
     | none => false)
  assertBool "CONTROL: ...and a block there declares no replenish-queue lock"
    (decide (endpointReceiveHandoffReplenishCores stDonBase donEp donServer = []))
  -- (vii) CONTROL: an owner homed on the receiver's own core — the migration is
  --       the identity, so the fix is keyed on the two homes and not on the pop.
  match preReturnHandoffState stPreReturnSameCore with
  | none => assertBool "row 57 same-core setup: call, rendezvous and hand-off succeed" false
  | some stSame =>
    assertBool "CONTROL: both homes are core 1"
      (decide (determineTargetCore stSame donServer = c1
               ∧ determineTargetCore stSame donClient = c1))
    match okExcept (cleanupPreReceiveDonationMigrated stSame donServer),
        okExcept (cleanupPreReceiveDonationChecked stSame donServer) with
    | some stMigSame, some stBareSame =>
      assertBool "CONTROL: the migrated and the bare return leave the same replenish queues"
        (Concurrency.allCores.all fun c =>
          replenishEntriesOn stMigSame c == replenishEntriesOn stBareSame c)
      assertBool "CONTROL: ...both on core 1, and both affinity-consistent"
        (replenishCountFor stMigSame c1 scClient == 1 && replenishAffinityConsistentB stMigSame
          && replenishAffinityConsistentB stBareSame)
    | _, _ => assertBool "row 57 same-core: both returns succeed" false

-- ============================================================================
-- §3.29 the `.replyRecv` scheduler footprint's replenish segment follows the spine
--        (WS-RR RR8.12 Cut C2, `v0.35.162`)
-- ============================================================================

/-! The live `.replyRecv` performs up to three SchedContext hand-offs, each migrating
a reservation's replenishments between two cores — the pop between its legs, the
receive leg's block-path return, and the re-donation to the receiver when the
receive leg dequeues a `Call` — and `schedLockSet_endpointReplyRecvOnCore` declares
their cores by re-running the spine and reading each hand-off at the state it runs
on, through its own arm selector.  The coverage theorems say the declared cores ARE
the migrations' endpoints; what no theorem states is that **every hand-off is
reachable by the live operations and the segment differs between the shapes**,
which is this section's subject.

Three shapes, each built through the live operations.  (a) The MCS steady state with
a second client on a third core: the pop and the re-donation both fire, and the
segment names three cores.  (b) A first client that never donated (a legacy
`.unbound` thread): the pop hands nothing back and the segment is EMPTY — and this
is the shape on which the `.receive` arm's pre-state reading, computed beside the
live one, declares two cores for a migration the `.replyRecv` transition does not
perform.  That divergence between the two receiving arms is the one
`docs/REGISTERED_DEBT.md`'s WS-CB row records: on a `.replyRecv` whose pop returned
nothing, a dequeued `Call` caller's context is not donated to an `.unbound`
receiver, where `.receive` and seL4-MCS's `receiveIPC` would donate.  The assertion
that pins it is labelled MEASURED and must flip when that row closes.  (c) A
delegated invoker that answers another server's client and then blocks holding a
loan of its own: the pop and the block-path return both fire, on four distinct
cores, and the post-receive half deschedules the holder the pop unbound. -/

/-- The second client, pinned to core 2, with its own context and a replenishment
on that core. -/
private def fpClient2 : SeLe4n.ThreadId := ⟨871⟩
private def fpClient2Sc : SeLe4n.SchedContextId := SchedContextId.ofNat 872

private def fpClient2SchedContext : SchedContext :=
  { scId := fpClient2Sc, budget := ⟨100⟩, period := ⟨1000⟩, priority := ⟨55⟩,
    deadline := ⟨0⟩, domain := ⟨0⟩, budgetRemaining := ⟨50⟩,
    boundThread := some fpClient2, isActive := true }

/-- The shape (c) needs: a second endpoint with its own passive server (home core
3) and a bound client pinned to core 2. -/
private def fpEp2 : SeLe4n.ObjId := ⟨874⟩
private def fpDelegate : SeLe4n.ThreadId := ⟨875⟩
private def fpClientX : SeLe4n.ThreadId := ⟨876⟩
private def fpClientXSc : SeLe4n.SchedContextId := SchedContextId.ofNat 877
private def fpReplyX : SeLe4n.ReplyId := ⟨878⟩

private def fpClientXSchedContext : SchedContext :=
  { scId := fpClientXSc, budget := ⟨100⟩, period := ⟨1000⟩, priority := ⟨45⟩,
    deadline := ⟨0⟩, domain := ⟨0⟩, budgetRemaining := ⟨50⟩,
    boundThread := some fpClientX, isActive := true }

/-- `stDonBase` — a bound client homed on the boot core, a passive server homed on
core 1 — plus the second client on core 2, with one replenishment per context on
its holder's home core.  The shape the invariant is about: a queue holding no entry
for a context satisfies it vacuously and could witness no migration. -/
private def stFpPassiveBase : SystemState :=
  let objs := stDonBase.objects
    |>.insert fpClient2Sc.toObjId (.schedContext fpClient2SchedContext)
    |>.insert fpClient2.toObjId
        (.tcb { mkTcb 871 55 (some c2) with schedContextBinding := .bound fpClient2Sc })
  let base : SystemState := { stDonBase with objects := objs }
  let sched := base.scheduler
    |>.setReplenishQueueOnCore c0 (ReplenishQueue.empty.insert scClient 100)
    |>.setReplenishQueueOnCore c2 (ReplenishQueue.empty.insert fpClient2Sc 100)
  { base with scheduler := sched }

/-- The same, with the FIRST client a legacy `.unbound` thread — its `Call` donates
nothing, so the server's reply hands nothing back. -/
private def stFpLegacyBase : SystemState :=
  let objs := stDonBase.objects
    |>.insert fpClient2Sc.toObjId (.schedContext fpClient2SchedContext)
    |>.insert fpClient2.toObjId
        (.tcb { mkTcb 871 55 (some c2) with schedContextBinding := .bound fpClient2Sc })
    |>.insert donClient.toObjId
        (.tcb { mkTcb 841 60 none with schedContextBinding := SchedContextBinding.unbound })
  let base : SystemState := { stDonBase with objects := objs }
  let sched := base.scheduler
    |>.setReplenishQueueOnCore c2 (ReplenishQueue.empty.insert fpClient2Sc 100)
  { base with scheduler := sched }

/-- `stDonBase` plus the second endpoint's pair: a passive delegate homed on core 3
and a bound client on core 2, each context's replenishment on its holder's home. -/
private def stFpDelegatedBase : SystemState :=
  let objs := stDonBase.objects
    |>.insert fpEp2 (.endpoint {})
    |>.insert fpClientXSc.toObjId (.schedContext fpClientXSchedContext)
    |>.insert fpClientX.toObjId
        (.tcb { mkTcb 876 45 (some c2) with schedContextBinding := .bound fpClientXSc })
    |>.insert fpDelegate.toObjId
        (.tcb { mkTcb 875 20 (some c3) with schedContextBinding := SchedContextBinding.unbound })
    |>.insert fpReplyX.toObjId (.reply { replyId := fpReplyX })
  let base : SystemState := { stDonBase with objects := objs }
  let sched := base.scheduler
    |>.setReplenishQueueOnCore c0 (ReplenishQueue.empty.insert scClient 100)
    |>.setReplenishQueueOnCore c2 (ReplenishQueue.empty.insert fpClientXSc 100)
  { base with scheduler := sched }

/-- The MCS steady state, built the way a real one arrives at it: the server blocks
on `Recv`, the first client `Call`s, the server's home core dispatches it, and the
second client `Call`s from its own core and queues behind the busy server. -/
private def fpSteadyState (base : SystemState) : Option SystemState := do
  let (stRecv, _) ← okPair (endpointReceiveDualOnCore donEp donServer (some donReply) c1 base)
  let (stCall, resCall) := endpointCallCrossCoreDispatch donEp donClient IpcMessage.empty
    AccessRightSet.empty (SeLe4n.Slot.ofNat 0) c0 stRecv
  let _ ← okExcept resCall
  let stDispatched ← okExcept (handleRescheduleSgiOnCore stCall c1)
  let (stQueued, resQueued) := endpointCallCrossCoreDispatch donEp fpClient2 IpcMessage.empty
    AccessRightSet.empty (SeLe4n.Slot.ofNat 0) c2 stDispatched
  let _ ← okExcept resQueued
  pure stQueued

/-- Shape (c)'s state: the first pair as above (no second client), then the delegate
blocks on the second endpoint, its client `Call`s from core 2 donating, and core 3
dispatches the delegate — which then answers the FIRST server's client. -/
private def fpDelegatedState (base : SystemState) : Option SystemState := do
  let (stRecv, _) ← okPair (endpointReceiveDualOnCore donEp donServer (some donReply) c1 base)
  let (stCall, resCall) := endpointCallCrossCoreDispatch donEp donClient IpcMessage.empty
    AccessRightSet.empty (SeLe4n.Slot.ofNat 0) c0 stRecv
  let _ ← okExcept resCall
  let stDispatched ← okExcept (handleRescheduleSgiOnCore stCall c1)
  let (stRecv2, _) ← okPair (endpointReceiveDualOnCore fpEp2 fpDelegate (some fpReplyX) c3
    stDispatched)
  let (stCall2, resCall2) := endpointCallCrossCoreDispatch fpEp2 fpClientX IpcMessage.empty
    AccessRightSet.empty (SeLe4n.Slot.ofNat 0) c2 stRecv2
  let _ ← okExcept resCall2
  okExcept (handleRescheduleSgiOnCore stCall2 c3)

/-- How many replenish-queue write locks a footprint names. -/
private def replenishMemberCount (fp : List (SchedLockId × Concurrency.AccessMode)) : Nat :=
  (fp.filter (fun p => p.1 matches SchedLockId.replenishQueue _)).length

private def hasReplenishWrite (fp : List (SchedLockId × Concurrency.AccessMode)) (c : CoreId) :
    Bool :=
  decide ((SchedLockId.replenishQueue ⟨c⟩, Concurrency.AccessMode.write) ∈ fp)

private def hasRunQueueWrite (fp : List (SchedLockId × Concurrency.AccessMode)) (c : CoreId) :
    Bool :=
  decide ((SchedLockId.runQueue ⟨c⟩, Concurrency.AccessMode.write) ∈ fp)

private def runReplyRecvFootprintChecks : IO Unit := do
  IO.println "--- §3.29 WS-RR RR8.12 Cut C2: the `.replyRecv` footprint's replenish segment ---"
  -- (a) the steady state: the pop AND the re-donation fire, on three cores.
  match fpSteadyState stFpPassiveBase with
  | none => assertBool "Cut C2 setup (a): recv, call, dispatch and second call succeed" false
  | some stQ =>
    assertBool "(a) setup: the server holds the first client's context on loan"
      (match stQ.getTcb? donServer with
       | some t => t.schedContextBinding == .donated scClient donClient | none => false)
    assertBool "(a) setup: the first Call's hand-off migrated that context's replenishment to core 1"
      (replenishCountFor stQ c1 scClient == 1 && replenishCountFor stQ c0 scClient == 0)
    assertBool "(a) setup: the second client's Call is queued, and its replenishment sits on core 2"
      (ipcStateIs stQ fpClient2 (.blockedOnCall donEp)
        && replenishCountFor stQ c2 fpClient2Sc == 1)
    assertBool "(a) setup: the answered frame heads the loaned context, bound to the server"
      (replyFrameHeadHolder? stQ donReply == some (scClient, donServer))
    assertBool "(a) setup: the affinity invariant holds before the ReplyRecv"
      (replenishAffinityConsistentB stQ)
    let seg := replyRecvHandoffReplenishCores donEp donServer donReply donClient IpcMessage.empty
      cnRoot (SeLe4n.Slot.ofNat 0) c1 stQ
    let fp := schedLockSet_endpointReplyRecvOnCore donEp donServer donReply donClient
      IpcMessage.empty cnRoot (SeLe4n.Slot.ofNat 0) c1 stQ
    -- The segment mirrors the spine: the pop's pair (server's home, client's home),
    -- nothing for the rendezvousing receive leg, the re-donation's pair (second
    -- client's home, server's home).
    assertBool "(a) the segment is the pop's pair, then the re-donation's pair: [1, 0, 2, 1]"
      (decide (seg = [c1, c0, c2, c1]))
    assertBool "(a) the footprint names replenish-queue write locks on cores 0, 1 and 2 -- and not 3"
      (hasReplenishWrite fp c0 && hasReplenishWrite fp c1 && hasReplenishWrite fp c2
        && !hasReplenishWrite fp c3 && replenishMemberCount fp == 3)
    assertBool "(a) ...and the run-queue write lock of the answered client's home core"
      (hasRunQueueWrite fp c0)
    -- The live arm, end to end: both migrations happen, between exactly those cores.
    match replyRecvBody donEp donServer donReply donClient IpcMessage.empty cnRoot
        (SeLe4n.Slot.ofNat 0) c1 stQ with
    | .error e => assertBool s!"(a) the live `.replyRecv` must succeed (got {reprStr e})" false
    | .ok (_, stOut) =>
      assertBool "(a) PAYOFF: the pop migrated the first context back to the client's home (1 -> 0)"
        (replenishCountFor stOut c0 scClient == 1 && replenishCountFor stOut c1 scClient == 0)
      assertBool "(a) PAYOFF: the re-donation migrated the second context to the server's home (2 -> 1)"
        (replenishCountFor stOut c1 fpClient2Sc == 1 && replenishCountFor stOut c2 fpClient2Sc == 0)
      assertBool "(a) PAYOFF: the affinity invariant holds after the ReplyRecv"
        (replenishAffinityConsistentB stOut)
      assertBool "(a) the bindings moved with the replenishments"
        (match stOut.getTcb? donServer, stOut.getTcb? donClient, stOut.getTcb? fpClient2 with
         | some s, some a, some b =>
             s.schedContextBinding == .donated fpClient2Sc fpClient2
               && a.schedContextBinding == .bound scClient
               && b.schedContextBinding == SchedContextBinding.unbound
         | _, _, _ => false)
    -- CONTROL: on THIS shape the `.receive` arm's pre-state reading of the receive
    -- leg, taken at the pop's post-state, agrees with the re-donation pair -- so an
    -- implementation that read the `.receive` segment there would pass (a) and be
    -- caught only by (b).  That is what makes (b) the measurement.
    let (st1, _) := endpointReplyOnCore donServer donClient IpcMessage.empty c1 stQ
    match replyRecvPopDonation donReply donClient st1 with
    | .error e => assertBool s!"(a) the pop must succeed (got {reprStr e})" false
    | .ok (returned?, st1p) =>
      assertBool "(a) CONTROL: the pop hands the loaned context back, naming the holder"
        (returned? == some (scClient, donServer))
      assertBool "(a) CONTROL: the `.receive` arm's pre-state segment at the pop's post-state agrees here"
        (decide (endpointReceiveHandoffReplenishCores st1p donEp donServer = [c2, c1]))
  -- (b) a first client that never donated: the pop hands nothing back, the segment
  --     is EMPTY, and the `.receive` reading declares two cores for a migration the
  --     `.replyRecv` transition does not perform.
  match fpSteadyState stFpLegacyBase with
  | none => assertBool "Cut C2 setup (b): recv, call, dispatch and second call succeed" false
  | some stQ =>
    assertBool "(b) setup: the server is passive and holds no loan -- the legacy client donated nothing"
      (match stQ.getTcb? donServer, stQ.getTcb? donClient with
       | some s, some a =>
           s.schedContextBinding == SchedContextBinding.unbound
             && a.schedContextBinding == SchedContextBinding.unbound
       | _, _ => false)
    assertBool "(b) setup: the answered frame heads no context"
      (replyFrameHeadHolder? stQ donReply == none)
    assertBool "(b) setup: the second client's Call is queued, bound, its replenishment on core 2"
      (ipcStateIs stQ fpClient2 (.blockedOnCall donEp)
        && replenishCountFor stQ c2 fpClient2Sc == 1)
    let seg := replyRecvHandoffReplenishCores donEp donServer donReply donClient IpcMessage.empty
      cnRoot (SeLe4n.Slot.ofNat 0) c1 stQ
    let fp := schedLockSet_endpointReplyRecvOnCore donEp donServer donReply donClient
      IpcMessage.empty cnRoot (SeLe4n.Slot.ofNat 0) c1 stQ
    assertBool "(b) PAYOFF: the segment is EMPTY" (decide (seg = []))
    assertBool "(b) PAYOFF: the footprint names NO replenish-queue write lock"
      (replenishMemberCount fp == 0)
    assertBool "(b) ...while it still names the answered client's run queue"
      (hasRunQueueWrite fp c0)
    let (st1, _) := endpointReplyOnCore donServer donClient IpcMessage.empty c1 stQ
    match replyRecvPopDonation donReply donClient st1 with
    | .error e => assertBool s!"(b) the pop must succeed (got {reprStr e})" false
    | .ok (returned?, st1p) =>
      assertBool "(b) the pop hands nothing back" (returned? == none)
      -- The decisive comparison: same state, same endpoint, same receiver -- the
      -- `.receive` arm's reading names two cores here.
      assertBool "(b) NEGATIVE: the `.receive` arm's pre-state segment declares TWO cores on this state"
        (decide (endpointReceiveHandoffReplenishCores st1p donEp donServer = [c2, c1]))
      -- ...and the reason the `.replyRecv` reading is the right one for THIS arm: at the
      -- state its post-receive half runs on, the `.receive` step WOULD donate --
      -- which is the divergence the register records, not a fact about the shape.
      let st2 := (endpointReceiveDualWithCapsOnCore donEp donServer (some donReply) cnRoot
        (SeLe4n.Slot.ofNat 0) c1 st1p).1
      assertBool "(b) the receive leg dequeues the second client's Call"
        (decide (rendezvousDequeuedCall st2 fpClient2 = true))
      assertBool "(b) MEASURED (register, WS-CB): the `.receive` arm's donation step WOULD hand the context over here"
        (match applyReceiveRendezvousDonation st2 donServer fpClient2 with
         | .ok stDon =>
             (match stDon.getTcb? donServer with
              | some t => t.schedContextBinding == .donated fpClient2Sc fpClient2
              | none => false)
         | .error _ => false)
    -- The live arm: no replenishment moves on any core (the exactness licence,
    -- measured), and no context is handed over (the divergence, measured).
    match replyRecvBody donEp donServer donReply donClient IpcMessage.empty cnRoot
        (SeLe4n.Slot.ofNat 0) c1 stQ with
    | .error e => assertBool s!"(b) the live `.replyRecv` must succeed (got {reprStr e})" false
    | .ok (_, stOut) =>
      assertBool "(b) PAYOFF: the live `.replyRecv` moves NO replenishment on any core"
        (Concurrency.allCores.all fun c => replenishEntriesOn stOut c == replenishEntriesOn stQ c)
      assertBool "(b) MEASURED (register, WS-CB): the `.replyRecv` never-donated arm hands NO context to the passive receiver"
        (match stOut.getTcb? donServer, stOut.getTcb? fpClient2 with
         | some s, some b =>
             s.schedContextBinding == SchedContextBinding.unbound
               && b.schedContextBinding == .bound fpClient2Sc
         | _, _ => false)
      assertBool "(b) ...although the second client IS the one now awaiting the server's reply"
        (match stOut.getTcb? fpClient2 with
         | some t => match t.ipcState with
                     | .blockedOnReply _ _ => true
                     | _ => false
         | none => false)
  -- (c) a delegated invoker: it answers the first server's client (the pop unbinds
  --     the server and migrates 1 -> 0) and then blocks on the empty endpoint holding
  --     its own loan (the block-path return migrates 3 -> 2).  Four cores, all named.
  match fpDelegatedState stFpDelegatedBase with
  | none => assertBool "Cut C2 setup (c): both pairs' recv, call and dispatch succeed" false
  | some stD =>
    assertBool "(c) setup: the server holds the first client's context, the delegate its own client's"
      (match stD.getTcb? donServer, stD.getTcb? fpDelegate with
       | some s, some d =>
           s.schedContextBinding == .donated scClient donClient
             && d.schedContextBinding == .donated fpClientXSc fpClientX
       | _, _ => false)
    assertBool "(c) setup: both replenishments sit on the holders' homes (cores 1 and 3)"
      (replenishCountFor stD c1 scClient == 1 && replenishCountFor stD c3 fpClientXSc == 1)
    assertBool "(c) setup: the first endpoint's send queue is empty, so the delegate's receive will block"
      (receiveRendezvousSender? stD donEp == none)
    assertBool "(c) setup: the delegate's own guard resolves its loan"
      (decide (preReceiveDonation? stD fpDelegate = some (fpClientXSc, fpClientX)))
    let seg := replyRecvHandoffReplenishCores donEp fpDelegate donReply donClient IpcMessage.empty
      cnRoot (SeLe4n.Slot.ofNat 0) c3 stD
    let fp := schedLockSet_endpointReplyRecvOnCore donEp fpDelegate donReply donClient
      IpcMessage.empty cnRoot (SeLe4n.Slot.ofNat 0) c3 stD
    assertBool "(c) the segment is the pop's pair, then the block-path return's pair: [1, 0, 3, 2]"
      (decide (seg = [c1, c0, c3, c2]))
    assertBool "(c) the footprint names replenish-queue write locks on all four cores"
      (hasReplenishWrite fp c0 && hasReplenishWrite fp c1 && hasReplenishWrite fp c2
        && hasReplenishWrite fp c3 && replenishMemberCount fp == 4)
    match replyRecvBody donEp fpDelegate donReply donClient IpcMessage.empty cnRoot
        (SeLe4n.Slot.ofNat 0) c3 stD with
    | .error e => assertBool s!"(c) the delegated `.replyRecv` must succeed (got {reprStr e})" false
    | .ok (_, stOut) =>
      assertBool "(c) PAYOFF: the pop migrated the first context back to its client's home (1 -> 0)"
        (replenishCountFor stOut c0 scClient == 1 && replenishCountFor stOut c1 scClient == 0)
      assertBool "(c) PAYOFF: the block-path return migrated the delegate's loan to its owner's home (3 -> 2)"
        (replenishCountFor stOut c2 fpClientXSc == 1 && replenishCountFor stOut c3 fpClientXSc == 0)
      assertBool "(c) PAYOFF: the affinity invariant holds after the delegated ReplyRecv"
        (replenishAffinityConsistentB stOut)
      assertBool "(c) the delegate parks `.blockedOnReceive` on the first endpoint, holding nothing"
        (ipcStateIs stOut fpDelegate (.blockedOnReceive donEp)
          && (match stOut.getTcb? fpDelegate with
              | some t => t.schedContextBinding == SchedContextBinding.unbound | none => false))
      assertBool "(c) ...its client holds its own context again, and the first client its own"
        (match stOut.getTcb? fpClientX, stOut.getTcb? donClient with
         | some x, some a =>
             x.schedContextBinding == .bound fpClientXSc && a.schedContextBinding == .bound scClient
         | _, _ => false)
      assertBool "(c) ...and the server the pop unbound is parked: `.unbound`, on no core"
        (match stOut.getTcb? donServer with
         | some s => s.schedContextBinding == SchedContextBinding.unbound
             && !runnableOnSomeCore stOut donServer && !runningOnSomeCore stOut donServer
         | none => false)

/-- **WS-RR RR8.12 Cut C3a**: the `.call` and `.reply` footprints, driven through the
live operations on the shapes where their replenish segments are non-empty, empty by
the guard, and empty by the path -- with the RR2.4 parametric footprint computed
beside the derived one on the shape where the two part. -/
private def runCallReplyFootprintChecks : IO Unit := do
  IO.println "--- §3.30 WS-RR RR8.12 Cut C3a: the `.call` and `.reply` footprints ---"
  let slot0 := SeLe4n.Slot.ofNat 0
  let mi0 : MessageInfo := { length := 0, extraCaps := 0, label := 0 }
  -- (a) a Call to a waiting passive server homed on another core: the donation
  --     migrates the client's replenishment 0 -> 1, and the segment names the pair.
  match okPair (endpointReceiveDualOnCore donEp donServer (some donReply) c1 stFpPassiveBase) with
  | none => assertBool "Cut C3a setup (a): the server's recv succeeds" false
  | some (stRecv, _) =>
    assertBool "(a) setup: the server waits on the endpoint, passive, homed on core 1"
      (endpointCallReceiver? stRecv donEp == some donServer
        && determineTargetCore stRecv donServer == c1
        && (match stRecv.getTcb? donServer with
            | some t => t.schedContextBinding == SchedContextBinding.unbound | none => false))
    let seg := endpointCallDispatchReplenishCores donEp donClient IpcMessage.empty
      AccessRightSet.empty slot0 c0 stRecv
    let callWriteSet := endpointCallDispatchWriteSet donEp donClient IpcMessage.empty
      AccessRightSet.empty slot0 c0 stRecv
    let fp := schedLockSet_endpointCallOnCore donEp donClient IpcMessage.empty
      AccessRightSet.empty slot0 c0 stRecv
    assertBool "(a) the replenish segment is the donation's pair: [caller's home 0, server's home 1]"
      (decide (seg = [c0, c1]))
    assertBool "(a) the write set opens with the server's home and the caller's own core"
      (decide (callWriteSet.take 2 = [c1, c0]))
    assertBool "(a) the footprint names run-queue write locks on cores 0 and 1 and replenish-queue write locks on 0 and 1, and no other replenish lock"
      (hasRunQueueWrite fp c0 && hasRunQueueWrite fp c1 && hasReplenishWrite fp c0
        && hasReplenishWrite fp c1 && replenishMemberCount fp == 2)
    -- The RR2.4 parametric footprint at the resolved cores, computed beside it.
    let param := endpointCallCrossCoreDispatchSchedLockSet c0 c1 c0 c1
    assertBool "(a) the derived footprint covers the RR2.4 parametric one at the resolved cores, member for member"
      (param.all (fun p => decide (p ∈ fp)))
    let (stCall, resCall) := endpointCallCrossCoreDispatch donEp donClient IpcMessage.empty
      AccessRightSet.empty slot0 c0 stRecv
    match resCall with
    | .error e => assertBool s!"(a) the live `.call` must succeed (got {reprStr e})" false
    | .ok _ =>
      assertBool "(a) PAYOFF: the live `.call` migrated the client's replenishment to the server's home (0 -> 1)"
        (replenishCountFor stCall c1 scClient == 1 && replenishCountFor stCall c0 scClient == 0)
      assertBool "(a) PAYOFF: the affinity invariant holds after the Call"
        (replenishAffinityConsistentB stCall)
  -- (b) a Call from a legacy `.unbound` client: the guard declines, so the segment is
  --     empty -- and the RR2.4 parametric shape is measured WIDER here.
  match okPair (endpointReceiveDualOnCore donEp donServer (some donReply) c1 stFpLegacyBase) with
  | none => assertBool "Cut C3a setup (b): the server's recv succeeds" false
  | some (stRecvL, _) =>
    assertBool "(b) setup: the client holds no context to hand on"
      (endpointCallDonatedSc? stRecvL donClient == none)
    let segL := endpointCallDispatchReplenishCores donEp donClient IpcMessage.empty
      AccessRightSet.empty slot0 c0 stRecvL
    let fpL := schedLockSet_endpointCallOnCore donEp donClient IpcMessage.empty
      AccessRightSet.empty slot0 c0 stRecvL
    assertBool "(b) the guard declines for an unbound caller, so the segment is empty and no replenish lock is declared"
      (decide (segL = []) && replenishMemberCount fpL == 0)
    assertBool "(b) ...while the run segment still names the server's home and the caller's core"
      (hasRunQueueWrite fpL c0 && hasRunQueueWrite fpL c1)
    let paramL := endpointCallCrossCoreDispatchSchedLockSet c0 c1 c0 c1
    assertBool "(b) NEGATIVE: the RR2.4 parametric shape declares two replenish locks on this state, the derived one none"
      (replenishMemberCount paramL == 2 && replenishMemberCount fpL == 0)
    let (stCallL, resL) := endpointCallCrossCoreDispatch donEp donClient IpcMessage.empty
      AccessRightSet.empty slot0 c0 stRecvL
    match resL with
    | .error e => assertBool s!"(b) the live legacy `.call` must succeed (got {reprStr e})" false
    | .ok _ =>
      assertBool "(b) PAYOFF: the live `.call` moves no replenishment on any core"
        (allCores.all (fun c =>
          replenishCountFor stCallL c fpClient2Sc == replenishCountFor stRecvL c fpClient2Sc
            && replenishCountFor stCallL c scClient == replenishCountFor stRecvL c scClient))
  -- (c) a Call with no receiver waiting: the block path.
  let segC := endpointCallDispatchReplenishCores donEp donClient IpcMessage.empty
    AccessRightSet.empty slot0 c0 stFpPassiveBase
  let fpC := schedLockSet_endpointCallOnCore donEp donClient IpcMessage.empty
    AccessRightSet.empty slot0 c0 stFpPassiveBase
  assertBool "(c) with no receiver the segment is empty and the run segment is the caller's own core alone"
    (endpointCallReceiver? stFpPassiveBase donEp == none && decide (segC = [])
      && hasRunQueueWrite fpC c0 && !hasRunQueueWrite fpC c1 && replenishMemberCount fpC == 0)
  -- (d) the `.reply` on the steady state: the server answers the first client from
  --     core 1, and the pop returns the loaned context 1 -> 0.
  match fpSteadyState stFpPassiveBase with
  | none => assertBool "Cut C3a setup (d): recv, call, dispatch and second call succeed" false
  | some stQ =>
    assertBool "(d) setup: the server executes on core 1 holding the client's context, and the client carries no fault"
      (determineExecutingCore stQ donServer == c1
        && (match stQ.getTcb? donServer with
            | some t => t.schedContextBinding == .donated scClient donClient | none => false)
        && !threadHasPendingFault stQ donClient)
    let segD := endpointReplyDispatchReplenishCores donServer donClient IpcMessage.empty c1 stQ
    let fpDisp := schedLockSet_endpointReplyOnCore donServer donClient IpcMessage.empty c1 stQ
    let fpD := schedLockSet_replyTransferOnCore donServer donClient mi0 #[] IpcMessage.empty c1 stQ
    assertBool "(d) the replenish segment is the return's pair: [holder's home 1, client's home 0]"
      (decide (segD = [c1, c0]))
    assertBool "(d) the arm's footprint IS the dispatch's on an unfaulted caller"
      (decide (fpD = fpDisp))
    assertBool "(d) the footprint names replenish-queue write locks on cores 0 and 1, and run-queue write locks on the client's home and the server's placement"
      (hasReplenishWrite fpD c0 && hasReplenishWrite fpD c1 && replenishMemberCount fpD == 2
        && hasRunQueueWrite fpD c0 && hasRunQueueWrite fpD c1)
    match replyTransferOnCore donServer donClient mi0 #[] IpcMessage.empty c1 stQ with
    | .error e => assertBool s!"(d) the live `.reply` must succeed (got {reprStr e})" false
    | .ok (_, stOut) =>
      assertBool "(d) PAYOFF: the live `.reply` migrated the context back to the client's home (1 -> 0)"
        (replenishCountFor stOut c0 scClient == 1 && replenishCountFor stOut c1 scClient == 0)
      assertBool "(d) PAYOFF: the affinity invariant holds after the reply"
        (replenishAffinityConsistentB stOut)
      assertBool "(d) ...and the server the pop unbound is parked: `.unbound`, on no core"
        (match stOut.getTcb? donServer with
         | some s => s.schedContextBinding == SchedContextBinding.unbound
             && !runnableOnSomeCore stOut donServer && !runningOnSomeCore stOut donServer
         | none => false)
  -- (e) the `.reply` on the legacy state: the answered frame heads no context.
  match fpSteadyState stFpLegacyBase with
  | none => assertBool "Cut C3a setup (e): recv, call, dispatch and second call succeed" false
  | some stL =>
    let segE := endpointReplyDispatchReplenishCores donServer donClient IpcMessage.empty c1 stL
    let fpE := schedLockSet_replyTransferOnCore donServer donClient mi0 #[] IpcMessage.empty c1 stL
    assertBool "(e) the server holds no loan, so the segment is empty and no replenish lock is declared"
      (decide (segE = []) && replenishMemberCount fpE == 0)
    assertBool "(e) ...while the run segment names the answered client's home"
      (hasRunQueueWrite fpE c0)
    match replyTransferOnCore donServer donClient mi0 #[] IpcMessage.empty c1 stL with
    | .error e => assertBool s!"(e) the live legacy `.reply` must succeed (got {reprStr e})" false
    | .ok (_, stOutE) =>
      assertBool "(e) PAYOFF: the live `.reply` moves no replenishment on any core"
        (allCores.all (fun c =>
          replenishCountFor stOutE c fpClient2Sc == replenishCountFor stL c fpClient2Sc))

-- ============================================================================
-- §3.31 the retype's TCB cleanup ends the thread's reservation the way the
--        suspend's G3 does (register row 62, `v0.35.164`)
-- ============================================================================

/-! `lifecyclePreRetypeCleanup`'s TCB arm — the destroy path every `.lifecycleRetype`
runs — used to run the bare `cleanupDonatedSchedContext` on a `.donated` holder
(a return that migrates no replenishment: register row 57's class, on the destroy
path) and, on a `.bound` thread, to remove only the `scThreadIndex` entry, leaving
the SchedContext bound to a destroyed thread with its replenishment queued on that
thread's home core.  After a successful retype `replenishQueueAffinityConsistent_smp`
was false in the first case and both it and `schedContextBindingConsistent` in the
second — and no theorem claimed either across the retype, which is how both were
silent rather than wrong.  Since `v0.35.164` the arm is `cancelDonationArmOnCore`,
the suspend pipeline's G3 match named: seL4's `finaliseCap` → `unbindFromSc`.

Both halves compute the RETIRED reading beside the live retype on the same state
(`retiredRetypeTcbCleanup`: the bare pop, the index-only removal, then the same
sweep and the same store), so every assertion is known to discriminate; the
CONTROL is an `.unbound` target, where the arm is the identity and the two readings
agree.  The live half drives `lifecycleRetypeDirectWithCleanup` — the wrapper the
`.lifecycleRetype` arm reaches — with a `.retype` capability on the target, so the
post-states are the kernel's own. -/

/-- The decidable reading of `schedContextBindingConsistent`, both directions,
over the object index: every `.bound scId` TCB has a SchedContext naming it back,
and every SchedContext's `boundThread` resolves to a TCB bound to or holding it. -/
private def schedContextBindingConsistentB (st : SystemState) : Bool :=
  st.objectIndex.all fun oid =>
    match st.getObject? oid with
    | some (.tcb t) =>
        match t.schedContextBinding with
        | .bound scId =>
            match st.getSchedContext? scId with
            | some sc => sc.boundThread == some t.tid
            | none => false
        | _ => true
    | some (.schedContext sc) =>
        match sc.boundThread with
        | some tid =>
            match st.getTcb? tid with
            | some t =>
                match t.schedContextBinding with
                | .bound scId' => scId' == SchedContextId.ofObjId oid
                | .donated scId' _ => scId' == SchedContextId.ofObjId oid
                | .unbound => false
            | none => false
        | none => true
    | _ => true

/-- `st` with the lifecycle object-type metadata the retype guard reads
(`lifecycleRetypeDirect` refuses a target whose recorded type disagrees with the
store), which the fixture builder does not record. -/
private def withRetypeTypes (st : SystemState)
    (typed : List (SeLe4n.ObjId × KernelObjectType)) : SystemState :=
  { st with lifecycle := { objectTypes := RobinHood.RHTable.ofList typed } }

/-- The object types of the donation fixture's five objects. -/
private def donFixtureTypes : List (SeLe4n.ObjId × KernelObjectType) :=
  [(donServer.toObjId, .tcb), (donClient.toObjId, .tcb), (scClient.toObjId, .schedContext),
   (donEp, .endpoint), (donReply.toObjId, .reply)]

/-- The authority a `.lifecycleRetype` presents: a capability on the target with
the `.retype` right (`lifecycleRetypeAuthority`). -/
private def retypeCapOn (target : SeLe4n.ObjId) : Capability :=
  { target := .object target, rights := AccessRightSet.ofList [.retype], badge := none }

/-- The replacement object: an empty endpoint, well-formed in any store. -/
private def retypeReplacement : KernelObject := .endpoint { sendQ := {}, receiveQ := {} }

/-- The RETIRED reading of the pipeline's TCB arm, followed by the same sweep and
the same store the live pipeline performs: the bare donated-context return, the
index-only removal for a `.bound` thread, the reference sweep, the replacement
stored.  Spelled here and nowhere else, so the assertions can show the live
pipeline changed something. -/
private def retiredRetypeTcbCleanup (st : SystemState) (tcb : TCB) : Option SystemState :=
  match cleanupDonatedSchedContext st tcb.tid with
  | .error _ => none
  | .ok st1 =>
      let st2 : SystemState := match tcb.schedContextBinding with
        | .bound scId =>
            { st1 with scThreadIndex := scThreadIndexRemove st1.scThreadIndex scId tcb.tid }
        | _ => st1
      some ((cleanupTcbReferences st2 tcb.tid).withObjectStored tcb.tid.toObjId retypeReplacement)

/-- The LIVE retype of a TCB through the wrapper the `.lifecycleRetype` arm reaches. -/
private def liveRetypeTcb (st : SystemState) (tid : SeLe4n.ThreadId) : Option SystemState :=
  (okExcept (lifecycleRetypeDirectWithCleanup (retypeCapOn tid.toObjId) tid.toObjId
    retypeReplacement st)).map Prod.snd

private def boundThreadOf (st : SystemState) (scId : SeLe4n.SchedContextId) :
    Option SeLe4n.ThreadId :=
  match st.getSchedContext? scId with
  | some sc => sc.boundThread
  | none => none

private def runRetypeReservationChecks : IO Unit := do
  IO.println "--- §3.31 register row 62: the retype's TCB cleanup ends the thread's reservation ---"
  -- (a) DONATED: the server holds the client's context on loan, homed on core 1
  --     with the replenishment there (§3.28's three-operation prefix).
  match preReturnHandoffState stPreReturnBase with
  | none => assertBool "row 62 setup: call, rendezvous and hand-off succeed" false
  | some stDon0 =>
    let stDon := withRetypeTypes stDon0 donFixtureTypes
    match stDon.getTcb? donServer with
    | none => assertBool "row 62 setup: the server resolves" false
    | some serverTcb =>
      assertBool "(a) setup: the server holds the client's context on loan"
        (serverTcb.schedContextBinding == .donated scClient donClient)
      assertBool "(a) setup: the server is current nowhere and holds no reply object"
        (!threadCurrentOnSomeCore stDon donServer && serverTcb.replyObject.isNone)
      assertBool "(a) setup: the replenishment sits on the server's home (core 1)"
        (replenishCountFor stDon c1 scClient == 1 && replenishCountFor stDon c0 scClient == 0)
      -- NEGATIVE: the retired arm returns the context and moves nothing.
      match retiredRetypeTcbCleanup stDon serverTcb with
      | none => assertBool "(a) NEGATIVE setup: the retired cleanup succeeds" false
      | some stOld =>
        assertBool "(a) NEGATIVE: the retired retype binds the context back to the client..."
          (boundThreadOf stOld scClient == some donClient)
        assertBool "(a) NEGATIVE: ...whose home is core 0, and leaves the replenishment on core 1"
          (decide (determineTargetCore stOld donClient = c0)
            && replenishCountFor stOld c1 scClient == 1 && replenishCountFor stOld c0 scClient == 0)
        assertBool "(a) NEGATIVE (the defect): the retired retype FALSIFIES the affinity invariant"
          (!replenishAffinityConsistentB stOld)
      -- PAYOFF: the live retype migrates with the return.
      match liveRetypeTcb stDon donServer with
      | none => assertBool "(a) the live retype of the donated holder succeeds" false
      | some stNew =>
        assertBool "(a) PAYOFF: the destroyed slot holds the replacement"
          (match stNew.getObject? donServer.toObjId with
           | some (.endpoint _) => true | _ => false)
        assertBool "(a) PAYOFF: the context is bound back to the client"
          (boundThreadOf stNew scClient == some donClient
            && (match stNew.getTcb? donClient with
                | some t => t.schedContextBinding == .bound scClient | none => false))
        assertBool "(a) PAYOFF: the retype migrated the replenishment to the client's home (core 0)"
          (replenishCountFor stNew c0 scClient == 1 && replenishCountFor stNew c1 scClient == 0)
        assertBool "(a) PAYOFF: the affinity invariant holds after the retype"
          (replenishAffinityConsistentB stNew)
        assertBool "(a) PAYOFF: the binding invariant holds after the retype"
          (schedContextBindingConsistentB stNew)
        -- The pipeline's first step IS the suspend's G3 arm: the live post-state's
        -- replenish queues are the arm-then-sweep reading's, core for core.
        match okExcept (cancelDonationArmOnCore stDon donServer serverTcb) with
        | none => assertBool "(a) the reservation arm succeeds on the holder" false
        | some stArm =>
          let stArmSwept := cleanupTcbReferences stArm donServer
          assertBool "(a) the live retype's replenish queues are the arm's, then the sweep's, on every core"
            (allCores.all (fun c =>
              replenishEntriesOn stNew c == replenishEntriesOn stArmSwept c))
  -- (b) BOUND: the client owns its context, pinned to core 1 with its replenishment
  --     there (`stPreReturnSameCore`), and is retyped.
  let stBound := withRetypeTypes stPreReturnSameCore donFixtureTypes
  match stBound.getTcb? donClient with
  | none => assertBool "(b) setup: the client resolves" false
  | some clientTcb =>
    assertBool "(b) setup: the client owns its context, homed on core 1, replenishment on core 1"
      (clientTcb.schedContextBinding == .bound scClient
        && decide (determineTargetCore stBound donClient = c1)
        && replenishCountFor stBound c1 scClient == 1
        && !threadCurrentOnSomeCore stBound donClient && clientTcb.replyObject.isNone)
    assertBool "(b) setup: both invariants hold before the retype"
      (schedContextBindingConsistentB stBound && replenishAffinityConsistentB stBound)
    -- NEGATIVE: the index-only removal leaves the context bound to a destroyed thread.
    match retiredRetypeTcbCleanup stBound clientTcb with
    | none => assertBool "(b) NEGATIVE setup: the retired cleanup succeeds" false
    | some stOld =>
      assertBool "(b) NEGATIVE: the retired retype leaves the context bound to the destroyed thread..."
        (boundThreadOf stOld scClient == some donClient
          && (match stOld.getObject? donClient.toObjId with
              | some (.endpoint _) => true | _ => false))
      assertBool "(b) NEGATIVE: ...with its replenishment still queued on core 1"
        (replenishCountFor stOld c1 scClient == 1)
      assertBool "(b) NEGATIVE (the defect): the retired retype FALSIFIES the binding invariant"
        (!schedContextBindingConsistentB stOld)
      assertBool "(b) NEGATIVE (the defect): ...and the affinity invariant, a destroyed thread homing on the boot core"
        (!replenishAffinityConsistentB stOld)
    -- PAYOFF: the live retype unbinds — seL4's `unbindFromSc` in `finaliseCap`.
    match liveRetypeTcb stBound donClient with
    | none => assertBool "(b) the live retype of the bound thread succeeds" false
    | some stNew =>
      assertBool "(b) PAYOFF: the context is unbound and inactive after the retype"
        (match stNew.getSchedContext? scClient with
         | some sc => sc.boundThread.isNone && !sc.isActive && sc.donationOrigin.isNone
         | none => false)
      assertBool "(b) PAYOFF: the replenishment was purged from the destroyed thread's home"
        (allCores.all (fun c => replenishCountFor stNew c scClient == 0))
      assertBool "(b) PAYOFF: the binding invariant holds after the retype"
        (schedContextBindingConsistentB stNew)
      assertBool "(b) PAYOFF: the affinity invariant holds after the retype"
        (replenishAffinityConsistentB stNew)
  -- (c) CONTROL: an `.unbound` target — the arm is the identity, so the live retype
  --     and the retired reading agree on every replenish queue and both invariants hold.
  let stCtl := withRetypeTypes stDonBase donFixtureTypes
  match stCtl.getTcb? donServer with
  | none => assertBool "(c) setup: the server resolves" false
  | some serverTcb =>
    assertBool "(c) setup: the server holds no reservation"
      (serverTcb.schedContextBinding == SchedContextBinding.unbound)
    match retiredRetypeTcbCleanup stCtl serverTcb, liveRetypeTcb stCtl donServer with
    | some stOld, some stNew =>
      assertBool "(c) CONTROL: on an unbound target the two readings agree on every replenish queue"
        (allCores.all (fun c => replenishEntriesOn stNew c == replenishEntriesOn stOld c))
      assertBool "(c) CONTROL: ...and both invariants hold after the retype"
        (schedContextBindingConsistentB stNew && replenishAffinityConsistentB stNew)
    | _, _ => assertBool "(c) CONTROL: both retypes of an unbound target succeed" false

-- ============================================================================
-- §3.32 the retype's SchedContext arm releases the binding the context holds
--        (register row 63, `v0.35.165`)
-- ============================================================================

/-! `lifecyclePreRetypeCleanup`'s `.schedContext` arm refused a context that heads
a reply stack and nothing else, so a context **bound** to a thread passed: the
retype left that thread `.bound scId` naming an object the slot no longer carries,
its `scThreadIndex` entry in place and `scId`'s replenish entries queued on its
home core under an id the slot's next occupant inherits.  seL4's `finaliseCap`
runs `schedContext_unbindAllTCBs` on a scheduling-context capability; since
`v0.35.165` `releaseSchedContextBinding` is that, per core.

The RETIRED reading is computed beside the live retype on the same state — the
stack-head guard alone, then the same scrub and the same store — so every
assertion is known to discriminate.  The CONTROL is a context bound to nothing,
where the release is the identity and the two readings agree. -/

/-- The LIVE retype of any object through the wrapper the `.lifecycleRetype` arm
reaches. -/
private def liveRetypeObj (st : SystemState) (target : SeLe4n.ObjId) : Option SystemState :=
  (okExcept (lifecycleRetypeDirectWithCleanup (retypeCapOn target) target
    retypeReplacement st)).map Prod.snd

/-- The RETIRED reading of the pipeline's SchedContext arm: the stack-head guard
and nothing else — the cleanup handed the state back unchanged — then the same
scrub and the same store the live pipeline performs.  Spelled here and nowhere
else. -/
private def retiredRetypeSchedContextCleanup (st : SystemState) (target : SeLe4n.ObjId) :
    Option SystemState :=
  match st.getObject? target with
  | none => none
  | some obj =>
      some ((scrubObjectMemory st target obj.objectType).withObjectStored target
        retypeReplacement)

/-- The fixture's client context with its binding cleared — the CONTROL's state,
where the release is the identity. -/
private def withUnboundSchedContext (st : SystemState) : Option SystemState :=
  match st.getSchedContext? scClient with
  | none => none
  | some sc =>
      some (st.withObjectStored scClient.toObjId (.schedContext { sc with boundThread := none }))

private def runRetypeSchedContextChecks : IO Unit := do
  IO.println "--- §3.32 register row 63: the retype's SchedContext arm releases the binding ---"
  let stSc := withRetypeTypes stPreReturnSameCore donFixtureTypes
  match stSc.getSchedContext? scClient, stSc.getTcb? donClient with
  | some sc, some clientTcb =>
    assertBool "(a) setup: the context is bound to the client, which is bound to it"
      (sc.boundThread == some donClient && clientTcb.schedContextBinding == .bound scClient)
    assertBool "(a) setup: the context heads no reply stack, so the arm's guard admits it"
      sc.scReply.isNone
    assertBool "(a) setup: its replenishment sits on the client's home (core 1)"
      (decide (determineTargetCore stSc donClient = c1)
        && replenishCountFor stSc c1 scClient == 1)
    assertBool "(a) setup: both invariants hold before the retype"
      (schedContextBindingConsistentB stSc && replenishAffinityConsistentB stSc)
    -- NEGATIVE: the retired arm stores the replacement over a context that is
    -- still bound, and releases nothing.
    match retiredRetypeSchedContextCleanup stSc scClient.toObjId with
    | none => assertBool "(b) NEGATIVE setup: the retired cleanup succeeds" false
    | some stOld =>
      assertBool "(b) NEGATIVE: the retired retype leaves the client bound to the destroyed context..."
        ((match stOld.getTcb? donClient with
          | some t => t.schedContextBinding == .bound scClient | none => false)
         && (stOld.getSchedContext? scClient).isNone)
      assertBool "(b) NEGATIVE (the defect): ...so the binding invariant is FALSIFIED"
        (!schedContextBindingConsistentB stOld)
      assertBool "(b) NEGATIVE: ...and the replenishment stays queued under the destroyed id"
        (replenishCountFor stOld c1 scClient == 1)
    -- PAYOFF: the live retype releases the binding — seL4's `unbindFromSc`.
    match liveRetypeObj stSc scClient.toObjId with
    | none => assertBool "(c) the live retype of the bound context succeeds" false
    | some stNew =>
      assertBool "(c) PAYOFF: the destroyed slot holds the replacement"
        (match stNew.getObject? scClient.toObjId with
         | some (.endpoint _) => true | _ => false)
      assertBool "(c) PAYOFF: the client is unbound after the retype"
        (match stNew.getTcb? donClient with
         | some t => t.schedContextBinding == SchedContextBinding.unbound | none => false)
      assertBool "(c) PAYOFF: the replenishment was purged from every core"
        (allCores.all (fun c => replenishCountFor stNew c scClient == 0))
      assertBool "(c) PAYOFF: the binding invariant holds after the retype"
        (schedContextBindingConsistentB stNew)
      assertBool "(c) PAYOFF: the affinity invariant holds after the retype"
        (replenishAffinityConsistentB stNew)
    -- CONTROL: a context bound to nothing — the release is the identity, so the
    -- two readings agree on every replenish queue and on the client's binding.
    match withUnboundSchedContext stSc with
    | none => assertBool "(d) CONTROL setup: the context resolves" false
    | some stCtl =>
      match retiredRetypeSchedContextCleanup stCtl scClient.toObjId,
            liveRetypeObj stCtl scClient.toObjId with
      | some stOldCtl, some stNewCtl =>
        assertBool "(d) CONTROL: on a context bound to nothing the two readings agree on every replenish queue"
          (allCores.all (fun c => replenishEntriesOn stNewCtl c == replenishEntriesOn stOldCtl c))
        assertBool "(d) CONTROL: ...and neither touches the client's own binding"
          ((match stNewCtl.getTcb? donClient, stOldCtl.getTcb? donClient with
            | some a, some b => a.schedContextBinding == b.schedContextBinding
            | _, _ => false))
      | _, _ => assertBool "(d) CONTROL: both retypes of an unbound context succeed" false
  | _, _ => assertBool "(a) setup: the context and the client resolve" false

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
  runDonationChecks
  runDonationMigrationChecks
  runCapTransferChecks
  runFlowCheckedChecks
  runLiveApiChecks
  runCancellationCompositionChecks
  runSuspendArmChecks
  runHandlerContentionChecks
  runDonationChainStructureChecks
  runDonationReturnPopChecks
  runDonationPushChecks
  runMiddleCallerRemovalChecks
  runReplyFrameRemovalChecks
  runReplyRecvLoopCompletionChecks
  runMiddleRemovalDepthThreeChecks
  runMiddleRemovalDepthFourChecks
  runDonationOriginIdReuseChecks
  runDonationOriginRedirectChecks
  runReceivePriorityHandoffChecks
  runReceiveReplenishSegmentChecks
  runReplyRecvHolderDescheduleChecks
  runPreReceiveReturnMigrationChecks
  runReplyRecvFootprintChecks
  runCallReplyFootprintChecks
  runRetypeReservationChecks
  runRetypeSchedContextChecks
  runTraceFixtureCheck
  IO.println "===================================="
  IO.println "All SM6.F cross-core IPC checks PASS."

end SeLe4n.Testing.SmpIpc

def main : IO Unit :=
  SeLe4n.Testing.SmpIpc.runSmpIpcChecks
