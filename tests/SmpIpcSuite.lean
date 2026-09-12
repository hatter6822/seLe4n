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
it, which is the same elision the pre-WS-RM fused step allowed. -/
private def runReplyRecvDonationSteps (tid recordedServer nextThread : SeLe4n.ThreadId)
    (serverCore : CoreId) (st : SystemState) : Except KernelError SystemState :=
  match replyRecvPopDonation recordedServer st with
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
    match runReplyRecvDonationSteps donServer donServer donServer c1 stCall with
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
    match runReplyRecvDonationSteps donDelegate donServer donClient c1 stCallD with
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
    match runReplyRecvDonationSteps donDelegate donServer donCaller2 c1 stCallQ with
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
  -- the *detach* at the cancellation (`detachReplyFrameAbove`), so a linked
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
    |>.withObject pushOuter.toObjId
        (.tcb { mkTcb 93 50 none with
                  ipcState := .blockedOnReply (SeLe4n.ObjId.ofNat 97) (some pushDonor) })
    |>.build)

/-- The donor's own reply object, fresh: linked to the donor, on no stack —
neither link set, which is what `donationPushFrame?` requires of a frame. -/
private def pushFreshHead : Reply :=
  { replyId := pushDonorReply, caller := some pushDonor }

/-- The well-formed depth-2 pre-state. -/
private def pushStore : SystemState :=
  pushStoreShaped (.donated pushSc pushOuter) (some pushDonorReply) pushFreshHead

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

/-- The whole of what a detach can write: both frames' links and the context's
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
  assertBool "OD5.2: the reclaim fires for the caller the holder names as owner"
    (Lifecycle.Suspend.cancelledCallerDonation? pushStore pushOuter
       { mkTcb 93 50 none with
           ipcState := .blockedOnReply (SeLe4n.ObjId.ofNat 97) (some pushDonor) }
       == some (pushSc, pushDonor))
  assertBool "OD5.2: the reclaim declines below the cut (the holder donated onward)"
    (Lifecycle.Suspend.cancelledCallerDonation?
       (pushStoreShaped .unbound (some pushDonorReply) pushFreshHead) pushOuter
       { mkTcb 93 50 none with
           ipcState := .blockedOnReply (SeLe4n.ObjId.ofNat 97) (some pushDonor) }
       == none)
  assertBool "OD5.2: the policy this kernel implements is `severAtCut`"
    (cancelledMiddleCallerPolicy == CancelledMiddleCallerPolicy.severAtCut)
  -- OD4.7: the `.call` footprint already declares every object the push writes.
  assertBool "OD4.7: the resolved `.call` footprint declares the donated context"
    (((lockSet_endpointCallOnCore pushStore (SeLe4n.ObjId.ofNat 97) pushDonor
        (SeLe4n.ObjId.ofNat 0)).pairs.any
        (fun p => p.1 == schedContextLock pushSc && p.2 == AccessMode.write)))

/-- **`v0.35.4`: the middle-caller detach, and the wedge it removes.**

Its own runner rather than a tail of the push checks: the C code generator
nests a `do`-block's statements, and a helper past roughly 150 Lean lines
compiles to an `if`-tree that can exceed clang's bracket limit.  The boundary
resets the nesting, and the concern is distinct anyway -- the push builds the
stack these checks then cut. -/
private def runMiddleCallerDetachChecks : IO Unit := do
  IO.println "--- §3.19 the middle-caller detach, and the wedge it removes (`v0.35.4`) ---"
  -- The state a depth-2 push leaves is exactly the one the pinning defect
  -- needed: two frames, the outer caller's below the donor's.  Cancelling the
  -- *outer* caller consumes a frame that is not the head, and before this cut
  -- the head went on linking down to it.  Both directions are exercised below,
  -- because a witness that ran only the repaired path would pass before the fix
  -- and after it.
  match donateSchedContext pushStore pushDonor pushServer pushSc with
  | .error e =>
    assertBool s!"the detach witness needs a depth-2 push (got {reprStr e})" false
  | .ok pushed =>
    -- The outer caller, carrying the reply object it is blocked on.  Built here
    -- rather than in `pushStoreShaped`, whose `pushOuter` is shared with every
    -- assertion above and whose `replyObject` none of them reads.
    let outerTcb : TCB :=
      { mkTcb 93 50 none with
          ipcState := .blockedOnReply (SeLe4n.ObjId.ofNat 97) (some pushDonor),
          replyObject := some pushOuterReply }
    -- Step one: the detach's WRITING arm.  Every `detachReplyFrameAbove` result
    -- proved elsewhere is discharged on a state whose frame has nothing above
    -- it, where the step is the identity; this is the arm that stores.
    let detached := detachFrameAboveThreadReply pushed outerTcb
    assertBool "the detach clears the `prev` of the frame ABOVE the cancelled one"
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
    -- detach omitted.  Every object is still there and every field the consume
    -- writes is identical; what changes is the relation between the head and the
    -- frame below it.  That state is what wedged the chain — the pop refuses and
    -- the context can never leave the server.
    let wedged := Lifecycle.Suspend.consumeReplyLink pushed pushOuter outerTcb
    assertBool "NEGATIVE: without the detach the head still links down to the consumed frame"
      (pushLinksOf wedged pushDonorReply == some (some pushOuterReply, some (.head pushSc)))
    assertBool "NEGATIVE: ...and the outer-caller resolution refuses it"
      (match replyStackOuterCaller? wedged pushSc with
       | .error e => e == KernelError.invalidArgument
       | .ok _ => false)
    assertBool "NEGATIVE: ...so the pop wedges, writing nothing"
      (match returnDonatedSchedContextResolved wedged pushServer pushSc pushDonor with
       | .error e => e == KernelError.invalidArgument
       | .ok _ => false)
    -- The detach is FAIL-CLOSED and the wrapper is TOTAL: a frame above that
    -- does not link back is refused by the primitive, and the cancellation still
    -- runs rather than failing — which is what keeps a severed stack's lower
    -- frames cancellable.  Both halves, since the primitive's refusal and the
    -- wrapper's fold are different facts.
    -- The severed state is itself the shape that must be refused: the frame
    -- below still links UP to the head, and the head no longer links down to it.
    -- That is the state a second cancellation — of the caller below the cut —
    -- meets, so the refusal and the wrapper's fold together are what keep a
    -- severed stack's lower frames cancellable rather than wedged in turn.
    assertBool "the detach refuses a frame above that does not link back"
      (match detachReplyFrameAbove detached pushOuterReply with
       | .error e => e == KernelError.invalidArgument
       | .ok _ => false)
    assertBool "...and the cancellation wrapper folds that refusal to the identity"
      (pushStackShape (detachFrameAboveThreadReply detached outerTcb)
         == pushStackShape detached)
    assertBool "...so the caller below a cut can still be cancelled, and leaves cleanly"
      (match (Lifecycle.Suspend.consumeReplyLink
                (detachFrameAboveThreadReply detached outerTcb)
                pushOuter outerTcb).getReply? pushOuterReply with
       | some r => r.isFree
       | none => false)
    -- ...and a frame above that names no Reply at all is a different refusal,
    -- so the two fail-closed arms are told apart rather than merged.
    assertBool "the detach refuses a frame above that resolves to no Reply"
      (match detachReplyFrameAbove
          (pushStoreShaped (.donated pushSc pushOuter) (some pushDonorReply)
            { pushFreshHead with next := some (.frame ⟨98⟩) })
          pushDonorReply with
       | .error e => e == KernelError.objectNotFound
       | .ok _ => false)
    assertBool "the detach is the identity for a frame with nothing above it"
      (pushStackShape (detachFrameAboveThreadReply pushed
         { outerTcb with replyObject := some pushDonorReply }) == pushStackShape pushed)
    assertBool "...and for a thread holding no reply object at all"
      (pushStackShape (detachFrameAboveThreadReply pushed
         { outerTcb with replyObject := none }) == pushStackShape pushed)

-- ============================================================================
-- WS-RM — seL4's `reply_remove` on the reply path (`v0.35.6`)
-- ============================================================================

/-- **WS-RM**: the depth-2 chain's outer caller, carrying the reply object it is
blocked on.

`§3.19`'s detach witness builds the same TCB for the *cancellation* path; the
reply path answers the very same frame, which is the point — one removal step,
two callers of it. -/
private def replyRemovalOuterTcb : TCB :=
  { mkTcb 93 50 none with
      ipcState := .blockedOnReply (SeLe4n.ObjId.ofNat 97) (some pushDonor),
      replyObject := some pushOuterReply }

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

private def runReplyFrameRemovalChecks : IO Unit := do
  IO.println "--- §3.20 WS-RM: the reply path takes the answered frame off its stack ---"
  match donateSchedContext pushStore pushDonor pushServer pushSc with
  | .error e =>
    assertBool s!"the removal witness needs a depth-2 push (got {reprStr e})" false
  | .ok pushed =>
    -- The stack a depth-2 `Call` chain leaves: `pushDonorReply` heads the
    -- context and links down to `pushOuterReply`, which links back up.
    let stChain : SystemState :=
      { pushed with
          objects := (pushed.objects.insert pushOuter.toObjId (.tcb replyRemovalOuterTcb)).insert
            replyRemovalDelegate.toObjId (.tcb (mkTcb 99 45 (some c1))) }
    assertBool "pre: the donor's frame heads the context and links down to the outer one"
      (pushLinksOf stChain pushDonorReply == some (some pushOuterReply, some (.head pushSc)))
    assertBool "pre: the outer frame links up to the head, heading nothing"
      (pushLinksOf stChain pushOuterReply == some (none, some (.frame pushDonorReply)))
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
    assertBool "PAYOFF: the in-order reply that follows succeeds — the wedge is gone"
      (match (endpointReplyOnCore pushServer pushDonor IpcMessage.empty bootCoreId
                { postOoO with
                    objects := postOoO.objects.insert pushDonor.toObjId
                      (.tcb { mkTcb 91 40 none with
                                schedContextBinding := .unbound,
                                ipcState := .blockedOnReply (SeLe4n.ObjId.ofNat 97)
                                  (some pushServer),
                                replyObject := some pushDonorReply }) }).2 with
       | .ok _ => true
       | .error _ => false)
    -- ...and the pop the reply chain runs after it resolves, rather than
    -- refusing a stale link.
    assertBool "PAYOFF: the pop resolves the remaining stack to its bottom"
      (match replyStackOuterCaller? postOoO pushSc with
       | .ok none => true | _ => false)
    assertBool "PAYOFF: ...so the donation return succeeds and settles the context"
      (match returnDonatedSchedContextResolved postOoO pushServer pushSc pushDonor with
       | .ok st' => pushBindingOf st' pushDonor == some (.bound pushSc)
       | .error _ => false)
    -- NEGATIVE, and the reason this witness exists: the SAME reply with the
    -- detach omitted.  Every object is present and every field the consume
    -- writes is identical; what changes is the head's link down to a frame whose
    -- caller is gone.  A fixture that exercised only the in-order path would
    -- pass before this cut and after it.
    let wedged := SystemState.consumeCallerReply pushOuter pushOuterReply stChain
    assertBool "NEGATIVE: without the detach the head still links down to the answered frame"
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
      match replyRecvPopDonation donServer stAfterReply with
      | .error e => assertBool s!"the donation pop must succeed (got {reprStr e})" false
      | .ok (returned?, stPopped) =>
        assertBool "the pop hands the context back to its original owner"
          (returned? == some scClient)
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
  runMiddleCallerDetachChecks
  runReplyFrameRemovalChecks
  runReplyRecvLoopCompletionChecks
  runReceivePriorityHandoffChecks
  runTraceFixtureCheck
  IO.println "===================================="
  IO.println "All SM6.F cross-core IPC checks PASS."

end SeLe4n.Testing.SmpIpc

def main : IO Unit :=
  SeLe4n.Testing.SmpIpc.runSmpIpcChecks
