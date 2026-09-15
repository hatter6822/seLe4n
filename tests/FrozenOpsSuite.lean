-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n
import SeLe4n.Testing.StateBuilder
import SeLe4n.Kernel.FrozenOps
import SeLe4n.Model.FrozenState
import SeLe4n.Model.Builder

open SeLe4n.Kernel.RobinHood
open SeLe4n.Kernel.Concurrency (bootCoreId)
open SeLe4n.Kernel.RadixTree
open SeLe4n.Kernel.FrozenOps
open SeLe4n.Model

namespace SeLe4n.Testing.FrozenOpsSuite

private def expect (label : String) (cond : Bool) : IO Unit := do
  if cond then
    IO.println s!"frozen-ops check passed [{label}]"
  else
    throw <| IO.userError s!"frozen-ops check failed [{label}]"

/-- Helper: construct a minimal empty FrozenSystemState. -/
private def emptyFrozenState : FrozenSystemState :=
  SeLe4n.Testing.emptyFrozenSystemState

/-- Helper: construct a test TCB. -/
private def mkTcb (tid : Nat) (prio : Nat := 0) (dom : Nat := 0) : TCB :=
  { tid := ⟨tid⟩, priority := ⟨prio⟩, domain := ⟨dom⟩,
    cspaceRoot := ⟨0⟩, vspaceRoot := ⟨0⟩, ipcBuffer := (SeLe4n.VAddr.ofNat 0) }

/-- Helper: construct a FrozenSystemState with given objects. -/
private def mkFrozenState (objs : List (ObjId × FrozenKernelObject))
    : FrozenSystemState :=
  SeLe4n.Testing.frozenStateOf objs

-- ============================================================================
-- Q7-T1: FrozenKernel Monad Tests (FO-001 to FO-003)
-- ============================================================================

/-- FO-001: frozenLookupObject — find existing object -/
private def fo001_lookupExisting : IO Unit := do
  let fst := mkFrozenState [(⟨1⟩, .tcb (mkTcb 1))]
  match frozenLookupObject ⟨1⟩ fst with
  | .ok (obj, _) => expect "lookup found TCB" (obj.objectType == .tcb)
  | .error _ => throw <| IO.userError "lookup should succeed"

/-- FO-002: frozenLookupObject — missing object returns error -/
private def fo002_lookupMissing : IO Unit := do
  let fst := mkFrozenState []
  match frozenLookupObject ⟨99⟩ fst with
  | .ok _ => throw <| IO.userError "should fail"
  | .error e => expect "missing → objectNotFound" (e == .objectNotFound)

/-- FO-003: frozenStoreObject — update existing TCB -/
private def fo003_storeObject : IO Unit := do
  let fst := mkFrozenState [(⟨1⟩, .tcb (mkTcb 1))]
  let tcb2 := mkTcb 1 5  -- changed priority
  match frozenStoreObject ⟨1⟩ (.tcb tcb2) fst with
  | .ok ((), fst') =>
      match fst'.objects.get? ⟨1⟩ with
      | some (.tcb t) => expect "updated priority" (t.priority == ⟨5⟩)
      | _ => throw <| IO.userError "should find updated TCB"
      expect "scheduler preserved" ((fst'.scheduler.current) == (fst.scheduler.current))
      expect "machine preserved" (fst'.machine.timer == fst.machine.timer)
  | .error _ => throw <| IO.userError "store should succeed"

-- ============================================================================
-- TPH-005: Frozen IPC Send/Receive
-- ============================================================================

/-- FO-004 (PR #822 review, Codex): frozenEndpointReply requires a resolved Reply
object.  A `blockedOnReply` caller with NO `replyObject` link is rejected
`.replyCapInvalid` — the frozen mirror of the live `.reply` path, which resolves
`reply.caller` and consumes it.  (The success path with a linked Reply object is
FO-004b.) -/
private def fo004_endpointReply : IO Unit := do
  let callerTcb : TCB := { mkTcb 2 with ipcState := .blockedOnReply ⟨10⟩ (some ⟨3⟩) }
  let fst := mkFrozenState [(⟨2⟩, .tcb callerTcb)]
  let msg : IpcMessage := { registers := #[], caps := #[], badge := Badge.ofNatMasked 0 }
  match frozenEndpointReply ⟨3⟩ ⟨2⟩ (⟨505⟩ : SeLe4n.ReplyId) msg fst with
  | .ok _ => throw <| IO.userError "reply to a caller with no Reply object must be rejected"
  | .error e => expect "no-reply-object frozen reply → replyCapInvalid" (e == .replyCapInvalid)

/-- FO-004b: frozenEndpointReply consumes the linked Reply object (PR #822
review): a successful reply clears the caller's `replyObject` forward link and
the Reply object's `caller` back-link, mirroring the runtime `consumeCallerReply`
single-use semantics. -/
private def fo004b_endpointReplyConsumesLink : IO Unit := do
  let rid : SeLe4n.ReplyId := ⟨505⟩
  let callerTcb : TCB := { mkTcb 2 with
    ipcState := .blockedOnReply ⟨10⟩ (some ⟨3⟩), replyObject := some rid }
  let replyObj : SeLe4n.Kernel.Reply := { replyId := rid, caller := some ⟨2⟩ }
  -- The replier is a live TCB: the reply's provenance is read from the thread
  -- that composed it, so an unresolvable one is refused (SM9.D audit).
  let fst := mkFrozenState
    [(⟨2⟩, .tcb callerTcb), (⟨3⟩, .tcb (mkTcb 3)), (rid.toObjId, .reply replyObj)]
  let msg : IpcMessage := { registers := #[], caps := #[], badge := Badge.ofNatMasked 0 }
  match frozenEndpointReply ⟨3⟩ ⟨2⟩ rid msg fst with
  | .ok ((), fst') =>
      match frozenLookupTcb fst' ⟨2⟩ with
      | some tcb =>
          expect "target unblocked" (tcb.ipcState == .ready)
          expect "forward reply link cleared" (tcb.replyObject == none)
      | none => throw <| IO.userError "target TCB missing"
      match fst'.objects.get? rid.toObjId with
      | some (.reply r) => expect "reply caller back-link consumed" (r.caller == none)
      | _ => throw <| IO.userError "reply object missing/retyped"
  | .error _ => throw <| IO.userError "reply should succeed"

/-- FO-004c (PR #895 review round 13): **a reply to a stack HEAD pops the
donation, so the Reply can be used again.**

`Reply.consumed` deliberately keeps a head's stack links — the live pop that
follows clears them — and this surface had no pop, so the answered Reply failed
`Reply.isFree` for good: never relinkable by the next `Call` rendezvous, never
retypeable.  `freeze` copies Reply objects verbatim, so a state captured
mid-donation-chain reaches the frozen phase carrying exactly this shape.

The witness checks the whole hand-off rather than the link alone, because a pop
that clears the links without moving the reservation would satisfy a link-only
assertion while losing the client's budget. -/
private def fo004c_replyToStackHeadPopsDonation : IO Unit := do
  let rid  : SeLe4n.ReplyId := ⟨505⟩
  let scId : SeLe4n.SchedContextId := ⟨77⟩
  let callerTcb : TCB := { mkTcb 2 with
    ipcState := .blockedOnReply ⟨10⟩ (some ⟨3⟩), replyObject := some rid }
  -- The passive server holds the caller's context by donation, and the context
  -- heads the reply stack at `rid` — the live depth-1 `Call` shape.
  let serverTcb : TCB := { mkTcb 3 with schedContextBinding := .donated scId ⟨2⟩ }
  let sc : SeLe4n.Kernel.SchedContext := { scId := scId, budget := ⟨100⟩, period := ⟨1000⟩, priority := ⟨0⟩, deadline := ⟨0⟩, domain := ⟨0⟩, budgetRemaining := ⟨50⟩, boundThread := some ⟨3⟩, scReply := some rid }
  let replyObj : SeLe4n.Kernel.Reply :=
    { replyId := rid, caller := some ⟨2⟩, prev := none, next := some (.head scId) }
  let fst := mkFrozenState
    [(⟨2⟩, .tcb callerTcb), (⟨3⟩, .tcb serverTcb), (⟨9⟩, .tcb (mkTcb 9)),
     (scId.toObjId, .schedContext sc), (rid.toObjId, .reply replyObj)]
  let msg : IpcMessage := { registers := #[], caps := #[], badge := Badge.ofNatMasked 0 }
  match frozenEndpointReplyWithDonationReturn ⟨3⟩ ⟨2⟩ rid msg fst with
  | .error _ => throw <| IO.userError "reply+donation-return should succeed"
  | .ok ((), fst') =>
      match fst'.getReply? rid with
      | some r => expect "answered head left free for reuse" r.isFree
      | none   => throw <| IO.userError "reply object missing"
      match fst'.getSchedContext? scId with
      | some c =>
          expect "context handed back to its owner" (c.boundThread == some ⟨2⟩)
          expect "context heads no stack now" (c.scReply == none)
      | none => throw <| IO.userError "SchedContext missing"
      match fst'.getTcb? ⟨2⟩ with
      | some t => expect "owner holds its reservation again"
                    (t.schedContextBinding == .bound scId)
      | none => throw <| IO.userError "owner TCB missing"
      match fst'.getTcb? ⟨3⟩ with
      | some t => expect "passive server is unbound again"
                    (t.schedContextBinding == .unbound)
      | none => throw <| IO.userError "server TCB missing"
      -- The point of the whole thing: the next rendezvous can link this Reply.
      match frozenLinkCallerReply fst' ⟨9⟩ rid with
      | .ok _    => expect "a fresh caller can be linked to the freed Reply" true
      | .error _ => throw <| IO.userError "Reply still unusable after the pop"

/-- FO-004e (PR #895 review round 14): **the server is descheduled when its
donation goes back.**

`applyReplyDonation` is the return *and* `removeRunnable replier`: a server that
has just handed its reservation back is `.unbound`, so leaving it on a run queue
lets the scheduler select a thread charged to nobody — the temporal-isolation
defect rounds 9-11 closed on the live `.replyRecv` arm.  Round 13 mirrored the
inner return and not the live caller that pairs it with the deschedule, and so
reproduced that defect here; `frozenApplyReplyDonation` is the mirror of the
function that pairs them, which is why the pairing can no longer be dropped.

The witness queues the server first, because a server that was never runnable
would pass a deschedule assertion without the deschedule ever running. -/
private def fo004e_replyDeschedulesTheServer : IO Unit := do
  let rid  : SeLe4n.ReplyId := ⟨505⟩
  let scId : SeLe4n.SchedContextId := ⟨77⟩
  let callerTcb : TCB := { mkTcb 2 with
    ipcState := .blockedOnReply ⟨10⟩ (some ⟨3⟩), replyObject := some rid }
  let serverTcb : TCB := { mkTcb 3 with schedContextBinding := .donated scId ⟨2⟩ }
  let sc : SeLe4n.Kernel.SchedContext := { scId := scId, budget := ⟨100⟩, period := ⟨1000⟩, priority := ⟨0⟩, deadline := ⟨0⟩, domain := ⟨0⟩, budgetRemaining := ⟨50⟩, boundThread := some ⟨3⟩, scReply := some rid }
  let replyObj : SeLe4n.Kernel.Reply :=
    { replyId := rid, caller := some ⟨2⟩, prev := none, next := some (.head scId) }
  let st0 := mkFrozenState
    [(⟨2⟩, .tcb callerTcb), (⟨3⟩, .tcb serverTcb),
     (scId.toObjId, .schedContext sc), (rid.toObjId, .reply replyObj)]
  let queued (s : FrozenSystemState) (t : SeLe4n.ThreadId) : Bool :=
    s.scheduler.byPriority.indexMap.toList.any (fun kv =>
      ((s.scheduler.byPriority.get? kv.1).getD []).contains t)
  match frozenEnsureRunnable st0 ⟨3⟩ with
  | .error _ => throw <| IO.userError "could not queue the server"
  | .ok st =>
      expect "the server starts runnable" (queued st ⟨3⟩)
      let msg : IpcMessage := { registers := #[], caps := #[], badge := Badge.ofNatMasked 0 }
      match frozenEndpointReplyWithDonationReturn ⟨3⟩ ⟨2⟩ rid msg st with
      | .error _ => throw <| IO.userError "reply+donation-return should succeed"
      | .ok ((), st') =>
          match st'.getTcb? ⟨3⟩ with
          | some t => expect "the server gave its reservation back"
                        (t.schedContextBinding == .unbound)
          | none => throw <| IO.userError "server TCB missing"
          expect "an unbound server is off the run queue" (!queued st' ⟨3⟩)
          -- ...and the caller it answered IS runnable, so the assertion above
          -- is about the deschedule rather than about an empty queue.
          expect "the answered caller is runnable" (queued st' ⟨2⟩)

/-- FO-004f (PR #895 review round 15): **priority inheritance is reverted when
the reply unblocks a waiter.**

A server blocked-on by a high-priority client carries that client's priority in
`TCB.pipBoost`, and `frozenEnsureRunnable` buckets by `frozenEffectivePriority`,
which reads it.  The reply makes the client `.ready`, so it stops being a waiter
— and this surface left the boost untouched, so the server stayed bucketed at a
priority inherited from a client it had already answered.  Both live reply
compositions recompute (`revertPriorityInheritance` /
`propagatePipChainCrossCore`).

The witness keeps a **second** waiter, so the assertion is about recomputing
from whoever is left rather than about clearing: a step that cleared the boost
unconditionally, one that left it at the answered client's priority, and one
that did nothing at all each fail it differently.  The no-donation arm is
deliberate — that is the arm the finding names, and it is also the only one on
which the bucket move is observable, since a donation return deschedules the
server outright (FO-004e). -/
private def fo004f_replyRevertsPriorityInheritance : IO Unit := do
  let rid : SeLe4n.ReplyId := ⟨505⟩
  -- ⟨2⟩ is the client being answered, ⟨4⟩ a second client still waiting.
  let answered : TCB := { mkTcb 2 200 with
    ipcState := .blockedOnReply ⟨10⟩ (some ⟨3⟩), replyObject := some rid }
  let stillWaiting : TCB := { mkTcb 4 150 with
    ipcState := .blockedOnReply ⟨10⟩ (some ⟨3⟩) }
  -- The server's own priority is 10; it has inherited 200 from ⟨2⟩.
  let serverTcb : TCB := { mkTcb 3 10 with pipBoost := some ⟨200⟩ }
  let replyObj : SeLe4n.Kernel.Reply := { replyId := rid, caller := some ⟨2⟩ }
  let st0 := mkFrozenState
    [(⟨2⟩, .tcb answered), (⟨3⟩, .tcb serverTcb), (⟨4⟩, .tcb stillWaiting),
     (rid.toObjId, .reply replyObj)]
  let inBucket (s : FrozenSystemState) (p : Nat) (t : SeLe4n.ThreadId) : Bool :=
    ((s.scheduler.byPriority.get? ⟨p⟩).getD []).contains t
  match frozenEnsureRunnable st0 ⟨3⟩ with
  | .error _ => throw <| IO.userError "could not queue the server"
  | .ok st =>
      expect "the server starts bucketed at the INHERITED priority" (inBucket st 200 ⟨3⟩)
      let msg : IpcMessage := { registers := #[], caps := #[], badge := Badge.ofNatMasked 0 }
      match frozenEndpointReplyWithDonationReturn ⟨3⟩ ⟨2⟩ rid msg st with
      | .error _ => throw <| IO.userError "reply should succeed"
      | .ok ((), st') =>
          match st'.getTcb? ⟨3⟩ with
          | some t =>
              expect "boost recomputed from the REMAINING waiter"
                (t.pipBoost == some ⟨150⟩)
          | none => throw <| IO.userError "server TCB missing"
          expect "and it left the bucket it inherited" (!inBucket st' 200 ⟨3⟩)
          expect "...for the one its new boost names" (inBucket st' 150 ⟨3⟩)
          -- The server holds no donation here, so the deschedule of FO-004e
          -- must NOT have fired: this is a re-bucket, not a removal.
          expect "a server with no donation stays runnable"
            (inBucket st' 150 ⟨3⟩)

/-- FO-004g (PR #895 review round 15): **a caller with no recorded server is not
repliable.**

Both live spellings answer `.replyCapInvalid` for `.blockedOnReply _ none` — the
bare `endpointReply` and `endpointReplyOnCore` — and the live comment records why
the `none => true` branch was retired: every production path records `some
receiver`, so the `none` case is invariant drift, and letting a reply through
there was rated a confused-deputy risk (AK1-B / I-H02).  This mirror bound the
recorded server and never read it.

The control replies to the SAME state with a server recorded, so the refusal is
known to be about the missing server rather than about anything else in the
fixture. -/
private def fo004g_replyNeedsARecordedServer : IO Unit := do
  let rid : SeLe4n.ReplyId := ⟨505⟩
  let replyObj : SeLe4n.Kernel.Reply := { replyId := rid, caller := some ⟨2⟩ }
  let mkState (server? : Option SeLe4n.ThreadId) : FrozenSystemState :=
    mkFrozenState
      [(⟨2⟩, .tcb { mkTcb 2 with
                    ipcState := .blockedOnReply ⟨10⟩ server?, replyObject := some rid }),
       (⟨3⟩, .tcb (mkTcb 3)), (rid.toObjId, .reply replyObj)]
  let msg : IpcMessage := { registers := #[], caps := #[], badge := Badge.ofNatMasked 0 }
  match frozenEndpointReply ⟨3⟩ ⟨2⟩ rid msg (mkState none) with
  | .ok _ => throw <| IO.userError "a reply with no recorded server must be refused"
  | .error e => expect "refused as an invalid reply capability" (e == .replyCapInvalid)
  -- ...and nothing is committed: the composite refuses for the same reason.
  match frozenEndpointReplyWithDonationReturn ⟨3⟩ ⟨2⟩ rid msg (mkState none) with
  | .ok _ => throw <| IO.userError "the composite must refuse it too"
  | .error e => expect "composite refuses identically" (e == .replyCapInvalid)
  -- The control: the same fixture with a server recorded goes through, so the
  -- refusal above is about `replyTarget` and not about the rest of the state.
  match frozenEndpointReply ⟨3⟩ ⟨2⟩ rid msg (mkState (some ⟨3⟩)) with
  | .ok ((), st) =>
      match st.getTcb? ⟨2⟩ with
      | some t => expect "control: a recorded server still replies" (t.ipcState == .ready)
      | none => throw <| IO.userError "target TCB missing"
  | .error _ => throw <| IO.userError "control should succeed"

/-- FO-004d: ...and the reply leg ALONE still agrees with the bare
`endpointReply`, which is what `FO-031` compares.  A Reply on no stack is
consumed outright, so the pop is the identity there and the composite and the
leg answer the same state — the control that keeps FO-004c honest about WHERE
the pop belongs. -/
private def fo004d_replyOffStackNeedsNoPop : IO Unit := do
  let rid : SeLe4n.ReplyId := ⟨505⟩
  let callerTcb : TCB := { mkTcb 2 with
    ipcState := .blockedOnReply ⟨10⟩ (some ⟨3⟩), replyObject := some rid }
  let replyObj : SeLe4n.Kernel.Reply := { replyId := rid, caller := some ⟨2⟩ }
  let fst := mkFrozenState
    [(⟨2⟩, .tcb callerTcb), (⟨3⟩, .tcb (mkTcb 3)), (rid.toObjId, .reply replyObj)]
  let msg : IpcMessage := { registers := #[], caps := #[], badge := Badge.ofNatMasked 0 }
  match frozenEndpointReply ⟨3⟩ ⟨2⟩ rid msg fst,
        frozenEndpointReplyWithDonationReturn ⟨3⟩ ⟨2⟩ rid msg fst with
  | .ok ((), a), .ok ((), b) =>
      match a.getReply? rid, b.getReply? rid with
      | some x, some y =>
          -- Off a stack `consumed` clears the links outright, so the pop has
          -- nothing to do and the two spellings leave the same record.
          expect "same Reply record either way"
            (x.caller == y.caller && x.prev == y.prev && x.next == y.next)
          expect "and it is free" x.isFree
      | _, _ => throw <| IO.userError "reply object missing"
  | _, _ => throw <| IO.userError "both spellings should succeed off a stack"

/-- FO-005 (PR #822 review, frozen mirror of E.2 / 6J-lYm): a DELEGATED replier —
NOT the recorded `replyTarget` server (⟨3⟩), but the reply is authorized by the
linked Reply object whose `caller` names the target — now SUCCEEDS.  Authority is
the Reply object, not the recorded replier (a copied/minted reply cap is
delegatable), exactly like the live `.reply` path. -/
private def fo005_replyDelegatedReplier : IO Unit := do
  let rid : SeLe4n.ReplyId := ⟨505⟩
  let callerTcb : TCB :=
    { mkTcb 2 with ipcState := .blockedOnReply ⟨10⟩ (some ⟨3⟩), replyObject := some rid }
  let replyObj : SeLe4n.Kernel.Reply := { replyId := rid, caller := some ⟨2⟩ }
  -- ⟨99⟩ is a live thread that is simply *not* the recorded server — which is
  -- what delegation means.  It was absent from the map before, which made the
  -- reply's provenance read the empty default rather than the composer's.
  let fst := mkFrozenState
    [(⟨2⟩, .tcb callerTcb), (⟨99⟩, .tcb (mkTcb 99)), (rid.toObjId, .reply replyObj)]
  let msg : IpcMessage := { registers := #[], caps := #[], badge := Badge.ofNatMasked 0 }
  -- replier ⟨99⟩ ≠ the recorded server ⟨3⟩, but presents the linked Reply cap (rid).
  match frozenEndpointReply ⟨99⟩ ⟨2⟩ rid msg fst with
  | .ok ((), fst') =>
      match frozenLookupTcb fst' ⟨2⟩ with
      | some tcb => expect "delegated replier delivers (target ready)" (tcb.ipcState == .ready)
      | none => throw <| IO.userError "target TCB missing"
  | .error _ => throw <| IO.userError "delegated replier with a valid linked Reply cap should succeed"

/-- FO-005b (PR #822 review 489): authority is the **presented** reply cap.  A replier
that presents a `replyId` which is NOT the caller's reciprocal forward link (it does
not hold the caller's reply cap) is rejected `.replyCapInvalid`, even though the caller
is `blockedOnReply` with a valid (different) linked Reply object — modelling that a
thread without the reply cap cannot deliver/consume the reply. -/
private def fo005b_replyWrongPresentedCap : IO Unit := do
  let rid : SeLe4n.ReplyId := ⟨505⟩
  let callerTcb : TCB :=
    { mkTcb 2 with ipcState := .blockedOnReply ⟨10⟩ (some ⟨3⟩), replyObject := some rid }
  let replyObj : SeLe4n.Kernel.Reply := { replyId := rid, caller := some ⟨2⟩ }
  let fst := mkFrozenState [(⟨2⟩, .tcb callerTcb), (rid.toObjId, .reply replyObj)]
  let msg : IpcMessage := { registers := #[], caps := #[], badge := Badge.ofNatMasked 0 }
  -- replier presents ⟨999⟩, NOT the caller's forward link rid (⟨505⟩) → rejected.
  match frozenEndpointReply ⟨99⟩ ⟨2⟩ (⟨999⟩ : SeLe4n.ReplyId) msg fst with
  | .ok _ => throw <| IO.userError "a replier presenting a non-matching reply cap must be rejected"
  | .error e => expect "wrong presented reply cap → replyCapInvalid" (e == .replyCapInvalid)

-- ============================================================================
-- TPH-006: Frozen Scheduler Tick
-- ============================================================================

/-- FO-006: frozenTimerTick — no current thread advances timer -/
private def fo006_timerTickIdle : IO Unit := do
  let fst := { emptyFrozenState with scheduler := { emptyFrozenState.scheduler with current := none } }
  match frozenTimerTick fst with
  | .ok ((), fst') =>
      expect "timer advanced" (fst'.machine.timer == fst.machine.timer + 1)
      expect "still idle" ((fst'.scheduler.current) == none)
  | .error _ => throw <| IO.userError "timer tick should succeed"

-- ============================================================================
-- TPH-007: Frozen CSpace Lookup (Radix O(1))
-- ============================================================================

/-- FO-007: frozenCspaceLookup — O(1) radix lookup -/
private def fo007_cspaceLookup : IO Unit := do
  -- Create a CNodeRadix with one slot
  let cap : Capability := {
    target := .object ⟨42⟩
    rights := .ofNat 7
    badge := none
  }
  let radix := (CNodeRadix.empty 0 0 4).insert (SeLe4n.Slot.ofNat 3) cap
  let cn : FrozenCNode := { depth := 1, guardWidth := 0, guardValue := 0, radixWidth := 4, slots := radix }
  let fst := mkFrozenState [(⟨10⟩, .cnode cn)]
  -- Lookup slot 3 (CPtr with value 3)
  match frozenCspaceLookup fst (SeLe4n.CPtr.ofNat 3) ⟨10⟩ with
  | .ok foundCap =>
      expect "found capability" (foundCap.target == .object ⟨42⟩)
  | .error _ => throw <| IO.userError "radix lookup should succeed"

/-- FO-008: frozenCspaceLookup — missing slot returns error -/
private def fo008_cspaceLookupMissing : IO Unit := do
  let radix := CNodeRadix.empty 0 0 4
  let cn : FrozenCNode := { depth := 1, guardWidth := 0, guardValue := 0, radixWidth := 4, slots := radix }
  let fst := mkFrozenState [(⟨10⟩, .cnode cn)]
  match frozenCspaceLookup fst (SeLe4n.CPtr.ofNat 5) ⟨10⟩ with
  | .ok _ => throw <| IO.userError "should fail"
  | .error e => expect "empty slot → invalidCapability" (e == .invalidCapability)

-- ============================================================================
-- TPH-008: Frozen VSpace Resolve
-- ============================================================================

/-- FO-009: frozenVspaceLookup — resolve virtual address -/
private def fo009_vspaceLookup : IO Unit := do
  -- Create a frozen VSpaceRoot with one mapping
  let mappingsRt := (RHTable.empty 16 : RHTable VAddr (PAddr × PagePermissions)).insert
    (SeLe4n.VAddr.ofNat 0x1000) ((SeLe4n.PAddr.ofNat 0x2000), default)
  let vsr : FrozenVSpaceRoot := { asid := ⟨1⟩, mappings := freezeMap mappingsRt }
  let asidRt := (RHTable.empty 16 : RHTable ASID ObjId).insert ⟨1⟩ ⟨20⟩
  let fst := { mkFrozenState [(⟨20⟩, .vspaceRoot vsr)] with
    asidTable := freezeMap asidRt }
  match frozenVspaceLookup ⟨1⟩ (SeLe4n.VAddr.ofNat 0x1000) fst with
  | .ok ((paddr, _perms), _) =>
      expect "resolved paddr" (paddr == (SeLe4n.PAddr.ofNat 0x2000))
  | .error _ => throw <| IO.userError "vspace lookup should succeed"

/-- FO-010: frozenVspaceLookup — unbound ASID returns error -/
private def fo010_vspaceLookupMissing : IO Unit := do
  let fst := emptyFrozenState
  match frozenVspaceLookup ⟨99⟩ (SeLe4n.VAddr.ofNat 0x1000) fst with
  | .ok _ => throw <| IO.userError "should fail"
  | .error e => expect "unbound ASID → asidNotBound" (e == .asidNotBound)

-- ============================================================================
-- TPH-009: Frozen Service Query
-- ============================================================================

/-- FO-011: frozenLookupServiceByCap — find service by endpoint -/
private def fo011_serviceLookup : IO Unit := do
  let reg : ServiceRegistration := {
    sid := ⟨1⟩
    iface := { ifaceId := ⟨1⟩, methodCount := 1, maxMessageSize := 64,
               maxResponseSize := 64, requiresGrant := false }
    endpointCap := { target := .object ⟨42⟩, rights := .ofNat 7, badge := none }
  }
  let regRt := (RHTable.empty 16 : RHTable ServiceId ServiceRegistration).insert ⟨1⟩ reg
  let fst := { emptyFrozenState with serviceRegistry := freezeMap regRt }
  match frozenLookupServiceByCap ⟨42⟩ fst with
  | .ok (found, _) => expect "found service" (found.sid == ⟨1⟩)
  | .error _ => throw <| IO.userError "service lookup should succeed"

/-- FO-012: frozenLookupServiceByCap — missing service returns error -/
private def fo012_serviceLookupMissing : IO Unit := do
  let fst := emptyFrozenState
  match frozenLookupServiceByCap ⟨99⟩ fst with
  | .ok _ => throw <| IO.userError "should fail"
  | .error e => expect "missing → objectNotFound" (e == .objectNotFound)

-- ============================================================================
-- TPH-013: Delete in Frozen (CSpace)
-- ============================================================================

/-- FO-013: frozenCspaceDelete — erase slot from frozen CNode -/
private def fo013_cspaceDelete : IO Unit := do
  let cap : Capability := { target := .object ⟨42⟩, rights := .ofNat 7, badge := none }
  let radix := (CNodeRadix.empty 0 0 4).insert (SeLe4n.Slot.ofNat 3) cap
  let cn : FrozenCNode := { depth := 1, guardWidth := 0, guardValue := 0, radixWidth := 4, slots := radix }
  let fst := mkFrozenState [(⟨10⟩, .cnode cn)]
  match frozenCspaceDelete ⟨10⟩ (SeLe4n.Slot.ofNat 3) fst with
  | .ok ((), fst') =>
      -- After delete, lookup should fail
      match frozenCspaceLookup fst' (SeLe4n.CPtr.ofNat 3) ⟨10⟩ with
      | .ok _ => throw <| IO.userError "deleted slot should be empty"
      | .error e => expect "deleted → invalidCapability" (e == .invalidCapability)
  | .error _ => throw <| IO.userError "delete should succeed"

-- ============================================================================
-- TPH-014: Notification Signal/Wait
-- ============================================================================

/-- FO-014: frozenNotificationSignal — accumulate badge on idle notification -/
private def fo014_notificationSignal : IO Unit := do
  let ntfn : Notification := { state := .idle, waitingThreads := SeLe4n.NoDupList.empty, pendingBadge := none }
  -- The signaller is a live TCB: the badge's provenance is read from it, so an
  -- unresolvable one is refused rather than defaulted or invented (SM9.D audit).
  let fst := mkFrozenState [(⟨5⟩, .notification ntfn), (⟨3⟩, .tcb (mkTcb 3))]
  match frozenNotificationSignal ⟨5⟩ ⟨3⟩ (Badge.ofNatMasked 0xFF) fst with
  | .ok ((), fst') =>
      match fst'.objects.get? ⟨5⟩ with
      | some (.notification ntfn') =>
          expect "state is active" (ntfn'.state == .active)
          expect "badge accumulated" (ntfn'.pendingBadge.isSome)
      | _ => throw <| IO.userError "notification should exist"
  | .error _ => throw <| IO.userError "signal should succeed"

/-- FO-015: frozenNotificationWait — consume pending badge -/
private def fo015_notificationWait : IO Unit := do
  let ntfn : Notification := { state := .active, waitingThreads := SeLe4n.NoDupList.empty, pendingBadge := some (Badge.ofNatMasked 42) }
  let waiterTcb := mkTcb 2
  let fst := mkFrozenState [(⟨5⟩, .notification ntfn), (⟨2⟩, .tcb waiterTcb)]
  match frozenNotificationWait ⟨5⟩ ⟨2⟩ fst with
  | .ok (badge, _fst') =>
      expect "badge consumed" (badge == some (Badge.ofNatMasked 42))
  | .error _ => throw <| IO.userError "wait should succeed"

-- ============================================================================
-- T7-D/F: Frozen IPC Queue Enqueue Tests (M-FRZ-1/2/3 validation, L-P01)
-- ============================================================================

/-- FO-016: frozenEndpointSend — no receiver, sender is enqueued in sendQ (M-FRZ-1) -/
private def fo016_sendEnqueuesSender : IO Unit := do
  let senderTcb := mkTcb 3
  let ep : Endpoint := { sendQ := {}, receiveQ := {} }
  let fst := mkFrozenState [(⟨3⟩, .tcb senderTcb), (⟨10⟩, .endpoint ep)]
  let msg : IpcMessage := { registers := #[⟨42⟩], caps := #[], badge := Badge.ofNatMasked 0 }
  match frozenEndpointSend ⟨10⟩ ⟨3⟩ msg fst with
  | .ok ((), fst') =>
      -- Verify sender TCB is now blockedOnSend
      match frozenLookupTcb fst' ⟨3⟩ with
      | some tcb =>
          expect "sender blockedOnSend" (tcb.ipcState == .blockedOnSend ⟨10⟩)
          expect "sender has pending message" (tcb.pendingMessage.isSome)
      | none => throw <| IO.userError "sender TCB missing"
      -- Verify endpoint sendQ has the sender enqueued
      match fst'.objects.get? ⟨10⟩ with
      | some (.endpoint ep') =>
          expect "sendQ head is sender" (ep'.sendQ.head == some ⟨3⟩)
          expect "sendQ tail is sender" (ep'.sendQ.tail == some ⟨3⟩)
      | _ => throw <| IO.userError "endpoint missing"
  | .error e => throw <| IO.userError s!"send should succeed, got: {reprStr e}"

/-- FO-017: frozenEndpointReceive — no sender, receiver is enqueued in receiveQ (M-FRZ-2) -/
private def fo017_receiveEnqueuesReceiver : IO Unit := do
  let recvTcb := mkTcb 4
  let ep : Endpoint := { sendQ := {}, receiveQ := {} }
  let fst := mkFrozenState [(⟨4⟩, .tcb recvTcb), (⟨10⟩, .endpoint ep)]
  match frozenEndpointReceive ⟨10⟩ ⟨4⟩ none fst with
  | .ok (_, fst') =>
      -- Verify receiver TCB is now blockedOnReceive
      match frozenLookupTcb fst' ⟨4⟩ with
      | some tcb =>
          expect "receiver blockedOnReceive" (tcb.ipcState == .blockedOnReceive ⟨10⟩)
      | none => throw <| IO.userError "receiver TCB missing"
      -- Verify endpoint receiveQ has the receiver enqueued
      match fst'.objects.get? ⟨10⟩ with
      | some (.endpoint ep') =>
          expect "receiveQ head is receiver" (ep'.receiveQ.head == some ⟨4⟩)
          expect "receiveQ tail is receiver" (ep'.receiveQ.tail == some ⟨4⟩)
      | _ => throw <| IO.userError "endpoint missing"
  | .error e => throw <| IO.userError s!"receive should succeed, got: {reprStr e}"

/-- FO-018: frozenEndpointCall — no receiver, caller enqueued in sendQ with blockedOnCall (M-FRZ-3) -/
private def fo018_callEnqueuesCaller : IO Unit := do
  let callerTcb := mkTcb 5
  let ep : Endpoint := { sendQ := {}, receiveQ := {} }
  let fst := mkFrozenState [(⟨5⟩, .tcb callerTcb), (⟨10⟩, .endpoint ep)]
  let msg : IpcMessage := { registers := #[⟨99⟩], caps := #[], badge := Badge.ofNatMasked 0 }
  match frozenEndpointCall ⟨10⟩ ⟨5⟩ msg fst with
  | .ok ((), fst') =>
      -- Verify caller TCB is now blockedOnCall
      match frozenLookupTcb fst' ⟨5⟩ with
      | some tcb =>
          expect "caller blockedOnCall" (tcb.ipcState == .blockedOnCall ⟨10⟩)
          expect "caller has pending message" (tcb.pendingMessage.isSome)
      | none => throw <| IO.userError "caller TCB missing"
      -- Verify endpoint sendQ has the caller enqueued
      match fst'.objects.get? ⟨10⟩ with
      | some (.endpoint ep') =>
          expect "sendQ head is caller" (ep'.sendQ.head == some ⟨5⟩)
          expect "sendQ tail is caller" (ep'.sendQ.tail == some ⟨5⟩)
      | _ => throw <| IO.userError "endpoint missing"
  | .error e => throw <| IO.userError s!"call should succeed, got: {reprStr e}"

/-- FO-019: frozenSchedule — select highest-priority thread as current (T7-D) -/
private def fo019_frozenSchedule : IO Unit := do
  let tid1 : ThreadId := ⟨1⟩
  let tid2 : ThreadId := ⟨2⟩
  let tcb1 := mkTcb 1 10  -- priority 10
  let tcb2 := mkTcb 2 50  -- priority 50 (higher)
  let objs := [(⟨1⟩, FrozenKernelObject.tcb tcb1), (⟨2⟩, FrozenKernelObject.tcb tcb2)]
  let objsMap := objs.foldl (fun acc (k, v) => acc.insert k v) (RHTable.empty 16)
  -- Set up scheduler with both threads by priority
  let byPrio := RHTable.empty 16
    |>.insert ⟨10⟩ [tid1]
    |>.insert ⟨50⟩ [tid2]
  let threadPrio := RHTable.empty 16
    |>.insert tid1 ⟨10⟩
    |>.insert tid2 ⟨50⟩
  let membership := RHTable.empty 16
    |>.insert tid1 ()
    |>.insert tid2 ()
  let st0 : FrozenSystemState := { emptyFrozenState with
    objects := freezeMap objsMap
    scheduler := { emptyFrozenState.scheduler with
      byPriority := freezeMap byPrio
      threadPriority := freezeMap threadPrio
      membership := freezeMap membership
      current := none
    }
  }
  match frozenSchedule st0 with
  | .ok (_, st1) =>
    expect "frozenSchedule selects highest priority" ((st1.scheduler.current) == some tid2)
    IO.println "frozen-ops check passed [FO-019: frozenSchedule]"
  | .error e => throw <| IO.userError s!"frozenSchedule failed: {reprStr e}"

/-- FO-020: frozenCspaceMint — insert cap into frozen CNode slot (T7-D) -/
private def fo020_frozenCspaceMint : IO Unit := do
  let cnodeId : ObjId := ⟨10⟩
  let epId : ObjId := ⟨11⟩
  -- Build a frozen CNode with an empty CNodeRadix (flat array)
  let radix := CNodeRadix.empty 0 0 4
  let frozenCNode : FrozenCNode := { depth := 1, guardWidth := 0, guardValue := 0, radixWidth := 4, slots := radix }
  let objs := [(cnodeId, FrozenKernelObject.cnode frozenCNode), (epId, FrozenKernelObject.endpoint {})]
  let objsMap := objs.foldl (fun acc (k, v) => acc.insert k v) (RHTable.empty 16)
  let st0 : FrozenSystemState := { emptyFrozenState with objects := freezeMap objsMap }
  let testCap : Capability := { target := .object epId, rights := .ofNat 7, badge := none }
  match frozenCspaceMint cnodeId (SeLe4n.Slot.ofNat 0) testCap st0 with
  | .ok ((), st1) =>
    -- Verify slot 0 now has the cap
    match frozenCspaceLookup st1 (SeLe4n.CPtr.ofNat 0) cnodeId with
    | .ok cap =>
      expect "frozenCspaceMint inserts cap" (cap.target == .object epId)
      IO.println "frozen-ops check passed [FO-020: frozenCspaceMint]"
    | .error e => throw <| IO.userError s!"lookup after mint failed: {reprStr e}"
  | .error e => throw <| IO.userError s!"frozenCspaceMint failed: {reprStr e}"

/-- FO-021: U-H01 regression — popped thread can be re-enqueued (multi-round IPC).
After frozenQueuePopHead, queuePPrev must be cleared so frozenQueuePushTail
does not reject the thread with `.illegalState`. This test exercises:
send (enqueue sender in sendQ) → receive (pop sender, deliver) → send again. -/
private def fo021_popThenPushRegression : IO Unit := do
  let senderTcb := mkTcb 3
  let receiverTcb := mkTcb 4
  let ep : Endpoint := { sendQ := {}, receiveQ := {} }
  let fst := mkFrozenState [
    (⟨3⟩, .tcb senderTcb),
    (⟨4⟩, .tcb receiverTcb),
    (⟨10⟩, .endpoint ep)
  ]
  let msg1 : IpcMessage := { registers := #[⟨42⟩], caps := #[], badge := Badge.ofNatMasked 0 }
  -- Round 1: sender sends (no receiver waiting → enqueued in sendQ)
  match frozenEndpointSend ⟨10⟩ ⟨3⟩ msg1 fst with
  | .error e => throw <| IO.userError s!"round1 send failed: {reprStr e}"
  | .ok ((), fst1) =>
  -- Round 1: receiver receives (pops sender from sendQ, delivers message)
  match frozenEndpointReceive ⟨10⟩ ⟨4⟩ none fst1 with
  | .error e => throw <| IO.userError s!"round1 receive failed: {reprStr e}"
  | .ok (_, fst2) =>
  -- Verify sender was popped and queue links cleared (including queuePPrev)
  match frozenLookupTcb fst2 ⟨3⟩ with
  | none => throw <| IO.userError "sender TCB missing after receive"
  | some tcb =>
      expect "sender queuePrev cleared" (tcb.queuePrev == none)
      expect "sender queueNext cleared" (tcb.queueNext == none)
      expect "sender queuePPrev cleared" (tcb.queuePPrev == none)
  -- Round 2: sender sends again (re-enqueue — must not fail with illegalState)
  let msg2 : IpcMessage := { registers := #[⟨99⟩], caps := #[], badge := Badge.ofNatMasked 0 }
  match frozenEndpointSend ⟨10⟩ ⟨3⟩ msg2 fst2 with
  | .error e => throw <| IO.userError s!"round2 re-send failed (U-H01 regression): {reprStr e}"
  | .ok ((), fst3) =>
  -- Verify sender is enqueued again
  match frozenLookupTcb fst3 ⟨3⟩ with
  | none => throw <| IO.userError "sender TCB missing after re-send"
  | some tcb =>
      expect "sender re-enqueued (blockedOnSend)" (tcb.ipcState == .blockedOnSend ⟨10⟩)
      expect "sender has queuePPrev after re-enqueue" (tcb.queuePPrev.isSome)
  IO.println "frozen-ops check passed [FO-021: U-H01 pop-then-push regression]"

/-- FO-022: provenance follows content through the frozen operations.

`FrozenSystemState.declassificationTaint` is required precisely so a snapshot
can be analysed for laundering chains, and preserving it across `freeze` buys
that only for the instant of the freeze.  These assertions are the ones that
fail if the frozen operations go back to carrying the table through unchanged:
each measures a *specific* identity reaching a thread that never held it, plus
the negative that says the transport does not keep what it handed on. -/
private def frozenProvenanceFollowsContent : IO Unit := do
  let senderTcb := mkTcb 3
  let receiverTcb := mkTcb 4
  let ep : Endpoint := { sendQ := {}, receiveQ := {} }
  let ntfn : Notification := { state := .idle, waitingThreads := SeLe4n.NoDupList.empty,
                               pendingBadge := none }
  let base := mkFrozenState [
    (⟨3⟩, .tcb senderTcb), (⟨4⟩, .tcb receiverTcb),
    (⟨10⟩, .endpoint ep), (⟨5⟩, .notification ntfn)
  ]
  -- Tag the sender with one identity, so the assertions below name a tag that
  -- exists nowhere else in the snapshot.
  let tagged : FrozenSystemState :=
    { base with declassificationTaint :=
        base.declassificationTaint.joinAt ⟨3⟩ (SeLe4n.Kernel.DeclassificationTaint.singleton 77) }
  expect "FO-022: the receiver starts untainted"
    (!((tagged.declassificationTaint ⟨4⟩).contains 77))
  -- A parked send followed by a receive moves the message; the provenance must
  -- move with it.
  let msg : IpcMessage := { registers := #[⟨7⟩], caps := #[], badge := Badge.ofNatMasked 0 }
  match frozenEndpointSend ⟨10⟩ ⟨3⟩ msg tagged with
  | .error e => throw <| IO.userError s!"FO-022 send failed: {reprStr e}"
  | .ok ((), fstSend) =>
  expect "FO-022: a parked send leaves the message in the sender, so nothing propagates"
    (!((fstSend.declassificationTaint ⟨4⟩).contains 77))
  match frozenEndpointReceive ⟨10⟩ ⟨4⟩ none fstSend with
  | .error e => throw <| IO.userError s!"FO-022 receive failed: {reprStr e}"
  | .ok (_, fstRecv) =>
  expect "FO-022: the receiver inherits the sender's provenance with the message"
    ((fstRecv.declassificationTaint ⟨4⟩).contains 77)
  -- A notification stores the signaller's provenance, and a wait moves it to the
  -- waiter and leaves the transport carrying none.
  match frozenNotificationSignal ⟨5⟩ ⟨3⟩ (Badge.ofNatMasked 0xFF) tagged with
  | .error e => throw <| IO.userError s!"FO-022 signal failed: {reprStr e}"
  | .ok ((), fstSig) =>
  expect "FO-022: a stored badge carries the signaller's provenance"
    ((fstSig.declassificationTaint ⟨5⟩).contains 77)
  match frozenNotificationWait ⟨5⟩ ⟨4⟩ fstSig with
  | .error e => throw <| IO.userError s!"FO-022 wait failed: {reprStr e}"
  | .ok (_, fstWait) =>
  expect "FO-022: the waiter inherits the badge's provenance"
    ((fstWait.declassificationTaint ⟨4⟩).contains 77)
  expect "FO-022: NEGATIVE — the consumed notification keeps none of it"
    (!((fstWait.declassificationTaint ⟨5⟩).contains 77))
  IO.println "frozen-ops check passed [FO-022: provenance follows frozen content]"

/-- FO-023 (PR #873 round 11): the two ways a frozen operation could claim a
delivery it had not made.

Both were surfaced by the provenance carriage rather than caused by it — the
taint flow asserts that content reached somewhere, which is only honest if the
content is actually there and its source is actually readable. -/
private def frozenDeliveryIsHonest : IO Unit := do
  -- (a) A signalled waiter receives the BADGE, not just the wake.  This branch
  -- cleared `pendingBadge` and readied the waiter while storing no message, so
  -- the badge vanished — while the flow below recorded it as delivered.
  let ntfn : Notification :=
    { state := .idle, waitingThreads := SeLe4n.NoDupList.empty, pendingBadge := none }
  let base := mkFrozenState
    [(⟨4⟩, .tcb (mkTcb 4)), (⟨6⟩, .tcb (mkTcb 6)), (⟨5⟩, .notification ntfn)]
  -- Wait first, so the signal below takes the *waiter* branch.
  match frozenNotificationWait ⟨5⟩ ⟨4⟩ base with
  | .error e => throw <| IO.userError s!"FO-023 wait failed: {reprStr e}"
  | .ok (_, fstWaiting) =>
  match frozenNotificationSignal ⟨5⟩ ⟨6⟩ (Badge.ofNatMasked 42) fstWaiting with
  | .error e => throw <| IO.userError s!"FO-023 signal failed: {reprStr e}"
  | .ok (_, fstSig) =>
  expect "FO-023: the signalled waiter is handed the badge, not only woken"
    (match frozenLookupTcb fstSig ⟨4⟩ with
     | some wt => match wt.pendingMessage with
                  | some m => m.badge == some (Badge.ofNatMasked 42)
                  | none => false
     | none => false)
  expect "FO-023: the notification is left holding none of it"
    (match fstSig.objects.get? ⟨5⟩ with
     | some (.notification n) => n.pendingBadge == none
     | _ => false)
  -- (b) A reply whose composing thread cannot be resolved is REFUSED rather
  -- than reading the total table's empty default and silently under-tagging.
  let rid : SeLe4n.ReplyId := ⟨505⟩
  let callerTcb : TCB :=
    { mkTcb 2 with ipcState := .blockedOnReply ⟨10⟩ (some ⟨3⟩), replyObject := some rid }
  let replyObj : SeLe4n.Kernel.Reply := { replyId := rid, caller := some ⟨2⟩ }
  let fstRep := mkFrozenState [(⟨2⟩, .tcb callerTcb), (rid.toObjId, .reply replyObj)]
  let msg : IpcMessage := { registers := #[], caps := #[], badge := Badge.ofNatMasked 0 }
  expect "FO-023: an unresolvable reply source is refused, not defaulted"
    (match frozenEndpointReply ⟨99⟩ ⟨2⟩ rid msg fstRep with
     | .ok _ => false
     | .error e => e == .objectNotFound)
  -- (c) The same for a signal's source, which has one failure mode more: an id
  -- naming a live NON-TCB object would read that object's provenance, so the
  -- snapshot could report a predecessor the badge never had.  Losing a link
  -- makes the analysis miss a chain; inventing one makes it name a false origin.
  let idle : Notification :=
    { state := .idle, waitingThreads := SeLe4n.NoDupList.empty, pendingBadge := none }
  let other : Notification :=
    { state := .idle, waitingThreads := SeLe4n.NoDupList.empty, pendingBadge := none }
  let fstSg := mkFrozenState [(⟨5⟩, .notification idle), (⟨8⟩, .notification other)]
  expect "FO-023: an absent signaller is refused, not defaulted"
    (match frozenNotificationSignal ⟨5⟩ ⟨7⟩ (Badge.ofNatMasked 9) fstSg with
     | .ok _ => false
     | .error e => e == .objectNotFound)
  expect "FO-023: a signaller naming a live non-TCB object cannot invent a predecessor"
    (match frozenNotificationSignal ⟨5⟩ ⟨8⟩ (Badge.ofNatMasked 9) fstSg with
     | .ok _ => false
     | .error e => e == .objectNotFound)
  -- (d) …and the send's source, on BOTH orderings.  The blocking path always
  -- resolved the sender; the rendezvous path did not, so whether a nonexistent
  -- sender was refused depended on whether a receiver happened to be waiting.
  let epEmpty : Endpoint := { sendQ := {}, receiveQ := {} }
  let fstNoRecv := mkFrozenState [(⟨10⟩, .endpoint epEmpty)]
  let sendMsg : IpcMessage :=
    { registers := #[], caps := #[], badge := Badge.ofNatMasked 0 }
  expect "FO-023: an absent sender is refused with no receiver waiting"
    (match frozenEndpointSend ⟨10⟩ ⟨77⟩ sendMsg fstNoRecv with
     | .ok _ => false
     | .error e => e == .objectNotFound)
  -- Same sender, same endpoint, but now a receiver is queued — the ordering
  -- that used to accept it.
  match frozenEndpointReceive ⟨10⟩ ⟨4⟩ none (mkFrozenState
      [(⟨10⟩, .endpoint epEmpty), (⟨4⟩, .tcb (mkTcb 4))]) with
  | .error _ =>
      -- A receive with no sender blocks the receiver; that is the state we want.
      throw <| IO.userError "FO-023: parking a receiver should succeed"
  | .ok (_, fstWithRecv) =>
    expect "FO-023: an absent sender is refused at a rendezvous too, not only when blocking"
      (match frozenEndpointSend ⟨10⟩ ⟨77⟩ sendMsg fstWithRecv with
       | .ok _ => false
       | .error e => e == .objectNotFound)
  IO.println "frozen-ops check passed [FO-023: a frozen delivery is honest]"

/-- FO-024 (PR #873 round 7): **a parked sender with no message is refused, not
dequeued.**

`frozenQueuePopHead` validated the head's blocking *state* and nothing else, so a
`.blockedOnSend` head carrying `pendingMessage := none` was accepted;
`frozenEndpointReceive` then stored that `none` in the receiver and still joined
the sender's provenance, inventing a causal predecessor for content that was
never delivered.

The state is malformed rather than reachable — the frozen send path parks with
`pendingMessage := some msg` — which is exactly why it has to be refused
structurally: a hand-built snapshot is what a frozen state IS. -/
private def frozenParkedSenderCarriesItsMessage : IO Unit := do
  let epParked : Endpoint := { sendQ := { head := some ⟨3⟩, tail := some ⟨3⟩ }, receiveQ := {} }
  let msg : IpcMessage := { registers := #[], caps := #[], badge := Badge.ofNatMasked 0 }
  -- The malformed snapshot: parked to send, holding nothing.
  let fstEmpty := mkFrozenState
    [(⟨10⟩, .endpoint epParked),
     (⟨3⟩, .tcb { mkTcb 3 with ipcState := .blockedOnSend ⟨10⟩, pendingMessage := none }),
     (⟨4⟩, .tcb (mkTcb 4))]
  expect "FO-024: a message-less parked sender is refused rather than dequeued"
    (match frozenEndpointReceive ⟨10⟩ ⟨4⟩ none fstEmpty with
     | .ok _ => false
     | .error e => e == .endpointStateMismatch)
  -- NEGATIVE, load-bearing: the SAME queue shape with a message succeeds and
  -- delivers, so the refusal above is about the missing message and not about
  -- the hand-built queue.
  let fstFull := mkFrozenState
    [(⟨10⟩, .endpoint epParked),
     (⟨3⟩, .tcb { mkTcb 3 with ipcState := .blockedOnSend ⟨10⟩, pendingMessage := some msg }),
     (⟨4⟩, .tcb (mkTcb 4))]
  expect "FO-024: the same shape WITH a message still delivers"
    (match frozenEndpointReceive ⟨10⟩ ⟨4⟩ none fstFull with
     | .error _ => false
     | .ok (_, fst') =>
       match frozenLookupTcb fst' ⟨4⟩ with
       | some recvTcb => recvTcb.pendingMessage.isSome
       | none => false)
  IO.println "frozen-ops check passed [FO-024: a parked sender carries its message]"

/-- FO-025 (PR #873 round 8): **the frozen signal honours bound delivery.**

With no ordinary waiter and a bound TCB parked on an endpoint, the live
`notificationSignalBound` dequeues that TCB and delivers the badge into its
`pendingMessage`.  The frozen path fell through to the storage branch instead:
the bound thread stayed blocked, the badge sat on the notification, and — once
SM9.D landed — the signaller's provenance was recorded on the notification rather
than on the thread that was supposed to receive the content.

Delivery and provenance are separate ways to get this wrong, so both are
asserted, together with the negative that says the storage branch did *not*
run. -/
private def frozenBoundNotificationDelivery : IO Unit := do
  let epId      : SeLe4n.ObjId := ⟨40⟩
  let notifId   : SeLe4n.ObjId := ⟨41⟩
  let bound     : SeLe4n.ThreadId := ⟨42⟩
  let signaller : SeLe4n.ThreadId := ⟨43⟩
  let badge := Badge.ofNatMasked 77
  -- The bound TCB is parked on the endpoint's receive queue, and the
  -- notification has no ordinary waiter — the live bound-delivery shape.
  let ep : Endpoint := { sendQ := {}, receiveQ := { head := some bound, tail := some bound } }
  let ntfn : Notification :=
    { state := .idle, waitingThreads := SeLe4n.NoDupList.empty, pendingBadge := none,
      boundTCB := some bound }
  let boundTcb : TCB :=
    { mkTcb 42 with ipcState := .blockedOnReceive epId, queuePPrev := some .endpointHead }
  let fst := mkFrozenState
    [(epId, .endpoint ep),
     (notifId, .notification ntfn),
     (⟨42⟩, .tcb boundTcb),
     (⟨43⟩, .tcb (mkTcb 43))]
  match frozenNotificationSignal notifId signaller badge fst with
  | .error _ => throw <| IO.userError "FO-025: bound delivery should succeed"
  | .ok ((), fst') =>
    expect "FO-025: the badge is delivered into the bound thread's pendingMessage"
      (match frozenLookupTcb fst' bound with
       | some t => (t.pendingMessage.bind (·.badge)) == some badge
       | none => false)
    expect "FO-025: the bound thread is unblocked and off the endpoint queue"
      ((match frozenLookupTcb fst' bound with
        | some t => decide (t.ipcState = .ready) && t.queuePPrev.isNone
        | none => false) &&
       (match fst'.objects.get? epId with
        | some (.endpoint e) => e.receiveQ.head.isNone
        | _ => false))
    -- NEGATIVE, load-bearing: the storage branch did NOT run.  If it had, the
    -- badge would sit on the notification and the provenance with it — which is
    -- exactly the state this cut replaced.
    expect "FO-025: NEGATIVE — the badge was not stored on the notification"
      (match fst'.objects.get? notifId with
       | some (.notification n) => n.pendingBadge.isNone
       | _ => false)
    expect "FO-025: the provenance follows the badge to the bound thread"
      ((fst'.declassificationTaint bound.toObjId) ==
        (fst.declassificationTaint signaller.toObjId).join
          (fst.declassificationTaint bound.toObjId))
  IO.println "frozen-ops check passed [FO-025: frozen bound notification delivery]"

/-! ## Frozen/live differential agreement

Every scenario above this point runs the frozen operation **alone**, asserting
against what its author read in the live transition and wrote into a comment.
That is how five separate divergences reached review: the frozen operation was
green the whole time, because nothing ever ran the transition it claims to
mirror.

These scenarios run both.  One `IntermediateState` is built, the live transition
runs on `ist.state`, the frozen one on `freeze ist`, and
`frozenRunAgrees` compares the results — the same refusal, or two successes
whose object stores, taint tables and current thread agree.  Naming the wrong
counterpart fails here too, because the comparison is against the transition
actually called; `fo033` pins exactly that. -/

/-- The shared fixture: one endpoint, one notification bound to a receiver, two
threads.  Small enough to read, and containing every kind the recorded
divergences touched. -/
private def diffTcb (n : Nat) : TCB :=
  { tid := ⟨n⟩, priority := ⟨0⟩, domain := ⟨0⟩, cspaceRoot := ⟨64⟩,
    vspaceRoot := ⟨0⟩, ipcBuffer := (SeLe4n.VAddr.ofNat 0) }

private def diffEpId    : SeLe4n.ObjId := ⟨60⟩
private def diffNotifId : SeLe4n.ObjId := ⟨61⟩
private def diffA       : SeLe4n.ThreadId := ⟨62⟩
private def diffB       : SeLe4n.ThreadId := ⟨63⟩
private def diffCnId    : SeLe4n.ObjId := ⟨64⟩
/-- A third thread: the **delegate** that holds a copied reply capability without
being the caller's recorded server.  Needed because the two actors above cannot
express delegation — `diffB` *is* the recorded server in every fixture here, which
is exactly why the round-15 operation differential could not see the divergence
round 22 found. -/
private def diffDelegate : SeLe4n.ThreadId := ⟨65⟩

/-- The actors share one CSpace root holding the operand capability at slot 0.

Without it the live side resolves no operand — `contentFlowEdges` goes through
`syscallOperandCap?`, which reads the caller's CSpace — so its taint plan is
empty and the provenance step compares as a no-op against a frozen operation
that performs one.  The scenarios would then agree only because every taint was
empty, which is agreement about nothing. -/
private def diffAddCSpace (ist : IntermediateState)
    (caps : List (SeLe4n.Slot × Capability)) : IntermediateState :=
  Builder.createObject ist diffCnId
    (.cnode { depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
              slots := SeLe4n.UniqueSlotMap.ofListWF caps })
    (fun _ h => by cases h; exact (SeLe4n.UniqueSlotMap.ofListWF caps).hWF)
    (fun _ h => nomatch h)

/-- The capability naming `oid`, as an actor's CSpace would hold it. -/
private def diffObjCap (oid : SeLe4n.ObjId) : Capability :=
  { target := .object oid,
    rights := AccessRightSet.ofList [.read, .write, .grant], badge := none }

/-! The three adders below take the object's *structure* rather than a
`KernelObject`, so the builder's CNode-slot and VSpace-mapping obligations are
discharged by `nomatch` on a literal constructor.  A list of `KernelObject`s
could not do that: the obligations quantify over a value the fold cannot see
into. -/

/-- Create the TCB **and** put it in the run queue.

Every thread in these scenarios is one that had been runnable and then blocked
or is about to be woken, which is the only way a live state reaches these
shapes.  Building them outside the run queue would model a state the live kernel
cannot produce — and would hide exactly what these scenarios are for, since a
wake's run-queue insert has nothing to insert into. -/
private def diffAddTcb (ist : IntermediateState) (t : TCB) : IntermediateState :=
  let withObj := Builder.createObject ist t.tid.toObjId (.tcb t)
    (fun _ h => nomatch h) (fun _ h => nomatch h)
  -- Only a `.ready` thread is in the run queue: a blocked one left it when it
  -- blocked, which is what makes the wake paths' re-insert observable.  Queuing
  -- blocked threads too would put the bucket in the state the wake wants to
  -- reach and hide whether the transition got it there.
  if t.ipcState == .ready then Builder.markRunnable withObj t.tid t.priority
  else withObj

private def diffAddEndpoint (ist : IntermediateState) (id : SeLe4n.ObjId) (e : Endpoint) :
    IntermediateState :=
  Builder.createObject ist id (.endpoint e) (fun _ h => nomatch h) (fun _ h => nomatch h)

private def diffAddNotification (ist : IntermediateState) (id : SeLe4n.ObjId)
    (n : Notification) : IntermediateState :=
  Builder.createObject ist id (.notification n) (fun _ h => nomatch h) (fun _ h => nomatch h)

private def diffAddReply (ist : IntermediateState) (rid : SeLe4n.ReplyId)
    (r : SeLe4n.Kernel.Reply) : IntermediateState :=
  Builder.createObject ist rid.toObjId (.reply r) (fun _ h => nomatch h) (fun _ h => nomatch h)

private def diffAddSchedContext (ist : IntermediateState) (scId : SeLe4n.SchedContextId)
    (sc : SeLe4n.Kernel.SchedContext) : IntermediateState :=
  Builder.createObject ist scId.toObjId (.schedContext sc)
    (fun _ h => nomatch h) (fun _ h => nomatch h)

/-- **WS-HP HP8.1**: the donated scheduling context the FO-042 halves below move.

Held by the recorded server, owed back to the answered caller, and — in the
donating half — recorded as heading the answered frame's stack, which is what
makes the head-driven trigger fire. -/
private def diffScId : SeLe4n.SchedContextId := SeLe4n.SchedContextId.ofNat 66

private def diffDonatedSc (head? : Option SeLe4n.ReplyId) : SeLe4n.Kernel.SchedContext :=
  { scId := diffScId, budget := ⟨100⟩, period := ⟨1000⟩, priority := ⟨40⟩,
    deadline := ⟨0⟩, domain := ⟨0⟩, budgetRemaining := ⟨50⟩,
    boundThread := some diffB, scReply := head?, isActive := true }

/-- **WS-HP HP4.7**: a reservation the *answered caller* holds in its own right.

The recipient guard's subject: a caller that acquired a scheduling context while
blocked is one whose binding the pop must not overwrite, and under the head-driven
trigger nothing the operation reads rules that state out. -/
private def diffOwnScId : SeLe4n.SchedContextId := SeLe4n.SchedContextId.ofNat 67

private def diffCallerOwnSc : SeLe4n.Kernel.SchedContext :=
  { scId := diffOwnScId, budget := ⟨80⟩, period := ⟨800⟩, priority := ⟨30⟩,
    deadline := ⟨0⟩, domain := ⟨0⟩, budgetRemaining := ⟨40⟩,
    boundThread := some diffA, isActive := true }

/-! ### Comparing like layers

A frozen operation is the syscall, not the bare transition: with no dispatcher in
the frozen phase it applies the provenance step inline, while the live kernel
applies it afterwards at the seam (`applySyscallTaint` in `dispatchSyscall*`).
Comparing a frozen operation against a bare live transition therefore compares
two different layers — and passes only while every taint is empty, which is
exactly what `mkEmptyIntermediateState` gives.  It would have started failing on
the first realistic tagged input, and reported the harness rather than the
kernel.

`liveWithTaint` composes the missing half, so both sides are the syscall.  The
tagged fixture below makes the comparison non-vacuous: with the actor carrying
provenance, an omitted or misdirected taint step changes the result. -/

/-- The decoded operands the taint plan reads, for a scenario driving `sid`. -/
private def diffDecoded (sid : SyscallId) (capAddr : SeLe4n.CPtr := SeLe4n.CPtr.ofNat 0)
    : SyscallDecodeResult :=
  { capAddr := capAddr, msgInfo := { label := 0, length := 0, extraCaps := 0 }, syscallId := sid }

/-- The live transition **plus** the provenance step the seam applies after it —
the whole of what the frozen operation does in one call. -/
private def liveWithTaint {α : Type} (sid : SyscallId) (actor : SeLe4n.ThreadId)
    (capAddr : SeLe4n.CPtr) (run : SystemState → Except KernelError (α × SystemState))
    (st : SystemState) : Except KernelError (α × SystemState) :=
  match run st with
  | .error e => .error e
  | .ok (a, post) =>
      .ok (a, SeLe4n.Kernel.applySyscallTaint
                (SeLe4n.Kernel.syscallTaintPlan st actor (diffDecoded sid capAddr)) st post)

/-- **The live `.reply` spine, in the shape `liveWithTaint` consumes.**

`endpointReplyCrossCoreDispatch` is what the live `.reply` arm routes through
(`replyTransferOnCoreChecked` → `replyTransferOnCore` → this), and it answers
`SystemState × Except _ (Option (CoreId × SgiKind))` because the runtime needs the
cross-core poke.  The frozen surface models no per-core scheduler, so the SGI is
discarded and the state compared; on a fixture whose threads are unpinned every
`determineTargetCore` answers `bootCoreId`, so the per-core writes land where
`frozenStateAgrees` reads them.

The **superseded** single-core composite `endpointReplyWithDonation` is
deliberately not used here (PR #895 review round 22): it has no production caller
and its bare reply leg refuses a delegated reply-cap holder, which the live spine
and the frozen mirror both accept. -/
private def liveReplySpine (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (st : SystemState) : Except KernelError (Unit × SystemState) :=
  match SeLe4n.Kernel.endpointReplyCrossCoreDispatch replier target msg bootCoreId st with
  | (st', .ok _) => .ok ((), st')
  | (_, .error e) => .error e

/-- **The live reply LEG, in the same shape** — and the sweep the round-22 finding
owed its sibling.

The review named the operation-level claim; the leg claim one table above asked
the identical question and had the identical answer wrong.  `frozenEndpointReply`
mirrors `endpointReplyOnCore`, whose `_replier` parameter is unused, and *not* the
bare `endpointReply`, which keeps the `replier == expected` gate the cross-core
spelling dropped.  Both claims were latent for the same reason — every fixture
here made the replier the recorded server, where the two coincide. -/
private def liveReplyLeg (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (st : SystemState) : Except KernelError (Unit × SystemState) :=
  match SeLe4n.Kernel.endpointReplyOnCore replier target msg bootCoreId st with
  | (st', .ok _) => .ok ((), st')
  | (_, .error e) => .error e

/-- FO-026: the signal, against the live entry the `.notificationSignal` arm
runs.  A notification with no ordinary waiter and a bound TCB parked on an
endpoint — the shape whose frozen handling diverged twice. -/
private def differentialNotificationSignalAgrees : IO Unit := do
  let badge := SeLe4n.Badge.ofNatMasked 77
  let ep : Endpoint := { sendQ := {}, receiveQ := { head := some diffA, tail := some diffA } }
  let ntfn : Notification :=
    { state := .idle, waitingThreads := SeLe4n.NoDupList.empty, pendingBadge := none,
      boundTCB := some diffA }
  let boundTcb : TCB := { diffTcb 62 with ipcState := .blockedOnReceive diffEpId, queuePPrev := some .endpointHead }
  let ist := diffAddTcb (diffAddTcb (diffAddNotification
    (diffAddEndpoint (diffAddCSpace mkEmptyIntermediateState [(SeLe4n.Slot.ofNat 0, diffObjCap diffNotifId)]) diffEpId ep) diffNotifId ntfn) boundTcb) (diffTcb 63)
  -- Control (the FO-031 discipline): both sides really deliver, so the
  -- agreement below is about a delivered signal rather than a shared refusal.
  expect "FO-026 control: the live bound-aware signal succeeds (not a shared refusal)"
    (SeLe4n.Kernel.notificationSignalBound diffNotifId badge ist.state).toOption.isSome
  expect "FO-026 control: and so does the frozen one"
    (frozenNotificationSignal diffNotifId diffB badge (freeze ist)).toOption.isSome
  expect "FO-026: the frozen signal agrees with the live bound-aware signal"
    (frozenRunAgrees unitResultAgrees
      (frozenNotificationSignal diffNotifId diffB badge (freeze ist))
      (liveWithTaint .notificationSignal diffB (SeLe4n.CPtr.ofNat 0)
        (SeLe4n.Kernel.notificationSignalBound diffNotifId badge) ist.state))

/-- FO-027: the wait, against `notificationWait`.  A notification holding a badge
so the consuming branch runs rather than the blocking one. -/
private def differentialNotificationWaitAgrees : IO Unit := do
  let ntfn : Notification :=
    { state := .active, waitingThreads := SeLe4n.NoDupList.empty,
      pendingBadge := some (SeLe4n.Badge.ofNatMasked 9) }
  let ist := diffAddTcb
    (diffAddNotification (diffAddCSpace mkEmptyIntermediateState [(SeLe4n.Slot.ofNat 0, diffObjCap diffNotifId)])
      diffNotifId ntfn) (diffTcb 62)
  -- Control: the badge really is consumed on both sides.
  expect "FO-027 control: the live wait succeeds (not a shared refusal)"
    (SeLe4n.Kernel.notificationWait diffNotifId diffA ist.state).toOption.isSome
  expect "FO-027 control: and so does the frozen one"
    (frozenNotificationWait diffNotifId diffA (freeze ist)).toOption.isSome
  expect "FO-027: the frozen wait agrees with the live wait"
    (frozenRunAgrees (fun a b => a == b)
      (frozenNotificationWait diffNotifId diffA (freeze ist))
      (liveWithTaint .notificationWait diffA (SeLe4n.CPtr.ofNat 0)
        (SeLe4n.Kernel.notificationWait diffNotifId diffA) ist.state))

/-- FO-028: the send, against `endpointSendDual`, with no receiver waiting — the
parking branch, whose frozen mirror grew the message-presence guard. -/
private def differentialEndpointSendAgrees : IO Unit := do
  let msg : IpcMessage := { registers := #[⟨5⟩], caps := #[], badge := none }
  let ist := diffAddTcb (diffAddTcb
    (diffAddEndpoint (diffAddCSpace mkEmptyIntermediateState [(SeLe4n.Slot.ofNat 0, diffObjCap diffEpId)]) diffEpId {}) (diffTcb 62)) (diffTcb 63)
  -- Control: the send really parks on both sides.
  expect "FO-028 control: the live send succeeds (not a shared refusal)"
    (SeLe4n.Kernel.endpointSendDual diffEpId diffA msg ist.state).toOption.isSome
  expect "FO-028 control: and so does the frozen one"
    (frozenEndpointSend diffEpId diffA msg (freeze ist)).toOption.isSome
  expect "FO-028: the frozen send agrees with the live send"
    (frozenRunAgrees unitResultAgrees
      (frozenEndpointSend diffEpId diffA msg (freeze ist))
      (liveWithTaint .send diffA (SeLe4n.CPtr.ofNat 0)
        (SeLe4n.Kernel.endpointSendDual diffEpId diffA msg) ist.state))

/-- FO-038: the wait, against `notificationWait`, with nothing pending — the
idle park.  The waiter goes in already holding a collected `pendingMessage`,
so the scenario pins the atomic clear the live path performs at the block:
before the mirror fix the frozen side parked the waiter still holding the
message, a live/frozen divergence on the mirror's own content channel
(PR #886 review). -/
private def differentialNotificationWaitParksAgrees : IO Unit := do
  let held : IpcMessage := { registers := #[⟨11⟩], caps := #[], badge := none }
  let ntfn : Notification :=
    { state := .idle, waitingThreads := SeLe4n.NoDupList.empty,
      pendingBadge := none }
  let ist := diffAddTcb
    (diffAddNotification (diffAddCSpace mkEmptyIntermediateState [(SeLe4n.Slot.ofNat 0, diffObjCap diffNotifId)])
      diffNotifId ntfn) { diffTcb 62 with pendingMessage := some held }
  -- Control: the wait really parks on both sides (no shared refusal).
  expect "FO-038 control: the live wait parks (not a shared refusal)"
    (SeLe4n.Kernel.notificationWait diffNotifId diffA ist.state).toOption.isSome
  expect "FO-038 control: and so does the frozen one"
    (frozenNotificationWait diffNotifId diffA (freeze ist)).toOption.isSome
  expect "FO-038: the frozen idle park agrees with the live one"
    (frozenRunAgrees (fun a b => a == b)
      (frozenNotificationWait diffNotifId diffA (freeze ist))
      (liveWithTaint .notificationWait diffA (SeLe4n.CPtr.ofNat 0)
        (SeLe4n.Kernel.notificationWait diffNotifId diffA) ist.state))

/-- FO-039: the idle park again, on a *bound* notification — the bound thread
itself waiting, the seL4-canonical shape.  The live block rebuilds the
notification carrying `boundTCB` forward; the frozen rebuild omitted the
field, silently resetting the binding to `none` on the frozen side only,
which FO-038's unbound fixture could not see (PR #886 review). -/
private def differentialNotificationWaitParksBoundAgrees : IO Unit := do
  let ntfn : Notification :=
    { state := .idle, waitingThreads := SeLe4n.NoDupList.empty,
      pendingBadge := none, boundTCB := some diffA }
  let ist := diffAddTcb
    (diffAddNotification (diffAddCSpace mkEmptyIntermediateState [(SeLe4n.Slot.ofNat 0, diffObjCap diffNotifId)])
      diffNotifId ntfn) (diffTcb 62)
  expect "FO-039 control: the live wait parks on the bound notification"
    (SeLe4n.Kernel.notificationWait diffNotifId diffA ist.state).toOption.isSome
  expect "FO-039 control: and so does the frozen one"
    (frozenNotificationWait diffNotifId diffA (freeze ist)).toOption.isSome
  expect "FO-039: the frozen bound-notification park agrees with the live one"
    (frozenRunAgrees (fun a b => a == b)
      (frozenNotificationWait diffNotifId diffA (freeze ist))
      (liveWithTaint .notificationWait diffA (SeLe4n.CPtr.ofNat 0)
        (SeLe4n.Kernel.notificationWait diffNotifId diffA) ist.state))

/-- FO-040: the badge consume on a *bound* notification — the same field, one
branch over: the live consume carries `boundTCB` through its rebuild and the
frozen one dropped it (the FO-039 sweep's sibling; a badge pending on a bound
notification is reachable, since bound delivery stores when the bound TCB is
not endpoint-parked). -/
private def differentialNotificationWaitConsumesBoundAgrees : IO Unit := do
  let ntfn : Notification :=
    { state := .active, waitingThreads := SeLe4n.NoDupList.empty,
      pendingBadge := some (SeLe4n.Badge.ofNatMasked 9), boundTCB := some diffA }
  let ist := diffAddTcb
    (diffAddNotification (diffAddCSpace mkEmptyIntermediateState [(SeLe4n.Slot.ofNat 0, diffObjCap diffNotifId)])
      diffNotifId ntfn) (diffTcb 62)
  expect "FO-040 control: the live consume succeeds on the bound notification"
    (SeLe4n.Kernel.notificationWait diffNotifId diffA ist.state).toOption.isSome
  expect "FO-040 control: and so does the frozen one"
    (frozenNotificationWait diffNotifId diffA (freeze ist)).toOption.isSome
  expect "FO-040: the frozen bound-notification consume agrees with the live one"
    (frozenRunAgrees (fun a b => a == b)
      (frozenNotificationWait diffNotifId diffA (freeze ist))
      (liveWithTaint .notificationWait diffA (SeLe4n.CPtr.ofNat 0)
        (SeLe4n.Kernel.notificationWait diffNotifId diffA) ist.state))

/-- FO-029: the receive, against `endpointReceiveDual`, dequeuing a parked
sender that carries its message — the rendezvous the round-11 guard admits. -/
private def differentialEndpointReceiveAgrees : IO Unit := do
  let msg : IpcMessage := { registers := #[⟨7⟩], caps := #[], badge := none }
  let ep : Endpoint := { sendQ := { head := some diffA, tail := some diffA }, receiveQ := {} }
  let parked : TCB := { diffTcb 62 with ipcState := .blockedOnSend diffEpId, pendingMessage := some msg, queuePPrev := some .endpointHead }
  let ist := diffAddTcb (diffAddTcb
    (diffAddEndpoint (diffAddCSpace mkEmptyIntermediateState [(SeLe4n.Slot.ofNat 0, diffObjCap diffEpId)]) diffEpId ep) parked) (diffTcb 63)
  -- Control: the rendezvous really completes on both sides.
  expect "FO-029 control: the live receive succeeds (not a shared refusal)"
    (SeLe4n.Kernel.endpointReceiveDual diffEpId diffB none ist.state).toOption.isSome
  expect "FO-029 control: and so does the frozen one"
    (frozenEndpointReceive diffEpId diffB none (freeze ist)).toOption.isSome
  expect "FO-029: the frozen receive agrees with the live receive"
    (frozenRunAgrees (fun a b => a == b)
      (frozenEndpointReceive diffEpId diffB none (freeze ist))
      (liveWithTaint .receive diffB (SeLe4n.CPtr.ofNat 0)
        (SeLe4n.Kernel.endpointReceiveDual diffEpId diffB none) ist.state))

/-- FO-030: the call, against `endpointCall`, with no receiver — the parking
branch again, on the arm that also stages a reply. -/
private def differentialEndpointCallAgrees : IO Unit := do
  let msg : IpcMessage := { registers := #[⟨11⟩], caps := #[], badge := none }
  let ist := diffAddTcb (diffAddTcb
    (diffAddEndpoint (diffAddCSpace mkEmptyIntermediateState [(SeLe4n.Slot.ofNat 0, diffObjCap diffEpId)]) diffEpId {}) (diffTcb 62)) (diffTcb 63)
  -- Control: the call really parks on both sides.
  expect "FO-030 control: the live call succeeds (not a shared refusal)"
    (SeLe4n.Kernel.endpointCall diffEpId diffA msg ist.state).toOption.isSome
  expect "FO-030 control: and so does the frozen one"
    (frozenEndpointCall diffEpId diffA msg (freeze ist)).toOption.isSome
  expect "FO-030: the frozen call agrees with the live call"
    (frozenRunAgrees unitResultAgrees
      (frozenEndpointCall diffEpId diffA msg (freeze ist))
      (liveWithTaint .call diffA (SeLe4n.CPtr.ofNat 0)
        (SeLe4n.Kernel.endpointCall diffEpId diffA msg) ist.state))

/-- FO-031: the reply LEG, against `endpointReplyOnCore` — the leg the live
`.reply` arm dispatches — delivering to a caller parked in `.blockedOnReply`.

Repointed from the bare single-core `endpointReply` at PR #895 review round 22:
that one keeps the `replier == expected` gate the cross-core spelling dropped, so
naming it made this claim false on a delegated reply-cap holder, which the frozen
leg accepts.  The delegated half below is the shape that separates them. -/
private def differentialEndpointReplyAgrees : IO Unit := do
  let msg : IpcMessage := { registers := #[⟨13⟩], caps := #[], badge := none }
  -- The reply's authority is the presented reply capability, so the fixture has
  -- to carry the whole link: the target parked in `.blockedOnReply` with its
  -- forward `replyObject`, and a Reply object naming it back.  Without those
  -- both sides refuse with `.replyCapInvalid` and the comparison passes without
  -- ever running a reply — a check that agrees because nothing happened.
  let rid : SeLe4n.ReplyId := ⟨505⟩
  let caller : TCB := { diffTcb 62 with ipcState := .blockedOnReply diffEpId (some diffB), replyObject := some rid }
  let ist := diffAddReply (diffAddTcb (diffAddTcb
    (diffAddEndpoint mkEmptyIntermediateState diffEpId {}) caller) (diffTcb 63))
    rid { replyId := rid, caller := some diffA }
  -- Control: the reply really happens on both sides, so the agreement below is
  -- about a delivered reply rather than a shared refusal.
  expect "FO-031 control: the live reply succeeds (not a shared refusal)"
    (liveReplyLeg diffB diffA msg ist.state).toOption.isSome
  expect "FO-031 control: and so does the frozen one"
    (frozenEndpointReply diffB diffA rid msg (freeze ist)).toOption.isSome
  expect "FO-031: the frozen reply agrees with the live reply"
    (frozenRunAgrees unitResultAgrees
      (frozenEndpointReply diffB diffA rid msg (freeze ist))
      (liveWithTaint .reply diffB (SeLe4n.CPtr.ofNat 0)
        (liveReplyLeg diffB diffA msg) ist.state))
  -- **The delegated half, at the leg** (PR #895 review round 22's sweep).  The
  -- frozen leg accepts a replier who is not the recorded server, and so does the
  -- live leg the kernel dispatches; the BARE `endpointReply` refuses it, which is
  -- why naming that one as the counterpart overstated agreement here too.
  let delegatedLeg := diffAddReply (diffAddTcb (diffAddTcb (diffAddTcb
    (diffAddEndpoint mkEmptyIntermediateState diffEpId {}) caller) (diffTcb 63))
    (diffTcb 65)) rid { replyId := rid, caller := some diffA }
  expect "FO-031 control: the live leg accepts a DELEGATED replier"
    (liveReplyLeg diffDelegate diffA msg delegatedLeg.state).toOption.isSome
  expect "FO-031 control: and the BARE single-core reply refuses it"
    (SeLe4n.Kernel.endpointReply diffDelegate diffA msg delegatedLeg.state).toOption.isNone
  expect "FO-031: the frozen leg agrees with the live leg when DELEGATED"
    (frozenRunAgrees unitResultAgrees
      (frozenEndpointReply diffDelegate diffA rid msg (freeze delegatedLeg))
      (liveWithTaint .reply diffDelegate (SeLe4n.CPtr.ofNat 0)
        (liveReplyLeg diffDelegate diffA msg) delegatedLeg.state))

/-- FO-041 (PR #895 review round 15): **the whole `.reply` OPERATION, against
`endpointReplyWithDonation`.**

FO-031 above compares the frozen reply against the bare `endpointReply` — a
**leg**.  The live `.reply` operation is that leg followed by the donation
return and a priority-inheritance revert, and nothing compared the frozen
composite against it, so the coverage table read "reply: checked" through three
consecutive review rounds in which the composite was found to be missing the
donation pop, then the server's deschedule, then the inheritance revert.  A
leg-level agreement is not an operation-level one, and
`frozenBranchOperationChecked` now states the difference; this scenario is what
makes its one `true` row honest.

Two halves, because the two divergences this round found fail differently.  The
first gives the recorded server an inherited boost, so a composite that skips
the revert leaves a `pipBoost` the live one clears — a TCB-field disagreement
`frozenStateAgrees` sees.  The second drops the recorded server from the
caller's `ipcState`, where the live operation refuses and a composite missing
the guard succeeds — a disagreement only the refusal half of `frozenRunAgrees`
can see, which is why that half exists.

**...and against WHICH live operation** (PR #895 review round 22).  This compared
the frozen composite against `endpointReplyWithDonation` — the *single-core*
donation-aware reply, which has no production caller and whose bare reply leg
refuses a delegated reply-cap holder.  The live `.reply` arm routes through
`endpointReplyCrossCoreDispatch`, which accepts one (PR #822 review 6J-lYm), and
so does `frozenEndpointReply`.  The two counterparts coincide only when the
replier **is** the recorded server, which every fixture here was — so the claim
read as agreement with the kernel while being agreement with a superseded sibling.

The comparison is `liveReplySpine` now, and the third half is the delegated shape
that separates them: a replier holding the caller's reply capability while the
`ipcState` records someone else.  Its control asserts the superseded composite
**refuses** exactly that input, so the choice of counterpart is measured here and
not merely named — the Lean pair
`endpointReplyCrossCoreDispatch_independent_of_replier` /
`endpointReplyWithDonation_refuses_delegated_replier` is the general form. -/
private def differentialEndpointReplyOperationAgrees : IO Unit := do
  let msg : IpcMessage := { registers := #[⟨13⟩], caps := #[], badge := none }
  let rid : SeLe4n.ReplyId := ⟨505⟩
  let caller : TCB := { diffTcb 62 with
    ipcState := .blockedOnReply diffEpId (some diffB), replyObject := some rid }
  -- The server has inherited the caller's priority; answering the caller is
  -- what makes that boost stale.
  let server : TCB := { diffTcb 63 with pipBoost := some ⟨200⟩ }
  let ist := diffAddReply (diffAddTcb (diffAddTcb
    (diffAddEndpoint mkEmptyIntermediateState diffEpId {}) caller) server)
    rid { replyId := rid, caller := some diffA }
  -- Control: the operation really runs on both sides, so the agreement below is
  -- about a delivered reply rather than a shared refusal.
  expect "FO-041 control: the live reply operation succeeds"
    (liveReplySpine diffB diffA msg ist.state).toOption.isSome
  expect "FO-041 control: and so does the frozen composite"
    (frozenEndpointReplyWithDonationReturn diffB diffA rid msg (freeze ist)).toOption.isSome
  -- ...and the boost really is there to begin with, so the comparison is about
  -- a reversion that happened rather than a field that was already `none`.
  expect "FO-041 control: the server starts with an inherited boost"
    (match (freeze ist).getTcb? diffB with
     | some t => t.pipBoost == some ⟨200⟩
     | none   => false)
  expect "FO-041: the frozen reply OPERATION agrees with the live one"
    (frozenRunAgrees unitResultAgrees
      (frozenEndpointReplyWithDonationReturn diffB diffA rid msg (freeze ist))
      (liveWithTaint .reply diffB (SeLe4n.CPtr.ofNat 0)
        (liveReplySpine diffB diffA msg) ist.state))
  -- The refusal half: a caller whose `ipcState` records no server at all.  Both
  -- sides must decline it with the same error — the live one has since AK1-B
  -- (I-H02), which rated letting a reply through there a confused-deputy risk.
  let unrecorded : TCB := { diffTcb 62 with
    ipcState := .blockedOnReply diffEpId none, replyObject := some rid }
  let ist' := diffAddReply (diffAddTcb (diffAddTcb
    (diffAddEndpoint mkEmptyIntermediateState diffEpId {}) unrecorded) (diffTcb 63))
    rid { replyId := rid, caller := some diffA }
  expect "FO-041: both refuse a caller with no recorded server"
    (frozenRunAgrees unitResultAgrees
      (frozenEndpointReplyWithDonationReturn diffB diffA rid msg (freeze ist'))
      (liveWithTaint .reply diffB (SeLe4n.CPtr.ofNat 0)
        (liveReplySpine diffB diffA msg) ist'.state))
  expect "FO-041 control: and the live side really refuses (not a shared success)"
    (liveReplySpine diffB diffA msg ist'.state).toOption.isNone
  -- **The delegated half** (PR #895 review round 22): the replier holds the
  -- caller's reply capability without being the recorded server.  `diffDelegate`
  -- is a third thread, so `replier ≠ expected` and the two candidate live
  -- counterparts part company here.
  let boosted : TCB := { diffTcb 63 with pipBoost := some ⟨200⟩ }
  let delegated := diffAddReply (diffAddTcb (diffAddTcb (diffAddTcb
    (diffAddEndpoint mkEmptyIntermediateState diffEpId {}) caller) boosted)
    (diffTcb 65)) rid { replyId := rid, caller := some diffA }
  expect "FO-041 control: the live spine accepts a DELEGATED replier"
    (liveReplySpine diffDelegate diffA msg delegated.state).toOption.isSome
  expect "FO-041 control: and so does the frozen composite"
    (frozenEndpointReplyWithDonationReturn diffDelegate diffA rid msg
      (freeze delegated)).toOption.isSome
  -- ...and the superseded single-core composite REFUSES it, which is what makes
  -- the choice of counterpart a measurement rather than a name.  Were the claim
  -- still stated against it, the row would be false on exactly this shape.
  expect "FO-041 control: the superseded single-core composite refuses it"
    (SeLe4n.Kernel.endpointReplyWithDonation diffDelegate diffA msg
      delegated.state).toOption.isNone
  expect "FO-041: the frozen composite agrees with the live spine when DELEGATED"
    (frozenRunAgrees unitResultAgrees
      (frozenEndpointReplyWithDonationReturn diffDelegate diffA rid msg (freeze delegated))
      (liveWithTaint .reply diffDelegate (SeLe4n.CPtr.ofNat 0)
        (liveReplySpine diffDelegate diffA msg) delegated.state))

/-- FO-042 (**WS-HP HP8.1**): **the operation with a donation actually on the
stack**, and the state on which the two candidate triggers part company.

FO-041 above compares the whole `.reply` operation, and through four review
rounds not one of its halves gave the recorded server a `.donated` binding — so
the donation pop the round-13 finding *added to this surface* has never been
executed by a differential, on either side.  A leg that is never taken is not
compared; that is this project's own *a witness drawn from a finding tests the
finding*, one level in: the fixtures grew to exhibit delegation, a stale boost and
a missing guard, and nobody went back and made the pop fire.

The two halves here are the pop and its trigger.

**The pop.**  The answered caller's Reply *heads* the donated context and the
context names it back, so both surfaces resolve a holder and hand the reservation
to the answered caller.  The controls assert the pre-state really is donating and
the post-state really moved it — agreement between two identities would otherwise
read exactly like agreement between two pops.

**The trigger.**  `HP4` made the live operation read the answered **frame**
(`replyFrameHeadHolder?`) where it had read the recorded server's `.donated`
binding, and until HP8.1 this surface still read the binding.  The second half is
a state where those two readings **disagree**: the server holds a donation and
the answered frame heads nothing.  The retired reading would pop here; the live
operation does not, and the frozen composite must not either.  The assertions
name both facts, so the choice of trigger is measured rather than described —
and that is also the mutation that decides it, since it keeps every token of the
donation and changes only which artefact records the stack. -/
private def differentialEndpointReplyDonationAgrees : IO Unit := do
  let msg : IpcMessage := { registers := #[⟨17⟩], caps := #[], badge := none }
  let rid : SeLe4n.ReplyId := ⟨506⟩
  -- The answered caller: blocked on its reply, holding the frame, and `.unbound`
  -- because it donated its context away at the `Call`.
  let caller : TCB := { diffTcb 62 with
    ipcState := .blockedOnReply diffEpId (some diffB), replyObject := some rid,
    schedContextBinding := SeLe4n.Kernel.SchedContextBinding.unbound }
  -- The recorded server: holds the donation, runnable, and carrying the boost the
  -- reversion must clear, so the two live steps are both observable.
  let server : TCB := { diffTcb 63 with
    pipBoost := some ⟨200⟩, schedContextBinding := .donated diffScId diffA }
  -- ### Half one: the frame HEADS the context, so both sides pop.
  let heading := diffAddSchedContext (diffAddReply (diffAddTcb (diffAddTcb
    (diffAddEndpoint mkEmptyIntermediateState diffEpId {}) caller) server)
    rid { replyId := rid, caller := some diffA, next := some (.head diffScId) })
    diffScId (diffDonatedSc (some rid))
  expect "FO-042 control: the answered frame heads the donated context"
    (SeLe4n.Kernel.replyFrameHeadHolder? heading.state rid == some (diffScId, diffB))
  expect "FO-042 control: ...and the frozen surface reads the same frame"
    (frozenReplyFrameHeadHolder? (freeze heading) rid == some (diffScId, diffB))
  expect "FO-042 control: the recorded server starts holding the donation"
    (match (freeze heading).getTcb? diffB with
     | some t => t.schedContextBinding == .donated diffScId diffA
     | none   => false)
  expect "FO-042 control: the live operation succeeds"
    (liveReplySpine diffB diffA msg heading.state).toOption.isSome
  expect "FO-042 control: and so does the frozen composite"
    (frozenEndpointReplyWithDonationReturn diffB diffA rid msg (freeze heading)).toOption.isSome
  -- The pop really happened: the reservation is back on its owner and the holder
  -- is unbound.  Asserted on the LIVE side, so the agreement below is agreement
  -- with a pop rather than between two no-ops.
  expect "FO-042: the live pop returns the context to the answered caller"
    (match (liveReplySpine diffB diffA msg heading.state).toOption with
     | some (_, post) =>
         (match post.getTcb? diffA with
          | some t => t.schedContextBinding == .bound diffScId
          | none   => false) &&
         (match post.getTcb? diffB with
          | some t => t.schedContextBinding == SeLe4n.Kernel.SchedContextBinding.unbound
          | none   => false)
     | none => false)
  expect "FO-042: the frozen reply OPERATION agrees with the live one, donation and all"
    (frozenRunAgrees unitResultAgrees
      (frozenEndpointReplyWithDonationReturn diffB diffA rid msg (freeze heading))
      (liveWithTaint .reply diffB (SeLe4n.CPtr.ofNat 0)
        (liveReplySpine diffB diffA msg) heading.state))
  -- ### Half two: the TRIGGERS DISAGREE.  Same donation, no stack frame.
  let unheaded := diffAddSchedContext (diffAddReply (diffAddTcb (diffAddTcb
    (diffAddEndpoint mkEmptyIntermediateState diffEpId {}) caller) server)
    rid { replyId := rid, caller := some diffA })
    diffScId (diffDonatedSc none)
  expect "FO-042 control: the binding-driven reading FIRES here (the server is donated)"
    (match (freeze unheaded).getTcb? diffB with
     | some t => t.schedContextBinding == .donated diffScId diffA
     | none   => false)
  expect "FO-042 control: ...while the head-driven reading does NOT (no frame heads it)"
    (SeLe4n.Kernel.replyFrameHeadHolder? unheaded.state rid == none
      && frozenReplyFrameHeadHolder? (freeze unheaded) rid == none)
  expect "FO-042: the live operation performs no pop on that state"
    (match (liveReplySpine diffB diffA msg unheaded.state).toOption with
     | some (_, post) =>
         match post.getTcb? diffB with
         | some t => t.schedContextBinding == .donated diffScId diffA
         | none   => false
     | none => false)
  expect "FO-042: and the frozen composite follows the LIVE trigger, not the retired one"
    (frozenRunAgrees unitResultAgrees
      (frozenEndpointReplyWithDonationReturn diffB diffA rid msg (freeze unheaded))
      (liveWithTaint .reply diffB (SeLe4n.CPtr.ofNat 0)
        (liveReplySpine diffB diffA msg) unheaded.state))
  -- ### Half three: the RECIPIENT GUARD.  Same donation on the stack, but the
  -- answered caller has acquired a reservation of its own while blocked, so the
  -- pop would overwrite it.  The live pop refuses (`donationRecipientAcceptable`,
  -- WS-HP HP4.6) and the frozen one must too — a mirror missing a live guard
  -- succeeds where the kernel refuses, which is the direction that matters.
  -- The guard is head-driven-specific: under the binding-driven reading the
  -- recipient was the binding's own recorded owner, which the operation had
  -- already seen hold nothing, so this half could not have existed before HP4.
  let ownCaller : TCB := { diffTcb 62 with
    ipcState := .blockedOnReply diffEpId (some diffB), replyObject := some rid,
    schedContextBinding := .bound diffOwnScId }
  let bound := diffAddSchedContext (diffAddSchedContext (diffAddReply (diffAddTcb (diffAddTcb
    (diffAddEndpoint mkEmptyIntermediateState diffEpId {}) ownCaller) server)
    rid { replyId := rid, caller := some diffA, next := some (.head diffScId) })
    diffScId (diffDonatedSc (some rid))) diffOwnScId diffCallerOwnSc
  expect "FO-042 control: the trigger still fires on this state"
    (SeLe4n.Kernel.replyFrameHeadHolder? bound.state rid == some (diffScId, diffB)
      && frozenReplyFrameHeadHolder? (freeze bound) rid == some (diffScId, diffB))
  expect "FO-042 control: ...and the answered caller already holds a reservation"
    (match (freeze bound).getTcb? diffA with
     | some t => t.schedContextBinding == .bound diffOwnScId
     | none   => false)
  expect "FO-042: the live pop REFUSES to overwrite it"
    (liveReplySpine diffB diffA msg bound.state).toOption.isNone
  expect "FO-042: and the frozen composite refuses it too, with the same error"
    (frozenRunAgrees unitResultAgrees
      (frozenEndpointReplyWithDonationReturn diffB diffA rid msg (freeze bound))
      (liveWithTaint .reply diffB (SeLe4n.CPtr.ofNat 0)
        (liveReplySpine diffB diffA msg) bound.state))
  -- ### Half four: the SENTINEL HOLDER.  A SchedContext bound to thread 0 is a
  -- malformed state no live invariant admits — and `Model.freeze` would copy one
  -- verbatim, which is what this surface's guards exist for.  The live pop
  -- promotes the holder through `ThreadId.toValid?` and answers
  -- `.invalidArgument`; the frozen one refuses on `holder.isReserved`, which is
  -- the same condition in this surface's own vocabulary (`frozenLookupTcb` is
  -- defined by it, and `isReserved` is exactly `= sentinel`).
  let sentinelSc : SeLe4n.Kernel.SchedContext :=
    { diffDonatedSc (some rid) with boundThread := some ⟨0⟩ }
  let sentinelHeld := diffAddSchedContext (diffAddReply (diffAddTcb (diffAddTcb
    (diffAddEndpoint mkEmptyIntermediateState diffEpId {}) caller) server)
    rid { replyId := rid, caller := some diffA, next := some (.head diffScId) })
    diffScId sentinelSc
  expect "FO-042 control: the trigger resolves a SENTINEL holder on both surfaces"
    (SeLe4n.Kernel.replyFrameHeadHolder? sentinelHeld.state rid == some (diffScId, ⟨0⟩)
      && frozenReplyFrameHeadHolder? (freeze sentinelHeld) rid == some (diffScId, ⟨0⟩))
  expect "FO-042: the live pop refuses a sentinel holder"
    (liveReplySpine diffB diffA msg sentinelHeld.state).toOption.isNone
  expect "FO-042: and the frozen composite refuses it with the same error"
    (frozenRunAgrees unitResultAgrees
      (frozenEndpointReplyWithDonationReturn diffB diffA rid msg (freeze sentinelHeld))
      (liveWithTaint .reply diffB (SeLe4n.CPtr.ofNat 0)
        (liveReplySpine diffB diffA msg) sentinelHeld.state))

/-- FO-043 (**WS-HP HP8.2**): **a MIDDLE frame**, which is the only shape on which
splicing and severing differ.

HP8.2 makes the frozen removal splice, and every scenario above kept passing
byte-identically when it did — which is the finding, not the reassurance.  A
two-frame stack's lower frame is its *bottom*, so both policies write the same
value into the frame above; the whole of FO-031 and FO-041/042 sits on stacks of
depth ≤ 2, so none of them can tell a spliced removal from a severed one.  Landing
HP8 on their evidence would have been HP5.5's gap on this surface: *a sweep for
fixtures that would break is not a sweep for fixtures that would exercise, and
only the second measures a flip.*

**The shape.**  Three frames, bottom → cut → top, with the *cut* frame the one
the reply answers:

* `bottomRid` is the bottom: `prev = none`, `next = some (.frame midRid)`.
* `midRid` is the answered caller's own reply object: `prev = some bottomRid`,
  `next = some (.frame topRid)`.
* `topRid` heads the donated context, and the context names it back.

So the removal takes a frame out of the middle.  After a **splice** the top frame
names the bottom and the bottom names the top back — the stack stays connected and
the reservation goes on travelling outward.  After a **sever** the top frame's
`prev` is cleared and the bottom is dropped from the stack for good, which is the
loss WS-HP exists to close.  The two write different values at two different keys,
so the assertions below discriminate; the last one is the mutation that decides it,
since it spells the retired sever's own values.

**No pop fires here, and that is correct.**  The cut frame heads nothing — the
*top* frame does — so `frozenReplyFrameHeadHolder?` answers `none` and the
donation stays where it is.  A middle reply removes a frame and moves no
reservation, which is exactly why the removal's connectivity is the whole content
of this scenario.

**And the splice's THIRD store is not observable through the composite, which is
why the last half asserts it on the primitive.**  Measured rather than assumed:
with `rid.prev := none` deleted the whole suite still passes, because the
`Reply.consumed` that follows clears the cut frame's links anyway on a frame that
heads nothing.  So an assertion about the cut frame's `prev` taken from the
composite's post-state is testing `consumed`, not the splice — an inert witness
reading as coverage, which is this project's own hazard.  The store is
load-bearing all the same (it is seL4's `reply_unlink` downward half, and without
it the cut frame keeps a `prev` nothing names back), and it would become
*observable* the moment `consumed` changed, so the half below drives
`frozenSpliceReplyFrameOut` directly with no consume after it. -/
private def differentialEndpointReplyMiddleFrameSplices : IO Unit := do
  let msg : IpcMessage := { registers := #[⟨17⟩], caps := #[], badge := none }
  let bottomRid : SeLe4n.ReplyId := ⟨507⟩
  let midRid    : SeLe4n.ReplyId := ⟨508⟩
  let topRid    : SeLe4n.ReplyId := ⟨509⟩
  -- The answered caller holds the MIDDLE frame.
  let caller : TCB := { diffTcb 62 with
    ipcState := .blockedOnReply diffEpId (some diffB), replyObject := some midRid,
    schedContextBinding := SeLe4n.Kernel.SchedContextBinding.unbound }
  -- The recorded server, holding the donation the TOP frame heads.
  let server : TCB := { diffTcb 63 with
    schedContextBinding := .donated diffScId diffA }
  let chain := diffAddSchedContext (diffAddReply (diffAddReply (diffAddReply
    (diffAddTcb (diffAddTcb (diffAddEndpoint mkEmptyIntermediateState diffEpId {})
      caller) server)
    bottomRid { replyId := bottomRid, caller := some diffDelegate,
                next := some (.frame midRid) })
    midRid { replyId := midRid, caller := some diffA, prev := some bottomRid,
             next := some (.frame topRid) })
    topRid { replyId := topRid, caller := some diffB, prev := some midRid,
             next := some (.head diffScId) })
    diffScId { diffDonatedSc (some topRid) with scReply := some topRid }
  -- The pre-state really is a three-frame stack, on both surfaces.
  expect "FO-043 control: the cut frame sits between two others (live)"
    (match chain.state.getReply? midRid with
     | some r => r.prev == some bottomRid && r.next == some (SeLe4n.Kernel.ReplyStackLink.frame topRid)
     | none   => false)
  expect "FO-043 control: ...and the frozen copy carries the same links"
    (match (freeze chain).getReply? midRid with
     | some r => r.prev == some bottomRid && r.next == some (SeLe4n.Kernel.ReplyStackLink.frame topRid)
     | none   => false)
  -- The cut frame heads NOTHING: the top frame does, so no pop fires and the
  -- removal's connectivity is the whole of what this scenario measures.
  expect "FO-043 control: the cut frame heads no context, so no pop fires"
    (SeLe4n.Kernel.replyFrameHeadHolder? chain.state midRid == none
      && frozenReplyFrameHeadHolder? (freeze chain) midRid == none)
  expect "FO-043 control: the live operation succeeds"
    (liveReplySpine diffB diffA msg chain.state).toOption.isSome
  expect "FO-043 control: and so does the frozen composite"
    (frozenEndpointReplyWithDonationReturn diffB diffA midRid msg (freeze chain)).toOption.isSome
  -- **The live side really splices.**  Asserted here so the agreement below is
  -- agreement with a splice rather than between two severs.
  expect "FO-043: the live removal SPLICES — the top frame names the bottom"
    (match (liveReplySpine diffB diffA msg chain.state).toOption with
     | some (_, post) =>
         (match post.getReply? topRid with
          | some t => t.prev == some bottomRid
          | none   => false) &&
         (match post.getReply? bottomRid with
          | some b => b.next == some (SeLe4n.Kernel.ReplyStackLink.frame topRid)
          | none   => false) &&
         (match post.getReply? midRid with
          | some m => m.prev == none
          | none   => false)
     | none => false)
  -- ...and the frozen composite agrees with it, link for link.
  expect "FO-043: the frozen removal splices the same way"
    (match (frozenEndpointReplyWithDonationReturn diffB diffA midRid msg
              (freeze chain)).toOption with
     | some (_, post) =>
         (match post.getReply? topRid with
          | some t => t.prev == some bottomRid
          | none   => false) &&
         (match post.getReply? bottomRid with
          | some b => b.next == some (SeLe4n.Kernel.ReplyStackLink.frame topRid)
          | none   => false) &&
         (match post.getReply? midRid with
          | some m => m.prev == none
          | none   => false)
     | none => false)
  expect "FO-043: and the whole frozen OPERATION agrees with the live one"
    (frozenRunAgrees unitResultAgrees
      (frozenEndpointReplyWithDonationReturn diffB diffA midRid msg (freeze chain))
      (liveWithTaint .reply diffB (SeLe4n.CPtr.ofNat 0)
        (liveReplySpine diffB diffA msg) chain.state))
  -- **NEGATIVE — the retired sever's own values**, spelled so that a revert of
  -- HP8.2 fails here rather than passing quietly.  Under the sever the top
  -- frame's `prev` is cleared and the bottom frame keeps naming the cut frame it
  -- can no longer reach, which is the state that drops every frame below a cut.
  expect "FO-043 NEGATIVE: the frozen removal does NOT sever the top frame"
    (match (frozenEndpointReplyWithDonationReturn diffB diffA midRid msg
              (freeze chain)).toOption with
     | some (_, post) =>
         !(match post.getReply? topRid with
           | some t => t.prev == none
           | none   => false)
     | none => false)
  expect "FO-043 NEGATIVE: ...nor leaves the bottom frame naming the cut frame"
    (match (frozenEndpointReplyWithDonationReturn diffB diffA midRid msg
              (freeze chain)).toOption with
     | some (_, post) =>
         !(match post.getReply? bottomRid with
           | some b => b.next == some (SeLe4n.Kernel.ReplyStackLink.frame midRid)
           | none   => false)
     | none => false)
  -- ### The primitive, with no consume after it.
  --
  -- All three stores at once, where the composite can only show two: the cut
  -- frame's own `prev := none` is the store `Reply.consumed` would mask, so this
  -- is the only place a deletion of it fails.  The live counterpart is asserted
  -- beside it, so the two are compared store for store rather than each against
  -- its own expectation.
  expect "FO-043: the frozen PRIMITIVE writes all three links, the cut frame's own included"
    (match (frozenSpliceReplyFrameOut (freeze chain) midRid).toOption with
     | some post =>
         (match post.getReply? topRid with
          | some t => t.prev == some bottomRid
          | none   => false) &&
         (match post.getReply? bottomRid with
          | some b => b.next == some (SeLe4n.Kernel.ReplyStackLink.frame topRid)
          | none   => false) &&
         (match post.getReply? midRid with
          | some m => m.prev == none && m.next == some (SeLe4n.Kernel.ReplyStackLink.frame topRid)
          | none   => false)
     | none => false)
  expect "FO-043: ...exactly as the live primitive does"
    (match (SeLe4n.Kernel.spliceReplyFrameOut chain.state midRid).toOption with
     | some post =>
         (match post.getReply? topRid with
          | some t => t.prev == some bottomRid
          | none   => false) &&
         (match post.getReply? bottomRid with
          | some b => b.next == some (SeLe4n.Kernel.ReplyStackLink.frame topRid)
          | none   => false) &&
         (match post.getReply? midRid with
          | some m => m.prev == none && m.next == some (SeLe4n.Kernel.ReplyStackLink.frame topRid)
          | none   => false)
     | none => false)

/-- FO-044 (**WS-HP HP10.8**): **the pop's recipient is the recorded ORIGIN**, on
a state where that is not the answered caller.

HP10.7 flipped the live arm and this scenario is why the frozen arm had to flip
with it: `frozenBranchOperationChecked .endpointReplyToBlockedCaller = true` is a
machine-checked claim that the two programs are run beside each other, and a
window in which the live one redirects and the mirror does not makes that claim an
over-claim rather than a failing test — every existing scenario keeps passing,
because none of them records an origin that differs from the answered caller.

**Two halves, and the second is what makes the first decisive.**  A selector that
fired unconditionally — handing the reservation to whatever the origin field says
regardless of the guards — would pass a half that only checks "the origin gets
it", so the second half fixes the origin *at* the answered caller and requires the
identity.  That is the shape §3.9b was built against, one surface over.

The stack is a single frame, which is the bottom of its own stack: the redirect
fires exactly there (`donationOriginRecipient?` answers only at
`replyStackOuterCaller? = .ok none`), and it is the depth-2 residue's shape after
the client's frame has been removed. -/
private def differentialEndpointReplyRedirectsToOrigin : IO Unit := do
  let rid : SeLe4n.ReplyId := SeLe4n.ReplyId.ofNat 71
  let msg : IpcMessage := { registers := #[], caps := #[], badge := Badge.ofNatMasked 0 }
  -- The answered caller: reply-blocked on the recorded server, holding nothing.
  let caller : TCB := { diffTcb 62 with
    ipcState := .blockedOnReply diffEpId (some diffB), replyObject := some rid,
    schedContextBinding := SeLe4n.Kernel.SchedContextBinding.unbound }
  -- The recorded server, holding the donation.
  let server : TCB := { diffTcb 63 with
    schedContextBinding := .donated diffScId diffA }
  -- **The origin**: a thread whose own frame left the stack, so it is awake, holds
  -- nothing, and is on no stack.  Both guards admit it — which is the state the
  -- depth-2 defect leaves behind.
  let origin : TCB := { diffTcb 65 with
    schedContextBinding := SeLe4n.Kernel.SchedContextBinding.unbound }
  -- ### Half one: the origin DIFFERS from the answered caller.
  let redirected := diffAddSchedContext (diffAddReply (diffAddTcb (diffAddTcb (diffAddTcb
    (diffAddEndpoint mkEmptyIntermediateState diffEpId {}) caller) server) origin)
    rid { replyId := rid, caller := some diffA, next := some (.head diffScId) })
    diffScId { diffDonatedSc (some rid) with donationOrigin := some diffDelegate }
  expect "FO-044 control: the answered frame heads the donated context"
    (SeLe4n.Kernel.replyFrameHeadHolder? redirected.state rid == some (diffScId, diffB))
  expect "FO-044 control: ...and it is the BOTTOM of its stack, where the redirect fires"
    (match SeLe4n.Kernel.replyStackOuterCaller? redirected.state diffScId with
     | .ok none => true
     | _        => false)
  expect "FO-044 control: the recorded origin is NOT the answered caller"
    (!(diffDelegate == diffA))
  -- **The live arm redirects** (HP10.7), asserted here so the agreement below is
  -- agreement with a redirect rather than between two unredirected pops.
  expect "FO-044: the live resolver answers the recorded origin"
    (SeLe4n.Kernel.donationOriginRecipient? redirected.state diffScId == some diffDelegate)
  expect "FO-044: ...and so does the frozen one"
    (frozenDonationOriginRecipient? (freeze redirected) diffScId == some diffDelegate)
  expect "FO-044 control: the live operation succeeds"
    (liveReplySpine diffB diffA msg redirected.state).toOption.isSome
  expect "FO-044 control: and so does the frozen composite"
    (frozenEndpointReplyWithDonationReturn diffB diffA rid msg (freeze redirected)).toOption.isSome
  -- **PAYOFF**: the reservation settles on the ORIGIN, on both surfaces — not on
  -- the answered caller, which is what stack reachability alone would name.
  expect "FO-044: the live pop binds the context to the ORIGIN"
    (match (liveReplySpine diffB diffA msg redirected.state).toOption with
     | some (_, post) =>
         (match post.getTcb? diffDelegate with
          | some t => t.schedContextBinding == .bound diffScId
          | none   => false)
     | none => false)
  expect "FO-044: ...and the frozen pop binds it to the same thread"
    (match (frozenEndpointReplyWithDonationReturn diffB diffA rid msg
              (freeze redirected)).toOption with
     | some (_, post) =>
         (match post.getTcb? diffDelegate with
          | some t => t.schedContextBinding == .bound diffScId
          | none   => false)
     | none => false)
  -- NEGATIVE: and the answered caller does NOT receive it, on either surface.  A
  -- mirror that ignored the origin would bind `diffA` and pass every control above.
  expect "FO-044 NEGATIVE: the answered caller is left unbound (live)"
    (match (liveReplySpine diffB diffA msg redirected.state).toOption with
     | some (_, post) =>
         (match post.getTcb? diffA with
          | some t => t.schedContextBinding == SeLe4n.Kernel.SchedContextBinding.unbound
          | none   => false)
     | none => false)
  expect "FO-044 NEGATIVE: ...and unbound on the frozen surface too"
    (match (frozenEndpointReplyWithDonationReturn diffB diffA rid msg
              (freeze redirected)).toOption with
     | some (_, post) =>
         (match post.getTcb? diffA with
          | some t => t.schedContextBinding == SeLe4n.Kernel.SchedContextBinding.unbound
          | none   => false)
     | none => false)
  expect "FO-044: and the whole frozen OPERATION agrees with the live one"
    (frozenRunAgrees unitResultAgrees
      (frozenEndpointReplyWithDonationReturn diffB diffA rid msg (freeze redirected))
      (liveWithTaint .reply diffB (SeLe4n.CPtr.ofNat 0)
        (liveReplySpine diffB diffA msg) redirected.state))
  -- ### Half two: the origin IS the answered caller, so the redirect is the
  -- identity.  A selector that fired unconditionally passes half one and breaks
  -- this, which is what makes the pair decisive rather than merely green.
  let sameOrigin := diffAddSchedContext (diffAddReply (diffAddTcb (diffAddTcb (diffAddTcb
    (diffAddEndpoint mkEmptyIntermediateState diffEpId {}) caller) server) origin)
    rid { replyId := rid, caller := some diffA, next := some (.head diffScId) })
    diffScId { diffDonatedSc (some rid) with donationOrigin := some diffA }
  -- **The resolver DECLINES here, and that is the point.**  The answered caller is
  -- `.blockedOnReply` at the state the resolver reads — it is waiting on this very
  -- reply — so `donationOriginRebindable` refuses it and the recipient comes from
  -- the FALLBACK rather than from the origin field.  The outcome is the same
  -- thread by a different route, which is exactly what makes this half
  -- discriminating: a selector that fired unconditionally would answer
  -- `some diffA`, pass every outcome assertion, and fail this one.
  expect "FO-044 half two: the resolver DECLINES a reply-blocked origin"
    (frozenDonationOriginRecipient? (freeze sameOrigin) diffScId == none
      && SeLe4n.Kernel.donationOriginRecipient? sameOrigin.state diffScId == none)
  expect "FO-044 half two: ...so the recipient is the answered caller by FALLBACK, on both surfaces"
    (SeLe4n.Kernel.replyDonationRecipient sameOrigin.state diffScId diffA == diffA
      && frozenReplyDonationRecipient (freeze sameOrigin) diffScId diffA == diffA)
  expect "FO-044 half two: the answered caller receives the reservation (frozen)"
    (match (frozenEndpointReplyWithDonationReturn diffB diffA rid msg
              (freeze sameOrigin)).toOption with
     | some (_, post) =>
         (match post.getTcb? diffA with
          | some t => t.schedContextBinding == .bound diffScId
          | none   => false)
     | none => false)
  expect "FO-044 half two: and the operations still agree"
    (frozenRunAgrees unitResultAgrees
      (frozenEndpointReplyWithDonationReturn diffB diffA rid msg (freeze sameOrigin))
      (liveWithTaint .reply diffB (SeLe4n.CPtr.ofNat 0)
        (liveReplySpine diffB diffA msg) sameOrigin.state))

/-- FO-035: **a receive that dequeues a `.blockedOnCall` caller** (PR #873
round 17).

`frozenQueuePopHead` accepts a `.blockedOnCall` head as well as a
`.blockedOnSend` one, and the frozen receive woke both -- `.ready`, back in the
run queue.  A caller does not become runnable at rendezvous: the live
`endpointReceiveDual` moves it to `.blockedOnReply` and links it to the
server-supplied reply object.  The branch was unreachable from the suite because
FO-029's queued sender is `.blockedOnSend`, and the coverage row said `.receive`
was checked.

The control asserts both sides succeed, so the agreement is about a completed
rendezvous rather than a shared refusal. -/
private def differentialReceiveFromBlockedCallerAgrees : IO Unit := do
  let msg : IpcMessage := { registers := #[⟨21⟩], caps := #[], badge := none }
  let rid : SeLe4n.ReplyId := ⟨506⟩
  let ep : Endpoint := { sendQ := { head := some diffA, tail := some diffA }, receiveQ := {} }
  let parkedCaller : TCB := { diffTcb 62 with ipcState := .blockedOnCall diffEpId, pendingMessage := some msg, queuePPrev := some .endpointHead }
  let ist := diffAddReply (diffAddTcb (diffAddTcb
    (diffAddEndpoint (diffAddCSpace mkEmptyIntermediateState
      [(SeLe4n.Slot.ofNat 0, diffObjCap diffEpId)]) diffEpId ep) parkedCaller) (diffTcb 63))
    rid { replyId := rid, caller := none }
  expect "FO-035 control: the live receive completes the call rendezvous"
    (SeLe4n.Kernel.endpointReceiveDual diffEpId diffB (some rid) ist.state).toOption.isSome
  expect "FO-035 control: and so does the frozen one"
    (frozenEndpointReceive diffEpId diffB (some rid) (freeze ist)).toOption.isSome
  expect "FO-035: the dequeued caller is parked for reply, not woken"
    (frozenRunAgrees (fun a b => a == b)
      (frozenEndpointReceive diffEpId diffB (some rid) (freeze ist))
      (liveWithTaint .receive diffB (SeLe4n.CPtr.ofNat 0)
        (SeLe4n.Kernel.endpointReceiveDual diffEpId diffB (some rid)) ist.state))
  -- And the fail-closed half: a call rendezvous with no reply object must be
  -- refused on both sides rather than stranding the caller `.blockedOnReply`.
  expect "FO-035: both refuse a call rendezvous carrying no reply object"
    (frozenRunAgrees (fun a b => a == b)
      (frozenEndpointReceive diffEpId diffB none (freeze ist))
      (liveWithTaint .receive diffB (SeLe4n.CPtr.ofNat 0)
        (SeLe4n.Kernel.endpointReceiveDual diffEpId diffB none) ist.state))

/-- The same signal, from an actor that **carries provenance**.

With every taint empty the comparison above says nothing about the provenance
step: an omitted or misdirected one is invisible.  Seeding the signalling
thread's tag makes the step observable, so this is what stops the like-layer
composition from being decoration. -/
private def differentialTaintedSignalAgrees : IO Unit := do
  let badge := SeLe4n.Badge.ofNatMasked 77
  let ep : Endpoint := { sendQ := {}, receiveQ := { head := some diffA, tail := some diffA } }
  let ntfn : Notification :=
    { state := .idle, waitingThreads := SeLe4n.NoDupList.empty, pendingBadge := none,
      boundTCB := some diffA }
  let boundTcb : TCB := { diffTcb 62 with ipcState := .blockedOnReceive diffEpId, queuePPrev := some .endpointHead }
  let ist0 := diffAddTcb (diffAddTcb (diffAddNotification
    (diffAddEndpoint (diffAddCSpace mkEmptyIntermediateState
        [(SeLe4n.Slot.ofNat 0, diffObjCap diffNotifId)]) diffEpId ep)
      diffNotifId ntfn) boundTcb) (diffTcb 63)
  -- The signaller carries a tag.  `declassificationTaint` is named by none of
  -- the four builder obligations, so seeding it leaves every proof unchanged.
  let tagged : SeLe4n.Kernel.DeclassificationTaint :=
    SeLe4n.Kernel.DeclassificationTaint.singleton 7
  let ist : IntermediateState := Builder.withTaint ist0 diffB.toObjId tagged
  expect "tagged control: the signalling thread really carries provenance"
    (!(ist.state.declassificationTaint diffB.toObjId == SeLe4n.Kernel.DeclassificationTaint.empty))
  expect "tagged: the frozen signal agrees with the live syscall, provenance included"
    (frozenRunAgrees unitResultAgrees
      (frozenNotificationSignal diffNotifId diffB badge (freeze ist))
      (liveWithTaint .notificationSignal diffB (SeLe4n.CPtr.ofNat 0)
        (SeLe4n.Kernel.notificationSignalBound diffNotifId badge) ist.state))
  -- …and the provenance actually moved, so the agreement is about a step that
  -- happened rather than two no-ops matching.
  expect "tagged control: the badge's recipient inherited the signaller's tag"
    (match frozenNotificationSignal diffNotifId diffB badge (freeze ist) with
     | .ok ((), fs) => !(fs.declassificationTaint diffA.toObjId == SeLe4n.Kernel.DeclassificationTaint.empty)
     | .error _ => false)

/-- FO-032: **refusals agree too.**  A frozen operation that accepts what the
live one refuses is a divergence no state comparison can see, there being no
live state to compare against — and a missing frozen guard is exactly how a
message-less parked sender reached the frozen dequeue.  Both sides are handed a
notification id that names no object. -/
private def differentialRefusalsAgree : IO Unit := do
  let missing : SeLe4n.ObjId := ⟨999⟩
  let ist := diffAddTcb mkEmptyIntermediateState (diffTcb 62)
  expect "FO-032: both refuse an absent notification, with the same error"
    (frozenRunAgrees (fun a b => a == b)
      (frozenNotificationWait missing diffA (freeze ist))
      (liveWithTaint .notificationWait diffA (SeLe4n.CPtr.ofNat 0)
        (SeLe4n.Kernel.notificationWait missing diffA) ist.state))

/-- FO-036: **a send naming a thread that does not exist** (PR #873 round 17).

On a rendezvous the message goes straight from the argument into the receiver's
TCB, so the live `endpointSendDual` never resolved `sender`: a caller naming a
nonexistent thread delivered anyway, and the receiver held a message attributed
to it.  Only the parking arm failed, and only because it happens to store into
the sender's own TCB.  The frozen mirror resolved the sender on both arms, so
the two disagreed on a concrete rendezvous input — and the frozen behaviour was
the correct one, which is why the live path is what changed.

The control is the same send from a sender that **does** exist: without it the
refusal below would pass against a fixture where nothing could ever be
delivered. -/
private def differentialSendFromAbsentSenderAgrees : IO Unit := do
  let msg : IpcMessage := { registers := #[⟨31⟩], caps := #[], badge := none }
  let ghost : SeLe4n.ThreadId := ⟨9997⟩
  let ep : Endpoint := { sendQ := {}, receiveQ := { head := some diffA, tail := some diffA } }
  let parkedReceiver : TCB := { diffTcb 62 with ipcState := .blockedOnReceive diffEpId, queuePPrev := some .endpointHead }
  let ist := diffAddTcb (diffAddTcb
    (diffAddEndpoint (diffAddCSpace mkEmptyIntermediateState
      [(SeLe4n.Slot.ofNat 0, diffObjCap diffEpId)]) diffEpId ep) parkedReceiver) (diffTcb 63)
  expect "FO-036 control: the same rendezvous delivers from a sender that exists"
    (SeLe4n.Kernel.endpointSendDual diffEpId diffB msg ist.state).toOption.isSome
  expect "FO-036 control: and the ghost really is absent"
    ((ist.state.getTcb? ghost).isNone)
  expect "FO-036: both refuse a rendezvous send from a nonexistent sender"
    (frozenRunAgrees unitResultAgrees
      (frozenEndpointSend diffEpId ghost msg (freeze ist))
      (liveWithTaint .send ghost (SeLe4n.CPtr.ofNat 0)
        (SeLe4n.Kernel.endpointSendDual diffEpId ghost msg) ist.state))
  expect "FO-036: and the live refusal leaves the receiver empty-handed"
    (match SeLe4n.Kernel.endpointSendDual diffEpId ghost msg ist.state with
     | .error _ => true
     | .ok _ => false)

/-- FO-037: **the send rendezvous actually delivering** (PR #873 audit).

FO-036 above enters the receiver-waiting arm but compares only its *refusal*
ordering, and the branch's known divergence sat on the delivery ordering: the
live `storeTcbReceiveComplete` clears the receiver's stashed reply object -- a
plain `Send` completing a server-first `Recv` moots the stash (D3/F-1) -- while
the frozen mirror kept it.  A claimed-checked branch whose substantive path is
never compared is the overstatement the branch keying exists to prevent, so this
scenario is the delivery comparison, with the stash **seeded**: the receiver
parks holding a reply object, which is exactly the field the two sides disagreed
on.  It fails against the stash-keeping frozen mirror and passes against the
field-exact one.

The run-queue halves ride along with bite of their own: the live delivery ends
in `ensureRunnable receiver` and the frozen one in `frozenEnsureRunnable`, and
`frozenStateAgrees` compares the buckets in both directions. -/
private def differentialSendRendezvousDeliversAgrees : IO Unit := do
  let msg : IpcMessage := { registers := #[⟨37⟩], caps := #[], badge := none }
  let rid : SeLe4n.ReplyId := ⟨507⟩
  let ep : Endpoint := { sendQ := {}, receiveQ := { head := some diffA, tail := some diffA } }
  -- The server parked on a server-first `Recv`, reply object stashed: the state
  -- the D3/F-1 clear exists for.
  let parkedReceiver : TCB := { diffTcb 62 with ipcState := .blockedOnReceive diffEpId, queuePPrev := some .endpointHead, pendingReceiveReply := some rid }
  let ist := diffAddReply (diffAddTcb (diffAddTcb
    (diffAddEndpoint (diffAddCSpace mkEmptyIntermediateState
      [(SeLe4n.Slot.ofNat 0, diffObjCap diffEpId)]) diffEpId ep) parkedReceiver) (diffTcb 63))
    rid { replyId := rid, caller := none }
  expect "FO-037 control: the receiver really parks holding a stashed reply"
    ((ist.state.getTcb? diffA).any (fun t => t.pendingReceiveReply.isSome))
  -- The live delivery clears the stash: the field the comparison is about.
  expect "FO-037 control: the live delivery clears the stash and hands over the message"
    (match SeLe4n.Kernel.endpointSendDual diffEpId diffB msg ist.state with
     | .ok ((), st') => (st'.getTcb? diffA).any (fun t =>
         t.pendingReceiveReply.isNone && t.pendingMessage.isSome)
     | .error _ => false)
  expect "FO-037: the frozen delivery agrees with the live delivery"
    (frozenRunAgrees unitResultAgrees
      (frozenEndpointSend diffEpId diffB msg (freeze ist))
      (liveWithTaint .send diffB (SeLe4n.CPtr.ofNat 0)
        (SeLe4n.Kernel.endpointSendDual diffEpId diffB msg) ist.state))

/-- FO-034: **waking a thread whose priority has no bucket.**

Every actor in the scenarios above sits at priority 0, so a wake always found a
bucket already there and the frozen enqueue's missing-key branch never ran.  It
answered `.illegalState`, on the reading that a snapshot with no bucket at that
priority could not represent the thread becoming runnable -- but the live
`ensureRunnable` creates the bucket through `RunQueue.insert`, so the frozen
model refused a transition the kernel performs.  A passive server blocked at
freeze time, never runnable and therefore in no bucket, is that case.

The bound TCB is parked at a priority no runnable thread holds, so the signal's
wake has to create the bucket on both sides. -/
private def differentialWakeAtUnqueuedPriorityAgrees : IO Unit := do
  let badge := SeLe4n.Badge.ofNatMasked 77
  let ep : Endpoint := { sendQ := {}, receiveQ := { head := some diffA, tail := some diffA } }
  let ntfn : Notification :=
    { state := .idle, waitingThreads := SeLe4n.NoDupList.empty, pendingBadge := none,
      boundTCB := some diffA }
  -- Priority 5: `diffTcb 63`, the only runnable thread, is at 0, so nothing put
  -- a bucket here and the wake is the first thing that needs one.
  let parkedServer : TCB := { diffTcb 62 with priority := ⟨5⟩, ipcState := .blockedOnReceive diffEpId, queuePPrev := some .endpointHead }
  let ist := diffAddTcb (diffAddTcb (diffAddNotification
    (diffAddEndpoint (diffAddCSpace mkEmptyIntermediateState
      [(SeLe4n.Slot.ofNat 0, diffObjCap diffNotifId)]) diffEpId ep) diffNotifId ntfn)
    parkedServer) (diffTcb 63)
  expect "FO-034: control — the woken thread's priority has no bucket to start with"
    ((freeze ist).scheduler.byPriority.get? ⟨5⟩ |>.isNone)
  expect "FO-034: the frozen wake creates the bucket the live wake creates"
    (frozenRunAgrees unitResultAgrees
      (frozenNotificationSignal diffNotifId diffB badge (freeze ist))
      (liveWithTaint .notificationSignal diffB (SeLe4n.CPtr.ofNat 0)
        (SeLe4n.Kernel.notificationSignalBound diffNotifId badge) ist.state))

/-- **The registry the runner executes**, paired with the **branch** each
scenario covers.

`frozenOpDifferentiallyChecked` was a hand-maintained table nothing consumed:
setting an arm `true` satisfied all three interlock theorems whether or not a
comparison existed, and deleting a scenario left the claim standing.  A coverage
claim no execution backs is the shape this whole harness exists to remove, so the
claim is checked against this list -- which is also the list the runner runs, so
the two cannot describe different sets.

Round 17 moved the key from syscall to branch.  Tying the claim to an executed
scenario was necessary and not sufficient: one scenario satisfied a whole
syscall, so `.send` read "checked" on a fixture with no receiver waiting while
the rendezvous branch had never been compared against anything.  The unit of the
claim is now the unit of the transition. -/
private def differentialScenarios :
    List (SeLe4n.Kernel.FrozenOps.FrozenOpBranch × IO Unit) :=
  [ (.notificationSignalToBoundThread,  differentialNotificationSignalAgrees),
    (.notificationSignalToBoundThread,  differentialWakeAtUnqueuedPriorityAgrees),
    (.notificationWaitConsumesBadge,    differentialNotificationWaitAgrees),
    (.notificationWaitConsumesBadge,    differentialNotificationWaitConsumesBoundAgrees),
    (.notificationWaitBlocks,           differentialNotificationWaitParksAgrees),
    (.notificationWaitBlocks,           differentialNotificationWaitParksBoundAgrees),
    (.endpointSendParks,                differentialEndpointSendAgrees),
    (.endpointSendToWaitingReceiver,    differentialSendFromAbsentSenderAgrees),
    (.endpointSendToWaitingReceiver,    differentialSendRendezvousDeliversAgrees),
    (.endpointReceiveFromBlockedSender, differentialEndpointReceiveAgrees),
    (.endpointReceiveFromBlockedCaller, differentialReceiveFromBlockedCallerAgrees),
    (.endpointCallParks,                differentialEndpointCallAgrees),
    (.endpointReplyToBlockedCaller,     differentialEndpointReplyAgrees) ]

/-- ...and the scenarios that compare a branch's **whole live operation**, not
only its leg (PR #895 review round 15).

Kept as its own list because it backs its own claim: the leg list above answers
`frozenBranchDifferentiallyChecked` and this one answers
`frozenBranchOperationChecked`, and merging them would let a leg scenario
satisfy an operation claim -- which is exactly the substitution that let
"reply: checked" stand while the frozen composite was missing three of the live
operation's steps in three consecutive review rounds.

A **relation**, not a map: a branch may carry more than one scenario, and
`.endpointReplyToBlockedCaller` carries three because they answer different
questions about the same claim.  FO-041 exercises the operation's shape (the
revert, the guard, a delegated cap holder) on states carrying no donation; FO-042
(WS-HP HP8.1) exercises the donation pop itself and the state on which the two
candidate triggers disagree; FO-043 (WS-HP HP8.2) exercises the *removal* on a
**middle** frame, the only shape on which splicing and severing differ — every
other scenario here sits on a stack of depth ≤ 2, where both policies write the
same value and neither can tell them apart.  Both reconciliation directions below
are set containment, so a further row adds coverage and claims nothing extra. -/
private def operationDifferentialScenarios :
    List (SeLe4n.Kernel.FrozenOps.FrozenOpBranch × IO Unit) :=
  [ (.endpointReplyToBlockedCaller,     differentialEndpointReplyOperationAgrees),
    (.endpointReplyToBlockedCaller,     differentialEndpointReplyDonationAgrees),
    (.endpointReplyToBlockedCaller,     differentialEndpointReplyMiddleFrameSplices),
    (.endpointReplyToBlockedCaller,     differentialEndpointReplyRedirectsToOrigin) ]

/-- The claim and the scenarios name the same syscalls, in both directions: a
scenario for a syscall the table does not claim, or a claim with no scenario,
fails here. -/
private def differentialRegistryMatchesClaim : IO Unit := do
  let covered := differentialScenarios.map Prod.fst
  expect "registry: every differentially-checked branch has a scenario"
    (SeLe4n.Kernel.FrozenOps.FrozenOpBranch.all.all (fun b =>
      !(SeLe4n.Kernel.FrozenOps.frozenBranchDifferentiallyChecked b) || covered.contains b))
  expect "registry: every scenario covers a branch the claim names"
    (covered.all (fun b => SeLe4n.Kernel.FrozenOps.frozenBranchDifferentiallyChecked b))
  -- The per-syscall view is derived, so it must not read `true` for a syscall
  -- whose branches are not all covered -- the overstatement this replaced.
  expect "registry: a syscall reads checked only when every branch of it is"
    (SyscallId.all.all (fun sid =>
      !(SeLe4n.Kernel.FrozenOps.frozenOpDifferentiallyChecked sid)
        || SeLe4n.Kernel.FrozenOps.FrozenOpBranch.all.all (fun b =>
             b.syscall != sid || covered.contains b)))
  -- ...and the operation-level claim against the operation-level scenarios, in
  -- both directions, for the same reason: a `true` row nothing runs is a claim
  -- about an execution that does not exist.
  let operationCovered := operationDifferentialScenarios.map Prod.fst
  expect "registry: every operation-checked branch has an operation scenario"
    (SeLe4n.Kernel.FrozenOps.FrozenOpBranch.all.all (fun b =>
      !(SeLe4n.Kernel.FrozenOps.frozenBranchOperationChecked b)
        || operationCovered.contains b))
  expect "registry: every operation scenario covers a branch the claim names"
    (operationCovered.all (fun b =>
      SeLe4n.Kernel.FrozenOps.frozenBranchOperationChecked b))

/-- FO-033: **the comparison has bite, and the table was wrong.**

`FrozenOps/Operations.lean`'s correspondence table named `notificationSignal` as
`frozenNotificationSignal`'s counterpart.  It is not: the frozen operation
mirrors the bound-aware composition the live `.notificationSignal` arm runs, and
on the bound shape the two disagree.  Asserting that disagreement is what makes
the six scenarios above evidence rather than decoration — a comparison that
returned `true` for everything would pass them all. -/
private def differentialComparisonHasBite : IO Unit := do
  let badge := SeLe4n.Badge.ofNatMasked 77
  let ep : Endpoint := { sendQ := {}, receiveQ := { head := some diffA, tail := some diffA } }
  let ntfn : Notification :=
    { state := .idle, waitingThreads := SeLe4n.NoDupList.empty, pendingBadge := none,
      boundTCB := some diffA }
  let boundTcb : TCB := { diffTcb 62 with ipcState := .blockedOnReceive diffEpId, queuePPrev := some .endpointHead }
  let ist := diffAddTcb (diffAddTcb (diffAddNotification
    (diffAddEndpoint mkEmptyIntermediateState diffEpId ep) diffNotifId ntfn) boundTcb) (diffTcb 63)
  expect "FO-033: NEGATIVE — the table-named counterpart does NOT agree"
    (!(frozenRunAgrees unitResultAgrees
        (frozenNotificationSignal diffNotifId diffB badge (freeze ist))
        (SeLe4n.Kernel.notificationSignal diffNotifId badge ist.state)))

end SeLe4n.Testing.FrozenOpsSuite

open SeLe4n.Testing.FrozenOpsSuite in
def main : IO Unit := do
  IO.println "=== Q7 Frozen Operations Test Suite ==="
  IO.println "--- Q7-T1: FrozenKernel Monad Tests ---"
  fo001_lookupExisting
  fo002_lookupMissing
  fo003_storeObject
  IO.println "--- TPH-005: Frozen IPC ---"
  fo004_endpointReply
  fo004b_endpointReplyConsumesLink
  fo004c_replyToStackHeadPopsDonation
  fo004d_replyOffStackNeedsNoPop
  fo004e_replyDeschedulesTheServer
  fo004f_replyRevertsPriorityInheritance
  fo004g_replyNeedsARecordedServer
  fo005_replyDelegatedReplier
  fo005b_replyWrongPresentedCap
  IO.println "--- TPH-006: Frozen Scheduler Tick ---"
  fo006_timerTickIdle
  IO.println "--- TPH-007: Frozen CSpace Lookup ---"
  fo007_cspaceLookup
  fo008_cspaceLookupMissing
  IO.println "--- TPH-008: Frozen VSpace Resolve ---"
  fo009_vspaceLookup
  fo010_vspaceLookupMissing
  IO.println "--- TPH-009: Frozen Service Query ---"
  fo011_serviceLookup
  fo012_serviceLookupMissing
  IO.println "--- TPH-013: Delete in Frozen ---"
  fo013_cspaceDelete
  IO.println "--- TPH-014: Notification Signal/Wait ---"
  fo014_notificationSignal
  fo015_notificationWait
  IO.println "--- T7-D/F: Frozen IPC Queue Enqueue (M-FRZ-1/2/3) ---"
  fo016_sendEnqueuesSender
  fo017_receiveEnqueuesReceiver
  fo018_callEnqueuesCaller
  IO.println "--- T7-D: Frozen Schedule & CSpace Mint ---"
  fo019_frozenSchedule
  fo020_frozenCspaceMint
  IO.println "--- U-H01: Multi-round IPC Regression ---"
  fo021_popThenPushRegression
  frozenProvenanceFollowsContent
  frozenDeliveryIsHonest
  frozenParkedSenderCarriesItsMessage
  frozenBoundNotificationDelivery
  IO.println "--- Frozen/live differential agreement ---"
  differentialRegistryMatchesClaim
  differentialScenarios.forM (fun s => s.2)
  operationDifferentialScenarios.forM (fun s => s.2)
  differentialTaintedSignalAgrees
  differentialRefusalsAgree
  differentialComparisonHasBite
  -- **Derived, not hand-kept** (PR #895 review round 15).  The literal that
  -- stood here read "33 scenarios" against 40 distinct `FO-` ids and 34 runner
  -- invocations: a number nothing computed, beside lists that compute
  -- themselves.  What is worth reporting is the differential coverage, and the
  -- two lists are exactly the two claims the registry reconciles.
  IO.println s!"=== All Q7 frozen ops tests passed ({differentialScenarios.length} leg + {operationDifferentialScenarios.length} operation differentials) ==="
