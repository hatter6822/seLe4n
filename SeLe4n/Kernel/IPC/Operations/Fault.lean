-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.DualQueue.Transport
import SeLe4n.Kernel.Capability.Operations
import SeLe4n.Kernel.Architecture.Fault

/-!
# WS-RR RR4.7–RR4.16 — fault IPC

The single-core half of the fault path: resolve a faulting thread's handler
capability, check its rights, build the fault message, deliver it as an
endpoint **Call**, and apply the handler's reply.

## Why a Call and not a Send

seL4's `sendFaultIPC` calls `sendIPC(blocking = true, do_call = true, …)`: the
faulting thread blocks *awaiting a reply*, and the handler receives a reply
capability with which to restart it.  That is exactly this model's
`endpointCall`, so the delivery transition **is** `endpointCall` with a
kernel-built message rather than a parallel transport.  Everything the Call
path already proves — queue well-formedness, donation ownership, reply
linkage, the `ipcInvariantFull` bundle — carries over by composition
(`IPC/Invariant/FaultPreservation.lean`); a second transport would have owed
all of it again.

## Fail-closed, by construction

`faultDeliver` is **total**: it returns a post-state and a disposition, never
an error.  Every way the delivery can fail — no handler capability, an
unresolvable one, one lacking rights, one naming something other than an
endpoint, a Call that cannot link a reply object — converges on the same
answer, seL4's `handleDoubleFault`: the thread is marked `.Inactive` and
descheduled.

That is not defensive coding; it is what makes RR4.19 provable.  A fault
path with an error arm would leave a caller free to ignore it and `eret`
back into the faulting instruction, which is precisely the livelock this
phase exists to remove.  Here there is no arm to ignore: on **both**
dispositions the faulting thread leaves the transition not runnable.
-/

namespace SeLe4n.Kernel

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel.Architecture
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1  RR4.7/RR4.8 — resolving the fault handler
-- ============================================================================

/-- WS-RR RR4.8: the rights a fault-handler endpoint capability must carry —
seL4's `sendFaultIPC` predicate, verbatim:

```c
if (cap_get_capType(handlerCap) == cap_endpoint_cap &&
    cap_endpoint_cap_get_capCanSend(handlerCap) &&
    (cap_endpoint_cap_get_capCanGrant(handlerCap) ||
     cap_endpoint_cap_get_capCanGrantReply(handlerCap)))
```

* **send** (`.write`) is the authority to deliver the fault message at all;
* **grant or grant-reply** is seL4's authority to hand the handler the reply
  capability the faulting thread will block on.  In this model the reply
  link is *structural* — the Call chain records `reply.caller` and the
  faulting thread's `replyObject` unconditionally, and a fault message
  carries no capabilities for `.grant` to authorise
  (`faultMessage_grant_is_inert`) — so the disjunct is a **policy** gate
  rather than a mechanism prerequisite: it is what keeps a capability minted
  as send-only (a client's handle on a server endpoint, say) from being
  configured as a fault handler and made to receive reply authority it was
  deliberately not given.  `.grantReply` is admitted on the same footing as
  `.grant` because seL4 admits it and because refusing it would turn every
  `seL4_CapRights_new(0, 1, 0, 1)` handler capability — the idiomatic shape,
  which withholds full grant from a fault handler — into a fail-closed
  suspend.

The audit round replaced a send-**and**-grant reading whose stated rationale
("grant is what lets the handler receive a reply capability") was false of
this model, where the reply link does not depend on any right.

**Stated as clauses, and the predicate is defined from them** (PR #887 review
round 3).  The outer list is a conjunction and each inner list a disjunction —
send, and grant or grant-reply — so the inventory below (`faultHandlerRights`,
the clauses flattened) and the predicate (`faultHandlerCapAuthorized`, the
clauses evaluated) are two readings of one definition rather than two
definitions a theorem tries to hold together.  The first cut pinned them with
`faultHandlerCapAuthorized_reads_faultHandlerRights`, whose conclusion was one
of its own hypotheses: it compiled with `.write` deleted from the inventory
and with `.read` added, which is the proof-level form of a presence check.
What holds now is `faultHandlerCapAuthorized_iff` — the exact seL4 form, which
an added or removed right breaks — and
`faultHandlerCapAuthorized_depends_only_on_faultHandlerRights`, the support
relation: two capabilities that agree on the inventory's rights get the same
verdict, so no right outside the inventory is consulted. -/
def faultHandlerRequiredRights : List (List AccessRight) := [[.write], [.grant, .grantReply]]

/-- WS-RR RR4.8: the rights the predicate consults — the clauses, flattened. -/
def faultHandlerRights : List AccessRight := faultHandlerRequiredRights.flatten

/-- The inventory, as the list a reader expects; a clause edit changes it. -/
theorem faultHandlerRights_eq : faultHandlerRights = [.write, .grant, .grantReply] := rfl

/-- WS-RR RR4.8: does a capability carry the rights a fault handler needs?
Every clause satisfied by at least one of its rights: send, and at least one
of the two grant rights. -/
def faultHandlerCapAuthorized (cap : Capability) : Bool :=
  faultHandlerRequiredRights.all (fun clause => clause.any (fun r => cap.hasRight r))

/-- WS-RR RR4.8: the authorization is exactly seL4's predicate, unfolded —
the form a caller checks against without reasoning through `Bool` algebra.
Since PR #887 review round 3 this is the drift pin between the clauses and
the predicate seL4 states: a right added to or removed from a clause changes
the left-hand side and not the right, and the theorem fails. -/
@[simp] theorem faultHandlerCapAuthorized_iff (cap : Capability) :
    faultHandlerCapAuthorized cap = true ↔
      (cap.hasRight .write = true ∧
        (cap.hasRight .grant = true ∨ cap.hasRight .grantReply = true)) := by
  simp [faultHandlerCapAuthorized, faultHandlerRequiredRights]

/-- PR #887 review round 3 (**the support relation**): the verdict is a
function of the inventory's rights alone — two capabilities that agree on
every right in `faultHandlerRights` are authorized alike.  This is what the
retired `faultHandlerCapAuthorized_reads_faultHandlerRights` meant to say and
did not: with `.write` dropped from the inventory the hypothesis no longer
covers it, and the proof fails. -/
theorem faultHandlerCapAuthorized_depends_only_on_faultHandlerRights
    (c₁ c₂ : Capability)
    (h : ∀ r ∈ faultHandlerRights, c₁.hasRight r = c₂.hasRight r) :
    faultHandlerCapAuthorized c₁ = faultHandlerCapAuthorized c₂ := by
  have hW := h .write (by simp [faultHandlerRights_eq])
  have hG := h .grant (by simp [faultHandlerRights_eq])
  have hR := h .grantReply (by simp [faultHandlerRights_eq])
  simp [faultHandlerCapAuthorized, faultHandlerRequiredRights, hW, hG, hR]

/-- WS-RR RR4.8 (**the negatives**): send alone is refused, and either grant
right alone is refused — the predicate is a conjunction, not a disjunction of
everything it names. -/
theorem faultHandlerCapAuthorized_false_of_no_send (cap : Capability)
    (h : cap.hasRight .write = false) : faultHandlerCapAuthorized cap = false := by
  simp [faultHandlerCapAuthorized, faultHandlerRequiredRights, h]

theorem faultHandlerCapAuthorized_false_of_no_grant (cap : Capability)
    (hG : cap.hasRight .grant = false) (hR : cap.hasRight .grantReply = false) :
    faultHandlerCapAuthorized cap = false := by
  simp [faultHandlerCapAuthorized, faultHandlerRequiredRights, hG, hR]

/-- WS-RR RR4.7: everything the delivery needs about a faulting thread's fault
handler, resolved from the pre-state in one pass.

`cspaceRoot` is the *faulting thread's* CSpace root, threaded because the Call
the delivery composes takes it as the source of any capabilities the message
transfers.  A fault message transfers none (`faultMessage_caps`), so it is
inert on this path — but naming the faulting thread's own root, rather than a
synthesised value, keeps the delivery a real instance of the Call rather than
one with a fabricated argument. -/
structure FaultHandlerTarget where
  /-- The endpoint object the handler capability names. -/
  endpoint : SeLe4n.ObjId
  /-- The handler capability itself — its badge rides on the fault message and
      its rights authorise the Call. -/
  cap : Capability
  /-- The faulting thread's CSpace root. -/
  cspaceRoot : SeLe4n.ObjId
  deriving Repr, DecidableEq

/-- WS-RR RR4.7 (**handler resolution**): resolve a fault-handler CPtr to the
endpoint it names, through the thread's own CSpace.  `resolveFaultHandler`
below supplies the thread's configured CPtr; `setThreadFaultHandlerOp`
supplies a candidate.

The four gates, in the order seL4 applies them (the first two are
`resolveFaultHandler`'s, the last two this function's):

1. the thread exists and **has** a fault-handler CPtr (`none` is seL4's
   "no handler configured", and takes the RR4.9 path);
2. the CPtr resolves through the thread's **own** CSpace root, at that
   root CNode's declared depth — the same resolution the syscall gate uses
   (`syscallResolveCap`), so a fault handler is addressed with exactly the
   authority its thread already has and no more;
3. the resolved capability satisfies `faultHandlerCapAuthorized` — send, and
   grant or grant-reply (RR4.8);
4. it names an object that really is an endpoint.

Read-only: resolution never mutates the state. -/
def resolveFaultHandlerCPtr (st : SystemState) (tcb : TCB) (cptr : SeLe4n.CPtr) :
    Except KernelError FaultHandlerTarget :=
  match st.getCNode? tcb.cspaceRoot with
  | none => .error .objectNotFound
  | some rootCn =>
      match resolveCapAddress tcb.cspaceRoot cptr rootCn.depth st with
      | .error e => .error e
      | .ok ref =>
          match SystemState.lookupSlotCap st ref with
          | none => .error .invalidCapability
          | some cap =>
              if faultHandlerCapAuthorized cap then
                match cap.target with
                | .object epId =>
                    match st.getEndpoint? epId with
                    | some _ =>
                        .ok { endpoint := epId, cap := cap,
                              cspaceRoot := tcb.cspaceRoot }
                    | none   => .error .invalidCapability
                | _ => .error .invalidCapability
              else .error .illegalAuthority

/-- WS-RR RR4.7: resolve a thread's configured fault handler — gates 1 and 2
of the resolution, then `resolveFaultHandlerCPtr` for gates 3 and 4.  Review
round (PR #887): the CPtr half is factored out so `setThreadFaultHandlerOp`
validates a candidate handler with the **same** resolution the fault path
will run, rather than a second copy of it. -/
def resolveFaultHandler (st : SystemState) (tid : SeLe4n.ThreadId) :
    Except KernelError FaultHandlerTarget :=
  match st.getTcb? tid with
  | none => .error .objectNotFound
  | some tcb =>
      match tcb.faultHandler with
      | none => .error .invalidCapability
      | some cptr => resolveFaultHandlerCPtr st tcb cptr

/-- WS-RR RR4.10 (**the negative**): a thread with no `faultHandler` never
resolves — the arm that sends it to the fail-closed suspend. -/
theorem resolveFaultHandler_none_of_noHandler (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb) (hNone : tcb.faultHandler = none) :
    resolveFaultHandler st tid = .error .invalidCapability := by
  simp [resolveFaultHandler, hTcb, hNone]

/-- WS-RR RR4.10: nor does a thread that is not a TCB at all. -/
theorem resolveFaultHandler_none_of_noThread (st : SystemState)
    (tid : SeLe4n.ThreadId) (hNone : st.getTcb? tid = none) :
    resolveFaultHandler st tid = .error .objectNotFound := by
  simp [resolveFaultHandler, hNone]

/-- WS-RR RR4.7/RR4.8 (**inversion**): everything a successful resolution
guarantees, established once.  Stated over the *result* rather than over the
branch that produced it, so a caller cannot reach a delivery through an arm
that skipped a gate — there is no successful arm that did. -/
theorem resolveFaultHandler_ok_inv (st : SystemState) (tid : SeLe4n.ThreadId)
    (tgt : FaultHandlerTarget)
    (hOk : resolveFaultHandler st tid = .ok tgt) :
    faultHandlerCapAuthorized tgt.cap = true ∧
    tgt.cap.target = .object tgt.endpoint ∧
    (st.getEndpoint? tgt.endpoint).isSome := by
  unfold resolveFaultHandler resolveFaultHandlerCPtr at hOk
  repeat' split at hOk
  all_goals (try (injection hOk with hEq; subst hEq))
  all_goals simp_all

/-- Review round (PR #887): the CPtr resolution's own inversion — what a
successful `resolveFaultHandlerCPtr` guarantees, the half the configuration
operation relies on. -/
theorem resolveFaultHandlerCPtr_ok_inv (st : SystemState) (tcb : TCB)
    (cptr : SeLe4n.CPtr) (tgt : FaultHandlerTarget)
    (hOk : resolveFaultHandlerCPtr st tcb cptr = .ok tgt) :
    faultHandlerCapAuthorized tgt.cap = true ∧
    tgt.cap.target = .object tgt.endpoint ∧
    (st.getEndpoint? tgt.endpoint).isSome ∧
    tgt.cspaceRoot = tcb.cspaceRoot := by
  unfold resolveFaultHandlerCPtr at hOk
  repeat' split at hOk
  all_goals (try (injection hOk with hEq; subst hEq))
  all_goals simp_all

/-- Review round (PR #887): a configured handler resolves exactly as its CPtr
does — the definitional bridge between the two resolutions. -/
theorem resolveFaultHandler_eq_cptr (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (cptr : SeLe4n.CPtr)
    (hTcb : st.getTcb? tid = some tcb) (hFh : tcb.faultHandler = some cptr) :
    resolveFaultHandler st tid = resolveFaultHandlerCPtr st tcb cptr := by
  simp [resolveFaultHandler, hTcb, hFh]

/-- WS-RR RR4.8 (**the rights check, as a theorem**): a resolved handler
capability always carries send **and** one of the grant rights — seL4's
`sendFaultIPC` predicate, over the result. -/
theorem resolveFaultHandler_authorized (st : SystemState) (tid : SeLe4n.ThreadId)
    (tgt : FaultHandlerTarget)
    (hOk : resolveFaultHandler st tid = .ok tgt) :
    tgt.cap.hasRight .write = true ∧
      (tgt.cap.hasRight .grant = true ∨ tgt.cap.hasRight .grantReply = true) :=
  faultHandlerCapAuthorized_iff tgt.cap |>.mp (resolveFaultHandler_ok_inv st tid tgt hOk).1

/-- WS-RR RR4.7: a resolved handler really names an endpoint object — so the
delivery's Call cannot fail on a wrong-kinded target. -/
theorem resolveFaultHandler_names_endpoint (st : SystemState) (tid : SeLe4n.ThreadId)
    (tgt : FaultHandlerTarget)
    (hOk : resolveFaultHandler st tid = .ok tgt) :
    tgt.cap.target = .object tgt.endpoint ∧ (st.getEndpoint? tgt.endpoint).isSome :=
  (resolveFaultHandler_ok_inv st tid tgt hOk).2

/-- WS-RR RR4.7: resolution is read-only.  Trivially true (the function
returns no state), and stated so a reader can see the delivery's only state
change is the Call itself. -/
theorem resolveFaultHandler_readOnly (st : SystemState) (tid : SeLe4n.ThreadId) :
    resolveFaultHandler st tid = resolveFaultHandler st tid := rfl

-- ============================================================================
-- §2  The fault message
-- ============================================================================

/-- WS-RR RR4.4: the `IpcMessage` a fault is delivered as.

The encoder (`Architecture.encodeFault`) owns the layout; this is the
model-side envelope: the encoded register array, the encoded `seL4_Fault_tag`
as the message label, the handler capability's badge (seL4 passes
`cap_endpoint_cap_get_capEPBadge(handlerCap)` to `sendIPC`, so a handler
serving several faulting threads through badged capabilities can tell them
apart), and **no capabilities**.

`capsGranted := false` is not merely the default: a fault message must never
transfer authority.  It is a diagnostic report the kernel writes about a
thread, so granting through it would let the *kernel* hand a handler
capabilities the faulting thread never offered — and it is what makes the
RR4.20 non-interference argument about a data flow alone. -/
def faultMessage (f : Fault) (ctx : FaultContext) (badge : Option SeLe4n.Badge) :
    IpcMessage :=
  { registers   := (Architecture.encodeFault f ctx).2
    caps        := #[]
    badge       := badge
    capsGranted := false
    label       := (Architecture.encodeFault f ctx).1.label }

/-- WS-RR RR4.4: the delivered label is the fault's `seL4_Fault_tag` — the
word that tells the handler which fault it is looking at. -/
@[simp] theorem faultMessage_label (f : Fault) (ctx : FaultContext)
    (badge : Option SeLe4n.Badge) :
    (faultMessage f ctx badge).label = Architecture.faultLabel f := rfl

/-- WS-RR RR4.4: and it is never the success/null label, so a handler can
never read a fault message as a completed receive. -/
theorem faultMessage_label_ne_null (f : Fault) (ctx : FaultContext)
    (badge : Option SeLe4n.Badge) :
    (faultMessage f ctx badge).label ≠ Architecture.FaultLabel.nullFault :=
  Architecture.faultLabel_ne_null f

/-- WS-RR RR4.4: a fault message carries no capabilities. -/
@[simp] theorem faultMessage_caps (f : Fault) (ctx : FaultContext)
    (badge : Option SeLe4n.Badge) : (faultMessage f ctx badge).caps = #[] := rfl

/-- WS-RR RR4.4: and grants none. -/
@[simp] theorem faultMessage_capsGranted (f : Fault) (ctx : FaultContext)
    (badge : Option SeLe4n.Badge) :
    (faultMessage f ctx badge).capsGranted = false := rfl

/-- WS-RR RR4.6 (**the prefilters never fire**): a fault message is inside
both bounds `endpointCall` checks before it looks at the endpoint.

This is what makes the delivery's failure surface depend on the *endpoint
state* alone — a fault can never be dropped because the kernel built a message
its own transport rejects. -/
theorem faultMessage_within_prefilters (f : Fault) (ctx : FaultContext)
    (badge : Option SeLe4n.Badge) :
    ¬ ((faultMessage f ctx badge).registers.size > maxMessageRegisters) ∧
    ¬ ((faultMessage f ctx badge).caps.size > maxExtraCaps) := by
  refine ⟨Nat.not_lt.mpr ?_, by simp⟩
  exact Architecture.encodeFault_within_budget f ctx

/-- WS-RR RR4.6: the message satisfies the model's payload bound predicate. -/
theorem faultMessage_bounded (f : Fault) (ctx : FaultContext)
    (badge : Option SeLe4n.Badge) : (faultMessage f ctx badge).bounded := by
  refine ⟨Architecture.encodeFault_within_budget f ctx, ?_⟩
  simp [faultMessage, maxExtraCaps]

/-- WS-RR RR4.5: the handler can recover the fault from the message it
received — the round trip, lifted to the delivered envelope.  Without it the
encoding would be a write-only format. -/
theorem faultMessage_decodes (f : Fault) (ctx : FaultContext)
    (badge : Option SeLe4n.Badge) :
    Architecture.decodeFault
        { length := Architecture.faultMessageLength f, extraCaps := 0,
          label := (faultMessage f ctx badge).label }
        (faultMessage f ctx badge).registers = some f :=
  Architecture.decodeFault_encodeFault f ctx

-- ============================================================================
-- §3  RR4.9 — the fail-closed dispositions
-- ============================================================================

/-- WS-RR RR4: what happened to a faulting thread. -/
inductive FaultDisposition where
  /-- The fault IPC reached `endpoint`; the faulting thread is blocked
      awaiting the handler's reply. -/
  | delivered (endpoint : SeLe4n.ObjId)
  /-- No usable fault handler, or a Call that could not complete: the thread
      was descheduled and marked `.Inactive`, fail-closed. -/
  | suspended
  deriving Repr, DecidableEq, Inhabited

/-- WS-RR RR4: record the fault a thread is blocked on — seL4's
`tptr->tcbFault = current_fault`, set before the fault IPC is sent so the
reply that answers it can find it.  Total: a non-TCB target is unchanged. -/
def recordPendingFault (st : SystemState) (tid : SeLe4n.ThreadId)
    (tf : ThreadFault) : SystemState :=
  match st.getTcb? tid with
  | some tcb =>
      let updated : KernelObject := .tcb { tcb with pendingFault := some tf }
      { st with objects := st.objects.insert tid.toObjId updated }
  | none => st

/-- WS-RR RR4.17 (frame): recording a fault is a single TCB write — the
scheduler is untouched, so a delivery's runnability statement reads through
it. -/
@[simp] theorem recordPendingFault_scheduler_eq (st : SystemState)
    (tid : SeLe4n.ThreadId) (tf : ThreadFault) :
    (recordPendingFault st tid tf).scheduler = st.scheduler := by
  simp only [recordPendingFault]
  cases st.getTcb? tid <;> simp

/-- WS-RR RR4.9 (**the no-handler policy**): deschedule the thread and mark
it `.Inactive`.

This is seL4's `handleDoubleFault` — `setThreadState(tptr,
ThreadState_Inactive)`, whose `scheduleTCB` removes a now-unrunnable thread
from the queue — and deliberately *not* the full `suspendThread` teardown.  A
faulting thread was **running**: it holds no IPC blocking state to cancel, no
endpoint queue membership to unlink, no priority inheritance to revert.
Running the cancellation machinery over it would be dead weight, and — the
reason that matters — `suspendThread` has error arms, which would give this
transition a failure mode.  It must not have one: RR4.19 is provable exactly
because *every* way the fault path can go wrong ends here, and this cannot go
wrong.

The outstanding `pendingFault` is deliberately **kept**: an `.Inactive`
thread carrying the fault that stopped it is what a monitor or debugger reads
to find out why, and it is what seL4's `handleDoubleFault` prints.  The reply
path clears it instead (`faultAbandon`), because there the fault has been
answered.

`ipcState` is deliberately **not** touched, which is what keeps this cheap to
verify: every `ipcInvariantFull` conjunct reads `ipcState`, the endpoint
queues, the donation chain or the reply links, and this writes none of them
(`threadState` is read by the scheduler's invariants, not the IPC bundle). -/
def faultSuspend (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  let st1 := removeRunnable st tid
  match st1.getTcb? tid with
  | some tcb =>
      let updated : KernelObject := .tcb { tcb with threadState := .Inactive }
      { st1 with objects := st1.objects.insert tid.toObjId updated }
  | none => st1

/-- WS-RR RR4.15: the reply-declined disposition — deschedule, mark
`.Inactive`, and **retire the answered fault**.

Distinct from `faultSuspend` in exactly that one clear.  seL4's
`doReplyTransfer` sets `receiver->tcbFault = seL4_Fault_NullFault_new()`
before choosing `Restart` or `Inactive`, because the fault *has* been
answered: leaving it recorded would let a second reply re-run
`handleFaultReply` against a fault that is already resolved, and would let a
handler restart a thread whose fault it never received.

The reply's delivered `pendingMessage` is deliberately left alone.  It is
`IpcMessage.empty` (a fault reply's payload is registers, not message
registers — `faultReply`), so it is the identity delivery: staging it yields
the all-zero success frame, which the restart write of the sibling arm
overwrites in the same transition.  Clearing it would additionally need a
state-dependent guard, since a `.blockedOnSend` or `.blockedOnCall` thread
must *keep* its message
(`blockedThreadsPendingMessageConsistent`), and would buy no behaviour. -/
def faultAbandon (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  let st1 := removeRunnable st tid
  match st1.getTcb? tid with
  | some tcb =>
      let updated : KernelObject :=
        .tcb { tcb with threadState := .Inactive, pendingFault := none }
      { st1 with objects := st1.objects.insert tid.toObjId updated }
  | none => st1

/-- WS-RR RR4.9: a suspended thread is `.Inactive` — the state the scheduler
never dispatches. -/
theorem faultSuspend_threadState (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (hTcb : (removeRunnable st tid).getTcb? tid = some tcb)
    (hObjInv : (removeRunnable st tid).objects.invExt) :
    (faultSuspend st tid).getTcb? tid = some { tcb with threadState := .Inactive } := by
  unfold faultSuspend
  simp only [hTcb]
  unfold SystemState.getTcb?
  rw [RHTable_getElem?_eq_get?,
      SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self _ tid.toObjId
        (KernelObject.tcb { tcb with threadState := .Inactive }) hObjInv]

/-- WS-RR RR4.9 (frame): descheduling and marking a thread `.Inactive` writes
the run queue and the current slot and nothing else in the scheduler — the
`.Inactive` store is an object write. -/
theorem faultSuspend_scheduler_eq (st : SystemState) (tid : SeLe4n.ThreadId) :
    (faultSuspend st tid).scheduler = (removeRunnable st tid).scheduler := by
  simp only [faultSuspend]
  cases (removeRunnable st tid).getTcb? tid <;> simp

/-- WS-RR RR4.15 (frame): the same for the reply-declined disposition. -/
theorem faultAbandon_scheduler_eq (st : SystemState) (tid : SeLe4n.ThreadId) :
    (faultAbandon st tid).scheduler = (removeRunnable st tid).scheduler := by
  simp only [faultAbandon]
  cases (removeRunnable st tid).getTcb? tid <;> simp

/-- `removeRunnable` writes the boot core's run-queue slot to `remove tid`. -/
@[simp] theorem removeRunnable_runQueueOnCore_self (st : SystemState)
    (tid : SeLe4n.ThreadId) :
    (removeRunnable st tid).scheduler.runQueueOnCore bootCoreId
      = (st.scheduler.runQueueOnCore bootCoreId).remove tid := by
  simp [removeRunnable]

/-- `removeRunnable` clears the boot core's current slot when it held `tid`. -/
theorem removeRunnable_currentOnCore_self (st : SystemState) (tid : SeLe4n.ThreadId) :
    (removeRunnable st tid).scheduler.currentOnCore bootCoreId
      = if st.scheduler.currentOnCore bootCoreId = some tid then none
        else st.scheduler.currentOnCore bootCoreId := by
  simp [removeRunnable]

/-- WS-RR RR4.9: **the suspended thread is out of the run queue and is not
current** — the half that makes "cannot re-execute the faulting instruction"
a fact rather than an intention.  Together with `faultSuspend_threadState`
this is the whole no-handler policy: not runnable, and marked so. -/
theorem faultSuspend_not_runnable (st : SystemState) (tid : SeLe4n.ThreadId) :
    tid ∉ (faultSuspend st tid).scheduler.runQueueOnCore bootCoreId ∧
    (faultSuspend st tid).scheduler.currentOnCore bootCoreId ≠ some tid := by
  rw [faultSuspend_scheduler_eq]
  refine ⟨?_, ?_⟩
  · rw [removeRunnable_runQueueOnCore_self]
    exact RunQueue.not_mem_remove_self _ tid
  · rw [removeRunnable_currentOnCore_self]
    split
    · simp
    · assumption

/-- WS-RR RR4.15: and the reply-declined disposition leaves the thread just as
unrunnable — a handler that says "do not continue" is obeyed. -/
theorem faultAbandon_not_runnable (st : SystemState) (tid : SeLe4n.ThreadId) :
    tid ∉ (faultAbandon st tid).scheduler.runQueueOnCore bootCoreId ∧
    (faultAbandon st tid).scheduler.currentOnCore bootCoreId ≠ some tid := by
  rw [faultAbandon_scheduler_eq]
  refine ⟨?_, ?_⟩
  · rw [removeRunnable_runQueueOnCore_self]
    exact RunQueue.not_mem_remove_self _ tid
  · rw [removeRunnable_currentOnCore_self]
    split
    · simp
    · assumption

-- ============================================================================
-- §4  RR4.15/RR4.16 — installing a restart frame
-- ============================================================================

/-- WS-RR RR4.15: install a handler-supplied restart frame and retire the
answered fault.

Two writes in one store: the registers (`TCB.withRestartFrame` — the RR4.16
mechanism, which *is* the syscall-return writeback plus the three registers a
restart reaches beyond it), and the `pendingFault` clear (seL4's
`receiver->tcbFault = seL4_Fault_NullFault_new()`, so a second reply cannot
re-run `handleFaultReply` against a fault that is already answered, and no
handler can restart a thread whose fault it never received).

Both are fields no `ipcInvariantFull` conjunct reads, which is why the whole
bundle transports across a restart by the one-TCB-rewrite lever rather than by
a case analysis.  The `pendingMessage` the reply delivered is left as
delivered — see `faultAbandon` for why that is right rather than merely
convenient. -/
def applyFaultRestart (st : SystemState) (faulted : SeLe4n.ThreadId)
    (frame : Architecture.FaultRestartFrame) : SystemState :=
  match st.getTcb? faulted with
  | some tcb =>
      let updated : KernelObject :=
        .tcb { tcb.withRestartFrame frame with pendingFault := none }
      { st with objects := st.objects.insert faulted.toObjId updated }
  | none => st

/-- WS-RR RR4.15 (frame): installing a restart frame never touches the
scheduler — it decides *where the thread resumes*, not *whether* it is
scheduled. -/
@[simp] theorem applyFaultRestart_scheduler_eq (st : SystemState)
    (faulted : SeLe4n.ThreadId) (frame : Architecture.FaultRestartFrame) :
    (applyFaultRestart st faulted frame).scheduler = st.scheduler := by
  simp only [applyFaultRestart]
  cases st.getTcb? faulted <;> simp

/-- WS-RR RR4.15: the restarted thread's saved `pc` is the frame's — the
statement RR4.19's progress argument consumes, since "the thread does not
silently re-execute the faulting instruction" is exactly "its saved `pc` is
what the handler chose". -/
theorem applyFaultRestart_pc (st : SystemState) (faulted : SeLe4n.ThreadId)
    (frame : Architecture.FaultRestartFrame) (tcb : TCB)
    (hTcb : st.getTcb? faulted = some tcb) (hObjInv : st.objects.invExt) :
    (applyFaultRestart st faulted frame).getTcb? faulted
      = some { tcb.withRestartFrame frame with pendingFault := none } := by
  simp only [applyFaultRestart, hTcb]
  unfold SystemState.getTcb?
  rw [RHTable_getElem?_eq_get?,
      SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self st.objects faulted.toObjId
        (KernelObject.tcb { tcb.withRestartFrame frame with pendingFault := none }) hObjInv]

/-- WS-RR RR4.15: and a restart **retires the fault** — the thread comes out of
it carrying no outstanding fault, so a second reply cannot re-answer the one
already answered. -/
theorem applyFaultRestart_clears_pendingFault (st : SystemState)
    (faulted : SeLe4n.ThreadId) (frame : Architecture.FaultRestartFrame) (tcb : TCB)
    (hTcb : st.getTcb? faulted = some tcb) (hObjInv : st.objects.invExt) :
    ∀ tcb', (applyFaultRestart st faulted frame).getTcb? faulted = some tcb' →
      tcb'.pendingFault = none := by
  intro tcb' h
  rw [applyFaultRestart_pc st faulted frame tcb hTcb hObjInv] at h
  cases h
  rfl


-- ============================================================================
-- §7  Review round (PR #887) — configuring a handler, and resuming past a fault
-- ============================================================================

/-- The post-state of a successful `setThreadFaultHandlerOp`: the target's TCB
with its `faultHandler` rewritten and nothing else touched — the shape every
preservation proof below reads off. -/
def installFaultHandler (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (cptr : SeLe4n.CPtr) : SystemState :=
  { st with
      objects := st.objects.insert tid.toObjId (.tcb { tcb with faultHandler := some cptr }) }

/-- **`seL4_TCB_SetSpace`'s fault endpoint, as a kernel operation.**  Install
`cptr` as the target thread's fault handler.

Before this operation existed, `TCB.faultHandler` had no writer outside the
test fixtures — production TCB creation leaves it `none` — so on a live
system every fault took the fail-closed suspend and the whole RR4 mechanism
was unreachable.  The CPtr is interpreted **in the target thread's own
CSpace**, exactly as seL4 documents (`fault_ep` "must be in the CSpace of
the thread being configured") and exactly as `resolveFaultHandler` reads it
at fault time.

**Validated at set time.**  seL4-classic stores whatever CPtr it is given
and discovers a bad one only when the thread faults; seL4-MCS validates the
endpoint when it is configured.  This model validates: the candidate must
resolve, through the target's CSpace, to an endpoint capability satisfying
`faultHandlerCapAuthorized` — the same `resolveFaultHandlerCPtr` the fault
path runs — so a misconfiguration is refused with its reason rather than
surfacing later as a suspended thread.  The fault-time check remains (the
capability may be revoked in between), and revoking the handler capability is
the fail-closed way to withdraw a handler: the next fault then suspends.

Authority is the caller's TCB capability with the write right, like every
other thread-configuration syscall.  The write itself is a one-TCB field
rewrite; it touches no scheduler or IPC state. -/
def setThreadFaultHandlerOp (st : SystemState) (vTargetTid : SeLe4n.ValidThreadId)
    (cptr : SeLe4n.CPtr) : Except KernelError SystemState :=
  match st.getTcb? vTargetTid.val with
  | none => .error .objectNotFound
  | some tcb =>
      match resolveFaultHandlerCPtr st tcb cptr with
      | .error e => .error e
      | .ok _ => .ok (installFaultHandler st vTargetTid.val tcb cptr)

/-- On the success path the step *is* the one-field rewrite. -/
theorem setThreadFaultHandlerOp_ok_eq (st : SystemState) (vTargetTid : SeLe4n.ValidThreadId)
    (cptr : SeLe4n.CPtr) (tcb : TCB) (tgt : FaultHandlerTarget)
    (hTcb : st.getTcb? vTargetTid.val = some tcb)
    (hR : resolveFaultHandlerCPtr st tcb cptr = .ok tgt) :
    setThreadFaultHandlerOp st vTargetTid cptr
      = .ok (installFaultHandler st vTargetTid.val tcb cptr) := by
  simp only [setThreadFaultHandlerOp, hTcb, hR]

/-- A handler is installed only if it resolved, through the target's CSpace,
to an authorised endpoint capability in the pre-state — the set-time
validation, as a theorem. -/
theorem setThreadFaultHandlerOp_validated (st st' : SystemState)
    (vTargetTid : SeLe4n.ValidThreadId) (cptr : SeLe4n.CPtr)
    (hStep : setThreadFaultHandlerOp st vTargetTid cptr = .ok st') :
    ∃ tcb tgt, st.getTcb? vTargetTid.val = some tcb ∧
      resolveFaultHandlerCPtr st tcb cptr = .ok tgt ∧
      faultHandlerCapAuthorized tgt.cap = true ∧
      (st.getEndpoint? tgt.endpoint).isSome := by
  cases hT : st.getTcb? vTargetTid.val with
  | none => simp [setThreadFaultHandlerOp, hT] at hStep
  | some tcb =>
      cases hR : resolveFaultHandlerCPtr st tcb cptr with
      | error e => simp [setThreadFaultHandlerOp, hT, hR] at hStep
      | ok tgt =>
          have hInv := resolveFaultHandlerCPtr_ok_inv st tcb cptr tgt hR
          exact ⟨tcb, tgt, rfl, hR, hInv.1, hInv.2.2.1⟩

/-- The post-state records the CPtr on the target — the field the fault path
reads. -/
theorem setThreadFaultHandlerOp_faultHandler (st st' : SystemState)
    (vTargetTid : SeLe4n.ValidThreadId) (cptr : SeLe4n.CPtr) (tcb : TCB)
    (hTcb : st.getTcb? vTargetTid.val = some tcb)
    (hObjInv : st.objects.invExt)
    (hStep : setThreadFaultHandlerOp st vTargetTid cptr = .ok st') :
    st'.getTcb? vTargetTid.val = some { tcb with faultHandler := some cptr } := by
  cases hR : resolveFaultHandlerCPtr st tcb cptr with
  | error e => simp [setThreadFaultHandlerOp, hTcb, hR] at hStep
  | ok tgt =>
      rw [setThreadFaultHandlerOp_ok_eq st vTargetTid cptr tcb tgt hTcb hR] at hStep
      cases hStep
      simp only [installFaultHandler]
      unfold SystemState.getTcb?
      rw [RHTable_getElem?_eq_get?,
        SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self st.objects vTargetTid.val.toObjId
          (KernelObject.tcb { tcb with faultHandler := some cptr }) hObjInv]

/-- Configuring a handler touches no scheduler state. -/
theorem setThreadFaultHandlerOp_scheduler_eq (st st' : SystemState)
    (vTargetTid : SeLe4n.ValidThreadId) (cptr : SeLe4n.CPtr)
    (hStep : setThreadFaultHandlerOp st vTargetTid cptr = .ok st') :
    st'.scheduler = st.scheduler := by
  cases hT : st.getTcb? vTargetTid.val with
  | none => simp [setThreadFaultHandlerOp, hT] at hStep
  | some tcb =>
      cases hR : resolveFaultHandlerCPtr st tcb cptr with
      | error e => simp [setThreadFaultHandlerOp, hT, hR] at hStep
      | ok tgt =>
          rw [setThreadFaultHandlerOp_ok_eq st vTargetTid cptr tcb tgt hT hR] at hStep
          cases hStep
          rfl

/-- A CPtr that does not resolve to an authorised endpoint capability is
refused — the negative that keeps "configured" and "usable" the same thing. -/
theorem setThreadFaultHandlerOp_rejects (st : SystemState)
    (vTargetTid : SeLe4n.ValidThreadId) (cptr : SeLe4n.CPtr) (tcb : TCB) (e : KernelError)
    (hTcb : st.getTcb? vTargetTid.val = some tcb)
    (hR : resolveFaultHandlerCPtr st tcb cptr = .error e) :
    setThreadFaultHandlerOp st vTargetTid cptr = .error e := by
  simp [setThreadFaultHandlerOp, hTcb, hR]

/-- **Resuming a thread that carries a fault retires the fault** — seL4's
`restart` semantics for a double-faulted thread, closing a misclassification
the review found.

The fail-closed suspend keeps `pendingFault` as a diagnostic.  `.tcbResume`
makes an `.Inactive` thread `.Ready` again, and if the fault stayed on the
TCB, the thread's next ordinary Call would be answered through
`replyTransferOnCore`'s fault branch: the server's reply would be decoded
against the stale fault and, for a VM fault, would reinstall the old snapshot
and rewind execution to the former fault PC.  So a resume answers the fault
itself, the way a payload-free handler reply does: the thread restarts at
the faulting instruction with the register window it held at the trap
(`faultRestartFrameOfContext`), and the fault is cleared.  If the handler
configuration was repaired in between (`setThreadFaultHandlerOp`), the
re-executed instruction faults again and is delivered this time; if not, it
suspends again — either way through the fault path, never through a stale
fault.  A thread carrying no fault is untouched. -/
def retirePendingFaultForResume (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  match st.getTcb? tid with
  | some tcb =>
      match tcb.pendingFault with
      | some tf => applyFaultRestart st tid (faultRestartFrameOfContext tf.context)
      | none => st
  | none => st

/-- After the retire step the thread carries no fault — so the ordinary reply
branch (`replyTransferOnCore_of_no_fault`) is the one every later reply to it
takes. -/
theorem retirePendingFaultForResume_pendingFault_none (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb) (hObjInv : st.objects.invExt) :
    ∀ tcb', (retirePendingFaultForResume st tid).getTcb? tid = some tcb' →
      tcb'.pendingFault = none := by
  intro tcb' hT'
  cases hF : tcb.pendingFault with
  | none =>
      have hEq : retirePendingFaultForResume st tid = st := by
        simp only [retirePendingFaultForResume, hTcb, hF]
      rw [hEq, hTcb] at hT'
      cases hT'
      exact hF
  | some tf =>
      have hEq : retirePendingFaultForResume st tid
          = applyFaultRestart st tid (faultRestartFrameOfContext tf.context) := by
        simp only [retirePendingFaultForResume, hTcb, hF]
      rw [hEq] at hT'
      exact applyFaultRestart_clears_pendingFault st tid _ tcb hTcb hObjInv tcb' hT'

/-- A thread with no fault is untouched — so on every resume of an ordinary
suspended thread the arm is the pre-review body verbatim. -/
theorem retirePendingFaultForResume_of_no_fault (st : SystemState)
    (tid : SeLe4n.ThreadId)
    (hNo : ∀ tcb : TCB, st.getTcb? tid = some tcb → tcb.pendingFault = none) :
    retirePendingFaultForResume st tid = st := by
  cases hT : st.getTcb? tid with
  | none => simp only [retirePendingFaultForResume, hT]
  | some tcb => simp only [retirePendingFaultForResume, hT, hNo tcb hT]

/-- The retire step touches no scheduler state: it writes registers and clears
a field, and the resume that follows is what makes the thread runnable. -/
@[simp] theorem retirePendingFaultForResume_scheduler_eq (st : SystemState)
    (tid : SeLe4n.ThreadId) :
    (retirePendingFaultForResume st tid).scheduler = st.scheduler := by
  cases hT : st.getTcb? tid with
  | none => simp only [retirePendingFaultForResume, hT]
  | some tcb =>
      cases hF : tcb.pendingFault with
      | none => simp only [retirePendingFaultForResume, hT, hF]
      | some tf =>
          simp only [retirePendingFaultForResume, hT, hF]
          exact applyFaultRestart_scheduler_eq st tid _

-- ============================================================================
-- §8  The trap frame's fault window, spilled into the thread (audit round;
--     relocated here in PR #887 review round 3 so the SVC seam can share it)
-- ============================================================================

/-- WS-RR RR4 (audit round): spill the trap frame's fault window into the
faulting thread's saved register context — the fault seam's twin of the SVC
seam's `Platform.FFI.writeFfiRegistersToTcb`.

`TCB.registerContext` is a partial mirror of the hardware file and, between
syscalls, holds the *last syscall's* arguments; the fault context has to be
built from what the thread held **at the trap**, because the unknown-syscall
message reports that window and a resume reinstalls it
(`applyFaultRestart`).  Total: a target that is not a TCB returns the state
unchanged, and the delivery then fails closed on its own lookup. -/
def writeFaultRegistersToTcb (st : SystemState) (tid : SeLe4n.ThreadId)
    (w : FaultRegisterWindow) : SystemState :=
  match st.getTcb? tid with
  | some tcb =>
      let tcb' : TCB := { tcb with registerContext := w.spill tcb.registerContext }
      { st with objects := st.objects.insert tid.toObjId (.tcb tcb') }
  | none => st

/-- The spill touches no scheduler state — it is a register write, and the
delivery it precedes is what deschedules the thread. -/
@[simp] theorem writeFaultRegistersToTcb_scheduler (st : SystemState)
    (tid : SeLe4n.ThreadId) (w : FaultRegisterWindow) :
    (writeFaultRegistersToTcb st tid w).scheduler = st.scheduler := by
  unfold writeFaultRegistersToTcb; cases st.getTcb? tid <;> rfl

/-- A target that is not a TCB is left alone. -/
theorem writeFaultRegistersToTcb_id_when_not_tcb (st : SystemState)
    (tid : SeLe4n.ThreadId) (w : FaultRegisterWindow) (hNone : st.getTcb? tid = none) :
    writeFaultRegistersToTcb st tid w = st := by
  unfold writeFaultRegistersToTcb; simp [hNone]

/-- The spilled thread's saved context is the spill of what it was. -/
theorem writeFaultRegistersToTcb_getTcb? (st : SystemState) (tid : SeLe4n.ThreadId)
    (w : FaultRegisterWindow) (tcb : TCB) (hTcb : st.getTcb? tid = some tcb)
    (hObjInv : st.objects.invExt) :
    (writeFaultRegistersToTcb st tid w).getTcb? tid
      = some { tcb with registerContext := w.spill tcb.registerContext } := by
  unfold writeFaultRegistersToTcb
  rw [hTcb]
  simp only
  unfold SystemState.getTcb?
  rw [RHTable_getElem?_eq_get?,
      SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self st.objects tid.toObjId
        (KernelObject.tcb { tcb with registerContext := w.spill tcb.registerContext }) hObjInv]

/-- **The fault context the entry delivers is the trap frame's**, word for
word: `sp` and `lr` are the saved `SP_EL0` and `x30`, and `x0`-`x7` are the
saved argument window — never the mirror's stale contents.  Composed from the
spill and `FaultRegisterWindow.ofRegisterFile_spill`; this is the theorem the
audit-round fix exists to make true. -/
theorem faultContextOfThread_writeFaultRegistersToTcb (st : SystemState)
    (tid : SeLe4n.ThreadId) (w : FaultRegisterWindow) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb) (hObjInv : st.objects.invExt)
    (faultIP spsr : UInt64) :
    faultContextOfThread (writeFaultRegistersToTcb st tid w) tid faultIP spsr =
      { faultIP := faultIP, sp := w.sp, lr := w.lr, spsr := spsr,
        gprs := (Array.range FaultContext.gprWindow).map w.gprAt } := by
  unfold faultContextOfThread
  rw [writeFaultRegistersToTcb_getTcb? st tid w tcb hTcb hObjInv]
  exact FaultRegisterWindow.ofRegisterFile_spill w tcb.registerContext faultIP spsr

end SeLe4n.Kernel
