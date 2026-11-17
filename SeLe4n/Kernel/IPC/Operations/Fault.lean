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
transfers.  A fault payload transfers none (`sendCapRequest_fault`), so it is
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

/-- WS-RR RR4.7 (**handler resolution**), WS-SX SX6.5: the fault handler is
the capability in the thread's fault-handler slot (`TCB.faultHandlerSlot`,
seL4-MCS's `tcbFaultHandler`), read as `handleFault` reads it
(`TCB_PTR_CTE_PTR(tptr, tcbFaultHandler)->cap`).  `TCB_SetSpace` copies the
slot's capability in only once it is a valid handler (`validFaultHandler`: an
endpoint capability with send and a grant right), so the delivery looks nothing
up through the thread's CSpace.

The gates, in seL4's order:

1. the thread exists;
2. the slot **holds** a capability: an empty slot is seL4's
   `seL4_Fault_CapFault` with `lookup_fault_missing_capability_new(0)`
   (`faulthandler.c`), which takes the RR4.9 path;
3. the capability satisfies `faultHandlerCapAuthorized` — send, and grant or
   grant-reply (RR4.8), the rights `sendFaultIPC` asserts;
4. it names an object that really is an endpoint.

Read-only: resolution never mutates the state. -/
def resolveFaultHandler (st : SystemState) (tid : SeLe4n.ThreadId) :
    Except KernelError FaultHandlerTarget :=
  match st.getTcb? tid with
  | none => .error .objectNotFound
  | some tcb =>
      match tcb.faultHandlerCap with
      | none => .error (.failedLookup false (.missingCapability 0))
      | some cap =>
          if faultHandlerCapAuthorized cap then
            match cap.target with
            | .object epId =>
                match st.getEndpoint? epId with
                | some _ =>
                    .ok { endpoint := epId, cap := cap, cspaceRoot := tcb.cspaceRoot }
                | none   => .error (.invalidCapability 0)
            | _ => .error (.invalidCapability 0)
          else .error .illegalAuthority

/-- WS-RR RR4.10 (**the negative**): a thread whose fault-handler slot is empty
never resolves — the arm that sends it to the fail-closed suspend — and the
refusal is seL4's missing-capability lookup fault at depth 0. -/
theorem resolveFaultHandler_none_of_noHandler (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb) (hNone : tcb.faultHandlerCap = none) :
    resolveFaultHandler st tid = .error (.failedLookup false (.missingCapability 0)) := by
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
  unfold resolveFaultHandler at hOk
  repeat' split at hOk
  all_goals (try (injection hOk with hEq; subst hEq))
  all_goals simp_all

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

/-- WS-RR RR4.6 (**the prefilter never fires**): a fault message is inside
the register bound `endpointCall` checks before it looks at the endpoint.

This is what makes the delivery's failure surface depend on the *endpoint
state* alone — a fault can never be dropped because the kernel built a message
its own transport rejects. -/
theorem faultMessage_within_prefilters (f : Fault) (ctx : FaultContext)
    (badge : Option SeLe4n.Badge) :
    ¬ ((faultMessage f ctx badge).registers.size > maxMessageRegisters) :=
  Nat.not_lt.mpr (Architecture.encodeFault_within_budget f ctx)

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
reply that answers it can find it.  Total: a non-TCB target is unchanged.
The write is the typed in-place rewrite `SystemState.updateTcb` (`v0.35.70`).

WS-ZA ZA4.7: it also marks the fault as the message the thread holds
(`ipcFaultSend`): a fault Call that blocks parks no message, and the receive
that takes it builds the message from `pendingFault` (`blockedSenderMessage`),
as seL4 builds it from `tcbFault`. -/
def recordPendingFault (st : SystemState) (tid : SeLe4n.ThreadId)
    (tf : ThreadFault) : SystemState :=
  st.updateTcb tid fun tcb => { tcb.setPendingFault (some tf) with ipcFaultSend := true }

-- **WS-RR RR8.16** (`v0.35.200`): relocated here from the staged
-- `IPC/Invariant/FaultPreservation.lean` — a frame over a production transition
-- that reads no staged surface belongs beside that transition, where the
-- production bundle lifts can cite it.

/-- WS-RR RR4.17: `recordPendingFault` preserves the object-store invariant —
one `insert` of a well-typed TCB. -/
theorem recordPendingFault_preserves_objects_invExt
    (st : SystemState) (tid : SeLe4n.ThreadId) (tf : ThreadFault)
    (hObjInv : st.objects.invExt) :
    (recordPendingFault st tid tf).objects.invExt := by
  unfold recordPendingFault
  exact SystemState.updateTcb_preserves_objects_invExt _ _ _ hObjInv

/-- **WS-RR RR8.16** (`v0.35.200`): recording a fault is a `kindPreservingWrite`
and writes neither derivation table — `updateTcb`'s own facts. -/
theorem recordPendingFault_kindPreservingWrite (st : SystemState)
    (tid : SeLe4n.ThreadId) (tf : ThreadFault) (hObjInv : st.objects.invExt) :
    kindPreservingWrite st (recordPendingFault st tid tf) :=
  SystemState.updateTcb_kindPreservingWrite st tid _ hObjInv

theorem recordPendingFault_cdt_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (tf : ThreadFault) :
    (recordPendingFault st tid tf).cdt = st.cdt :=
  SystemState.updateTcb_cdt st tid _

/-- WS-RR RR4.17 (frame): recording a fault is a single TCB write — the
scheduler is untouched, so a delivery's runnability statement reads through
it. -/
@[simp] theorem recordPendingFault_scheduler_eq (st : SystemState)
    (tid : SeLe4n.ThreadId) (tf : ThreadFault) :
    (recordPendingFault st tid tf).scheduler = st.scheduler := by
  unfold recordPendingFault
  exact SystemState.updateTcb_scheduler st tid _

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
(`threadState` is read by the scheduler's invariants, not the IPC bundle).

The `.Inactive` store is the typed in-place rewrite `SystemState.updateTcb`
over the descheduled state (`v0.35.70`): the identity on a miss, which is the
totality this transition must keep. -/
def faultSuspend (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  (removeRunnable st tid).updateTcb tid fun tcb => { tcb with threadState := .Inactive }

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
  (removeRunnable st tid).updateTcb tid fun tcb =>
    { tcb.setPendingFault none with threadState := .Inactive }

/-- WS-RR RR4.9: a suspended thread is `.Inactive` — the state the scheduler
never dispatches. -/
theorem faultSuspend_threadState (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (hTcb : (removeRunnable st tid).getTcb? tid = some tcb)
    (hObjInv : (removeRunnable st tid).objects.invExt) :
    (faultSuspend st tid).getTcb? tid = some { tcb with threadState := .Inactive } := by
  unfold faultSuspend
  rw [SystemState.updateTcb_getTcb?_self _ _ _ hObjInv, hTcb]
  rfl

/-- WS-RR RR4.9 (frame): descheduling and marking a thread `.Inactive` writes
the run queue and the current slot and nothing else in the scheduler — the
`.Inactive` store is an object write. -/
theorem faultSuspend_scheduler_eq (st : SystemState) (tid : SeLe4n.ThreadId) :
    (faultSuspend st tid).scheduler = (removeRunnable st tid).scheduler := by
  unfold faultSuspend
  exact SystemState.updateTcb_scheduler _ _ _

/-- WS-RR RR4.15 (frame): the same for the reply-declined disposition. -/
theorem faultAbandon_scheduler_eq (st : SystemState) (tid : SeLe4n.ThreadId) :
    (faultAbandon st tid).scheduler = (removeRunnable st tid).scheduler := by
  unfold faultAbandon
  exact SystemState.updateTcb_scheduler _ _ _

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
convenient.  The store is the typed in-place rewrite `SystemState.updateTcb`
(`v0.35.70`).  WS-ZA ZA6.31: inlined, so a restart built from the thread's
own context (the resume's, `retirePendingFaultForResume`) writes that
context's words into the register file and builds no frame record. -/
@[inline] def applyFaultRestart (st : SystemState) (faulted : SeLe4n.ThreadId)
    (frame : Architecture.FaultRestartFrame) : SystemState :=
  st.updateTcb faulted fun tcb => ((tcb.withRestartFrame frame).setPendingFault none)

/-- WS-RR RR4.16: and it preserves the object-store invariant. -/
theorem applyFaultRestart_preserves_objects_invExt
    (st : SystemState) (tid : SeLe4n.ThreadId) (frame : Architecture.FaultRestartFrame)
    (hObjInv : st.objects.invExt) :
    (applyFaultRestart st tid frame).objects.invExt := by
  unfold applyFaultRestart
  exact SystemState.updateTcb_preserves_objects_invExt _ _ _ hObjInv

/-- **WS-RR RR8.16** (`v0.35.200`): installing a restart frame is a
`kindPreservingWrite` and writes neither derivation table. -/
theorem applyFaultRestart_kindPreservingWrite (st : SystemState)
    (faulted : SeLe4n.ThreadId) (frame : Architecture.FaultRestartFrame)
    (hObjInv : st.objects.invExt) :
    kindPreservingWrite st (applyFaultRestart st faulted frame) :=
  SystemState.updateTcb_kindPreservingWrite st faulted _ hObjInv

theorem applyFaultRestart_cdt_eq (st : SystemState) (faulted : SeLe4n.ThreadId)
    (frame : Architecture.FaultRestartFrame) :
    (applyFaultRestart st faulted frame).cdt = st.cdt :=
  SystemState.updateTcb_cdt st faulted _

/-- WS-RR RR4.15 (frame): installing a restart frame never touches the
scheduler — it decides *where the thread resumes*, not *whether* it is
scheduled. -/
@[simp] theorem applyFaultRestart_scheduler_eq (st : SystemState)
    (faulted : SeLe4n.ThreadId) (frame : Architecture.FaultRestartFrame) :
    (applyFaultRestart st faulted frame).scheduler = st.scheduler := by
  unfold applyFaultRestart
  exact SystemState.updateTcb_scheduler st faulted _

/-- **WS-RR RR8.12 Cut C6d** (frame): and it never touches the machine — the
restart frame goes into the *thread's* saved context, not into the executing
core's register bank, which is what makes the restart per-core silent and so
confined to the empty core set. -/
@[simp] theorem applyFaultRestart_machine_eq (st : SystemState)
    (faulted : SeLe4n.ThreadId) (frame : Architecture.FaultRestartFrame) :
    (applyFaultRestart st faulted frame).machine = st.machine := by
  unfold applyFaultRestart
  exact SystemState.updateTcb_machine st faulted _

/-- WS-RR RR4.15: the restarted thread's saved `pc` is the frame's — the
statement RR4.19's progress argument consumes, since "the thread does not
silently re-execute the faulting instruction" is exactly "its saved `pc` is
what the handler chose". -/
theorem applyFaultRestart_pc (st : SystemState) (faulted : SeLe4n.ThreadId)
    (frame : Architecture.FaultRestartFrame) (tcb : TCB)
    (hTcb : st.getTcb? faulted = some tcb) (hObjInv : st.objects.invExt) :
    (applyFaultRestart st faulted frame).getTcb? faulted
      = some ((tcb.withRestartFrame frame).setPendingFault none) := by
  unfold applyFaultRestart
  rw [SystemState.updateTcb_getTcb?_self _ _ _ hObjInv, hTcb]
  rfl

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

/-- WS-ZA ZA6.22: **retire a thread's fault record and nothing else** — the
fault cleared, the saved registers, the scheduler and the machine untouched.
The resume's retire takes this branch for a thread some core still holds
(`retirePendingFaultForResume`). -/
def discardPendingFault (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  st.updateTcb tid fun tcb => (tcb.setPendingFault none)

theorem discardPendingFault_preserves_objects_invExt (st : SystemState)
    (tid : SeLe4n.ThreadId) (hObjInv : st.objects.invExt) :
    (discardPendingFault st tid).objects.invExt :=
  SystemState.updateTcb_preserves_objects_invExt _ _ _ hObjInv

@[simp] theorem discardPendingFault_scheduler_eq (st : SystemState) (tid : SeLe4n.ThreadId) :
    (discardPendingFault st tid).scheduler = st.scheduler :=
  SystemState.updateTcb_scheduler st tid _

@[simp] theorem discardPendingFault_machine_eq (st : SystemState) (tid : SeLe4n.ThreadId) :
    (discardPendingFault st tid).machine = st.machine :=
  SystemState.updateTcb_machine st tid _

/-- The retired thread is its record with the fault cleared. -/
theorem discardPendingFault_getTcb?_self (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (hTcb : st.getTcb? tid = some tcb) (hObjInv : st.objects.invExt) :
    (discardPendingFault st tid).getTcb? tid = some (tcb.setPendingFault none) := by
  unfold discardPendingFault
  rw [SystemState.updateTcb_getTcb?_self _ _ _ hObjInv, hTcb]
  rfl


-- ============================================================================
-- §7  Review round (PR #887) — resuming past a fault
-- ============================================================================

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
configuration was repaired in between (`TCB_SetSpace`'s fault endpoint), the
re-executed instruction faults again and is delivered this time; if not, it
suspends again — either way through the fault path, never through a stale
fault.  A thread carrying no fault is untouched.

WS-ZA ZA6.22: a thread whose registers some core still holds
(`MachineState.residentOnSomeCore`: a core it ran on was vacated by a remote
suspend and has not yet taken the entry that saves them) has its fault record
retired without the restart frame (`discardPendingFault`).  That core's save
writes its live registers over the TCB's, so a frame written here would be lost
while the record it answers was cleared; and the live registers are the
thread's context, not the fault window, because it ran after the fault.  Once
every cancellation restore retires the record (`TCB.restoredToReady`) a thread
that ran carries none, so the branch is the fail-safe for a state the restores
already exclude; it is what makes the resume's register write land only on a
thread no core holds (`retirePendingFaultForResume_registers_of_resident`). -/
def retirePendingFaultForResume (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  match st.getTcb? tid with
  | some tcb =>
      match tcb.pendingFault with
      | some tf =>
          if st.machine.residentOnSomeCore tid then discardPendingFault st tid
          else applyFaultRestart st tid (faultRestartFrameOfContext tf.context)
      | none => st
  | none => st

/-- WS-ZA ZA6.31: **the compiled resume retire** — the fault asked of the
thread's kind code, and the restart frame read from the fault words of the
thread the write is handed (`TCB.faultWords`), so the retire builds no decoded
record and captures no thread (`retirePendingFaultForResume_eq_impl`). -/
@[inline] def retirePendingFaultForResumeImpl (st : SystemState) (tid : SeLe4n.ThreadId) :
    SystemState :=
  match st.getTcb? tid with
  | some tcb =>
      if tcb.faultWords.isFault then
        if st.machine.residentOnSomeCore tid then discardPendingFault st tid
        else st.updateTcb tid fun t =>
          ((t.withRestartFrame (faultRestartFrameOfContext t.faultWords.context)).setPendingFault
            none)
      else st
  | none => st

@[csimp] theorem retirePendingFaultForResume_eq_impl :
    @retirePendingFaultForResume = @retirePendingFaultForResumeImpl := by
  funext st tid
  unfold retirePendingFaultForResume retirePendingFaultForResumeImpl
  cases hT : st.getTcb? tid with
  | none => rfl
  | some tcb =>
    simp only []
    cases hF : tcb.pendingFault with
    | none =>
      have hI : tcb.faultWords.isFault = false := by
        rw [← TCB.pendingFault_isSome, hF]; rfl
      simp only [hI, Bool.false_eq_true, ↓reduceIte]
    | some tf =>
      have hI : tcb.faultWords.isFault = true := by
        rw [← TCB.pendingFault_isSome, hF]; rfl
      have hC : tf.context = tcb.faultWords.context := ThreadFaultWords.decode_context hF
      simp only [hI, ↓reduceIte]
      split
      · rfl
      · unfold applyFaultRestart
        rw [SystemState.updateTcb_eq_of_some hT, SystemState.updateTcb_eq_of_some hT, hC]

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
      cases hR : st.machine.residentOnSomeCore tid with
      | true =>
          have hEq : retirePendingFaultForResume st tid = discardPendingFault st tid := by
            simp only [retirePendingFaultForResume, hTcb, hF, hR, if_true]
          rw [hEq, discardPendingFault_getTcb?_self st tid tcb hTcb hObjInv] at hT'
          cases hT'; rfl
      | false =>
          have hEq : retirePendingFaultForResume st tid
              = applyFaultRestart st tid (faultRestartFrameOfContext tf.context) := by
            simp only [retirePendingFaultForResume, hTcb, hF, hR, Bool.false_eq_true, if_false]
          rw [hEq] at hT'
          exact applyFaultRestart_clears_pendingFault st tid _ tcb hTcb hObjInv tcb' hT'

/-- WS-ZA ZA6.22: after the retire step the thread carries no fault, whatever
the store held — the form the resume's restore consumes (`TCB.restoredToReady`
clears the record, so it rewrites nothing only on a thread carrying none). -/
theorem retirePendingFaultForResume_noFault (st : SystemState) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt) :
    ∀ tcb', (retirePendingFaultForResume st tid).getTcb? tid = some tcb' →
      tcb'.pendingFault = none := by
  cases hT : st.getTcb? tid with
  | none =>
      intro tcb' h
      rw [show retirePendingFaultForResume st tid = st by
        simp only [retirePendingFaultForResume, hT], hT] at h
      cases h
  | some tcb => exact retirePendingFaultForResume_pendingFault_none st tid tcb hT hObjInv

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
          split
          · exact discardPendingFault_scheduler_eq st tid
          · exact applyFaultRestart_scheduler_eq st tid _

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
unchanged, and the delivery then fails closed on its own lookup.  The write is
the typed in-place rewrite `SystemState.updateTcb` (`v0.35.69`), as the SVC
seam's spill and the return-frame staging are. -/
@[inline] def writeFaultRegistersToTcb (st : SystemState) (tid : SeLe4n.ThreadId)
    (w : FaultRegisterWindow) : SystemState :=
  st.updateTcb tid fun tcb => { tcb with registerContext := w.spill tcb.registerContext }

/-- The spill touches no scheduler state — it is a register write, and the
delivery it precedes is what deschedules the thread. -/
@[simp] theorem writeFaultRegistersToTcb_scheduler (st : SystemState)
    (tid : SeLe4n.ThreadId) (w : FaultRegisterWindow) :
    (writeFaultRegistersToTcb st tid w).scheduler = st.scheduler := by
  unfold writeFaultRegistersToTcb; exact SystemState.updateTcb_scheduler st tid _

/-- A target that is not a TCB is left alone. -/
theorem writeFaultRegistersToTcb_id_when_not_tcb (st : SystemState)
    (tid : SeLe4n.ThreadId) (w : FaultRegisterWindow) (hNone : st.getTcb? tid = none) :
    writeFaultRegistersToTcb st tid w = st := by
  unfold writeFaultRegistersToTcb; exact SystemState.updateTcb_eq_self_of_none hNone _

/-- The spilled thread's saved context is the spill of what it was. -/
theorem writeFaultRegistersToTcb_getTcb? (st : SystemState) (tid : SeLe4n.ThreadId)
    (w : FaultRegisterWindow) (tcb : TCB) (hTcb : st.getTcb? tid = some tcb)
    (hObjInv : st.objects.invExt) :
    (writeFaultRegistersToTcb st tid w).getTcb? tid
      = some { tcb with registerContext := w.spill tcb.registerContext } := by
  unfold writeFaultRegistersToTcb
  rw [SystemState.updateTcb_getTcb?_self st tid _ hObjInv, hTcb]
  rfl

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
        x0 := w.x0, x1 := w.x1, x2 := w.x2, x3 := w.x3,
        x4 := w.x4, x5 := w.x5, x6 := w.x6, x7 := w.x7 } := by
  unfold faultContextOfThread
  rw [writeFaultRegistersToTcb_getTcb? st tid w tcb hTcb hObjInv]
  exact FaultRegisterWindow.ofRegisterFile_spill w tcb.registerContext faultIP spsr

end SeLe4n.Kernel
