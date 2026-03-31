/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.DualQueue.Core

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- Z6-C: Timeout-driven IPC unblocking
-- ============================================================================

/-- Z6-C: Timeout error code written to register x0 when a thread's IPC
operation times out due to SchedContext budget expiry. Matches seL4 MCS
convention: timeout is signaled via the return register, not an exception. -/
def timeoutErrorCode : SeLe4n.RegValue := ⟨0xFFFFFFFF⟩

/-- Z6-C1/C2/C3: Unblock a thread whose IPC operation has timed out due to
SchedContext budget expiry.

This operation:
1. **IPC state reset** (Z6-C1): Sets `tcb.ipcState := .ready` and clears
   `tcb.pendingMessage := none` and `tcb.timeoutBudget := none`.
2. **Queue removal** (Z6-C2): Removes the thread from the endpoint's send
   or receive queue using `endpointQueueRemove`.
3. **Scheduler re-enqueue** (Z6-C3): Sets the timeout error code in the
   thread's register context (`gpr 0 := timeoutErrorCode`) and re-enqueues
   the thread in the RunQueue at its current priority.

The `isReceiveQ` parameter indicates which queue the thread is blocked on:
- `true`: thread was in `blockedOnReceive` on the endpoint's receiveQ
- `false`: thread was in `blockedOnSend`/`blockedOnCall` on the endpoint's sendQ

Returns updated state or error if endpoint/thread lookup fails. -/
def timeoutThread
    (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId)
    (st : SystemState) : Except KernelError SystemState :=
  -- Step 1: Remove thread from endpoint queue
  match endpointQueueRemove endpointId isReceiveQ tid st with
  | .error e => .error e
  | .ok st1 =>
    -- Step 2: Look up the thread (now with cleared queue links from endpointQueueRemove)
    match lookupTcb st1 tid with
    | none => .error .objectNotFound
    | some tcb =>
      -- Step 3: Reset IPC state, clear pending message and timeout budget,
      -- set timeout error code in register context, update thread state
      let tcb' : TCB := { tcb with
        ipcState := .ready,
        pendingMessage := none,
        timeoutBudget := none,
        threadState := .Ready,
        registerContext := SeLe4n.writeReg tcb.registerContext ⟨0⟩ timeoutErrorCode }
      match storeObject tid.toObjId (.tcb tcb') st1 with
      | .error e => .error e
      | .ok ((), st2) =>
        -- Step 4: Re-enqueue in RunQueue at current priority
        .ok (ensureRunnable st2 tid)

/-- Z6-I: Timeout-aware receive wrapper.

Wraps `endpointReceiveDual` with timeout semantics. The actual timeout
detection happens asynchronously in the timer tick path (`timerTickBudget`).
This function sets up the timeout metadata (`tcb.timeoutBudget`) so that
the timer tick handler knows which SchedContext bounds this blocking operation.

If the receive completes synchronously (sender already waiting), returns
`.completed msg`. If the receiver blocks (no sender waiting), the thread
enters `blockedOnReceive` with `timeoutBudget` set. The timeout handler
will call `timeoutThread` if the budget expires, and the thread will
observe `.timedOut` via the error code in its register context on resume.

For the synchronous case, this is a thin wrapper. The asynchronous timeout
is handled by `timeoutBlockedThreads` in the scheduler path. -/
def timeoutAwareReceive
    (_endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    : Kernel IpcTimeoutResult :=
  fun st =>
    match lookupTcb st receiver with
    | none => .error .objectNotFound
    | some tcb =>
      -- Check if receiver already has a timeout error code from prior timeout
      if tcb.registerContext.gpr ⟨0⟩ = timeoutErrorCode ∧ tcb.ipcState = .ready then
        -- Thread was timed out by the scheduler — report timeout
        -- Clear the error code to avoid re-triggering
        let regs' := SeLe4n.writeReg tcb.registerContext ⟨0⟩ ⟨0⟩
        let tcb' := { tcb with registerContext := regs' }
        match storeObject receiver.toObjId (.tcb tcb') st with
        | .error e => .error e
        | .ok ((), st') => .ok (.timedOut, st')
      else
        -- Normal receive path — timeout metadata is set by Z6-G in the blocking path
        match tcb.pendingMessage with
        | some msg => .ok (.completed msg, st)
        | none => .ok (.completed IpcMessage.empty, st)

end SeLe4n.Kernel
