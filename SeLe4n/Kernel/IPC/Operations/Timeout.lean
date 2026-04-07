/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.DualQueue.Core
import SeLe4n.Kernel.Scheduler.PriorityInheritance.Propagate

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- Z6-C: Timeout-driven IPC unblocking
-- ============================================================================

/-- Z6-C: Timeout error code written to register x0 when a thread's IPC
operation times out due to SchedContext budget expiry. Matches seL4 MCS
convention: timeout is signaled via the return register, not an exception.

**AE4-F (U-23/IPC-01): Timeout Detection Sentinel — Design Rationale**

`timeoutAwareReceive` detects prior timeouts via a composite check:
  (1) gpr x0 = timeoutErrorCode (0xFFFFFFFF), AND
  (2) ipcState = .ready

The AND condition mitigates false positives: legitimate IPC messages are
delivered via `pendingMessage` and set ipcState to `.waitingForReply` or
`.blocked`, not `.ready`. The gpr x0 sentinel is only written by
`timeoutThread`, which also sets ipcState to `.ready`.

For H3 hardware binding, consider replacing with a dedicated
`timedOut : Bool` field on TCB to eliminate the sentinel pattern entirely.
The composite check is sound for the current model but fragile if future
operations modify gpr x0 without updating ipcState simultaneously. -/
def timeoutErrorCode : SeLe4n.RegValue := ⟨0xFFFFFFFF⟩

/-- Z6-C1/C2/C3: Unblock a thread whose IPC operation has timed out due to
SchedContext budget expiry.

This operation:
1. **Queue removal** (Z6-C2): Removes the thread from the endpoint's send
   or receive queue using `endpointQueueRemove`.
2. **IPC state reset** (Z6-C1): Sets `tcb.ipcState := .ready` and clears
   `tcb.pendingMessage := none` and `tcb.timeoutBudget := none`.
3. **Scheduler re-enqueue** (Z6-C3): Sets the timeout error code in the
   thread's register context (`gpr 0 := timeoutErrorCode`) and re-enqueues
   the thread in the RunQueue at its current priority.

The `isReceiveQ` parameter indicates which queue the thread is blocked on:
- `true`: thread was in `blockedOnReceive` on the endpoint's receiveQ
- `false`: thread was in `blockedOnSend`/`blockedOnCall` on the endpoint's sendQ

**Precondition (AUD-Z6-2):** The caller must ensure `tid` refers to a thread
in a blocking IPC state (`blockedOnSend`, `blockedOnReceive`, `blockedOnCall`,
or `blockedOnReply`) on the endpoint identified by `endpointId`. The sole caller
`timeoutBlockedThreads` validates this via `tcbBlockingInfo`, which returns
`none` for non-blocking states. Calling this on a non-blocked thread would
incorrectly reset its state and write the timeout error code.

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
      -- D4-N: Capture blocking server before clearing ipcState — if the thread
      -- was in blockedOnReply, the server's pipBoost must be recomputed after
      -- this client is removed from the blocking graph.
      let maybeBlockingServer := match tcb.ipcState with
        | .blockedOnReply _ (some serverId) => some serverId
        | _ => none
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
        let st3 := ensureRunnable st2 tid
        -- D4-N: Revert PIP for the server if the timed-out thread was a waiter.
        -- Now that the client's ipcState is cleared, waitersOf won't include it,
        -- so revertPriorityInheritance correctly recomputes the server's pipBoost
        -- from remaining waiters only.
        match maybeBlockingServer with
        | some serverId =>
          .ok (PriorityInheritance.revertPriorityInheritance st3 serverId)
        | none => .ok st3

/-- Z6-I: Timeout-aware receive wrapper.

Checks whether a thread was timed out by the scheduler during a prior
blocking receive. The actual timeout is applied asynchronously by
`timeoutBlockedThreads` in the timer tick path (`timerTickBudget`), which
sets the timeout error code in register x0 and resets ipcState to `.ready`.

Detection: if `gpr x0 = timeoutErrorCode ∧ ipcState = .ready`, the thread
was timed out → returns `.timedOut` and clears the error code. Otherwise,
returns `.completed msg` with any pending message (or `IpcMessage.empty`).

The `endpointId` parameter is reserved for future validation (confirming the
timeout applies to the expected endpoint). It is not currently used. -/
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
