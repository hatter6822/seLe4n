/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- WS-G4/F-P02: O(1) amortized remove via RunQueue. -/
def removeRunnable (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  { st with
      scheduler := {
        st.scheduler with
          runQueue := st.scheduler.runQueue.remove tid
          current := if st.scheduler.current = some tid then none else st.scheduler.current
      }
  }

/-- WS-G4/F-P02: O(1) amortized insert via RunQueue.
    Priority defaults to 0 when TCB priority is not yet modelled. -/
def ensureRunnable (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  if tid ∈ st.scheduler.runQueue then
    st
  else
    match st.objects[tid.toObjId]? with
    | some (.tcb tcb) =>
        { st with
            scheduler := {
              st.scheduler with
                runQueue := st.scheduler.runQueue.insert tid tcb.priority
            }
        }
    | _ => st

def lookupTcb (st : SystemState) (tid : SeLe4n.ThreadId) : Option TCB :=
  if tid.isReserved then
    none
  else
    match st.objects[tid.toObjId]? with
    | some (.tcb tcb) => some tcb
    | _ => none

/-- If lookupTcb succeeds, the underlying objects map has a TCB at tid.toObjId. -/
theorem lookupTcb_some_objects
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (h : lookupTcb st tid = some tcb) :
    st.objects[tid.toObjId]? = some (.tcb tcb) := by
  unfold lookupTcb at h
  cases hRes : tid.isReserved
  · -- false
    simp [hRes] at h; revert h
    cases hObj : st.objects[tid.toObjId]? with
    | none => simp
    | some obj => cases obj <;> simp
  · -- true: contradiction
    simp [hRes] at h

def storeTcbIpcState (st : SystemState) (tid : SeLe4n.ThreadId) (ipcState : ThreadIpcState) : Except KernelError SystemState :=
  match lookupTcb st tid with
  | none => .error .objectNotFound
  | some tcb =>
      match storeObject tid.toObjId (.tcb { tcb with ipcState := ipcState }) st with
      | .error e => .error e
      | .ok ((), st') => .ok st'

/-- WS-L1/L1-C: Variant of `storeTcbIpcState` that accepts a pre-looked-up
TCB, bypassing the internal `lookupTcb`. Use when the caller has already
validated the TCB and no intervening operation has modified it. -/
def storeTcbIpcState_fromTcb (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (ipcState : ThreadIpcState) : Except KernelError SystemState :=
  match storeObject tid.toObjId (.tcb { tcb with ipcState := ipcState }) st with
  | .error e => .error e
  | .ok ((), st') => .ok st'

/-- WS-L1/L1-C: Equivalence theorem — `_fromTcb` produces identical results
to the original when the provided TCB matches the state. -/
theorem storeTcbIpcState_fromTcb_eq
    (hLookup : lookupTcb st tid = some tcb) :
    storeTcbIpcState_fromTcb st tid tcb ipcState =
    storeTcbIpcState st tid ipcState := by
  unfold storeTcbIpcState_fromTcb storeTcbIpcState
  simp [hLookup]

/-- WS-F1: Store a pending IPC message in a thread's TCB.
Used during IPC send to stage the message for transfer. -/
def storeTcbPendingMessage (st : SystemState) (tid : SeLe4n.ThreadId) (msg : Option IpcMessage) : Except KernelError SystemState :=
  match lookupTcb st tid with
  | none => .error .objectNotFound
  | some tcb =>
      match storeObject tid.toObjId (.tcb { tcb with pendingMessage := msg }) st with
      | .error e => .error e
      | .ok ((), st') => .ok st'

/-- WS-F1: Combined store of IPC state and pending message in a single TCB update.
Avoids two separate storeObject calls and simplifies proof tracking. -/
def storeTcbIpcStateAndMessage (st : SystemState) (tid : SeLe4n.ThreadId)
    (ipcState : ThreadIpcState) (msg : Option IpcMessage) : Except KernelError SystemState :=
  match lookupTcb st tid with
  | none => .error .objectNotFound
  | some tcb =>
      match storeObject tid.toObjId (.tcb { tcb with ipcState := ipcState, pendingMessage := msg }) st with
      | .error e => .error e
      | .ok ((), st') => .ok st'

/-- WS-L1/L1-B: Variant of `storeTcbIpcStateAndMessage` that accepts a
pre-looked-up TCB, bypassing the internal `lookupTcb`. Use when the caller
has already validated the TCB on the same state. -/
def storeTcbIpcStateAndMessage_fromTcb (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (ipcState : ThreadIpcState) (msg : Option IpcMessage)
    : Except KernelError SystemState :=
  match storeObject tid.toObjId (.tcb { tcb with ipcState := ipcState, pendingMessage := msg }) st with
  | .error e => .error e
  | .ok ((), st') => .ok st'

/-- WS-L1/L1-B: Equivalence theorem — `_fromTcb` produces identical results
to the original when the provided TCB matches the state. All existing
preservation theorems for `storeTcbIpcStateAndMessage` apply to `_fromTcb`
via rewriting with this theorem. -/
theorem storeTcbIpcStateAndMessage_fromTcb_eq
    (hLookup : lookupTcb st tid = some tcb) :
    storeTcbIpcStateAndMessage_fromTcb st tid tcb ipcState msg =
    storeTcbIpcStateAndMessage st tid ipcState msg := by
  unfold storeTcbIpcStateAndMessage_fromTcb storeTcbIpcStateAndMessage
  simp [hLookup]

/-- WS-L1: `lookupTcb` is preserved when `storeObject` targets a notification
(different ObjId from any TCB). Used to justify `_fromTcb` usage after an
intervening notification store. Accepts both `((), st')` and `pair` forms. -/
theorem lookupTcb_preserved_by_storeObject_notification
    {st : SystemState} {pair : Unit × SystemState} {tid : SeLe4n.ThreadId}
    {tcb : TCB} {notifId : SeLe4n.ObjId} {ntfn : Notification}
    {obj : KernelObject}
    (hLookup : lookupTcb st tid = some tcb)
    (hNtfn : st.objects[notifId]? = some (.notification ntfn))
    (hObjInv : st.objects.invExt)
    (hStore : storeObject notifId obj st = .ok pair) :
    lookupTcb pair.2 tid = some tcb := by
  have hStore' : storeObject notifId obj st = .ok ((), pair.2) := by
    rw [show pair = ((), pair.2) from by cases pair; rfl] at hStore; exact hStore
  have hTcbObj := lookupTcb_some_objects st tid tcb hLookup
  have hNe : tid.toObjId ≠ notifId := by
    intro heq; rw [← heq] at hNtfn; rw [hNtfn] at hTcbObj; cases hTcbObj
  have hPreserved := storeObject_objects_ne st pair.2 notifId tid.toObjId obj hNe hObjInv hStore'
  unfold lookupTcb at hLookup ⊢
  rw [hPreserved]
  exact hLookup

-- ============================================================================
-- Z7: SchedContext Donation Helpers
-- ============================================================================

/-- Z7-B2: Transfer a client's SchedContext to a passive server during IPC Call.

Performs the bidirectional binding:
1. Server TCB gets `schedContextBinding := .donated(clientScId, clientTid)`
2. SchedContext `boundThread` updated to point to server

**Preconditions** (enforced by caller `endpointCall`):
- Server has `schedContextBinding = .unbound` (passive)
- Client has `schedContextBinding = .bound clientScId`
- SchedContext `sc.boundThread = some clientTid`

Returns the updated state or error if lookups fail.

**Atomicity contract (AC3-A / I-02)**:
This function performs 2 sequential `storeObject` mutations (through states
`st` → `st1` → `st2`) with an intermediate lookup:
  1. `storeObject` SchedContext with `boundThread := some serverTid` → `st1`.
  2. `lookupTcb st1 serverTid` to find the server TCB (pure read, no mutation).
  3. `storeObject` server TCB with `schedContextBinding := .donated` → `st2`.
In the `KernelM` monad (`Except KernelError`), `.error` carries **no state** —
only the error value. If step 1 succeeds but step 2 or 3 fails, the
intermediate state `st1` is discarded by the monad's `bind` operation and the
caller receives `.error` with no access to the partial state. There is no
"partial state leak" risk in the pure model.
On hardware, kernel transitions execute with interrupts disabled (single-core
microkernel), so no concurrent observer can see intermediate states. -/
def donateSchedContext
    (st : SystemState)
    (clientTid : SeLe4n.ThreadId) (serverTid : SeLe4n.ThreadId)
    (clientScId : SeLe4n.SchedContextId) : Except KernelError SystemState :=
  -- Step 1: Look up the SchedContext
  match st.objects[clientScId.toObjId]? with
  | some (.schedContext sc) =>
    -- AUD-3b: Defense-in-depth — verify SchedContext is bound to the caller
    if sc.boundThread != some clientTid then .error .invalidArgument
    else
    -- Step 2: Update SchedContext to point to server
    let sc' := { sc with boundThread := some serverTid }
    match storeObject clientScId.toObjId (.schedContext sc') st with
    | .error e => .error e
    | .ok ((), st1) =>
      -- Step 3: Look up and update server TCB with donated binding
      match lookupTcb st1 serverTid with
      | none => .error .objectNotFound
      | some serverTcb =>
        let serverTcb' := { serverTcb with
          schedContextBinding := .donated clientScId clientTid }
        match storeObject serverTid.toObjId (.tcb serverTcb') st1 with
        | .error e => .error e
        | .ok ((), st2) =>
          -- S-05/PERF-O1: Add server to per-SchedContext thread index
          .ok { st2 with scThreadIndex :=
            (scThreadIndexAdd st2.scThreadIndex clientScId serverTid) }
  | _ => .error .objectNotFound

/-- Z7-C2: Return a donated SchedContext from a server back to the original
client after reply.

Performs the reverse binding:
1. SchedContext `boundThread` updated to point back to original client
2. Client TCB gets `schedContextBinding := .bound scId`
3. Server TCB gets `schedContextBinding := .unbound`

**Preconditions** (enforced by caller `endpointReply`):
- Server has `schedContextBinding = .donated(scId, originalOwner)`

Returns the updated state or error if lookups fail.

**Atomicity contract (AC3-A / I-02 / I-03)**:
This function performs 3 sequential `storeObject` mutations through states
`st` → `st1` → `st2` → `st3`. The same monad-level atomicity argument as
`donateSchedContext` applies: on `.error`, no intermediate state is returned
to the caller. The `Except.bind` combinator discards partial states on
failure. On hardware, interrupts are disabled throughout kernel transitions,
providing single-core atomicity for the 3-step update sequence. -/
def returnDonatedSchedContext
    (st : SystemState)
    (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId)
    (originalOwner : SeLe4n.ThreadId) : Except KernelError SystemState :=
  -- Step 1: Look up and update SchedContext to point back to original owner
  match st.objects[scId.toObjId]? with
  | some (.schedContext sc) =>
    let sc' := { sc with boundThread := some originalOwner }
    match storeObject scId.toObjId (.schedContext sc') st with
    | .error e => .error e
    | .ok ((), st1) =>
      -- Step 2: Look up and update client TCB with bound binding
      match lookupTcb st1 originalOwner with
      | none => .error .objectNotFound
      | some clientTcb =>
        let clientTcb' := { clientTcb with
          schedContextBinding := .bound scId }
        match storeObject originalOwner.toObjId (.tcb clientTcb') st1 with
        | .error e => .error e
        | .ok ((), st2) =>
          -- Step 3: Look up and update server TCB to unbound
          match lookupTcb st2 serverTid with
          | none => .error .objectNotFound
          | some serverTcb =>
            let serverTcb' := { serverTcb with
              schedContextBinding := .unbound }
            match storeObject serverTid.toObjId (.tcb serverTcb') st2 with
            | .error e => .error e
            | .ok ((), st3) =>
              -- S-05/PERF-O1: Remove server from per-SchedContext thread index
              .ok { st3 with scThreadIndex :=
                (scThreadIndexRemove st3.scThreadIndex scId serverTid) }
  | _ => .error .objectNotFound

/-- Z7-E: Clean up an active donation when a server with `.donated` binding
blocks on receive without replying first (abnormal path).

Returns the SchedContext to the original owner and sets the server to unbound.
This prevents resource leaks when a server drops a call without replying. -/
def cleanupActiveDonation
    (st : SystemState)
    (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId)
    (originalOwner : SeLe4n.ThreadId) : Except KernelError SystemState :=
  returnDonatedSchedContext st serverTid scId originalOwner

/-- AI4-A (M-01): Clean up stale donation before a server blocks on receive.

If the receiver has a `.donated` binding from a previous call that was never
replied to (abnormal path), return the SchedContext to the original owner
before blocking. Otherwise, return the state unchanged.

Moved from Donation.lean to Endpoint.lean to break the import cycle
(Donation.lean → Transport.lean → Core.lean → Operations.lean → Endpoint.lean).
This placement allows Transport.lean to call the function via its transitive
import chain. -/
def cleanupPreReceiveDonation (st : SystemState) (receiver : SeLe4n.ThreadId) : SystemState :=
  match lookupTcb st receiver with
  | none => st
  | some recvTcb =>
    match recvTcb.schedContextBinding with
    | .donated scId originalOwner =>
      match returnDonatedSchedContext st receiver scId originalOwner with
      | .error _ => st    -- Defensive: return unchanged on error
      | .ok st' => st'
    | _ => st             -- No donation to clean up

/-- Z7: storeObject preserves the scheduler field. -/
private theorem storeObject_scheduler_eq_z7 (st : SystemState) (oid : SeLe4n.ObjId)
    (obj : KernelObject) (pair : Unit × SystemState)
    (h : storeObject oid obj st = .ok pair) :
    pair.2.scheduler = st.scheduler := by
  unfold storeObject at h; cases h; rfl

/-- Z7-C: returnDonatedSchedContext only modifies objects — scheduler preserved. -/
theorem returnDonatedSchedContext_scheduler_eq
    (st st' : SystemState)
    (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId)
    (originalOwner : SeLe4n.ThreadId)
    (h : returnDonatedSchedContext st serverTid scId originalOwner = .ok st') :
    st'.scheduler = st.scheduler := by
  unfold returnDonatedSchedContext at h
  revert h
  cases hObj : st.objects[scId.toObjId]? with
  | none => intro h; cases h
  | some obj =>
    cases obj with
    | schedContext sc =>
      simp only []
      cases hS1 : storeObject scId.toObjId _ st with
      | error _ => intro h; cases h
      | ok p1 =>
        simp only []
        cases hL1 : lookupTcb p1.2 originalOwner with
        | none => intro h; cases h
        | some _ =>
          simp only []
          cases hS2 : storeObject originalOwner.toObjId _ p1.2 with
          | error _ => intro h; cases h
          | ok p2 =>
            simp only []
            cases hL2 : lookupTcb p2.2 serverTid with
            | none => intro h; cases h
            | some _ =>
              simp only []
              cases hS3 : storeObject serverTid.toObjId _ p2.2 with
              | error _ => intro h; cases h
              | ok p3 =>
                simp only [Except.ok.injEq]
                intro hEq; subst hEq
                have h1 := storeObject_scheduler_eq_z7 st _ _ _ hS1
                have h2 := storeObject_scheduler_eq_z7 p1.2 _ _ _ hS2
                have h3 := storeObject_scheduler_eq_z7 p2.2 _ _ _ hS3
                exact h3.trans (h2.trans h1)
    | _ => simp only []; intro h; cases h

/-- Signal a notification: wake one waiter or mark one pending badge.

**U5-J/U-M29: Wake-path pendingMessage overwrite**: When a waiter is present,
the wake path creates a badge-only `IpcMessage` and stores it in the waiter's
`pendingMessage` field via `storeTcbIpcStateAndMessage`. This unconditionally
overwrites any previous `pendingMessage` value. This is safe because:
1. `notificationWaiterConsistent` guarantees threads in the wait queue have
   `ipcState = .blockedOnNotification oid` — they entered via `notificationWait`
   which transitions from `.ready` without modifying `pendingMessage`.
2. The `storeTcbIpcStateAndMessage` call atomically sets both `ipcState := .ready`
   AND `pendingMessage := some badgeMsg`, so the overwrite is the intended
   delivery mechanism, not a loss of prior state.
AF5-A (AF-12): `pendingMessage = none` for waiting threads IS formally proven:
defined as `waitingThreadsPendingMessageNone` in IPC/Invariant/Defs.lean
with preservation theorems in IPC/Invariant/WaitingThreadHelpers.lean
(helper extraction in WS-AC Phase AC1-A). The safety argument is now both
structural (entry path analysis above) AND formally verified. -/
def notificationSignal (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) : Kernel Unit :=
  fun st =>
    match st.objects[notificationId]? with
    | some (.notification ntfn) =>
        match ntfn.waitingThreads with
        | waiter :: rest =>
            let nextState : NotificationState := if rest.isEmpty then .idle else .waiting
            let ntfn' : Notification := {
              state := nextState
              waitingThreads := rest
              pendingBadge := none
            }
            match storeObject notificationId (.notification ntfn') st with
            | .error e => .error e
            | .ok ((), st') =>
                -- R3-A/M-16: Deliver signaled badge to woken waiter via pendingMessage.
                -- In seL4, the badge from Signal is returned as the Wait syscall's result.
                let badgeMsg : IpcMessage := { IpcMessage.empty with badge := some badge }
                match storeTcbIpcStateAndMessage st' waiter .ready (some badgeMsg) with
                | .error e => .error e
                | .ok st'' => .ok ((), ensureRunnable st'' waiter)
        | [] =>
            -- WS-F5/D1c: Use word-bounded Badge.bor for accumulation.
            -- U8-C/U-L24: Notification word overflow note: Badge.bor uses
            -- unbounded Lean Nat internally (bitwise OR). In the formal model
            -- this is correct — no overflow is possible. However, on real
            -- hardware (ARM64), notification words are 64-bit. The hardware
            -- binding workstream (WS-V) must enforce 64-bit word width by
            -- masking Badge values to 2^64 - 1 at the platform boundary.
            -- Badge.ofNatMasked already applies a 64-bit mask, and Badge.bor
            -- preserves the mask (see Badge.bor definition in Prelude.lean).
            -- AF5-D (AF-15): Nat round-trip via `Badge.ofNatMasked badge.toNat`
            -- is safe: `ofNatMasked` applies `% machineWordMax` (64-bit masking).
            -- `bor_valid` theorem (AC3/I-04) proves result validity.
            -- H3 hardware binding: verify masking consistency at ABI boundary.
            let mergedBadge : SeLe4n.Badge :=
              match ntfn.pendingBadge with
              | some existing => SeLe4n.Badge.bor existing badge
              | none => SeLe4n.Badge.ofNatMasked badge.toNat
            let ntfn' : Notification := {
              state := .active
              waitingThreads := []
              pendingBadge := some mergedBadge
            }
            storeObject notificationId (.notification ntfn') st
    | some _ => .error .invalidCapability
    | none => .error .objectNotFound

/-- Wait on a notification: consume pending badge or block the caller.

WS-G7/F-P11: Duplicate-wait check uses O(1) TCB ipcState lookup instead of
O(n) list membership scan. If the waiter's ipcState is already
`.blockedOnNotification notificationId`, the thread is already waiting and
`alreadyWaiting` is returned.

WS-G7/F-P11: Waiter is prepended (`waiter :: waitingThreads`) instead of
appended (`waitingThreads ++ [waiter]`), reducing enqueue from O(n) to O(1).
FIFO ordering is not required by the seL4 notification spec — any waiter may
be woken on signal. -/
def notificationWait
    (notificationId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId) : Kernel (Option SeLe4n.Badge) :=
  fun st =>
    match st.objects[notificationId]? with
    | some (.notification ntfn) =>
        match ntfn.pendingBadge with
        | some badge =>
            let ntfn' : Notification := { state := .idle, waitingThreads := [], pendingBadge := none }
            match storeObject notificationId (.notification ntfn') st with
            | .error e => .error e
            | .ok ((), st') =>
                match storeTcbIpcState st' waiter .ready with
                | .error e => .error e
                | .ok st'' => .ok (some badge, st'')
        | none =>
            -- WS-G7/F-P11: O(1) duplicate check via TCB ipcState instead of O(n) list membership
            match lookupTcb st waiter with
            | none => .error .objectNotFound
            | some tcb =>
                if tcb.ipcState = .blockedOnNotification notificationId then
                  .error .alreadyWaiting
                else
                  let ntfn' : Notification := {
                    state := .waiting
                    waitingThreads := waiter :: ntfn.waitingThreads
                    pendingBadge := none
                  }
                  match storeObject notificationId (.notification ntfn') st with
                  | .error e => .error e
                  | .ok ((), st') =>
                      -- WS-L1/L1-C: Use _fromTcb — storeObject at notificationId
                      -- does not modify waiter's TCB, so tcb is still valid in st'
                      match storeTcbIpcState_fromTcb st' waiter tcb (.blockedOnNotification notificationId) with
                      | .error e => .error e
                      | .ok st'' => .ok (none, removeRunnable st'' waiter)
    | some _ => .error .invalidCapability
    | none => .error .objectNotFound

-- ============================================================================
-- F-12: Supporting lemmas for notification waiting-list proofs (WS-D4)
-- ============================================================================

/-- `storeTcbIpcState` preserves objects at IDs other than `tid.toObjId`. -/
theorem storeTcbIpcState_preserves_objects_ne
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState)
    (oid : SeLe4n.ObjId)
    (hNe : oid ≠ tid.toObjId)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    st'.objects[oid]? = st.objects[oid]? := by
  unfold storeTcbIpcState at hStep
  cases hTcb : lookupTcb st tid with
  | none =>
    simp [hTcb] at hStep
  | some tcb =>
    simp only [hTcb] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq : pair.snd = st' := Except.ok.inj hStep
      subst hEq
      exact storeObject_objects_ne st pair.2 tid.toObjId oid
        (.tcb { tcb with ipcState := ipc }) hNe hObjInv hStore

/-- `storeTcbIpcState` preserves notification objects (it only writes TCBs). -/
theorem storeTcbIpcState_preserves_notification
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState)
    (notifId : SeLe4n.ObjId)
    (ntfn : Notification)
    (hNtfn : st.objects[notifId]? = some (.notification ntfn))
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    st'.objects[notifId]? = some (.notification ntfn) := by
  by_cases hEq : notifId = tid.toObjId
  · subst hEq
    unfold storeTcbIpcState at hStep
    have hLookup : lookupTcb st tid = none := by
      unfold lookupTcb; simp [hNtfn]
    simp [hLookup] at hStep
  · rw [storeTcbIpcState_preserves_objects_ne st st' tid ipc notifId hEq hObjInv hStep]
    exact hNtfn

/-- `removeRunnable` only modifies the scheduler; all objects are preserved. -/
theorem removeRunnable_preserves_objects
    (st : SystemState)
    (tid : SeLe4n.ThreadId) :
    (removeRunnable st tid).objects = st.objects := by
  rfl

/-- WS-E3/H-09: `ensureRunnable` only modifies the scheduler; all objects are preserved. -/
theorem ensureRunnable_preserves_objects
    (st : SystemState)
    (tid : SeLe4n.ThreadId) :
    (ensureRunnable st tid).objects = st.objects := by
  unfold ensureRunnable
  split
  · rfl
  · split <;> rfl

/-- WS-E3/H-09: `storeTcbIpcState` does not modify the scheduler. -/
theorem storeTcbIpcState_scheduler_eq
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    st'.scheduler = st.scheduler := by
  unfold storeTcbIpcState at hStep
  cases hTcb : lookupTcb st tid with
  | none =>
    simp [hTcb] at hStep
  | some tcb =>
    simp only [hTcb] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq := Except.ok.inj hStep
      subst hEq
      exact storeObject_scheduler_eq st pair.2 tid.toObjId _ hStore

/-- WS-E3/H-09: `storeTcbIpcState` preserves endpoint objects. -/
theorem storeTcbIpcState_preserves_endpoint
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState)
    (epId : SeLe4n.ObjId)
    (ep : Endpoint)
    (hEp : st.objects[epId]? = some (.endpoint ep))
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    st'.objects[epId]? = some (.endpoint ep) := by
  by_cases hEq : epId = tid.toObjId
  · subst hEq
    unfold storeTcbIpcState at hStep
    have hLookup : lookupTcb st tid = none := by
      unfold lookupTcb; simp [hEp]
    simp [hLookup] at hStep
  · rw [storeTcbIpcState_preserves_objects_ne st st' tid ipc epId hEq hObjInv hStep]
    exact hEp

/-- WS-E3/H-09: `storeTcbIpcState` preserves CNode objects. -/
theorem storeTcbIpcState_preserves_cnode
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState)
    (cnodeId : SeLe4n.ObjId)
    (cn : CNode)
    (hCn : st.objects[cnodeId]? = some (.cnode cn))
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    st'.objects[cnodeId]? = some (.cnode cn) := by
  by_cases hEq : cnodeId = tid.toObjId
  · subst hEq
    unfold storeTcbIpcState at hStep
    have hLookup : lookupTcb st tid = none := by
      unfold lookupTcb; simp [hCn]
    simp [hLookup] at hStep
  · rw [storeTcbIpcState_preserves_objects_ne st st' tid ipc cnodeId hEq hObjInv hStep]
    exact hCn

/-- WS-E3/H-09: `storeTcbIpcState` preserves VSpaceRoot objects. -/
theorem storeTcbIpcState_preserves_vspaceRoot
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState)
    (oid : SeLe4n.ObjId)
    (vs : VSpaceRoot)
    (hVs : st.objects[oid]? = some (.vspaceRoot vs))
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    st'.objects[oid]? = some (.vspaceRoot vs) := by
  by_cases hEq : oid = tid.toObjId
  · subst hEq
    unfold storeTcbIpcState at hStep
    have hLookup : lookupTcb st tid = none := by
      unfold lookupTcb; simp [hVs]
    simp [hLookup] at hStep
  · rw [storeTcbIpcState_preserves_objects_ne st st' tid ipc oid hEq hObjInv hStep]
    exact hVs

/-- WS-E3/H-09: Backward CNode preservation: if post-state has a CNode, pre-state had it.
`storeTcbIpcState` only writes TCBs, so it cannot create or modify CNode objects. -/
theorem storeTcbIpcState_cnode_backward
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState)
    (oid : SeLe4n.ObjId)
    (cn : CNode)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcState st tid ipc = .ok st')
    (hCn : st'.objects[oid]? = some (.cnode cn)) :
    st.objects[oid]? = some (.cnode cn) := by
  by_cases hEq : oid = tid.toObjId
  · subst hEq
    unfold storeTcbIpcState at hStep
    cases hLookup : lookupTcb st tid with
    | none =>
      simp [hLookup] at hStep;
    | some tcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
        simp only [hStore] at hStep
        have := Except.ok.inj hStep; subst this
        rw [storeObject_objects_eq st pair.2 tid.toObjId _ hObjInv hStore] at hCn; cases hCn
  · rw [storeTcbIpcState_preserves_objects_ne st st' tid ipc oid hEq hObjInv hStep] at hCn; exact hCn

/-- WS-E3/H-09: Backward endpoint preservation for `storeTcbIpcState`. -/
theorem storeTcbIpcState_endpoint_backward
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState)
    (oid : SeLe4n.ObjId)
    (ep : Endpoint)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcState st tid ipc = .ok st')
    (hEp : st'.objects[oid]? = some (.endpoint ep)) :
    st.objects[oid]? = some (.endpoint ep) := by
  by_cases hEq : oid = tid.toObjId
  · subst hEq
    unfold storeTcbIpcState at hStep
    cases hLookup : lookupTcb st tid with
    | none =>
      simp [hLookup] at hStep;
    | some tcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
        simp only [hStore] at hStep
        have := Except.ok.inj hStep; subst this
        rw [storeObject_objects_eq st pair.2 tid.toObjId _ hObjInv hStore] at hEp; cases hEp
  · rw [storeTcbIpcState_preserves_objects_ne st st' tid ipc oid hEq hObjInv hStep] at hEp; exact hEp

/-- WS-E3/H-09: Backward notification preservation for `storeTcbIpcState`. -/
theorem storeTcbIpcState_notification_backward
    (st st' : SystemState)
    (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState)
    (oid : SeLe4n.ObjId)
    (ntfn : Notification)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcState st tid ipc = .ok st')
    (hNtfn : st'.objects[oid]? = some (.notification ntfn)) :
    st.objects[oid]? = some (.notification ntfn) := by
  by_cases hEq : oid = tid.toObjId
  · subst hEq
    unfold storeTcbIpcState at hStep
    cases hLookup : lookupTcb st tid with
    | none =>
      simp [hLookup] at hStep
    | some tcb =>
      simp only [hLookup] at hStep
      cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
        simp only [hStore] at hStep
        have := Except.ok.inj hStep; subst this
        rw [storeObject_objects_eq st pair.2 tid.toObjId _ hObjInv hStore] at hNtfn; cases hNtfn
  · rw [storeTcbIpcState_preserves_objects_ne st st' tid ipc oid hEq hObjInv hStep] at hNtfn; exact hNtfn

/-- WS-G7/F-P11: Double-wait is rejected: if the waiter's TCB ipcState is
already `.blockedOnNotification notifId`, `notificationWait` returns
`alreadyWaiting`. Uses O(1) TCB lookup instead of O(n) list membership. -/
theorem notificationWait_error_alreadyWaiting
    (waiter : SeLe4n.ThreadId)
    (notifId : SeLe4n.ObjId)
    (st : SystemState)
    (ntfn : Notification)
    (tcb : TCB)
    (hObj : st.objects[notifId]? = some (.notification ntfn))
    (hNoBadge : ntfn.pendingBadge = none)
    (hTcb : lookupTcb st waiter = some tcb)
    (hBlocked : tcb.ipcState = .blockedOnNotification notifId) :
    notificationWait notifId waiter st = .error .alreadyWaiting := by
  unfold notificationWait
  simp [hObj, hNoBadge, hTcb, hBlocked]

/-- Decomposition: on the badge-consumed path, the post-state notification
has an empty waiting list. -/
theorem notificationWait_badge_path_notification
    (st st' : SystemState)
    (notifId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId)
    (badge : SeLe4n.Badge)
    (hObjInv : st.objects.invExt)
    (hStep : notificationWait notifId waiter st = .ok (some badge, st')) :
    ∃ ntfn', st'.objects[notifId]? = some (.notification ntfn') ∧ ntfn'.waitingThreads = [] := by
  unfold notificationWait at hStep
  cases hObj : st.objects[notifId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _
    | schedContext _ => simp [hObj] at hStep
    | notification ntfn =>
      simp only [hObj] at hStep
      cases hBadge : ntfn.pendingBadge with
      | none =>
        simp only [hBadge] at hStep
        -- WS-G7: lookupTcb match
        cases hLookup : lookupTcb st waiter with
        | none => simp [hLookup] at hStep
        | some tcb =>
          simp only [hLookup] at hStep
          split at hStep
          · simp at hStep
          · revert hStep
            cases hStore : storeObject notifId _ st with
            | error e => simp
            | ok pair =>
              simp only []
              intro hStep
              -- WS-L1: rewrite _fromTcb back to original for proof compatibility
              have hLookup' := lookupTcb_preserved_by_storeObject_notification hLookup hObj hObjInv hStore
              rw [storeTcbIpcState_fromTcb_eq hLookup'] at hStep
              revert hStep
              cases hTcb : storeTcbIpcState pair.2 waiter _ with
              | error e => simp
              | ok st2 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨h, _⟩
                exact absurd h (by simp)
      | some b =>
        simp only [hBadge] at hStep
        let newNtfn : Notification := { state := .idle, waitingThreads := [], pendingBadge := none }
        revert hStep
        cases hStore : storeObject notifId (.notification newNtfn) st with
        | error e => simp
        | ok pair =>
          simp only []
          intro hStep
          revert hStep
          cases hTcb : storeTcbIpcState pair.2 waiter .ready with
          | error e => simp
          | ok st2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq]
            intro ⟨_, hStEq⟩
            subst hStEq
            have hNtfnStored : pair.2.objects[notifId]? = some (.notification newNtfn) :=
              storeObject_objects_eq st pair.2 notifId (.notification newNtfn) hObjInv hStore
            have hPairObjInv : pair.2.objects.invExt := by
              unfold storeObject at hStore; cases hStore
              exact RHTable_insert_preserves_invExt _ _ _ hObjInv
            have hNtfnPreserved : st2.objects[notifId]? = some (.notification newNtfn) :=
              storeTcbIpcState_preserves_notification pair.2 st2 waiter .ready notifId newNtfn hNtfnStored hPairObjInv hTcb
            exact ⟨newNtfn, hNtfnPreserved, rfl⟩

/-- WS-G7/F-P11: Decomposition: on the wait path, the post-state notification has the
waiter prepended. The waiter's TCB existed and was not already blocked on this
notification. -/
theorem notificationWait_wait_path_notification
    (st st' : SystemState)
    (notifId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : notificationWait notifId waiter st = .ok (none, st')) :
    ∃ ntfn ntfn',
      st.objects[notifId]? = some (.notification ntfn) ∧
      ntfn.pendingBadge = none ∧
      st'.objects[notifId]? = some (.notification ntfn') ∧
      ntfn'.waitingThreads = waiter :: ntfn.waitingThreads := by
  unfold notificationWait at hStep
  cases hObj : st.objects[notifId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _
    | schedContext _ => simp [hObj] at hStep
    | notification ntfn =>
      simp only [hObj] at hStep
      cases hBadge : ntfn.pendingBadge with
      | some b =>
        simp only [hBadge] at hStep
        revert hStep
        cases hStore : storeObject notifId (.notification { state := .idle, waitingThreads := [], pendingBadge := none }) st with
        | error e => simp
        | ok pair =>
          simp only []
          intro hStep
          revert hStep
          cases hTcb : storeTcbIpcState pair.2 waiter .ready with
          | error e => simp
          | ok st2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq]
            intro ⟨h, _⟩
            exact absurd h (by simp)
      | none =>
        simp only [hBadge] at hStep
        -- WS-G7: match on lookupTcb
        cases hLookup : lookupTcb st waiter with
        | none => simp [hLookup] at hStep
        | some tcb =>
          simp only [hLookup] at hStep
          -- ipcState check
          by_cases hBlocked : tcb.ipcState = .blockedOnNotification notifId
          · simp [hBlocked] at hStep
          · simp only [hBlocked, ite_false] at hStep
            let ntfn' : Notification := { state := .waiting, waitingThreads := waiter :: ntfn.waitingThreads, pendingBadge := none }
            revert hStep
            cases hStore : storeObject notifId (.notification ntfn') st with
            | error e => simp
            | ok pair =>
              simp only []
              intro hStep
              -- WS-L1: rewrite _fromTcb back to original for proof compatibility
              have hLookup' := lookupTcb_preserved_by_storeObject_notification hLookup hObj hObjInv hStore
              rw [storeTcbIpcState_fromTcb_eq hLookup'] at hStep
              revert hStep
              cases hTcb : storeTcbIpcState pair.2 waiter (.blockedOnNotification notifId) with
              | error e => simp
              | ok st2 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, hStEq⟩
                have hRemObj : (removeRunnable st2 waiter).objects = st2.objects := rfl
                have hNtfnStored : pair.2.objects[notifId]? = some (.notification ntfn') :=
                  storeObject_objects_eq st pair.2 notifId (.notification ntfn') hObjInv hStore
                have hPairObjInv : pair.2.objects.invExt := by
                  unfold storeObject at hStore; cases hStore
                  exact RHTable_insert_preserves_invExt _ _ _ hObjInv
                have hNtfnPreserved : st2.objects[notifId]? = some (.notification ntfn') :=
                  storeTcbIpcState_preserves_notification pair.2 st2 waiter
                    (.blockedOnNotification notifId) notifId ntfn' hNtfnStored hPairObjInv hTcb
                refine ⟨ntfn, ntfn', rfl, hBadge, ?_, rfl⟩
                rw [← hStEq, hRemObj]
                exact hNtfnPreserved

