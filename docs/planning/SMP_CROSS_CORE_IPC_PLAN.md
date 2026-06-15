# SM6 — Cross-Core IPC (WS-SM Phase 6)

> **Phase**: SM6 of WS-SM
> **Parent overview**: [`SMP_MULTICORE_COMPLETION_PLAN.md`](SMP_MULTICORE_COMPLETION_PLAN.md)
> **Audited cut**: `v0.31.2`
> **Target releases**: v0.83.0 .. v0.90.x
> **Calendar estimate**: 8-12 weeks
> **Sub-task count**: 60-80 across ~22-32 PRs

## 1. Phase goal

SM6 makes IPC work across cores under per-object fine locks.
Each IPC operation declares its lock-set (per SM3.B.3); cross-
core wake routes through SM5.C; the existing IPC invariant
bundle (15 conjuncts post-R4) carries through per-core under
2PL serializability (Cor 2.1.11).

**Concrete deliverables**:

1. **Endpoint call** across cores (SM6.A): caller TCB (W),
   sender's CNode (R), endpoint (W), receiver TCB (W if
   unblock). Cross-core call wakes receiver via SGI.
2. **Notification** across cores (SM6.B): caller TCB (R),
   notification (W), receiver TCB (W if unblock).
3. **Reply path** across cores (SM6.C): caller TCB (W), reply
   object (W), receiver TCB (W).
4. **IPC invariant bundle per-core** (SM6.D): 15-conjunct
   bundle, restricted to per-core endpoint/notification views.
5. **Cancellation** across cores (SM6.E): atomic under lock-set.
6. **Tests + fixtures** (SM6.F).

## 2. Dependencies

- **SM3**: per-object lock-set discipline.
- **SM4**: per-core SchedulerState.
- **SM5**: per-core wakeThread, SGI wake.

## 3. Mathematical foundations

### 3.1 IPC lock-set table

| Operation | Lock-set (LockId × AccessMode, in acquire order) |
|-----------|--------------------------------------------------|
| `endpointSend` | caller TCB (R), endpoint (W) |
| `endpointSendNonBlocking` | caller TCB (R), endpoint (W) |
| `endpointReceive` | caller TCB (W), endpoint (W) |
| `endpointCall` | sender CNode (R), caller TCB (W), receiver TCB (W if unblock), endpoint (W) |
| `endpointCallWithCaps` | sender CNode (R), dest CNode (W), caller TCB (W), receiver TCB (W), endpoint (W) |
| `endpointReply` | reply object (W), receiver TCB (W), caller TCB (W) |
| `endpointReplyRecv` | reply object (W), receiver TCB (W), caller TCB (W), endpoint (W) |
| `notificationSignal` | caller TCB (R), notification (W), receiver TCB (W if unblock) |
| `notificationWait` | caller TCB (W), notification (W) |
| `cancelIpcBlocking` | victim TCB (W), endpoint/notification (W) |
| `cancelDonation` | donor TCB (W), receiver TCB (W), SchedContext (W) |

All locks acquired in `LockId` ascending order (hierarchical).
Within-kind by ObjId.val.

### 3.2 Cross-core call

When caller (on c) and receiver (on c') are on different cores:

```
endpointCall on c:
  1. Acquire lock-set (LockId-ordered).
  2. Resolve capability → endpoint.
  3. Marshal message into IPC buffer.
  4. If receiver is waiting on endpoint:
     a. Dequeue receiver from endpoint queue.
     b. Set receiver state to .runnable.
     c. enqueueRunnableOnCore (receiver's core).
     d. If receiver's core ≠ c: emit .reschedule SGI to c'.
  5. Set caller state to .blocked (waiting for reply).
  6. (caller's currentOnCore c becomes none).
  7. Release lock-set.
  8. Run chooseThreadOnCore c to pick next thread on c.
```

**Theorem 3.2.1** (`endpointCall_emits_sgi_if_remote_receiver`).

When `endpointCall` unblocks a receiver on a different core,
the operation emits a `.reschedule` SGI to the receiver's core.

```lean
theorem endpointCall_emits_sgi_if_remote_receiver
    (s : SystemState) (callerTid : ThreadId) (capArg : CPtr)
    (msgInfo : MessageInfo) (executingCore : CoreId) :
    let (s', sgi?) := endpointCall s callerTid capArg msgInfo executingCore
    ∀ rt ∈ unblockedReceiver s' s,
      let target := determineTargetCore s rt
      target ≠ executingCore →
      sgi? = some (target, .reschedule)
```

### 3.3 Per-core IPC invariant bundle

The existing `ipcInvariantFull` (15 conjuncts post-R4) restricts
to per-core endpoint/notification views:

    def ipcInvariantFull_perCore (s : SystemState) : Prop :=
      ipcStateQueueMembershipConsistent_perCore s ∧
      endpointQueueNoDup_perCore s ∧
      queueNextBlockingConsistent_perCore s ∧
      queueHeadBlockedConsistent_perCore s ∧
      donationOwnerValid_perCore s ∧
      replyChainStructured_perCore s ∧
      -- ... 9 more conjuncts (existing R4 list, all per-core
      -- versions) ...

Each `_perCore` variant restricts to threads on a specific core
(via `cpuAffinity` field).

**Theorem 3.3.1** (`ipcInvariantFull_perCore_preservation`). Each
of the 6 IPC operations (send, receive, call, reply, signal,
wait) preserves `ipcInvariantFull_perCore` under its lock-set
held precondition.

Per operation, the proof is the existing single-core proof with
the lock-set precondition added (Cor 2.1.11).

### 3.4 Cancellation atomicity

```lean
theorem cancelIpcBlocking_atomic_under_lockSet
    (s : SystemState) (tid : ThreadId) (c : CoreId) :
    lockSetHeld c (lockSet_cancelIpcBlocking tid) s →
    cancelIpcBlocking s tid = .ok s' →
    -- All endpoint/notification queue mutations are atomic.
    True
```

The atomicity follows from 2PL (Theorem 2.1.10).

## 4. Architectural choices

### 4.1 Why lock-set sizes are bounded

The largest lock-set is `endpointCallWithCaps` with 5 locks. The
WCRT analysis (SM5.J) uses lock-set size as a factor; we cap at
8 for analysis purposes. Operations with potentially larger
lock-sets are refactored (none currently exceed 5).

### 4.2 Why receiver unblock under sender's lock-set

`endpointCall` unblocks the receiver during the call's atomic
window. The lock-set extends to include the receiver's TCB
(write). This:
- Ensures the unblock and the run-queue enqueue are atomic with
  respect to other cores.
- Avoids a 2-step rendezvous (would require an extra lock/release
  cycle on the receiver's TCB).

### 4.3 Donation chain across cores

When caller on c donates SchedContext to receiver on c', the
SC's `boundTcb` changes. The lock-set includes the SC, and the
donation operation under fine locks is serializable.

SM5's `donation_perCore_consistent` extends here: if the receiver
inherits the SC and is on a different core, the SC's CBS
replenish queue migrates per SM5.H.4.

## 5. Detailed sub-task breakdown

### SM6.A — Endpoint call across cores (4 PRs, 10 sub-tasks)

**Status: LANDED (v0.31.65); live dispatch + production promotion (v0.31.66).**
Axiom-clean (`propext` / `Classical.choice` / `Quot.sound` only); Tier 0–3 green.
At v0.31.65 the modules landed staged; **at v0.31.66 the live `.call` dispatch
routes through them and the 14 dispatch modules are promoted to production**
(staged-only 71 → 57) — see the "Live `.call` arm" note below.  The cross-core
transition `endpointCallOnCore` and the SM6.A theorems live in
`SeLe4n/Kernel/IPC/CrossCore/EndpointCall.lean` (+ `EndpointCallNI.lean` for
the boot-core non-interference slice, `EndpointCallNiPerCore.lean` for the
per-core / ∀-core (`lowEquivalent_smp`) non-interference, `EndpointCallInvariant.lean`
for IPC-invariant preservation, `EndpointCallEntry.lean` for the WithCaps +
donation + FFI driver, `EndpointCallDispatch.lean` for the below-API live `.call`
dispatch); the 20-assertion runtime suite is
`tests/SmpCrossCoreCallSuite.lean` (`lake exe smp_cross_core_call_suite`).

**Non-interference (per-core / ∀-core).** `endpointCallOnCore_call_path_NI_smp`
strengthens the boot-core `projectState` NI to `lowEquivalent_smp`: a high
cross-core call is invisible to a low observer on *every* core — the remote core
the receiver is woken onto, the executing core where the caller is descheduled
(and its current thread cleared), and every bystander core.  The proof rests on a
machine-register frame family for the object steps (the `*_machine_eq` mirrors of
the `*_scheduler_eq` family) plus per-core run-queue / current-thread projection
lemmas: every scheduler edit touches only *high* threads the observer filters out.

**Invariant preservation (full).** `endpointCallOnCore` provably preserves the
whole fifteen-conjunct `ipcInvariantFull` (`endpointCallOnCore_preserves_ipcInvariantFull`),
deriving `ipcInvariant`, `dualQueueSystemInvariant`, `allPendingMessagesBounded`,
and `badgeWellFormed` internally via a reusable lookup-only congruence family
(`dualQueueSystemInvariant_of_getElem_eq` &c.) — one conjunct *more* than the
single-core theorem; only the scheduler-sensitive `passiveServerIdle` is carried
as a hypothesis, as single-core does.

**Live SGI-dispatch seam.** The SM5.F.4 diff-based cross-core SGI dispatch is now
wired into a live syscall entry: `syscallDispatchCrossCoreEntry`
(`@[export lean_syscall_dispatch_cross_core]` in
`SeLe4n/Kernel/SyscallDispatchEntry.lean`) runs `syscallDispatchFromAbi`
atomically via `modifyGetKernelState`, then fires the diff-recovered
`computeCrossCoreSgis` via `fireCrossCoreSgis` — the syscall analogue of
`perCoreTimerTickEntry`.  Single-core-inert / trace-safe
(`syscallDispatchCrossCoreEntry_sgis_nil_single_core`).

**Live `.call` arm — LANDED (v0.31.66).**  The pure cross-core `.call` dispatch
ops live **below the API layer** in
`SeLe4n/Kernel/IPC/CrossCore/EndpointCallDispatch.lean` (FFI-free):
`endpointCallWithCapsOnCore`, `endpointCallCrossCoreDispatch`, and the
info-flow-checked `endpointCallCrossCoreDispatchChecked` (the cross-core
analogue of `endpointCallChecked`).  The live `API.dispatchWithCap{,Checked}`
`.call` arm now routes through them — the receiver woken on its *home* core, the
caller descheduled on its *own* core (derived from the live state by
`determineExecutingCore st tid`, no hardware-core parameter threaded through the
`Kernel`-monad chain).  The SMP dispatch infrastructure is **promoted to
production** (staged-only 71 → 57; 14 modules: lock hierarchy + per-core scheduler
+ cross-core call).  The dispatch reaches the cross-core arm through the
*production* entry already wired — `syscall_dispatch_inner` (`@[export]` in
`Platform.FFI`) → `syscallDispatchFromAbi` → `syscallEntryChecked` →
`dispatchWithCapChecked` → `endpointCallCrossCoreDispatchChecked` — so **no Rust
extern change is needed** for the dispatch.  Validated: trace fixture
byte-identical, all 8 `.call` dispatch suites pass, partition + AK7 green.
**Cross-core completion — LANDED (v0.31.67).**  The two v0.31.66 follow-ups are
closed (PR #820 review #1/#3/#5): (1) **cross-core SGI firing** — the SGI-firing
seam `SyscallDispatchEntry` (`@[export lean_syscall_dispatch_cross_core]`) + its
closure (`PriorityInheritance.PerCore`, `Concurrency.Runtime`) are **promoted to
production** (staged-only 57 → 54), and the Rust `svc_dispatch` extern is flipped
to it — the live syscall commits the verified post-state then fires the
diff-recovered cross-core `.reschedule` SGIs (`computeCrossCoreSgis` +
`fireCrossCoreSgis`), single-core-inert.  (2) **per-core caller identification** —
`syscallDispatchFromAbi` / `syscallEntryChecked` now take an explicit
`executingCore` and read `currentOnCore executingCore`;
`syscallDispatchCrossCoreEntry` threads the hardware `currentCoreId`,
`syscallDispatchInner` passes `bootCoreId` (boot-pinned, unchanged); the five
`syscallDispatchFromAbi_*` bridges are generalised to an arbitrary core.  The
`.call` arm's donation propagation also switches to the cross-core chain walk
`propagatePipChainCrossCore` (review #3 — migrates each boosted server's bucket on
its home core).  Validated: trace byte-identical, all `.call` + SMP suites pass,
partition (54) + AK7 + Rust HAL (724) green.

| Sub | Description | Landed symbol | Status |
|-----|-------------|---------------|--------|
| SM6.A.1 | Migrate `endpointCall` to acquire lock-set (cross-core) | `endpointCallOnCore`, `removeRunnableOnCore` (+ bootCore bridge), `endpointCallOnCore_{rendezvous,noReceiver}_eq` | ✓ |
| SM6.A.2 | `endpointCall_lockSet_correct` | `endpointCallOnCore_lockSet_correct` | ✓ |
| SM6.A.3 | Cross-core wake via `wakeThread` (Theorem 3.2.1) | `endpointCallOnCore_emits_sgi_if_remote_receiver` (+ `_no_sgi_if_local_receiver`) | ✓ |
| SM6.A.4 | `endpointCall_perCore_blocking` | `endpointCallOnCore_perCore_blocking` | ✓ |
| SM6.A.5 | Donation chain lock-set extension | `lockSet_endpointCall_donation_extension` | ✓ |
| SM6.A.6 | Reply state allocation under lock-set | `endpointCallOnCore_reply_linkage_under_lockSet` (+ `lockSet_endpointCall_caller_tcb_write_mem`: the caller-TCB write lock is a *member* of the footprint) | ✓ |
| SM6.A.7 | `endpointCall_call_path_NI` (cross-core variant) | `endpointCallOnCore_call_path_NI` (boot-core `projectState`) + `endpointCallOnCore_call_path_NI_smp` (per-core / ∀-core `lowEquivalent_smp` — invisible on *every* core) | ✓ |
| SM6.A.8 | `endpointCallWithCaps_lockSet_correct` | `endpointCallWithCaps_lockSet_correct` (+ `lockSet_endpointCallWithCaps`) | ✓ |
| SM6.A.9 | `endpointCall_atomic_under_lockSet` | `endpointCallOnCore_atomic_under_lockSet` (+ `endpointCallOnCore_withLockSet_preserves_objects_invExt`: invariant carried *through* the 2PL fold) | ✓ |
| SM6.A.10 | 8 cross-core call scenarios | `tests/SmpCrossCoreCallSuite.lean` (20 runtime assertions) | ✓ |

> **Model note.** This kernel has no separate Reply *object* (the `.reply`
> lock-kind is N/A — `lockHeld` is `False` for it); the reply linkage is the
> caller's `blockedOnReply endpointId (some receiver)` TCB state, written under
> the caller-TCB **write** lock already in `lockSet_endpointCall`. SM6.A.6 is
> therefore "reply *state* allocation under lock-set" rather than reply-object
> allocation. The SGI theorem (SM6.A.3) is stated at the wake-site state
> (`determineTargetCore st'' receiver`); `cpuAffinity` is unchanged by the
> intervening pop+store, so this coincides with the pre-state target core.

### SM6.B — Notification across cores (3 PRs, 8 sub-tasks)

**Status: LANDED (v0.31.68); proof-thoroughness completion (v0.31.69); bound
notifications + LIVE bound-aware dispatch (v0.31.70); bind/unbind-notification
syscalls — end-to-end userspace ABI (v0.31.71).**  **v0.31.71** adds the
`tcbBindNotification` / `tcbUnbindNotification` `SyscallId` variants threaded
through the full Lean + Rust ABI (encodings, `permittedKinds` + lock-sets +
consistency + SM3.B inventory, enforcement-boundary, the live
`API.dispatchCapabilityOnly` arms, decoders, and the Rust `sele4n-types` /
`sele4n-hal` mirrors + conformance) — so userspace can create / tear down the
binding, making the live bound-delivery reachable end-to-end.
Axiom-clean (`propext` / `Classical.choice` / `Quot.sound` only); Tier 0–3 green;
trace fixture byte-identical.  **v0.31.70** implements the seL4 bound-notification
relation (`Notification.boundTCB` field + `bind`/`unbindNotification` +
`notificationSignalBound{,OnCore}` bound-delivery, `Operations/NotificationBind.lean`
+ `CrossCore/NotificationBind{,Dispatch}.lean`) and wires the live
`API.dispatchWithCap{,Checked}` `.notificationSignal` arms through the
info-flow-checked cross-core bound dispatch — so a signal to a bound notification
delivers the badge directly to its `BlockedOnReceive` TCB on the running kernel
(`NotificationSignal` / `NotificationInvariant` + the bound stack promoted to
production; staged 57 → 55).  The cross-core transitions
`notificationSignalOnCore` / `notificationWaitOnCore` and the SM6.B theorems live
in `SeLe4n/Kernel/IPC/CrossCore/NotificationSignal.lean`
(+ `NotificationSignalNI.lean` for the boot-core / per-core / ∀-core
(`lowEquivalent_smp`) non-interference of **both** signal *and* wait,
+ `NotificationInvariant.lean` for the `objects.invExt` / `ipcInvariant`
preservation of both ops); the 42-assertion runtime suite is
`tests/SmpCrossCoreNotificationSuite.lean`
(`lake exe smp_cross_core_notification_suite`).  The cross-core transition modules
are **production** — `NotificationSignal` / `NotificationInvariant` /
`NotificationBind{,Dispatch}` entered the import closure with the live
`.notificationSignal` dispatch; only `NotificationSignalNI.lean` remains staged.

**v0.31.72 (audit closure — live wake SGI).** An audit found that the live wake did
not actually poke the remote core: the diff-based SGI re-derivation `crossCoreSgiBody`
(SM5.F.4), which the syscall entry runs on the committed `(pre, post)` diff, gated
*only* on an effective run-queue bucket change (a PIP boost).  A notification /
endpoint-call wake leaves the woken thread's effective priority unchanged, so the
re-derivation produced **no** SGI and the freshly-runnable remote thread waited for
that core's next local timer tick — the operation surfaced the SGI (`…_remote_wake`)
but the live path dropped it.  `crossCoreSgiBody` now *also* fires a `.reschedule`
SGI when a thread becomes **newly runnable on a remote home core** (proven by
`crossCoreSgiBody_remote_wake`), so the live re-derivation matches the operation's own
surfaced SGI for SM6.A receivers and SM6.B notification waiters / bound TCBs alike.
Single-core inertness (`computeCrossCoreSgis_nil_single_core`) and the PIP-boost /
immaterial-boost / non-runnable-holder gates are all preserved; `tests/SmpPipSuite.lean`
gains the cross-core-wake firing assertions.

**PR-review remediation (v0.31.73).** Four further correctness/security findings from
the PR #821 review are closed: **(#2)** the cross-core `notificationSignalOnCore` /
`notificationWaitOnCore` reconstructed the notification without `boundTCB`, silently
destroying a bound notification's binding on every ordinary signal/wait — every
reconstruction site now carries `boundTCB := ntfn.boundTCB` (trace byte-identical, the
value only differs for bound notifications); **(#3)** the checked bound-signal dispatch
only proved `signaler → notification`, so a bound delivery to a *low* receiver TCB
could leak a high notification's badge — it now also requires `notification → receiver`
(`securityFlowsTo`) when `boundDeliveryTarget?` resolves, fail-closed; **(#4)** the live
`.notificationWait` arms still descheduled on the boot core — they now route through
`notificationWaitCrossCoreDispatch{,Checked}` (per-core via `determineExecutingCore`);
**(#5)** `lockSet_notificationSignalBoundOnCore` extends the signal footprint with the
endpoint-write + bound-TCB-write locks on the bound-delivery path (the dequeue/TCB
writes were outside the 2PL footprint), with `permittedKinds .notificationSignal`
gaining `.endpoint`.  **Review #1 closed (v0.31.74):** the *bind* syscall no longer takes the notification
as a raw ObjId — `.tcbBindNotification`'s `msgRegs[0]` is now a CPtr resolved through
the caller's CSpace via the verified `syscallLookupCap` (`resolveCapAddress` + slot
lookup + `hasRight .write`), and `bindNotification` runs only if the resolved cap
targets a notification.  A TCB-cap holder must additionally hold a notification
capability, so it can no longer hijack/deny an arbitrary notification.  (Wire format
unchanged → no Rust/conformance change; `TcbBindNotificationArgs.notificationId` →
`.notificationCPtr`.)

**Tracked-debt closure (v0.31.75).** Both remaining debt items are now closed.
**(a) Single-core binding preservation:** the single-core `notificationSignal` /
`notificationWait` (`IPC/Operations/Endpoint.lean`) shared the #2 reconstruction
pattern (dropping `boundTCB`); all four reconstruction sites now carry
`boundTCB := ntfn.boundTCB`, with the dependent invariant proofs updated
(`NotificationPreservation/{Signal,Wait}`, `Invariant/Structural/StoreObjectFrame`,
`Capability/Invariant/Authority`) — trace byte-identical, `notificationQueueWellFormed`
being `boundTCB`-independent.  **(b) Bind-authority dispatch test:**
`SyscallDispatchSuite.sd050_bindNotification_requires_ntfn_cap` dispatches
`.tcbBindNotification` through a CSpace-with-caps fixture and asserts authorized-bind
success, no-cap → `.invalidCapability`, and read-only-cap → `.illegalAuthority`.

**Deep-audit closure (v0.31.76).**  The bound-delivery 2PL footprint is now
**proven-covered**, not just runtime-tested: `lockSet_notificationSignalBoundOnCore_{endpoint,boundTcb}_write_mem`
(via the new forward lemma `insertOrMerge_preserves_mem_of_ne`) prove the
endpoint-write and bound-TCB-write locks — the writes `endpointQueueRemoveDual` +
the badge/`.ready` store perform — are members of the bound lock-set.  **Remaining
proof-depth debt (recorded, not silent): bound-delivery non-interference.**  The
delivery branch of `notificationSignalBoundOnCore` lacks a formal NI theorem (the
plain signal/wait/call have `_signal_path_NI` etc.).  It is genuinely foundational:
`endpointQueueRemoveDual` relinks the dequeued TCB's queue *neighbours* and
`boundDeliveryTarget?` does not constrain the endpoint's other receivers, so all-high
NI needs a dual-queue label invariant ("threads queued on a high endpoint share its
label") the codebase has not built (SM6.A's `.call` NI sidesteps it via
`endpointQueuePopHead`).  The covert channel is already prevented operationally by the
#3 flow gate (`notificationSignalBoundCrossCoreDispatchChecked_flow_denied_to_receiver`,
proven).  **Closure target:** prove
`endpointQueueRemoveDual_preserves_projection{,OnCore}` under an endpoint-queue-label
hypothesis, then chain into `notificationSignalBoundOnCore_delivery_path_NI{,_smp}`.

**Proof-thoroughness completion (v0.31.69)** closes the gaps to SM6.A's bar:
`notification{Signal,Wait}OnCore_preserves_{objects_invExt,ipcInvariant}`
(invariant preservation, `NotificationInvariant.lean`); the wait operation brought
to parity with the signal — path reductions
(`notificationWaitOnCore_{badge,block}_eq`), per-core caller blocking
(`notificationWaitOnCore_perCore_blocking`), and cross-core NI
(`notificationWaitOnCore_block_path_NI{,_smp}`); the honest *pre-state* SGI target
(`notificationSignalOnCore_remote_wake_preState` via `determineTargetCore_congr` +
the store affinity-frame lemmas); the lock-set / transition coherence
(`notificationSignalWaiter?_eq_wake_head` — the pre-resolved waiter *is* the woken
thread); and the multi-waiter theorem strengthened to capture the notification's
`state` transition + `pendingBadge` clearing.

`notificationSignalOnCore` mirrors the single-core `notificationSignal` with one
cross-core substitution — the head waiter's wake routes through the SM5.C
`wakeThread … executingCore` (enqueued on the waiter's *home* core, surfacing the
optional `.reschedule` SGI) — and the signaller does **not** block.
`notificationWaitOnCore` blocks the caller on *its own* core via the SM6.A
`removeRunnableOnCore … executingCore`.  The lock-sets
`lockSet_notificationSignal` / `lockSet_notificationWait` (SM3.B.3) are unchanged.

> **Model note.**  SM6.B.6's *lock-set* "binding (notification ↔ TCB)" is the
> woken-waiter TCB write lock plus the notification write lock — *both* ends of
> the signal's wake covered by a held write lock — proved via the unconditional
> `self_write_mem_insertOrMerge`.  **Separately, the full seL4 bound-notification
> relation is now implemented (v0.31.70):** the `Notification.boundTCB` ⇄
> `TCB.boundNotification` binding (`bindNotification` / `unbindNotification`,
> `Operations/NotificationBind.lean`) and the bound-delivery path
> (`notificationSignalBound{,OnCore}` — a signal to a notification whose bound TCB
> is `BlockedOnReceive` delivers the badge directly to it, dequeuing it from its
> endpoint), wired **live** through `API`'s `.notificationSignal` arms via
> `notificationSignalBoundCrossCoreDispatch{,Checked}`.  (The latent
> `TCB.boundNotification` field thus gained its consuming operations, per the
> implement-the-improvement rule.)

| Sub | Description | Landed symbol | Status |
|-----|-------------|---------------|--------|
| SM6.B.1 | Migrate `notificationSignal`/`notificationWait` to lock-set (cross-core) | `notificationSignalOnCore`, `notificationWaitOnCore` (+ `notificationSignalOnCore_{waiter,noWaiter}_eq`, `lockSet_notificationSignalOnCore`, `notificationSignalOnCore_lockSet_correct`, `notificationWaitOnCore_lockSet_correct`) | ✓ |
| SM6.B.2 | `notificationSignal_remote_wake` | `notificationSignalOnCore_remote_wake` (+ `_no_sgi_if_local_waiter`, `_noWaiter_no_sgi`) | ✓ |
| SM6.B.3 | Multi-waiter discipline preserved | `notificationSignalOnCore_wakes_head` (one wake per signal, head ∉ NoDup remainder) + `notificationSignalOnCore_remaining_waiters` (observable post-state carries exactly the remaining list, read through the object-invisible wake) | ✓ |
| SM6.B.4 | `notificationWait_atomic_under_lockSet` | `notificationWaitOnCore_atomic_under_lockSet` (+ `notificationSignalOnCore_atomic_under_lockSet` companion) | ✓ |
| SM6.B.5 | `notificationSignal_perCore_consistent` | `notificationSignalOnCore_perCore_consistent` (wake confined to the waiter's home core) | ✓ |
| SM6.B.6 | Binding (notification ↔ TCB) lock-set | `lockSet_notificationSignal_notification_write_mem` + `lockSet_notificationSignal_waiter_tcb_write_mem` (both ends write-locked; `self_write_mem_insertOrMerge`) | ✓ |
| SM6.B.7 | `notificationSignal_perCore_NI` | `notificationSignalOnCore_signal_path_NI` (boot-core `projectState`) + `notificationSignalOnCore_signal_path_NI_smp` (per-core / ∀-core `lowEquivalent_smp` — invisible on *every* core) | ✓ |
| SM6.B.8 | 6 cross-core notification scenarios | `tests/SmpCrossCoreNotificationSuite.lean` (42 runtime assertions) | ✓ |

### SM6.C — Reply path across cores (4 PRs, 10 sub-tasks)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM6.C.1 | Migrate `endpointReply` to lock-set | (refactor) | M |
| SM6.C.2 | Cross-core reply: wake caller | `endpointReply_remote_wake` | L |
| SM6.C.3 | Donation chain across cores extension | `donation_perCore_consistent` extension | L |
| SM6.C.4 | Reply payload delivery to right TCB | `endpointReply_perCore_delivery` | M |
| SM6.C.5 | `endpointReplyRecv` combined op lock-set | `endpointReplyRecv_lockSet_correct` | M |
| SM6.C.6 | Reply object lifecycle | `replyObject_lifecycle_under_lockSet` | M |
| SM6.C.7 | Reply-replay protection | Theorem | M |
| SM6.C.8 | Cross-core reply NI | `endpointReply_perCore_NI` | M |
| SM6.C.9 | Reply chain length bound (donation k > 2) | Theorem | M |
| SM6.C.10 | 8 reply scenarios | Tests | L |

### SM6.D — IPC across-core invariant bundle (2 PRs, 6 sub-tasks)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM6.D.1 | `ipcInvariantFull_perCore` (15 conjuncts) | Aggregate | L |
| SM6.D.2 | 6 per-operation preservation theorems | Theorems | XL |
| SM6.D.3 | `ipcStateQueueMembershipConsistent_perCore` | Theorem | M |
| SM6.D.4 | `endpointQueueNoDup_perCore` | Theorem | M |
| SM6.D.5 | `queueNextBlockingConsistent_perCore` | Theorem | M |
| SM6.D.6 | `queueHeadBlockedConsistent_perCore` | Theorem | M |

### SM6.E — Cancellation across cores (3 PRs, 6 sub-tasks)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM6.E.1 | Migrate `cancelIpcBlocking` to lock-set | (refactor) | M |
| SM6.E.2 | `cancelIpcBlocking_atomic_under_lockSet` | Theorem | M |
| SM6.E.3 | `cancelDonation` (R5.A) under lock-set | (refactor) | M |
| SM6.E.4 | `cancelDonation_atomic_under_lockSet` | Theorem | M |
| SM6.E.5 | Cross-core cancellation (spans cores) | `cancellation_cross_core_correct` | L |
| SM6.E.6 | 6 cancellation scenarios | Tests | M |

### SM6.F — Tests + fixtures (3 PRs, 6 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM6.F.1 | `tests/SmpIpcSuite.lean` (30+ scenarios) | XL |
| SM6.F.2 | `tests/SmpNotificationSuite.lean` (15+ scenarios) | L |
| SM6.F.3 | `tests/SmpCancellationSuite.lean` (10+ scenarios) | M |
| SM6.F.4 | `tests/fixtures/smp_ipc_4core.expected` | M |
| SM6.F.5 | `scripts/test_qemu_smp_ipc.sh` | M |
| SM6.F.6 | Surface anchors | S |

## 6. Verification strategy

### 6.1 What SM6 proves

~25 substantive theorems (per §5 tables).

### 6.2 What SM6 assumes

- SM3 lock-set discipline.
- SM5 cross-core wake via SGI.
- Existing R4 IPC invariant bundle (15 conjuncts).

## 7. Risk inventory

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Lock-set ordering for IPC introduces deadlock | LOW | CRIT | Theorem 2.1.9 covers all hierarchical orders |
| Receiver wake races with sender's lock-release | LOW | HIGH | SGI emission under lock-set held; release-acquire pairing |
| Donation across cores leaks CBS budget | LOW | MED | Migration under lock-set; SM5.H.4 |
| Reply payload delivered to wrong TCB | LOW | CRIT | Lock-set includes caller TCB; serialized |
| `endpointCallWithCaps` lock-set too large | MED | MED | 5 locks at max; refactor if exceeds 8 |
| Cancellation interleaves with wake | LOW | HIGH | Lock-set includes target TCB; atomic |
| IPC test fixture diverges between runs | MED | LOW | Deterministic boot trace; SGI ordering preserved |

## 8. Acceptance gate

- [ ] All 6 IPC operations under lock-set.
- [ ] Cross-core wake works for call/signal/reply.
- [ ] `ipcInvariantFull_perCore` 15-conjunct preserved by all 6 ops.
- [ ] Cancellation atomic under lock-set.
- [ ] 2-thread cross-core IPC works.
- [ ] 4-thread SMP rendezvous test passes.
- [ ] Tier 0..4 green.

## 9. Cross-references

- **Previous**: [`SMP_PER_CORE_SCHEDULER_PLAN.md`](SMP_PER_CORE_SCHEDULER_PLAN.md)
- **Next**: [`SMP_TLB_SHOOTDOWN_PLAN.md`](SMP_TLB_SHOOTDOWN_PLAN.md)

## 10. Theorem catalogue for SM6

~25 substantive theorems including:
- `endpointCall_emits_sgi_if_remote_receiver`
- `endpointCall_perCore_blocking`
- `notificationSignal_remote_wake`
- `endpointReply_perCore_delivery`
- `donation_perCore_consistent`
- `ipcInvariantFull_perCore`
- `cancelIpcBlocking_atomic_under_lockSet`
- `cancelDonation_atomic_under_lockSet`
- `cancellation_cross_core_correct`
- 6 per-operation preservation theorems

## Appendix A — Verification commands

```bash
source ~/.elan/env
lake build SeLe4n.Kernel.IPC
lake build SmpIpcSuite
./scripts/test_qemu_smp_ipc.sh
```

---

*SM6 brings IPC to SMP. The 15-conjunct invariant bundle from R4
carries through unchanged structurally; cross-core wake is the
substantive new work.*
