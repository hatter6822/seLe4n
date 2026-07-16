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
4. **IPC invariant bundle per-core** (SM6.D): the full invariant
   bundle (15 conjuncts as planned; twenty at landing time),
   restricted to per-core endpoint/notification views.
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
| `cancelIpcBlocking` | victim TCB (W), endpoint/notification (W), consumed Reply object (W — SM6.E: the `.blockedOnReply` teardown severs `reply.caller`, the SM6.D reply-object fold) |
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
dispatch); the runtime suite (35 assertions at v0.32.58, incl. the SM6.D block) is
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
| SM6.A.10 | 8 cross-core call scenarios | `tests/SmpCrossCoreCallSuite.lean` (35 runtime assertions at v0.32.58, incl. the SM6.D §block) | ✓ |

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

**Status: LANDED (v0.31.77); live `.reply` / `.replyRecv` dispatch + production
promotion.**  Axiom-clean (`propext` / `Classical.choice` / `Quot.sound` only);
Tier 0–3 green; trace fixture byte-identical.  The cross-core reply transitions
`endpointReplyOnCore` / `endpointReceiveDualOnCore` / `endpointReplyRecvOnCore` and
the SM6.C theorems live in `SeLe4n/Kernel/IPC/CrossCore/EndpointReply.lean`
(+ `EndpointReplyInvariant.lean` for `objects.invExt` / `ipcInvariant` preservation,
`EndpointReplyNI.lean` for the boot-core + per-core / ∀-core (`lowEquivalent_smp`)
non-interference, `EndpointReplyDispatch.lean` for the below-API live
`.reply` / `.replyRecv` dispatch with donation return + cross-core PIP reversion);
the 27-assertion runtime suite is `tests/SmpCrossCoreReplySuite.lean`
(`lake exe smp_cross_core_reply_suite`).

`endpointReplyOnCore` mirrors the single-core `endpointReply` with one cross-core
substitution — the unblocked caller (the recorded `blockedOnReply` thread) is woken
through the SM5.C `wakeThread … executingCore` (enqueued on the caller's *home*
core, surfacing the optional `.reschedule` SGI) — and the replier does **not**
block.  `endpointReceiveDualOnCore` (the receive leg of `replyRecv`) blocks the
server on *its own* core via `removeRunnableOnCore … executingCore` and wakes a
`blockedOnSend` rendezvous sender on *its* home core; `endpointReplyRecvOnCore`
composes the two legs, surfacing the union of their cross-core SGIs.  The
confused-deputy gate (`replier == expected` against the caller's recorded
`replyTarget`) is unchanged, and a delivered reply leaves the caller `.ready` so a
replay fails closed (`.replyCapInvalid`) — the SM6.C.7 single-use barrier.

**Live `.reply` / `.replyRecv` arms — LANDED (v0.31.77).**  The pure cross-core
reply dispatch ops live **below the API layer** in
`SeLe4n/Kernel/IPC/CrossCore/EndpointReplyDispatch.lean` (FFI-free):
`endpointReplyCrossCoreDispatch` / `endpointReplyRecvCrossCoreDispatch` (reply +
`applyReplyDonationOnCore` return + cross-core PIP reversion
`propagatePipChainCrossCore`) and the info-flow-checked
`endpointReplyCrossCoreDispatchChecked` / `endpointReplyRecvCrossCoreDispatchChecked`.
The live `API.dispatchWithCap{,Checked}` `.reply` / `.replyRecv` arms now route
through them (executing core derived from the live state by
`determineExecutingCore st tid`).  The cross-core reply stack
(`EndpointReply` / `EndpointReplyInvariant` / `EndpointReplyDispatch`) is **promoted
to production** (only `EndpointReplyNI` remains staged); the two
`checkedDispatch_{reply,replyRecv}_eq_unchecked_when_allowed` equivalence theorems
are re-proven through the cross-core flow-allowed lemmas.  Validated: trace fixture
byte-identical, all reply + SMP suites pass, partition (56 staged) + AK7 green.

> **Model note.**  This kernel has no separate Reply *object* (the `.reply`
> lock-kind is N/A — `lockHeld` is `False` for it; see SM6.A's model note).  The
> reply *linkage* is the caller's `blockedOnReply endpointId (some replier)` TCB
> state, written under the caller-TCB **write** lock already in
> `lockSet_endpointReply` (the `replyTargetTid` member).  SM6.C.6 ("reply object
> lifecycle") is therefore the lifecycle of that reply *state* — `blockedOnReply →
> .ready` under the caller-TCB write lock — and SM6.C.7 ("reply-replay protection")
> is the consumption of that linkage.

| Sub | Description | Landed symbol | Status |
|-----|-------------|---------------|--------|
| SM6.C.1 | Migrate `endpointReply` to lock-set (cross-core) | `endpointReplyOnCore` (+ `endpointReplyOnCore_{reply,not_blocked,wrong_replier}_eq`, `lockSet_endpointReplyOnCore`, `endpointReplyOnCore_lockSet_correct`, `lockSet_endpointReplyOnCore_correct`) | ✓ |
| SM6.C.2 | Cross-core reply: wake caller | `endpointReplyOnCore_remote_wake` (+ `_no_sgi_if_local`, `_not_blocked_no_sgi`) | ✓ |
| SM6.C.3 | Donation chain across cores extension | `lockSet_endpointReply_donation_extension` + `applyReplyDonationOnCore` (cross-core return; `applyReplyDonationOnCore_bootCoreId` bridge) + cross-core PIP reversion via `propagatePipChainCrossCore` | ✓ |
| SM6.C.4 | Reply payload delivery to right TCB | `endpointReplyOnCore_perCore_delivery` (+ `storeTcbIpcStateAndMessage_fromTcb_self`) | ✓ |
| SM6.C.5 | `endpointReplyRecv` combined op lock-set | `endpointReplyRecv_lockSet_correct` (+ `endpointReplyRecvOnCore`, `endpointReceiveDualOnCore`, `lockSet_endpointReplyRecvOnCore{,_correct}`) | ✓ |
| SM6.C.6 | Reply object lifecycle | `lockSet_endpointReply_target_tcb_write_mem` (caller-TCB write lock covers the `blockedOnReply → .ready` reply-state write) + delivery | ✓ |
| SM6.C.7 | Reply-replay protection | `endpointReplyOnCore_replay_rejected` (+ `_not_blocked_eq` / `_wrong_replier_eq`: a delivered reply consumes the linkage; replay / confused-deputy fail closed) | ✓ |
| SM6.C.8 | Cross-core reply NI | `endpointReplyOnCore_reply_path_NI` (boot-core `projectState`) + `endpointReplyOnCore_reply_path_NI_smp` (per-core / ∀-core `lowEquivalent_smp` — invisible on *every* core) | ✓ |
| SM6.C.9 | Reply chain length bound (donation k > 2) | `endpointReply_donation_chain_length_bounded` (`propagatePipChainCrossCore` emits ≤ `fuel` SGIs; with `fuel = objectIndex.length`, acyclicity bounds any k-deep chain) | ✓ |
| SM6.C.10 | 8 reply scenarios | `tests/SmpCrossCoreReplySuite.lean` (27 runtime assertions) | ✓ |

### SM6.D — IPC across-core invariant bundle (2 PRs, 6 sub-tasks)

**Status: LANDED (v0.32.58).**  Axiom-clean (`propext` / `Classical.choice` /
`Quot.sound` only); Tier 0–3 green; trace fixture byte-identical.  The per-core
bundle definitions live in `SeLe4n/Kernel/IPC/Invariant/PerCoreBundle.lean`
(production) and the preservation layer in
`SeLe4n/Kernel/IPC/Invariant/PerCoreBundlePreservation.lean` (production); the
cross-core call flagship lives with the SM6.A invariant surface in
`SeLe4n/Kernel/IPC/CrossCore/EndpointCallInvariant.lean` (staged).  Surface
anchors + theorem witnesses + runtime home-core coherence assertions:
`tests/SmpCrossCoreCallSuite.lean` §SM6.D.

**Restriction discipline.**  A conjunct whose *subject* is a thread restricts
to the threads **homed** on core `c` — `threadHomeCore` = `cpuAffinity`,
defaulting to `bootCoreId`, provably the operational wake target
(`determineTargetCore_eq_threadHomeCore`).  Shared-object clauses
(notification well-formedness, badges, per-endpoint dual-queue
well-formedness, head-disjointness, the backward reply-linkage clause) are
carried whole in every core's view (endpoints/notifications are shared
kernel objects; restricting them by queue-member affinity would *weaken*
the bundle); witness positions (reachability `prev`, donation `owner`) are
never restricted.  The one scheduler-reading conjunct uses the SM4.D
per-core `passiveServerIdle_perCore`.  The decomposition is **exact**:
`ipcInvariantFull_smp st ↔ ipcInvariantFull st ∧ passiveServerIdle_smp st`
(`ipcInvariantFull_smp_iff_full_and_passive_smp`) — nothing weakened,
nothing silently strengthened.

**Bundle width note.**  §3.3 sketched the aggregate over the fifteen
R4-era conjuncts; `ipcInvariantFull` grew to **twenty** conjuncts during
the SM6.D reply-object hardening (reply↔caller linkage, server-first
receive stash, donation-owner uniqueness, queue-tail blocking, strict
link-target blocking), and the landed `ipcInvariantFull_perCore` mirrors
the current twenty-conjunct bundle — dropping the five newer conjuncts
from the per-core view would re-open on the SMP surface exactly the
false-assurance gaps they closed.  The fifteen-conjunct planned form is
recoverable as `ipcInvariantCore_of_smp`.

**Preservation architecture (SM6.D.2).**  Nineteen conjuncts ride the
existing single-core whole-bundle theorems
(`…_preserves_ipcInvariantFull`, `Structural/DualQueueMembership.lean`)
through the exact-decomposition bridges — precisely §3.3's "the existing
single-core proof carries through", with zero duplication.  The per-core
`passiveServerIdle` slice is the genuinely new SMP obligation: it rides a
new core-parameterised pullback-frame family
(`passiveServerIdleFrameOnCore` + per-store micro-frames + one
composition per operation), built on the SM4.B per-core independence
algebra — **no idle-core assumption anywhere** (unlike the SM4.D-era
`…_smp_of_singleCore_and_idle` lifters, these theorems hold with all
four cores actively scheduling).  The 2PL lock-set precondition story is
unchanged from SM6.A/B/C: the transitions are pure and the
`…_atomic_under_lockSet` theorems carry them through the `withLockSet`
fold (Cor 2.1.11), so the per-core bundle holds at every 2PL commit
point.

> **Scope note (updated at the v0.32.59 completion pass).**  The former
> OnCore proof-depth gap is **closed**: every cross-core transition now
> carries a whole-bundle theorem and a per-core flagship —
> `notificationSignalOnCore` / `notificationWaitOnCore`
> (`IPC/CrossCore/NotificationInvariant.lean` §3–§6) and
> `endpointReplyOnCore` / `endpointReceiveDualOnCore` /
> `endpointReplyRecvOnCore` (`IPC/CrossCore/EndpointReplyInvariant.lean`
> §4–§11), all `…_preserves_ipcInvariantFull{,_perCore}`,
> **unconditional over success/failure** (error paths return the
> pre-state).  The proof lever is the SM6.D transfer layer
> (`IPC/Invariant/LookupCongruence.lean`, production): pointwise-lookup
> congruences for every conjunct + the `OffSchedulerAgrees` relation,
> consumed by per-operation *agreement dichotomies* (`…_post_agrees`) —
> a cross-core transition either fails or runs the same object-store
> spine as its single-core counterpart and diverges only in scheduler
> placement, so the single-core whole-bundle theorem carries across.
> The composed `endpointReplyRecvOnCore` is closed **compositionally**
> through its two legs (the `replyStashValid` fold is read at each
> leg's own input state, avoiding cross-state fold alignment), with the
> receive leg's pre-state facts transported across the reply leg by the
> effect characterisations `endpointReplyOnCore_tcb_backward` /
> `_endpoint_backward` / `_preserves_replyIdEstablishFresh` /
> `_reuse_freshens`; its `hReplyIdValid` premise is **disjunctive**,
> covering the faithful seL4-MCS one-object-reuse pattern the runtime
> fold enables.  The capability-carrying trio behind the live `.send`
> dispatch is likewise covered
> (`endpointSendDualWithCaps/endpointReceiveDualWithCaps/endpointCallWithCaps_preserves_ipcInvariantFull_perCore`
> + `ipcUnwrapCaps_passiveServerIdleFrameOnCore`,
> `PerCoreBundlePreservation.lean` §6).
>
> **Remaining tracked debt (recorded, not silent):**
> 1. **Bound-notification delivery** (`notificationSignalBoundOnCore`):
>    whole-bundle preservation of the bound-TCB delivery path needs the
>    `endpointQueueRemoveDual` per-conjunct suite (~14 of the twenty
>    conjuncts lack `endpointQueueRemoveDual_preserves_…` lemmas — the
>    queue-splice PopHead-class proofs).  Closure target:
>    `endpointQueueRemoveDual_preserves_<conjunct>` (membership / NoDup
>    / next-blocking / head- and tail-blocked / next-target first) →
>    `notificationSignalBoundOnCore_preserves_ipcInvariantFull{,_perCore}`.
>    Already covered today: at the **bound-op level**, `objects.invExt`
>    and `ipcInvariant` (`NotificationBind.lean`, + the dispatch-level
>    mirrors) plus the SM6.B lock-set/2PL theorems; at the
>    **`endpointQueueRemoveDual` step level**, additionally
>    `dualQueueSystemInvariant`, the scheduler contract
>    (`…_ipcSchedulerContractPredicates{,_smp}`), `tail_of_nonTail`, and
>    the tcb/endpoint/notification transports.
> 2. **`withLockSet` bundle preservation**: the lock acquire/release
>    steps rewrite an object's *lock* field, so the lookup-congruence
>    layer does not apply; carrying `ipcInvariantFull_perCore` through
>    the runtime `withLockSet` bracket needs a semantic-fields-agree
>    relation plus per-conjunct lock-write congruences.  Closure target:
>    `acquireLockOnObject/releaseLockOnObject_preserves_ipcInvariantFull`
>    → `withLockSet_preserves_ipcInvariantFull_perCore` (the generic
>    `withLockSet_invariant_preserved` fold is already in place, cf.
>    `objects.invExt`).  Until then the bundle holds at every 2PL commit
>    point via the transitions' purity + the `…_atomic_under_lockSet`
>    theorems, exactly as at v0.32.58.
> 3. **Completeness sugar** (non-load-bearing): per-conjunct `_smp_iff`
>    exactness for the fourteen unnamed conjuncts (the aggregate
>    exactness `ipcInvariantFull_smp_iff_full_and_passive_smp` already
>    subsumes their round-trip), a named `ipcInvariantCore_perCore`
>    slice, and relocating `threadHomeCore` onto `TCB` as a method.
>    Sharper per-core theorem forms are deliberately *not* queued: the
>    whole-bundle theorems already take the global bundle
>    (`ipcInvariantFull st`), and `ipcInvariantFull_perCore_of_full` is
>    the one-application sharp lift for any consumer holding a per-core
>    passive slice.

| Sub | Description | Landed symbol | Status |
|-----|-------------|---------------|--------|
| SM6.D.1 | `ipcInvariantFull_perCore` aggregate | `ipcInvariantFull_perCore` (twenty named fields) + `ipcInvariantFull_smp` + `ipcInvariantFull_perCore_of_full` / `ipcInvariantFull_of_smp` / `ipcInvariantCore_of_smp` + exactness `ipcInvariantFull_smp_iff_full_and_passive_smp` + boot witness `default_ipcInvariantFull_perCore{,_smp}` | ✓ |
| SM6.D.2 | 6 per-operation preservation theorems | `endpointSendDual/endpointReceiveDual/endpointCall/endpointReply/endpointReplyRecv/notificationSignal/notificationWait_preserves_ipcInvariantFull_perCore` + cross-core flagship `endpointCallOnCore_preserves_ipcInvariantFull_perCore` (+ `passiveServerIdleFrameOnCore` micro-frame family, per-op compositions, `endpointCallOnCore_preserves_passiveServerIdle_perCore`) | ✓ |
| SM6.D.3 | `ipcStateQueueMembershipConsistent_perCore` | def + `_perCore_of_global` + `_of_forall_perCore` + exactness `ipcStateQueueMembershipConsistent_smp_iff` | ✓ |
| SM6.D.4 | `endpointQueueNoDup_perCore` | def + bridges + `endpointQueueNoDup_smp_iff` | ✓ |
| SM6.D.5 | `queueNextBlockingConsistent_perCore` | def + bridges + `queueNextBlockingConsistent_smp_iff` | ✓ |
| SM6.D.6 | `queueHeadBlockedConsistent_perCore` | def + bridges + `queueHeadBlockedConsistent_smp_iff` | ✓ |
| SM6.D completion (v0.32.59) | OnCore whole-bundle closures + WithCaps trio + transfer layer | `LookupCongruence.lean` (per-conjunct `…_of_getElem_eq` ×20 + `ipcInvariantFull_of_getElem_eq` + `OffSchedulerAgrees` + step congruences); `notificationSignalOnCore/notificationWaitOnCore/endpointReplyOnCore/endpointReceiveDualOnCore_post_agrees` + `…_preserves_ipcInvariantFull{,_perCore}`; compositional `endpointReplyRecvOnCore_preserves_ipcInvariantFull{,_perCore}` (+ transports `endpointReplyOnCore_tcb_backward/_endpoint_backward/_preserves_replyIdEstablishFresh/_reuse_freshens`); `endpointSendDualWithCaps/endpointReceiveDualWithCaps/endpointCallWithCaps_preserves_ipcInvariantFull_perCore` + `ipcUnwrapCaps_passiveServerIdleFrameOnCore`; boot-frame exactness `passiveServerIdleFrameOnCore_boot_iff` | ✓ |

(The remaining fourteen bundle conjuncts also received per-core forms +
both bridges each — `tcbQueueLinkIntegrity/tcbQueueChainAcyclic/
dualQueueSystemInvariant/allPendingMessagesBounded/
waitingThreadsPendingMessageNone/blockedThreadTimeoutConsistent/
donationChainAcyclic/donationOwnerValid/donationBudgetTransfer/
blockedOnReplyHasTarget/replyCallerLinkage{,Reciprocal}/
blockedOnReplyHasReplyObject/pendingReceiveReplyWellFormed/
donationOwnerUnique/endpointQueueTailBlockedConsistent/
queueNextTargetBlocked`, each `_perCore` — so the aggregate is fully
per-core, not just the four named rows.)

### SM6.E — Cancellation across cores (3 PRs, 6 sub-tasks) — LANDED (v0.32.60) + completion cut (v0.32.61) + PR-review cuts (v0.32.62–65) + audit-closure cut (v0.32.66)

Deliverable module: `SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean`
(**production** — imported by `SeLe4n.lean`), plus the single-core
cancellation invariant surface in
`Lifecycle/Invariant/SuspendPreservation.lean` and
`Lifecycle/Operations/CleanupPreservation.lean`, and the
`lockSet_tcbSuspend` / `permittedKinds .tcbSuspend` reply extension in
`Concurrency/Locks/LockSetTransitions.lean`.

**Architecture.**  The cross-core cancellation composite is the
G2+G4+G7 slice of the suspend pipeline generalised across cores:
`cancelIpcBlockingOnCore` runs the (pure, scheduler-silent) single-core
object teardown `cancelIpcBlocking`, then removes the victim from its
**home** core's run queue / current slot (the new `descheduleThread`
primitive — the SM5.C `wakeThread` dual), surfacing a `.reschedule` SGI
exactly when the victim was **actively current on a remote core** (a
merely-queued remote victim needs no poke; a victim current on the
executing core is rescheduled synchronously by the caller; a `tid` that
resolves to no TCB pokes nothing — the wake ghost-guard, mirrored).
The donation side (`cancelBoundDonationOnCore` /
`cancelDonationOnCore`) fixes the single-core arm's hardcoded
`bootCoreId` replenish-queue purge: the SC's pending replenishments are
purged from the **victim's home core's** queue (SM5.H
`replenishQueueAffinityConsistentOnCore` places them there), with the
single-core form recovered definitionally at the boot core
(`cancelBoundDonationOnCore_bootCoreId`, the SM5.A bridge pattern).

**Footprint honesty (SM6.E.1).**  The plan's §3.1 cancellation rows
landed as `lockSet_cancelIpcBlocking` (victim TCB W; blocked-on
endpoint/notification W; **and the consumed Reply object W** — the
SM6.D reply-object fold made `cancelIpcBlocking` sever
`reply.caller` on the `.blockedOnReply` arm, a write the suspend
footprint had never declared) and `lockSet_cancelDonation` (victim TCB
W; SchedContext W; donated-arm original-owner TCB W).  Closing that gap
required extending `permittedKinds .tcbSuspend` with `.reply` and
threading an optional `consumedReplyId` through `lockSet_tcbSuspend`
(now a 5-extension footprint, size 8 = `maxLockSetSize` exactly).
Both cancellation footprints are member-by-member covered by the
enclosing suspend footprint (`lockSet_tcbSuspend_*_write_mem` ×6) — the
formal content of "the cancellation sub-operations run inside the
`.tcbSuspend` 2PL bracket with every write under a held lock".

| Sub | Description | Landed symbol | Status |
|-----|-------------|---------------|--------|
| SM6.E.1 | Migrate `cancelIpcBlocking` to lock-set | `lockSet_cancelIpcBlocking` + pre-resolution (`cancelBlockedEndpoint?`/`cancelBlockedNotification?`/`cancelConsumedReply?`) + state-resolved `lockSet_cancelIpcBlockingOnCore` + consistency/Nodup (`lockSet_consistent_cancelIpcBlocking`, `cancelIpcBlockingOnCore_lockSet_correct`) + write coverage (`lockSet_cancelIpcBlocking_{victim_tcb,blocked_endpoint,blocked_notification,consumed_reply}_write_mem`) + suspend coverage (`lockSet_tcbSuspend_*_write_mem`, incl. the new `consumedReplyId` extension) | ✓ |
| SM6.E.2 | `cancelIpcBlocking_atomic_under_lockSet` | landed (exact plan name) + the cross-core companion `cancelIpcBlockingOnCore_atomic_under_lockSet` (both via `lockSet_atomic_under_2pl`) | ✓ |
| SM6.E.3 | `cancelDonation` (R5.A) under lock-set | `lockSet_cancelDonation` + pre-resolution (`cancelBindingSc?`/`cancelDonatedOwner?`) + state-resolved form + consistency + write coverage + the per-core arms `cancelBoundDonationOnCore` (home-core replenish purge: `_replenishQueue_purged`/`_replenishQueue_ne`/`_runQueue_current_eq`) and dispatcher `cancelDonationOnCore` (error paths return the pre-state) | ✓ |
| SM6.E.4 | `cancelDonation_atomic_under_lockSet` | landed (exact plan name) + the per-core companion `cancelDonationOnCore_atomic_under_lockSet` | ✓ |
| SM6.E.5 | Cross-core cancellation (spans cores) | `descheduleThread` (wakeThread dual: `_emits_sgi_if_remote_current`, `_no_sgi_if_local`/`_no_sgi_if_not_current`/`_no_sgi_if_ghost`, `_descheduled_on_home`, `_independent_of_other_core`) + `cancelIpcBlockingOnCore` (reductions `_state_eq`/`_objects_eq`/`_eq_descheduleThread`/`_ready_eq_descheduleThread`, SGI family, `_preserves_objects_invExt`) + the flagship `cancellation_cross_core_correct` (remote poke ∧ full home-core deschedule ∧ per-core locality ∧ object-level fidelity) | ✓ |
| SM6.E.6 | 6 cancellation scenarios | `tests/SmpCancellationSuite.lean` — 17 scenario groups / 107 assertions (endpoint-/notification-/reply-blocked remote-homed victims; running-remote SGI vs running-local no-SGI; bound-donation home-core purge; donated return-to-owner **with §2b replenishment-migration assertions**; dispatcher identity + ghost + `withLockSet` bracket; **completion cut**: notification sole-waiter state correction + two-waiter retention, 3-deep mid-queue splice link patches, mirror SGI (boot-homed victim cancelled from a remote core), the live `suspendThreadOnCore` (remote SGI + diff-seam recovery + local inline successor dispatch + `.Inactive` rejection + single-core inertness), and send-/receive-blocked teardown arms; **v0.32.62 PR-review cut**: the §3.14 PIP-donation-drop scenario — suspending a reply-blocked client drops the server's donated `pipBoost`, re-keys the server's home-core run-queue bucket, and the diff seam pokes both the server's and the victim's home cores; single-core mirror; **v0.32.63**: the §3.15 disinheritance-scheduling scenarios — the deboosted boot current is preempted inline by a mid-priority bystander (single-core mirror included), and a still-current remote server's core is poked by the diff seam's deboosted-current rule), wired Tier-2 (`smp_cancellation_suite`) + Tier-3 anchors | ✓ |

Supporting invariant surface (single-core, production):
`cancelIpcBlocking_preserves_objects_invExt` (+ per-helper lemmas
`spliceOutMidQueueNode`/`removeFromAllEndpointQueues`/
`removeFromAllNotificationWaitLists`/`consumeReplyLink`/
`clearReplyObjectCaller`/`clearTcbReplyObject` `_preserves_objects_invExt`),
`cancelBoundDonation`/`cancelDonatedDonation`/`cancelDonation`
`_preserves_objects_invExt`,
`cleanupDonatedSchedContext_preserves_objects_invExt`, and the ∀-core
`cancelDonatedDonation_scheduler_eq`.
(`returnDonatedSchedContext_preserves_objects_invExt` was promoted from
`private` to feed the donated arm.)

**Completion cut (v0.32.61) — the four tracked-debt items of the
v0.32.60 landing, closed or narrowed:**

1. **Live `.tcbSuspend` cross-core dispatch — CLOSED.**
   `suspendThreadOnCore` (Cancellation.lean §13) is the complete per-core
   suspend (the `resumeThreadOnCore` mirror): home-core G7-precapture,
   per-core donation arms, home-core `removeRunnableOnCore`, and the
   local/remote reschedule seam (`handleRescheduleSgiOnCore` inline vs. a
   `.reschedule` SGI to the victim's home core), with
   `suspendThreadOnCore_{rejects_absent,rejects_inactive,sgi_remote_reschedule,local_no_sgi}`.
   The `API.dispatchCapabilityOnly` `.tcbSuspend` arm routes through it
   (`determineExecutingCore`, the SM6.A per-core caller identification);
   the surfaced SGI is dropped at the pure layer and re-derived by the diff
   seam — `crossCoreSgiBody` gained the SM6.E **descheduled-current rule**
   (`crossCoreSgiBody_remote_deschedule`: fire `.reschedule` when a victim
   was actively current on a remote home core and is neither current nor
   queued there in the post-state; single-core inertness preserved).  The
   AN9-D atomicity bracket is flipped to the new FFI seam
   `suspend_thread_cross_core` (`SyscallDispatchEntry.suspendThreadCrossCoreEntry`,
   commit-then-fire; Rust `sele4n_suspend_thread` extern updated).
   Validated: golden trace byte-identical, `syscall_dispatch_suite` /
   `smp_pip_suite` / `smp_cancellation_suite` green, Rust HAL 724 green.
2. **Cancellation non-interference — LANDED (staged `CancellationNI`).**
   Every SM6.E-*new* state effect is discharged **substantively**:
   `descheduleThread_cancellation_NI{,_smp}` (high-victim home-core
   deschedule invisible on every core),
   `cancelIpcBlockingOnCore_ready_cancellation_NI{,_smp}` (the `.ready` /
   suspend-of-running-victim composite, fully substantive), the ∀-core
   replenish-queue frames (`setReplenishQueueOnCore_preserves_projection{,OnCore}`,
   `migrateSchedContextReplenishment_preserves_projectionOnCore`), and
   `cancelDonatedDonationOnCore_cancellation_NI{,_smp}` (substantive
   migration leg).  The blocked-arm composites
   (`cancelIpcBlockingOnCore_cancellation_NI{,_smp}`) consume the
   **single-core teardown projection** as their one hypothesis — the same
   obligation the production closure form
   (`suspendThread_preserves_projection` G3, AK6-F.18) has always
   documented for the sequential pipeline; closing that single-core
   closure form (per-sweep projection lemmas) closes the cross-core NI
   with no further work.  Registered in `Platform/Staged.lean` +
   `scripts/staged_module_allowlist.txt` (staged-only 56 → 57).
3. **Whole-bundle preservation — groundwork landed, per-conjunct status:**
   * **CLOSED — `ipcInvariant` (the notification well-formedness
     conjunct)**, across the entire cancellation surface: the fold
     keystone `RHTable.fold_preserves_of_lookup` (the step learns the
     visited key's stored value), the state-correcting notification-sweep
     proof (`notificationQueueWellFormed_filter_correct` — the sweep's
     sole-waiter `.idle` correction is exactly what makes this conjunct
     provable), and
     `{spliceOutMidQueueNode,removeFromAllEndpointQueues,removeFromAllNotificationWaitLists,restoreToReady,clearTcbReplyObject,clearReplyObjectCaller,consumeReplyLink,cancelIpcBlocking,cancelBoundDonation,cancelDonatedDonation,cancelDonation,cleanupDonatedSchedContext}_preserves_ipcInvariant`
     + the OnCore family
     (`{descheduleThread,cancelIpcBlockingOnCore,cancelBoundDonationOnCore,cancelDonatedDonationOnCore,cancelDonationOnCore}_preserves_ipcInvariant`)
     + the reusable transports (`ipcInvariant_of_objects_eq`,
     `notification_lookup_of_insert_no_notification`,
     `ipcInvariant_insert_{no_notification,tcb,endpoint}`).
   * **CLOSED — `objects.invExt`** (v0.32.60, retained).
   * **OPEN — the remaining `ipcInvariantFull` conjuncts** (queue
     membership / NoDup / next-blocking / head-blocked, the reply
     conjuncts, …): the sweeps rewrite every endpoint/notification, so
     each conjunct needs its own fold lemma
     (`removeFromAllEndpointQueues_preserves_<conjunct>` — the
     queue-splice PopHead-class proofs, kin of the SM6.D
     `endpointQueueRemoveDual` debt).  The per-key machinery this cut
     landed (`fold_preserves_of_lookup`, the `_tcb_lookup` /
     `_no_tcb` characterisations) is the intended engine.  Closure
     target unchanged:
     `cancelIpcBlockingOnCore_preserves_ipcInvariantFull{,_perCore}`.
4. **Pre/post resolution discharge — CLOSED.**  The teardown's per-key
   TCB frames (`spliceOutMidQueueNode_tcb_lookup`, the sweeps'
   `_tcb_lookup` / `_no_tcb` families via the fold keystone,
   `restoreToReady`/`clearTcbReplyObject`/`consumeReplyLink`
   `_tcb_lookup`) compose into `cancelIpcBlocking_tcb_lookup` /
   `cancelIpcBlocking_getTcb?_none` →
   `cancelIpcBlocking_determineTargetCore_eq` /
   `cancelIpcBlocking_getTcb?_isSome_eq`, discharging both frame
   hypotheses **unconditionally** over the standing store invariant:
   `cancelIpcBlockingOnCore_eq_descheduleThread_closed` (only `invExt`).

**Completion cut — additional surface.**  Observational atomicity
(plan §5.3, cancellation instance): the SM3.C.7 guarded observer layer
(`AcquireInsensitiveOn`/`ReleaseInsensitiveOn` +
`lockSet_observer_atomic_on`, `LockSet2PL` §4c) instantiated at the
victim-`ipcState` observer — `updateObjectLockAt_getTcb?_ipcState` (lock
writes are lock-field-only), `acquireLockOnObject`/`releaseLockOnObject`
`_preserves_objects_invExt` (guard stability), and the capstone
`cancelIpcBlockingOnCore_observer_atomic` (the 2PL machinery is invisible
to the cancellation's decisive observable).  Boot-instance bridges + the
SM5.H corollaries: `cancelIpcBlockingOnCore_bootHome_state_eq`,
`cancelDonationOnCore_bootHome_{ok,error}`,
`descheduleThread_fully_descheduled` (placement discipline ⇒ system-wide
deschedule), `cancelBoundDonationOnCore_replenishments_purged` (affinity
discipline ⇒ system-wide purge).  Two **pre-existing single-core defects**
found by this cut's proof work were fixed and are regression-tested:
`removeFromAllNotificationWaitLists` left a sole-waiter cancellation in an
`ipcInvariant`-violating `.waiting`-with-`[]` state (now state-correcting,
suite §3.9), and `suspendThread`'s G7 reschedule guard read the current
slot **after** G4 had cleared it, making the suspend-the-running-thread
reschedule unreachable (now a G7-precapture read, mirrored by
`suspendThreadOnCore`; suite §3.12 exercises the successor dispatch).
The TOCTOU shape of pre-state resolution is documented at the resolution
sites (lock-conflict serialisation + the AN9-D interrupt bracket).

**PR-review cut (v0.32.62) — PR #831 P2 remediation + the two root-cause
layers beneath it:**

1. **Suspend PIP-revert ordering fix (a third pre-existing single-core
   defect).**  `suspendThread` ran `revertPriorityInheritance` at the
   *victim*, *before* `cancelIpcBlocking` cleared the victim's `ipcState`,
   so every chain member's `pipBoost` recomputed from a `waitersOf` still
   containing the victim — a fixed-point no-op: a server holding the
   suspended victim's donated priority retained it indefinitely (the
   SM6.C replay barrier means no later reply-path revert runs for the
   consumed reply).  Both `suspendThread` and `suspendThreadOnCore` now
   use `timeoutThread`'s D4-N capture → clear → revert-from-server order
   (G2-precapture via `blockingServer`; the walk runs on the
   post-teardown state).
2. **Per-core bucket migration.**  `suspendThreadOnCore`'s revert walk is
   the SM5.F.4 `propagatePipChainCrossCore` (revert-capable per
   `revert_eq_propagate`): each chain member's run-queue bucket migrates
   on **its** home core (`updatePipBoostOnCore`), closing the SM5.F
   per-core-PIP-migration gap for the suspend path (previously tracked at
   the timeout site).
3. **Diff-fired suspend-entry SGIs (the review's exact ask).**
   `suspendThreadCrossCoreEntry` fires
   `computeCrossCoreSgis pre post execCore` — exactly as
   `syscallDispatchCrossCoreEntry` — so the G2b re-bucketing pokes ride
   the diff alongside the re-derived victim-deschedule poke
   (`crossCoreSgiBody_remote_deschedule`); single-core inertness via
   `computeCrossCoreSgis_nil_single_core`.
4. **Chain-walk obligation declared.**  `pipChainStart_tcbSuspend` (the
   fourth `pipChainStart_<τ>` marker; SM3.B inventory 98 → 99, chainStart
   3 → 4), with the SM3.C consumer contract amended: the suspend chain
   start (the captured server) is not a static-footprint member — the
   SM3.C.11 walker's first CAS-acquisition covers it (deadlock-freedom
   rests on bounded-retry try-acquisition, not static inclusion).

Suite §3.14 (PIP-donation drop: boost dropped, home-core bucket re-keyed,
diff pokes both remote cores, single-core mirror); trace byte-identical.

**PR-review cut 2 (v0.32.63) — disinheritance scheduling points (two P2s
on the v0.32.62 cut):** a suspend that deboosts a **still-current** server
created no scheduling point — locally G7 fired only when the *victim* was
current, and remotely `crossCoreSgiBody` fired only for queued threads or
a *cleared* current slot.  Fixed at both levels:

1. **Local preemption gate.**  Both suspend forms snapshot the executing
   core's current thread's effective priority at entry
   (`currentEffectivePrio?`, `Lifecycle/Suspend.lean`) and, when it is
   still current with a strictly lower effective priority after the
   pipeline (`currentDeboostedFrom`), run the gated local scheduling point
   (`handleRescheduleSgiOnCore`).  The per-core G7 dispatch is factored
   into `suspendRescheduleOnCore` with arm-level SGI-discipline lemmas
   (`suspendRescheduleOnCore_sgi_shape` / `_local_no_sgi`).
2. **Deboosted-current diff rule.**  `crossCoreSgiBody` gains a fourth
   rule (`crossCoreSgiBody_remote_deboost_current`): a thread still
   current on its remote home core whose effective priority *dropped*
   fires a `.reschedule` there.  A raise fires nothing; single-core
   inertness preserved.

Suite §3.15 (local preemption + single-core mirror + remote
still-current poke); trace byte-identical.

**PR-review cut 3 (v0.32.64) — scheduler-lock footprint closure:**
`suspendThreadOnCoreSchedLockSet` gains the executing core (both run-queue
write locks, via the shared `sortedSchedCorePair` segment shape; ascending
acquisition re-proven compositionally); the SM3.C.11 chain-walk contract now
requires each step to hold the member's TCB write lock AND its home-core
`SchedLockId.runQueue` write lock (the `updatePipBoostOnCore` re-bucketing
is state-discovered — outside any static footprint — and the declaration
covers the `.call`/`.reply`/`.replyRecv` walks identically); and
`candidateOutranksCurrentOnCore`'s TCB-field comparison is documented sound
under `boundThreadPriorityConsistent` (the `_of_agree` bridge), with the
obligation to switch to `resolveEffectivePrioDeadline` if that invariant is
ever relaxed.  Suite §3.15(d).

**PR-review cut 4 (v0.32.65) — running-core suspend + write-set honesty
(one P1, two P2s):** an unbound victim (home = boot) can be CURRENT on a
secondary core (unbinding a running thread is admitted — the migration
reject gate fires only when the new affinity forbids the running core);
the home-keyed suspend marked it `.Inactive` while that core kept
executing it, unpoked.  Fixed: `runningCoreOf?` resolves the actual
running core; `suspendThreadOnCore` deschedules it (G4b) and keys G7 on
it; `crossCoreSgiBody`'s descheduled/deboosted rules re-keyed to the
pre-state running core (single-core inertness re-proven with the
empty-secondary-current-slot premise).  Write-set honesty: the
endpoint/notification sweeps insert only changed objects, and the splice's
neighbour-TCB writes are declared footprint members
(`cancelSpliceNeighbors?` → two `.tcb` write locks in the state-resolved
cancel footprint).  Suite §3.16 + neighbour-lock assertions.

**Audit-closure cut (v0.32.66)** — a three-auditor deep audit (plan
conformance + vacuity / live-dispatch security / diff-seam semantics +
coverage) returned "substantively implemented, zero sorry/axiom, authority
sound, fail-closed, no CVE-class findings" and this cut lands every
surviving finding: the running-core run-queue lock in the suspend footprint
(`sortedSchedCoreTriple`), the EDF deadline dimension in the diff rules
(queued deadline change + weakened-current deadline-later fire; suite
§3.17), the `currentThreadUniqueAcrossCores` invariant slice (boot witness
+ deschedule preservation; full-surface adoption tracked WS-SM debt), the
AK6-F.18 G3 projection-sketch correction (the splice's neighbour queue-link
writes ride the SM6.B dual-queue endpoint-label debt — the `hTeardownProj`
obligation of the staged `CancellationNI`), the donation-side observer
capstone (`cancelDonationOnCore_observer_atomic`), and the doc/authority
hardening set (live-target header, running-core SGI docstrings, capstone
cross-references, the `suspend_thread_cross_core` self-authorization
obligation, queue-branch precedence + neighbour-lock convention notes).
**Newly registered tracked debt (audit adjacents)**:
`schedContextConfigure` is boot-pinned on two per-core queues (its
replenish purge and run-queue re-bucket touch `bootCoreId` only —
`SchedContext/Operations.lean`; the SM5.H-discipline migration is an
SM-phase follow-on), and full-surface `currentThreadUniqueAcrossCores`
preservation.

### SM6.F — Tests + fixtures (3 PRs, 6 sub-tasks) — LANDED (v0.32.67)

**Status: LANDED (v0.32.67).**  The SM6 closure phase: the aggregate
end-to-end suites, the golden 4-core IPC trace fixture, the Tier-4 QEMU
handshake exerciser, and the Tier-3 surface anchors.  Where the per-phase
suites (SM6.A.10 / SM6.B.8 / SM6.C.10 / SM6.E.6) exercise each transition in
isolation, the SM6.F aggregates drive **multi-step pipelines** composing the
SM6 transitions with the SM5 per-core scheduler (`handleRescheduleSgiOnCore`
dispatch on the SGI's target core) into full client/server round trips —
closing the §8 acceptance-gate items "2-thread cross-core IPC works" and
"4-thread SMP rendezvous test passes" on the live operations.

| Sub | Description | Landed artefact | Status |
|-----|-------------|-----------------|--------|
| SM6.F.1 | `tests/SmpIpcSuite.lean` (30+ scenarios) | `lake exe smp_ipc_suite` — **125 runtime assertions across 14 scenario groups (§3.1–§3.14) + the §9 golden-trace check**: the 2-thread cross-core call/reply round trip (call SGI → target-core handler dispatch → reply SGI → handler dispatch, payload delivered both ways, replay barrier), the interleaved 4-thread rendezvous (cross-pair framing + payload isolation + per-thread terminal placement), the cross-core send/receive rendezvous (`blockedOnSend` sender woken to its home core), client-first ordering (`blockedOnCall` → receive completes the same rendezvous), the server `endpointReplyRecvOnCore` steady-state loop (SGI union, one-object reuse-safe fresh-reply linkage), fail-closed error paths (absent/wrong-kind/oversized/replay/no-stash — pre-state returned), state-resolved 2PL footprints (kinds/NoDup/membership + the **exact resolved footprint size** and the §4.1 WCRT-fits-1 ms-tick property), live-dispatch coherence (`determineExecutingCore` + `endpointCallCrossCoreDispatch`), the **SchedContext donation round trip** (`applyCallDonation` → server `.donated` at the donated effective priority → `applyReplyDonationOnCore` returns it), **capability transfer** (`ipcUnwrapCaps` grant-gated + the `ipcMessageTooManyCaps` bound), **info-flow-checked dispatch** (call + reply `…CrossCoreDispatchChecked` allowed-vs-`.flowDenied`), the **live API dispatch** path (`dispatchSyscall`/`dispatchSyscallChecked` `.call`: CSpace cap resolution + authority gate + cross-core, authorized/no-cap/read-only/wrong-kind/flow-denied), **cancellation × IPC** (cancel a reply-blocked client ⇒ the server's reply fails closed), and **scheduler contention** (a woken server does not preempt a higher-priority current).  The 4-thread pipeline carries **step attribution** on failure.  Tier-2 (`test_tier2_negative.sh`) + Tier-3 anchors | ✓ |
| SM6.F.2 | `tests/SmpNotificationSuite.lean` (15+ scenarios) | `lake exe smp_notification_suite` — **74 runtime assertions across 10 scenario groups (§3.1–§3.10)**: per-core wait blocking, the wait → cross-core signal → SGI → handler-dispatch round trip, multi-waiter head-first drain (each waiter woken to its **own** home core, per-waiter badge isolation), waiterless badge accumulation (`Badge.bor`) + the non-blocking consume, the **remote bound-TCB delivery** round trip (bind → signal-bound → endpoint dequeue → SGI to the bound TCB's home core → handler dispatch), the bind/unbind lifecycle, fail-closed error paths, independence framing + state-resolved 2PL footprints (exact size + WCRT-fits-budget), the **three-waiter FIFO drain** (successive signals wake the list head first, each to a distinct home core 1/2/3), and **checked cross-core dispatch** (the unchecked wait dispatch descheds on the caller's own core; the checked bound signal fails closed on a denied signaler→notification flow AND on the review-#3 notification→receiver badge-leak gate).  Tier-2 + Tier-3 anchors | ✓ |
| SM6.F.3 | `tests/SmpCancellationSuite.lean` (10+ scenarios) | landed with SM6.E.6 (v0.32.60–66): 107 runtime assertions across 17 scenario groups — see the SM6.E table | ✓ |
| SM6.F.4 | `tests/fixtures/smp_ipc_4core.expected` | the deterministic 16-line `[smp-ipc-4core]` golden trace (+ `.sha256` companion, auto-gated by `test_tier2_trace.sh`'s companion walk), computed line-by-line from the live SM6 transition decisions and verified **byte-for-byte** inside `smp_ipc_suite` §9 (regen: `lake exe smp_ipc_suite \| grep '^\[smp-ipc-4core\]'` — see `tests/fixtures/README.md`) | ✓ |
| SM6.F.5 | `scripts/test_qemu_smp_ipc.sh` | the Tier-4 QEMU `-smp 4` cross-core IPC handshake exerciser, registered in `test_tier4_smp_bootcheck.sh`; SKIPs (with the formal-coverage banner) until the SM9.E bootable kernel-image `[[bin]]` target exists — the sibling discipline of the SM5 QEMU scripts; pass gate: `[smp-test] cross-core-ipc: reply delivered across cores` | ✓ |
| SM6.F.6 | Surface anchors | in-suite `#check` anchor blocks (§1 of both aggregates: transitions, dispatches, pre-resolution helpers, acceptance-gate theorems, SM6.D.2 six-op preservation) + the Tier-3 grep anchors in `test_tier3_invariant_surface.sh` (runner defs, Tier-2 wiring, pipeline/trace emitters, fixture + sha256 presence, lakefile registrations, the QEMU exerciser registration) | ✓ |

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

- [x] All 6 IPC operations under lock-set (SM6.A.2/.8, SM6.B.1, SM6.C.1/.5, SM6.E.1/.3 — declared footprints + state-resolved forms + `…_lockSet_correct` + `…_atomic_under_lockSet` across send/receive/call/reply+replyRecv/signal/wait and the cancellation arms).
- [x] Cross-core wake works for call/signal/reply (SM6.A.3 Thm 3.2.1, SM6.B.2, SM6.C.2; live diff-seam re-derivation `crossCoreSgiBody_remote_wake`, v0.31.72).
- [x] `ipcInvariantFull_perCore` preserved by all 6 ops (SM6.D, v0.32.58 — the bundle grew to twenty conjuncts by landing time; the fifteen-conjunct core is `ipcInvariantCore_of_smp`).
- [x] Cancellation atomic under lock-set (SM6.E, v0.32.60 — `cancelIpcBlocking_atomic_under_lockSet` / `cancelDonation_atomic_under_lockSet` + the OnCore companions; footprints covered member-by-member by the reply-extended `lockSet_tcbSuspend`).
- [x] 2-thread cross-core IPC works (SM6.F.1 §3.1 — the composed call → SGI → handler-dispatch → reply → SGI → handler-dispatch round trip on the live operations, payload delivered both ways).
- [x] 4-thread SMP rendezvous test passes (SM6.F.1 §3.2 — two interleaved client/server pairs across all four cores, cross-pair framing + payload isolation + per-thread terminal placement).
- [x] Tier 0..4 green (SM6.F, v0.32.67 — Tiers 0–3 substantive; the Tier-4 QEMU sub-tests SKIP by design until the SM9.E bootable kernel-image target exists, exactly as the SM1–SM5 QEMU siblings).

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
- `cancelIpcBlocking_atomic_under_lockSet` (landed, SM6.E — plus the
  cross-core companion `cancelIpcBlockingOnCore_atomic_under_lockSet`)
- `cancelDonation_atomic_under_lockSet` (landed, SM6.E — plus
  `cancelDonationOnCore_atomic_under_lockSet`)
- `cancellation_cross_core_correct` (landed, SM6.E — remote poke ∧
  home-core deschedule ∧ per-core locality ∧ object-level fidelity)
- 6 per-operation preservation theorems

## Appendix A — Verification commands

```bash
source ~/.elan/env
lake build SeLe4n.Kernel.IPC.CrossCore.EndpointCall SeLe4n.Kernel.IPC.CrossCore.EndpointReply \
           SeLe4n.Kernel.IPC.CrossCore.NotificationSignal SeLe4n.Kernel.IPC.CrossCore.Cancellation
lake exe smp_ipc_suite
lake exe smp_notification_suite
lake exe smp_cancellation_suite
./scripts/test_qemu_smp_ipc.sh
```

---

*SM6 brings IPC to SMP. The 15-conjunct invariant bundle from R4
carries through unchanged structurally; cross-core wake is the
substantive new work.*
