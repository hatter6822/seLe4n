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

**Status: LANDED (v0.31.65).** Axiom-clean (`propext` / `Classical.choice` /
`Quot.sound` only); Tier 0–3 green; staged (production partition 64 → 69). The
cross-core transition `endpointCallOnCore` and the SM6.A theorems live in
`SeLe4n/Kernel/IPC/CrossCore/EndpointCall.lean` (+ `EndpointCallNI.lean` for
the non-interference slice, `EndpointCallInvariant.lean` for IPC-invariant
preservation, `EndpointCallEntry.lean` for the WithCaps + donation + FFI
driver); the 21-assertion runtime suite is `tests/SmpCrossCoreCallSuite.lean`
(`lake exe smp_cross_core_call_suite`).

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
(`syscallDispatchCrossCoreEntry_sgis_nil_single_core`).  Runtime wiring of
`endpointCallOnCore`'s *receiver wake* into this path (so a remote `.call`
receiver fires its reschedule), and the Rust switchover from the boot-pinned
`syscall_dispatch_inner`, remain gated on the SM5.I per-core dispatch seam (the
executing core threaded into `syscallDispatchFromAbi`) — the SM5.F tracked debt.

| Sub | Description | Landed symbol | Status |
|-----|-------------|---------------|--------|
| SM6.A.1 | Migrate `endpointCall` to acquire lock-set (cross-core) | `endpointCallOnCore`, `removeRunnableOnCore` (+ bootCore bridge), `endpointCallOnCore_{rendezvous,noReceiver}_eq` | ✓ |
| SM6.A.2 | `endpointCall_lockSet_correct` | `endpointCallOnCore_lockSet_correct` | ✓ |
| SM6.A.3 | Cross-core wake via `wakeThread` (Theorem 3.2.1) | `endpointCallOnCore_emits_sgi_if_remote_receiver` (+ `_no_sgi_if_local_receiver`) | ✓ |
| SM6.A.4 | `endpointCall_perCore_blocking` | `endpointCallOnCore_perCore_blocking` | ✓ |
| SM6.A.5 | Donation chain lock-set extension | `lockSet_endpointCall_donation_extension` | ✓ |
| SM6.A.6 | Reply state allocation under lock-set | `endpointCallOnCore_reply_linkage_under_lockSet` (+ `lockSet_endpointCall_caller_tcb_write_mem`: the caller-TCB write lock is a *member* of the footprint) | ✓ |
| SM6.A.7 | `endpointCall_call_path_NI` (cross-core variant) | `endpointCallOnCore_call_path_NI` (+ `{enqueueRunnableOnCore,removeRunnableOnCore,wakeThread}_preserves_projection`) | ✓ |
| SM6.A.8 | `endpointCallWithCaps_lockSet_correct` | `endpointCallWithCaps_lockSet_correct` (+ `lockSet_endpointCallWithCaps`) | ✓ |
| SM6.A.9 | `endpointCall_atomic_under_lockSet` | `endpointCallOnCore_atomic_under_lockSet` (+ `endpointCallOnCore_withLockSet_preserves_objects_invExt`: invariant carried *through* the 2PL fold) | ✓ |
| SM6.A.10 | 8 cross-core call scenarios | `tests/SmpCrossCoreCallSuite.lean` (21 runtime assertions) | ✓ |

> **Model note.** This kernel has no separate Reply *object* (the `.reply`
> lock-kind is N/A — `lockHeld` is `False` for it); the reply linkage is the
> caller's `blockedOnReply endpointId (some receiver)` TCB state, written under
> the caller-TCB **write** lock already in `lockSet_endpointCall`. SM6.A.6 is
> therefore "reply *state* allocation under lock-set" rather than reply-object
> allocation. The SGI theorem (SM6.A.3) is stated at the wake-site state
> (`determineTargetCore st'' receiver`); `cpuAffinity` is unchanged by the
> intervening pop+store, so this coincides with the pre-state target core.

### SM6.B — Notification across cores (3 PRs, 8 sub-tasks)

| Sub | Description | Theorem | Est |
|-----|-------------|---------|-----|
| SM6.B.1 | Migrate `notificationSignal` to lock-set | (refactor) | M |
| SM6.B.2 | `notificationSignal_remote_wake` | Theorem | L |
| SM6.B.3 | Multi-waiter discipline preserved | Theorem | M |
| SM6.B.4 | `notificationWait_atomic_under_lockSet` | Theorem | M |
| SM6.B.5 | `notificationSignal_perCore_consistent` | Theorem | M |
| SM6.B.6 | Binding (notification ↔ TCB) lock-set | Theorem | M |
| SM6.B.7 | `notificationSignal_perCore_NI` | Theorem | M |
| SM6.B.8 | 6 cross-core notification scenarios | Tests | L |

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
