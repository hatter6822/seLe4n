# Proof and Invariant Map

Where the kernel's invariants live, how they compose, and how to find the
theorem that covers a transition you care about.

This chapter is a **map**, not a history. What each version added is in
[`CHANGELOG.md`](https://github.com/hatter6822/seLe4n/blob/main/CHANGELOG.md);
what a claim rests on is in
[`CLAIM_EVIDENCE_INDEX.md`](https://github.com/hatter6822/seLe4n/blob/main/docs/CLAIM_EVIDENCE_INDEX.md);
what new code must assume about the tree today is in `CLAUDE.md`'s *Standing
constraints and registered debt*.

## 1. How invariants are layered

Four layers, each composing the one below:

1. **Component invariants** — one focused safety condition
   (`cdtAcyclicity`, `queueCurrentConsistent`, `badgeWellFormed`).
2. **Subsystem bundles** — the conjunction a subsystem's transitions preserve
   (`capabilityInvariantBundle`, `ipcInvariantFull`).
3. **Cross-subsystem bundles** — properties no single subsystem owns, because
   they relate two (`crossSubsystemInvariant`).
4. **Per-core lifts** — the SMP form of a bundle, quantified over cores
   (`ipcInvariantFull_perCore`, `schedulerInvariantStructural_perCore`).

The layering is what keeps proof scripts reviewable and bounds the blast radius
of a new transition: a transition proves the bundle at its own layer, and the
composition carries it upward.

**Every subsystem follows the Operations / Invariant split**: `Operations.lean`
holds the transitions, `Invariant.lean` holds the proofs. Either may be a
re-export hub over a sibling directory of per-concern submodules.

## 2. Finding a theorem

Naming is systematic, so the name tells you what the statement is:

| Suffix | Statement |
|--------|-----------|
| `<op>_preserves_<inv>` | `<inv>` holds before ⟹ it holds after `<op>` |
| `<op>_establishes_<inv>` | `<inv>` holds after `<op>`, unconditionally |
| `<inv>_perCore` | the per-core lift, quantified over `CoreId` |
| `<op>OnCore` | the per-core form of a transition |
| `<x>_iff` | the two readings of `<x>` are equivalent |
| `<x>_of_<y>` | `<x>` follows from `<y>` |

So `endpointCallCrossCoreDispatch_preserves_ipcInvariantFull` is the cross-core
`.call` dispatch arm preserving the full IPC bundle, and you will find it beside
the transition it is about.

```bash
# what preserves this invariant?
rg "preserves_ipcInvariantFull" SeLe4n/ --type lean -l

# what does this module prove?
rg "^theorem|^lemma" SeLe4n/Kernel/IPC/Invariant/Defs.lean
```

`docs/codebase_map.json` carries the machine-readable declaration inventory —
every module, every `def`/`theorem`/`structure`, and cross-file call
resolution. Regenerate it with
`python3 scripts/generate_codebase_map.py --pretty`.

## 3. The bundles

### 3.1 Scheduler — `SeLe4n/Kernel/Scheduler/Invariant.lean`

```
schedulerInvariantBundle := queueCurrentConsistent ∧ runQueueUnique ∧ currentThreadValid
```

Extended forms add EDF ordering, domain consistency and time-slice positivity
(`schedulerInvariantBundleExtended`, `…Full`). The **structural** family
(`schedulerInvariantStructural`) is the register-bank-independent core: it is
what survives a per-core dispatch that rewrites the shared machine registers,
which is why the SMP proofs compose over it rather than over the full aggregate.

Per-core lifts live in `Scheduler/Invariant/PerCore.lean` and
`PerCoreInvariantSuite.lean`. Liveness — WCRT bounds, non-starvation — is in
`Scheduler/Liveness/` and `Scheduler/Operations/PerCoreWcrt.lean`.

> The liveness capstones are **hypothesis-conditional**: `hBandProgress` is an
> externalized deployment hypothesis, and the trace model is still boot-core
> pinned. Any document citing them must state the hypothesis. Owner: **WS-SL**.

### 3.2 Capability — `SeLe4n/Kernel/Capability/Invariant/`

```
capabilityInvariantBundle :=
  cspaceLookupSound ∧ cspaceSlotCountBounded ∧ cdtCompleteness ∧ cdtAcyclicity
  ∧ cspaceDepthConsistent ∧ objects.invExt ∧ replyCapPointsToValidReply
```

`cdtAcyclicity` and `cdtCompleteness` are the capability derivation tree's
structural guarantees — the two that make revocation terminate and make it
complete. `objects.invExt` is the Robin Hood table's own well-formedness
(§3.6), carried here because capability lookup goes through it.

Two invariants that were once state-level predicates are now **structural**:
`CNode.slots` is a `UniqueSlotMap` and `Notification.waitingThreads` is a
`NoDupList ThreadId`, so uniqueness is a property of the type rather than a
conjunct anything has to re-prove. That is the preferred direction: enforce an
invariant in the representation when you can.

### 3.3 IPC — `SeLe4n/Kernel/IPC/Invariant/`

`ipcInvariantFull` is the kernel's largest bundle — **twenty conjuncts**:

| Group | Conjuncts |
|-------|-----------|
| Notification and message well-formedness | `ipcInvariant`, `allPendingMessagesBounded`, `badgeWellFormed` |
| Queue structure | `dualQueueSystemInvariant`, `endpointQueueNoDup`, `ipcStateQueueMembershipConsistent`, `queueNextBlockingConsistent`, `queueHeadBlockedConsistent`, `endpointQueueTailBlockedConsistent`, `queueNextTargetBlocked` |
| Blocked-thread coherence | `blockedThreadsPendingMessageConsistent`, `blockedThreadTimeoutConsistent`, `blockedOnReplyHasTarget`, `pendingReceiveReplyWellFormed` |
| Reply linkage | `replyCallerLinkage` |
| SchedContext donation | `donationChainAcyclic`, `donationOwnerValid`, `donationOwnerUnique`, `donationBudgetTransfer`, `passiveServerIdle` |

**The bundle is de-threaded end to end.** No theorem in the
`*_preserves_ipcInvariantFull*` / `*_establishes_ipcInvariantFull*` family binds
any conjunct on a **post** state as a hypothesis — a threaded conjunct would
make the theorem assume what it claims to prove.
`scripts/check_ipc_invariant_dethreading.py` (Tier 0) measures this over the
comment-free code view, deriving the conjunct set and each bundle's own
pre-state rather than matching binder names, and reports **zero** conjuncts
bound on a post-state across all **176** statements in the family, with the
conjunct set and the bundle family both derived from the sources.  The figure is
spelled in the form the gate reads, so a cut that grows the family fails until
this sentence is corrected — it said 146 while the tree measured 170, unwatched,
because the claim was phrased in words the gate's locator does not match.

The payoff is at the dispatcher:

| Theorem | Covers | Layer |
|---------|--------|-------|
| `dispatchCapabilityOnly_preserves_ipcInvariantFull` | every capability-gated arm | production, `Kernel/API.lean` |
| `dispatchWithCap_preserves_ipcInvariantFull` | + the IPC fall-through arms | staged, `IPC/Invariant/DispatchPayoff.lean` |
| `dispatchSyscall_preserves_ipcInvariantFull` | + the lookup/taint prologue | staged, same module |
| `dispatchWithCapChecked_…` / `dispatchSyscallChecked_…` | the flow-checked mirror of both | staged, same module |

Each holds under a **pre-state quiescence pack** — every field dischargeable
before the step — with machine-checked inhabitation witnesses, so an
unsatisfiable pack field cannot hide. The state-shaped fields are collected in
`IPC/Invariant/Reachability.lean` (`ipcReachable`, boot-inhabited).

> **A bare reply's post-state does not satisfy `donationOwnerValid`.**
> `endpointReply` wakes the answered caller `.ready` while the recorded server
> still holds the donation; the SchedContext returns at the next stage, because
> the server needs that budget *while* it replies. The honest statement is
> `ipcInvariantFullExceptDonationOwner`, which the donation return upgrades back.
> Do not assume `ipcInvariantFull` of a state between a reply and its donation
> return.

**The donation chain sits beside the bundle, not inside it.** WS-OD OD2
(`v0.34.125`) added `SchedContext.scReply` — the head of a context's MCS reply
stack — and `donationChainWellFormed`
([`Defs.lean`](../../SeLe4n/Kernel/IPC/Invariant/Defs.lean)): the stack is
**doubly linked** (`Reply.prev` down, `Reply.next` up, with the context recorded
on the head frame alone), every `prev` link is answered by the frame it names,
and each context's head walks a **terminating** chain (`donationChainFrom`,
fuel-bounded). It is a conjunct of `ipcReachable`, not of
`ipcInvariantFull`, which keeps its twenty; and it is *preserved* through
`donationChainFrame` rather than assumed. The frame is stated over the two
projections the walk actually reads (`replyStackLinks?`,
`schedContextStackHead?`), so it **is** the read set rather than an
over-approximation of it. The donation **pop** writes all three (WS-OD OD3.1,
`v0.34.126`) and carries its own preservation theorem (OD3.8, `v0.34.132`); the
donation **push** writes the new frame's two links, the old head's upward link
and the context's head (OD4.1, `v0.35.2`; five stores since `v0.35.4`) and
carries `donateSchedContext_preserves_donationChainWellFormed`. The **detach**
(`v0.35.4`) is the third writer: it cuts a frame out of the *middle* of a stack
in `O(1)` by clearing the `prev` of the frame above it, which is what the upward
link exists for and what stops a cancelled middle caller's frame from being left
on a stack with its caller gone — pinning its Reply and its SchedContext against
every retype.
With the push live the predicate is no longer vacuous — a depth-2 Call leaves a
two-frame stack — which is the order this workstream was numbered for: the
invariant and its frames landed at OD2, before the transitions that must
preserve them.

OD3.1–OD3.3 (`v0.34.126`) landed the transition that **reads** it. The donation
return is a four-write reply-stack pop with a fail-closed head validation, and
`returnDonatedSchedContext_eq_legacy_of_none` proves it is the pre-OD3 body at
`newOwner? = none` over a context heading no stack. Three statements moved with
it, because three claims stopped being true: exact Reply preservation became a
Reply **frame**, the binding trichotomy widened at the target, and the two
reusable frames that asserted whole-object Reply identity dropped to the
`caller` projection the conjunct they serve actually reads.

OD4–OD6 (`v0.35.2`) made the chain **live** and closed the workstream.
`applyCallDonation`'s guard reads the caller's *effective* scheduling context, so
a `.donated` caller donates onward and seL4-MCS's passive-server pattern works at
call depth ≥ 2; all six pop sites resolve their new owner from their own
pre-state through `replyStackOuterCaller?`; and the improvement is stated as a
theorem rather than as the absence of a regression —
`passiveServerHoldsDonatedContext_atCallDepthTwo` says a passive server reached
at depth ≥ 2 holds a SchedContext bound to itself. Two refusals keep a reused
Reply from redirecting a donation: `linkReply` will not re-link a Reply that
still names a donated context, and the pop refuses to read past a below-head
frame donating a *different* context. `maxLockSetSize` does not move — the
`.call` footprint already write-locks every object the push writes — so no
published WCRT or covert-channel figure is recomputed.
See [`SELE4N_SPEC.md`](../spec/SELE4N_SPEC.md) §8.12.7 for the canonical text.

**The reply path runs `reply_remove` too** (WS-RM, `v0.35.6`).  `v0.35.4` wired
the detach into the **cancellation** path and left the **reply** path relying on
the answered frame being the head — which every reply of the nested Call pattern
satisfies and a *delegated* reply capability answering out of order does not.
`removeCallerReplyFrame` is the one removal step, called by
`endpointReplyOnCore` and by both single-core spines; `.reply` and `.replyRecv`
declare the frame it writes (`answeredReplyFrameAbove?`, resolved from the same
expression the arm's existing reply member comes from), which takes the declared
lock-set ceiling to **22**; the reply leg's head case is stated as
`donationChainWellFormedExcept` and discharged by the donation pop that follows
it in the same transition
(`endpointReplyCrossCoreDispatch_preserves_donationChainWellFormed`, with the
fault reply and the reply *transfer* composing it); and `.replyRecv`'s pop moved
**between** the legs, which is seL4-MCS's own `doReplyTransfer` → `reply_remove`
→ `receiveIPC` order and which the receive leg's re-link requires, since
`Reply.isFree` reads both stack links.  What keeps the surface closed is derived
rather than listed: `ReplyStackWriteCensus` (Tier 1) collects every definition
that writes reply-stack data from the elaborated environment and requires each to
name a chain result or to be recorded as a half-step of the composite that does —
with the primitive list it starts from held to the code by a second, independent
derivation, since `storeObject` takes a whole object and a record update can
rewrite a stack link without naming any helper.  The cost is stated with the fix:
removing a caller from the *middle* of a chain does not preserve the donation
accounting, so a delegate answering an owner out of order leaves that owner
`.unbound` and the context settles on the intermediate caller — seL4-MCS's own
`reply_remove` answer, pinned by `tests/SmpIpcSuite.lean` §3.20 rather than
described.  See [`SELE4N_SPEC.md`](../spec/SELE4N_SPEC.md) §8.12.8 for the
canonical text.

**A donation moves budget, period and deadline — not priority or domain**
(`v0.35.3`).  Closing WS-OD surfaced an authority crossing in both directions:
`updatePrioritySource` classified `.bound` and `.donated` alike, so
`.tcbSetPriority` on a thread *holding* a donated context wrote the **donor's**
`SchedContext.priority` though the syscall is gated on a TCB-write right over
the server alone; and `schedContextConfigure` propagated into `sc.boundThread`'s
TCB, which after a donation is the *donee*, so a capability on the client's
reservation rewrote the server's own priority **and migrated its scheduling
domain**.  The remedy is seL4-MCS's own split — a donee runs its client's work
on the client's reservation at **its own** priority and in its own partition,
and rises to the client's band only through priority inheritance.  One
classifier decides which SchedContext supplies a thread's thread-owned
parameters — `SchedContextBinding.ownScId?`, the reservation a thread *owns*
(`some` on `.bound`, `none` on `.unbound` and `.donated`), as against `scId?`,
the one it *runs on* — one resolver answers
(`SystemState.threadBasePriority`), and every reader is pinned to it by theorem
— `resolveEffectivePrioDeadline_fst_eq_threadBasePriority`,
`getCurrentPriority_eq_threadBasePriority` (by `rfl`),
`effectiveSchedParams_priority_deadline_eq_resolve`,
`effectiveBucketPriority_eq_resolveEffective` — so the split cannot be unpicked
one site at a time.  Two invariants follow the read: a donee's recorded
run-queue bucket is its own base priority
(`effectiveParamsMatchRunQueue{,OnCore}`), and `boundThreadPriorityConsistent`
ranges over `.bound` alone, where quantified over every binding **the donation
falsified it** whenever the donor's and the donee's base priorities differed —
the reservation's `priority` had to equal one before the hand-off and the other
after, and the hand-off writes neither field.  Budget,
period and deadline stay the reservation's at every depth, and the five budget
predicates keep their merged arm — pinned as such, so the split cannot leak into
the budget question.  `schedContextConfigureBoundPropagate` gates both
propagations on the bound thread **owning** the reservation, through one
predicate both halves consult so they cannot diverge, and `effectiveSchedParams` reports a donee's own
domain, since every live domain filter reads `tcb.domain`.  `maxLockSetSize` is
unmoved at **14**.

### 3.4 Lifecycle — `SeLe4n/Kernel/Lifecycle/Invariant/`

`lifecycleInvariantBundle` covers identity aliasing, stale-reference exclusion
and capability-reference validity across retype, suspend, resume and cleanup.
Retype is the sharp edge: `retypeFromUntyped` must not overlap an existing
region (`untypedRegionsDisjoint`, §3.5) and must not leave a stale reference to
the object it consumed.

### 3.5 Cross-subsystem — `SeLe4n/Kernel/CrossSubsystem.lean`

Twelve predicates that no single subsystem owns, because each relates two:

```
registryEndpointValid ∧ registryInterfaceValid ∧ registryDependencyConsistent
∧ noStaleEndpointQueueReferences ∧ noStaleNotificationWaitReferences
∧ serviceGraphInvariant ∧ schedContextStoreConsistent ∧ schedContextNotDualBound
∧ schedContextRunQueueConsistent ∧ blockingAcyclic ∧ lifecycleObjectTypeLockstep
∧ untypedRegionsDisjoint
```

`blockingAcyclic` is the priority-inheritance blocking graph's acyclicity — the
property that makes PIP propagation terminate. `serviceGraphInvariant` is the
service dependency graph's, for the same reason.

### 3.6 Data structures — `RobinHood/`, `RadixTree/`

The object store is a verified **Robin Hood hash table**. `RHTable.invExt`
bundles well-formedness, distance correctness, key uniqueness and probe-chain
dominance; `allTablesInvExtK` lifts it over every map and set field of
`SystemState`. Lookup soundness, insertion preservation and resize correctness
are proven, so the O(1) claim is a theorem rather than a benchmark.

The CNode radix tree is a verified flat-array structure with the same
treatment.

### 3.7 Architecture — `SeLe4n/Kernel/Architecture/`

ARM64 page tables (`VSpace.lean`, `VSpaceInvariant.lean`) carry W^X exclusion
(`wxExclusiveInvariant`), alignment and permission monotonicity. `Fault.lean`
carries the fault wire format with a round-trip theorem and a
message-register-budget bound. `proofLayerInvariantBundle` composes the
architecture layer with the scheduler bundle for the boot path.

### 3.8 Information flow — `SeLe4n/Kernel/InformationFlow/`

The security layer is its own stack: labels and a lattice (`Policy.lean`),
state projection (`Projection.lean`), non-interference over a 35-constructor
`KernelOperation` surface, taint propagation, declassification with a causal
provenance trail, and the per-core (SMP) lift of all of it.

Accepted covert channels are **enumerated rather than assumed away**:
`acceptedCovertChannel_perCoreCount` pins the count, and each has a named
justification. Lock contention is one of them.
[`INFORMATION_FLOW_ROADMAP.md`](https://github.com/hatter6822/seLe4n/blob/main/docs/INFORMATION_FLOW_ROADMAP.md)
is the canonical text.

### 3.9 Concurrency — `SeLe4n/Kernel/Concurrency/`

The memory model, the verified `TicketLock` and `RwLock` with mutex and
fairness theorems, per-object lock sets, two-phase locking, deadlock-freedom
and serializability.

**Each lock is refined to the Rust the kernel runs, and each bridge derives
its trace correspondence rather than assuming it** (WS-RR RR6, v0.34.50).
Three bridges, one per lock kind:

| Lock | Bridge | Relation | Capstone |
|------|--------|----------|----------|
| `TicketLock` | `Locks/TicketLockRefinement.lean` | `ticketLockSim` | `ticketTrace_preserves_ticketLockSim` |
| CAS-retry `RwLock` | `Locks/RwLockRefinement.lean` | `rwLockSim` (writer bit + reader count) | `rust_rwLock_refines_lean_honest` |
| **deployed** `QueuedRwLock` | `Locks/QueuedRwLockRefinement.lean` | `queuedSim` (adds waiters ↔ ticket interval) | `queuedRwLock_refines_rwLockSpec` |

Two things the table is making precise. The **deployed** reader-writer lock is
the ticket-FIFO `QueuedRwLock` — `STATIC_RW_LOCK_POOL` is `[QueuedRwLock; 4]`,
pinned by `build.rs` — so the lock the kernel runs is the one the Lean FIFO
spec describes, and its refinement was proved *before* the pool was repointed.
And no capstone takes its own conclusion as a hypothesis: the CAS-retry
bridge's `_honest` forms carry no `ListBlockBisim` premise (`honestBlock`, the
load-then-CAS trace-shape predicate, derives it), the ticket bridge's fourth
conjunct is a real "a pure load leaves both states unchanged" statement rather
than a tautology, and `ticketLockSim_not_universal` exhibits a pair the
relation does **not** relate. And no bridge claims a no-op the code does not
perform: the ticket bridge has no block for a re-acquisition by a queued or
holding core or a release by a non-holder (`TicketLockState.callerContract`
states what it covers, `ticketBlock_respects_contract` that every shape is
inside it — PR #890 review round 4, the sweep round 2's CAS-retry fix owed its
sibling), while the deployed `QueuedRwLock` alone turns those spec no-ops into
branches, because the unwind relies on them there.

A queued core may **withdraw** its request. The operation exists at every
level: `RwLockOp.cancel` in the spec (v0.34.51), a tombstoned ledger and
skip-aware promotion in the ticket-FIFO refinement (v0.34.52), and
`QueuedRwLock::cancel` in the deployed lock (v0.34.53). The deployed form
splits the acquisition — `enqueue`, spin on `is_served`, then exactly one of
`complete_read`, `complete_write` or `cancel` — because the fused
`acquire_read` / `acquire_write` never expose an abandonable ticket. The
withdrawal slot is one word per core, so `enqueue` parks until the core's
previous withdrawal has been retired (v0.34.56, the workstream's closure
audit): the first cut let a second ticket be taken over an unclaimed
withdrawal, and a second `cancel` then overwrote it and stalled the lock on a
ticket nobody held — a sequence every documented contract permitted, which the
four withdrawal models missed because each withdrew once per core. The Lean
model enables the issue only for a core holding no ticket and proves the
publish never overwrites (`QueuedTicketWf.publish_slot_empty`). What
withdrawal changes for a reader of these theorems: a conclusion of the form
"`c` *leaves the queue*" is satisfied by a withdrawal and is unchanged, while
one of the form "`c` *becomes the holder*" now carries an explicit
no-withdrawal-in-window premise. Both two-phase-locking consumers emit a
withdrawal since v0.34.54: `withLockSet`'s shrinking phase and the revalidated
entry's refusal path are one definition, `unwindAll`, which withdraws before it
releases — the order is what lets `unwindAll_leaves_no_queued_request` hold with
no distinctness or resolvability condition on the footprint. The bracket stays
invisible to every observer, so the golden trace is byte-identical.

The identity that unwind relies on — a release by a non-holder changes nothing
— is the deployed lock's own since PR #890 review round 2, not only the spec's:
`QueuedRwLock` keeps a held word per core, every entry point — the withdrawal
included, since round 3 — reads the caller's word first, and `queuedSim`'s
fifth conjunct (`queuedHeldSim`) relates the
words to `readers` / `writerHeld`, so the bridge's holder no-op blocks are the
one held-word load, derived from the relation rather than asserted of a stutter
the code never performed. The class behind rounds 2 and 3 — the lock not knowing
the executing core's own situation — is closed at the cause: a third per-core
word, `request`, records the core's one live ticket, every entry point decides
the core's case on its three words before it writes, `queuedSim`'s sixth
conjunct (`queuedRequestsSim`) relates that word to the live ledger, and every
per-core branch hypothesis of `queuedBlock` is now stated on the words the
implementation reads, with the spec's branch derived from the relations inside
`queuedBlock_preserves_queuedSim` — so a queued core's second acquisition is a
derived no-op block too (`acquireRead_queued`), and a relation that pinned a
word to the wrong fact would fail the proof. The CAS-retry bridge makes the
opposite honest choice for the undeployed lock: no no-op block at all, and a
stated caller contract.

Round 5 of the same review found the interval the bridge folds away: after a
writer's release the head waiter is *served* but not yet *completed*, the spec
had promoted it, and the deployed `cancel` there retired the served ticket —
one holder fewer than the spec. The spec was wrong in the same place: its
`cancel` was the neutral filter while the lock's withdrawal of a served head
passes the turn to the readers behind it, so whether a queued reader was a
spec holder depended on how it had been queued. The spec moved: a withdrawal
at the head now promotes the reader run it uncovers
(`RwLockState.cancelPromotes`, `rwLock_cancel_admits_only_the_head_reader_run`),
both bridges fold that promotion, and with it the deployed lock can decide on
its own words which withdrawals the spec has already admitted — a served
writer with no reader, a reader with no live write request ahead of it, found
through a fourth per-core word that records each request's **mode** — and
realises the admission instead (`CancelOutcome::Holding`; the release that
follows every withdrawal releases it). `queuedSim`'s seventh conjunct
(`queuedRequestModesSim`) pins that mode word to the spec's queued mode, the
Tier-5 oracle holds every withdrawal's verdict to the spec's and prints
identities per step, and the loom models tally that both verdicts occur.

And a delay bound now names its denominator. `RwLockExecution` carries a per-step
cost (v0.34.55), so the admission and contention bounds have cycle-denominated
forms alongside the step forms — each conditional on a per-critical-section
ceiling, which is an assumption about a deployment's code rather than something
the kernel derives, and each collapsing back to the step bound at unit cost. The
hardware-tick conversion needs a counter frequency, so it lives with the
platform rather than with the lock.

> Two standing caveats. **Kernel entry is serialised by one global ticket
> lock**, so live WCRT is weaker than the fine-lock bound `PerCoreWcrt.lean`
> proves. And **SM3.C.9's `@[export]` body migration is not finished**: outside
> the syscall seam the bodies are not wrapped in `withLockSet`, so per-object
> fine locks remain a model-level discipline there. Both are registered debt
> with closure targets.
>
> `lockSetForSyscall` answers `some` for eight of the thirty-five syscalls since
> WS-RR RR7.11 — the suspend arm plus the seven IPC hot-path arms — each with its
> coverage proof (`.replyRecv` declares for a **delegated** reply too since WS-OD
> OD3.5: the transition returns the *recorded* server's donation, and that
> server's own TCB lock is now declared unconditionally, so the round-6 refusal
> that answered `none` there is retired), while the remaining twenty-seven answer `none` and their
> callers keep the coarser serialisation. WS-RR RR7.12 makes the **syscall seam
> acquire** those eight: the entry resolves the footprint from its own decode,
> acquires, re-resolves at the state the growing phase ended in, refuses on
> change, and unwinds — with the undeclared arms running bit-identically to
> before. The **per-core scheduler entries** still bracket nothing.
>
> How much of the kernel that is, is measured rather than asserted: WS-RR RR7.13
> derives the state-committing `@[export]` set from the elaborated environment
> and reconciles it against a registry in both directions, so a new seam that
> commits without a bracket fails the build. **Seven seams commit; five bracket**
> (WS-RR RR7.39; two before it).
> The same cut moved `maxLockSetSize` from 8 to 9: a `.replyRecv` that both
> returns a donation and installs capabilities is nine locks, the ninth being
> the state-level lock the install's derivation-tree write needs. **WS-OD OD3.5
> (`v0.34.128`) moved it again, 9 to 11**, on the same footprint: that arm
> performs *two* SchedContext hand-offs and declared one, and the eleventh
> member is the recorded server's own TCB, which is what lets a reply answered
> through a delegated capability declare a footprint at all. **WS-OD OD3.7
> (`v0.34.130`) moved it again, 11 to 13**, on the same footprint once more and
> for the first time on objects the transition *reads*: the donation return walks
> one link past the reply-stack head and then validates that frame's caller's TCB
> before binding a context to it. **WS-OD OD3.13 (`v0.34.137`) moved it a fourth
> time, 13 to 14**, for the queue-structure TCB the receive leg relinks — the
> last of the four arms that were writing one without naming it. The constant is
> the WCRT headline's first factor, so the per-lock critical section the RPi5's
> 1 ms tick admits falls 37 µs → 30 µs → 25 µs → **23 µs** across the four cuts,
> and the 60 µs envelope rises to 2520 µs. Every one of those figures is derived
> from the constant by theorem, so read it off `admissibleCriticalSection`
> rather than off this sentence. **WS-OD OD3.14 (`v0.34.141`) moved it not at
> all**, deliberately: the priority-inheritance chain a receive rendezvous must
> now walk is state-discovered and unbounded, so its locks are declared through
> the `pipChainStart_<τ>` markers the SM3.C walker consumes rather than through
> `lockSet_<τ>` — which is what keeps the static footprint an honest declaration
> of the *static* locks. **PR #894's review (`v0.35.5`) moved it 16 → 21**, on
> that same arm a fifth time: `.replyRecv`'s receive leg *is* `.receive`'s
> transition, so with no queued sender it runs the pre-receive donation return on
> the **invoking** thread — and the arm's own return runs after the receive leg,
> so the invoker still carries the `.donated` binding it entered with. On a
> non-delegated reply the recorded server *is* the invoker, which is the
> coincidence delegation breaks; two threads cannot share a scheduling context,
> so a delegated `.replyRecv` wrote four kernel objects under no declared lock.
> **No reachable state takes up the whole ceiling**:
> `lockSet_endpointReplyRecvOnCore_size_le_eighteen` bounds every state at
> eighteen with no hypothesis, because the re-donation members and the
> pre-receive return are mutually exclusive on the send queue.
>
> At HEAD, the declared lock-set ceiling is **22**, the RPi5 tick admits **15 µs** per lock, and the uniform 60 µs envelope is **3960 µs** —
> the canonical spelling `scripts/check_lock_ceiling_figures.py` (Tier 0, WS-OD
> OD3.15) holds to the Lean sources, so this chapter cannot go stale behind the
> constant the way it did between OD3.7 and OD3.14. See
> [`docs/spec/SELE4N_SPEC.md`](../spec/SELE4N_SPEC.md) §SM3.C.9 for the
> canonical statement.

> **A blocking arm returns no frame** (WS-RR RR7.17, `v0.34.68`). Which
> syscalls return a value is decided from the caller's **post-state**, never
> from its number — a `.send` that finds a waiting receiver returns, one that
> parks does not. `blockingArm_returns_no_frame` and its family state that both
> ways, state that the staged registers are not consulted on the blocking arm
> (so a blocked caller's own argument spill cannot reach the boundary as a
> return value), and compose onto the exported seam, where the trap layer reads
> the outcome tag. The Rust `ReturnShape` mirror lost its wildcard and gained a
> cross-check: both sides render the same `id → shape` table against one
> fixture, so two total functions cannot disagree silently.

> **The answer a forcibly unblocked thread gets** (WS-RR RR7.14, `v0.34.67`).
> A thread taken out of a blocking IPC has no value to receive, and until this
> cut both unblocking paths staged nothing — so the SM10.1 context restore
> would have delivered the thread's own argument spill back as a return value.
> `timeoutThread` now stages `Architecture.timeoutFrame` (`.ipcTimeout`) and
> `cancelIpcBlocking`'s four blocked arms stage
> `Architecture.cancelledIpcFrame` (`.ipcCancelled`, a new `KernelError` at
> discriminant 57): a caller may reissue a timed-out request, but a cancelled
> one may name an endpoint that is gone, so conflating them would make a
> correct userspace retry impossible. Two paths stage nothing on purpose and
> are pinned as negatives — the `.ready` arm, and `restoreToReady`, the
> *resume* spelling of the same field clear, since `.tcbResume` restarts a
> thread where it was. **Delivery is still owed to WS-BP BP7**: a staged frame
> reaches no hardware register while `contextRestoreSeamLive` is `false`.

## 4. Per-core (SMP) lifts

Every bundle above has a per-core form that quantifies over `CoreId` and reads
`currentOnCore c` / `runQueueOnCore c` instead of the boot core's slots. The
lift is not mechanical: a per-core statement is strictly stronger, and several
lifts required new frame lemmas showing a transition on core `c` leaves core
`c'`'s view alone.

Per-phase theorem inventories are registered in
`SeLe4n/Kernel/Concurrency/PhaseTheoremManifest.lean`, one entry per phase
SM0..SM10.

> **The SMP theorem total is measured, not summed.** The inventories hold 1119
> entries, of which **909 are theorems** — the rest are `def`s (lock-set
> footprints, per-core predicates, WCRT cost functions). Quote 909, and quote
> it as theorems. A propositionality census resolves each identifier against the
> environment and fails elaboration on drift; adding a phase without an entry
> fails elaboration, and adding an inventory no phase claims fails Tier 0.
>
> Eight of the eleven phases register **zero** theorems — six have no inventory
> and two carry assumption ledgers the count correctly excludes. That gap is
> real, and the honest zero is what makes it visible.

## 5. What the invariants are checked by

| Layer | Mechanism |
|-------|-----------|
| The proofs themselves | Lean's type checker — no `sorry`, no `axiom` |
| Named surface still exists | Tier 3 `test_tier3_invariant_surface.sh` anchors |
| Bundles are not self-assuming | `check_ipc_invariant_dethreading.py` (Tier 0) |
| No axiom crept in | `check_module_axioms.py`, environment-driven (one shared dependency walk, cross-checked against `Lean.collectAxioms`) |
| Proofs are not vacuous one-liners | `check_proof_depth.py` |
| Production does not import staged | `check_production_staging_partition.sh` |
| Runtime behaviour matches the model | Tier 2 trace + determinism + negative-state suites |

Tier 3 anchors read the **comment-free code view**, so a symbol surviving only
in a docstring cannot satisfy one.

## 6. Reading further

| For | Read |
|-----|------|
| The specification these invariants formalize | [`SELE4N_SPEC.md`](https://github.com/hatter6822/seLe4n/blob/main/docs/spec/SELE4N_SPEC.md) |
| What seL4 does, for comparison | [`SEL4_SPEC.md`](https://github.com/hatter6822/seLe4n/blob/main/docs/spec/SEL4_SPEC.md) |
| Every claim and its evidence | [`CLAIM_EVIDENCE_INDEX.md`](https://github.com/hatter6822/seLe4n/blob/main/docs/CLAIM_EVIDENCE_INDEX.md) |
| The security model and its boundaries | [`THREAT_MODEL.md`](https://github.com/hatter6822/seLe4n/blob/main/docs/THREAT_MODEL.md) |
| How to build and run any of this | [`DEVELOPMENT.md`](https://github.com/hatter6822/seLe4n/blob/main/docs/DEVELOPMENT.md) |
