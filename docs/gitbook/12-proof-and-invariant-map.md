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
pre-state rather than matching binder names, and reports zero across all 146
statements.

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
its trace correspondence rather than assuming it** (WS-RR RR6, v0.34.49).
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
relation does **not** relate.

> Two standing caveats. **Kernel entry is serialised by one global ticket
> lock**, so live WCRT is weaker than the fine-lock bound `PerCoreWcrt.lean`
> proves. And **SM3.C.9 is deferred**: the `@[export]` bodies are, with one
> exception, not yet wrapped in `withLockSet`, so per-object fine locks remain a
> model-level discipline. Both are registered debt with closure targets.

## 4. Per-core (SMP) lifts

Every bundle above has a per-core form that quantifies over `CoreId` and reads
`currentOnCore c` / `runQueueOnCore c` instead of the boot core's slots. The
lift is not mechanical: a per-core statement is strictly stronger, and several
lifts required new frame lemmas showing a transition on core `c` leaves core
`c'`'s view alone.

Per-phase theorem inventories are registered in
`SeLe4n/Kernel/Concurrency/PhaseTheoremManifest.lean`, one entry per phase
SM0..SM10.

> **The SMP theorem total is measured, not summed.** The inventories hold 1116
> entries, of which **906 are theorems** — the rest are `def`s (lock-set
> footprints, per-core predicates, WCRT cost functions). Quote 906, and quote
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
