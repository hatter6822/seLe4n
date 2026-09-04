# WS-LC — Lock datatype completion (the two SM2.C residuals)

> **Status**: IN FLIGHT — **LC1 LANDED at v0.34.50** (all eighteen sub-tasks);
> LC2..LC4 not started.
> **Parent overview**: [`SMP_MULTICORE_COMPLETION_PLAN.md`](SMP_MULTICORE_COMPLETION_PLAN.md)
> **Predecessor**: [`SMP_RELEASE_READINESS_PLAN.md`](SMP_RELEASE_READINESS_PLAN.md) RR6 (v0.34.49), which closed SM2.C-defer's refinement work and deliberately did not absorb these two
> **Debt rows closed**: `docs/REGISTERED_DEBT.md` table C — **SM2.C-T** and **SM2.C-C**
> **Target releases**: v0.34.50 → v0.34.53
> **Sub-task count**: 51 across 4 phases (LC1..LC4), each phase numbered in
> the order it is to be implemented

## 1. Phase goal

Two rows of the debt register describe the SM2.C lock model's *datatype* as
incomplete, and both were re-registered rather than closed when WS-RR RR6
landed:

| Row | What is missing |
|---|---|
| **SM2.C-C** | `RwLockOp` has no cancel, so a two-phase-locking growing phase that queued on a contended member cannot withdraw. `releaseAll` is the identity for a non-holder (`rwLock_release_by_nonholder_preserves_waiters`), so the shrinking phase leaves the request behind to be promoted later and strand the lock. |
| **SM2.C-T** | `RwLockExecution` carries no timestamps, so `writerWaitDepth` and every bound built on it counts **lock operations**, not time. A holder may occupy its critical section for an unbounded real interval with no operation recorded. |

This workstream closes both. It is scoped ahead of WS-RR RR7 because RR7.7 and
the fine-lock migration tracks widen `withLockSet` footprints onto more syscall
arms, and the cancel is what makes those footprints *unwindable*.

**Not a live defect today.** `WithLockSet.lean`'s own docstring already states
that the growing phase enqueues under contention and runs the action either way
("it does not by itself establish mutual exclusion"), pins both directions
(`lockSetAcquiredState_grants_when_free` /
`lockSetAcquiredState_does_not_grant_when_contended`), and records that live
exclusion comes from SM5.I's global kernel-entry ticket lock. Nothing that was
covered is being un-covered; a documented model limitation is being closed.

**Concrete deliverables**, in the order the phases deliver them:

1. **LC1** — the abstract withdrawal exists, preserves every INV-R conjunct,
   and the CAS-retry lock's refinement bridge relates it. Lean only; nothing
   live changes.
2. **LC2** — the *deployed* `QueuedRwLock` can withdraw a mid-queue ticket, and
   the ticket-FIFO refinement relates that to the abstract operation.
3. **LC3** — the two consumers: `revalidatedEntry`'s refusal path and
   `withLockSet`'s shrinking phase both perform a full unwind.
4. **LC4** — SM2.C-T: the execution carries a per-step cost, so the CC-5
   contention bound and the release budget have a cycle denomination.

## 2. Scope and sequencing

### 2.1 Phase map

| Phase | Scope | Sub-tasks | Size | Version |
|-------|-------|-----------|------|---------|
| LC1 | The abstract cancel, its invariant preservation, the liveness restatement, and the CAS-retry bridge | 18 | L | v0.34.50 |
| LC2 | The queued lock's withdrawal: tombstoned ledger, skip prefix, Rust protocol, loom/miri, Tier-5 | 13 | L | v0.34.51 |
| LC3 | The two-phase-locking consumers: `cancelAll`, the revalidated refusal unwind, the `withLockSet` unwind | 9 | M | v0.34.52 |
| LC4 | SM2.C-T: the timed execution and the cycle-denominated bounds | 11 | M | v0.34.53 |

### 2.2 Why this order

**LC1 before LC2** is the semantic half of the numbering rule: LC2 makes a
concrete transition reachable, and the abstract operation it refines — with its
invariant preservation — must exist first, or the deployed lock would gain a
withdrawal three sub-tasks ahead of the theorems that cover it.

**LC2 before LC3** for the same reason one level up: LC3's `withLockSet` unwind
is live on the `.tcbSuspend` arm, so the operation it emits must already be
refined by the lock the kernel instantiates.

**LC4 last** because the cancel changes *which* liveness conclusions hold —
"becomes the holder" gains a no-withdrawal premise, "leaves the queue" does not
— and the cycle layer should be built on the final statements rather than
restated after them.

**No phases may overlap.** LC1 and LC4 both edit `Locks/RwLock.lean`; LC2 and
LC3 both edit `Locks/WithLockSet.lean` and the Rust lock bridge. Sequential
execution is the contract.

### 2.3 Three design cruxes, decided up front

**Crux 1 — the queued ledger must tombstone, not shrink (LC2).**
`QueuedTicketWf.ledgerTickets` says the ghost ledger's ticket column is
*exactly* the contiguous `ticketRange nowServing (nextTicket - nowServing)`. A
mid-queue withdrawal that removed the entry would falsify it outright, and with
it `ledger_length`, `ticket_holder_unique`, `await_turn_depth`,
`QueuedTicketWf.preserved` and the FIFO payoff `queuedRwLock_admits_in_spec_order`.
So the element type becomes `Nat × Option CoreId`: the ticket column stays
contiguous and every arithmetic consequence survives verbatim; only the holder
column gains `none`. Rejected: a tail-only cancel (decrement `nextTicket`) keeps
the type but does not serve the two-phase-locking case, where the refused member
is generally mid-queue; weakening `ledgerTickets` to Nodup-and-bounded loses the
arithmetic that proves `await_turn` terminates.

**Crux 2 — the Rust cancel is a store-then-load race (LC2).** `take_ticket` is
an unconditional `fetch_add` and `now_serving` advances exactly once per issued
ticket, by whoever that ticket admits; a core that never reaches a `pass_turn`
stalls the lock permanently, and a `pass_turn` off the head would admit two
cores at once. The resolution is a per-core withdrawal slot plus a bounded skip
loop: publish the withdrawal, **then** check whether we are the head, and let a
compare-and-swap arbitrate between the canceller and the previous holder's skip
loop so exactly one of them clears a given slot and advances. Ordering is what
makes this correct, which is why loom coverage is a deliverable and not a
nicety.

**Crux 3 — reuse the repository's existing cost vocabulary (LC4).** There is no
notion of time anywhere under `SeLe4n/Kernel/Concurrency/`, but three
conventions already exist: `FineLockFlow.elapsedBetween` with its ceiling
hypothesis, `PerCoreWcrt.lean`'s per-critical-section cycle cost, and
`Architecture/TimerModel.lean`'s counter-to-tick conversion. The execution gains
a `stepCost` field with **no default**, so every construction site declares its
cost model explicitly; `FairTrace` and `MAX_RELEASE_DELAY` keep their step
denomination, so the decidable fairness fixtures are untouched and the tick
layer is derived on top rather than substituted for them.

## 3. LC1 — the abstract cancel and its CAS-retry bridge

**Acceptance**: `RwLockOp` has five constructors; every `cases op` in
`Locks/RwLock.lean` is exhaustive with no catch-all arm reached by the new one;
every INV-R conjunct is preserved; the "becomes the holder" liveness family
carries an explicit no-withdrawal window premise and the "leaves the queue"
family does not; the CAS-retry bridge relates the new operation; and the queued
bridge's cancel-free restriction is a proved theorem rather than an omission.

| ID | Sub-task | Consumes | Evidence |
|----|----------|----------|----------|
| LC1.1 | `RwLockOp.cancel (core : CoreId)`, an exhaustive `RwLockOp.isCancel`, and the three prose sites that assert "four operations" | — | `RwLockOp.isCancel_cancel` |
| LC1.2 | `applyOp`'s fifth arm — filter `c` out of `waiters`, write nothing else — with the three frame facts by `rfl`, the sublist lemma, and the two membership lemmas | LC1.1 | `RwLockState.applyOp_cancel_readers` / `_writerHeld` / `_waiters`, `applyOp_cancel_waiters_sublist` |
| LC1.3 | INV-R1..R5 preservation, `rwLock_wf_invariant` widened to the full conjunct tuple, and `RwLockState.applyOp_preserves_wf`'s new arm | LC1.2 | `rwLock_cancel_preserves_wf` |
| LC1.4 | `RwLockKernelStep.cancel` and its arms in `stateAt_reachable` and `RwLockReachable_implies_wf`, so a withdrawing trace is reachable and therefore well-formed | LC1.3 | `RwLockExecution.stateAt_reachable` |
| LC1.5 | `coreOfOp` and `modeOfOp` rewritten exhaustively — the latter had a `| _ => .read` catch-all that would have silently mis-classified a withdrawing writer | LC1.1 | the two definitions elaborate with no wildcard arm |
| LC1.6 | The window predicate `RwLockExecution.noCancelIn`, its narrowing and empty-window lemmas, and the decidable whole-trace form `cancelFree` a fixture can discharge | LC1.1 | `noCancelIn.mono`, `noCancelIn_self`, `cancelFree.noCancelIn` |
| LC1.7 | `leave_waiters_implies_holder`'s **conclusion** widened with a withdrawal disjunct, rather than its hypotheses narrowed — the honest shape, since leaving the queue by withdrawing is a real outcome | LC1.2 | the theorem's third disjunct |
| LC1.8 | `promote_prefix_inclusion` gated on `isCancel = false`, plus the two helpers that let a caller *derive* that gate from an admission instead of assuming it | LC1.6 | `holderAt_succ_iff_of_cancel`, `not_cancel_of_becomes_holder` |
| LC1.9 | The `List.idxOf` helpers — stated over `[BEq α] [LawfulBEq α]` rather than `[DecidableEq α]`, because `idxOf` is indexed by the `BEq` instance and a derived one does not unify — and `applyOp_preserves_waiter_order`'s cancel arm | LC1.2 | `idxOf_filter_le`, `idxOf_filter_lt` |
| LC1.10 | The largest repair: `rwLock_fifo_admission_temporal`'s cancel case, taken first so the design is validated while little is spent | LC1.8, LC1.9 | the theorem elaborates |
| LC1.11 | The writer liveness chain threaded with the window premise: persistence across a window, one-step progress, the liveness theorem, and both admission-step bounds | LC1.10 | `rwLock_writer_liveness`, `rwLock_writer_admissionStepAfter_bounded` |
| LC1.12 | The mode-generic chain threaded the same way, so the reader instance moves with the writer one rather than drifting | LC1.11 | `rwLock_queued_liveness`, `rwLock_reader_liveness`, `rwLock_queued_admissionStepAfter_bounded` |
| LC1.13 | The wait-depth family re-audited: the persistence disjunctions gain a withdrawal alternative, and the depth inequalities are confirmed to run in the safe direction — a withdrawal ahead of you only *decreases* your depth | LC1.12 | `queued_writer_persists_or_admitted`, `queued_persists_or_admitted_at_mode` |
| LC1.14 | The payoff theorems a two-phase-locking unwind cites: the request is gone, nobody else's is disturbed, the order is preserved, nobody is admitted, nobody waits longer, and a withdrawal is not an effective release | LC1.13 | `rwLock_cancel_removes_request`, `rwLock_cancel_admits_no_one`, `rwLock_cancel_not_effective_release` |
| LC1.15 | The CAS-retry bridge: a withdrawal performs no atomic access on a queueless lock, stated explicitly rather than absorbed by the polymorphic no-op constructor, plus the two derived-lemma arms it forces | LC1.14 | `opCorresponds.cancel_no_queue`, `honestBlock.cancel_no_queue` |
| LC1.16 | The queued bridge's restriction made explicit and self-invalidating: every trace the ticket-FIFO block relation covers is proved cancel-free, so the omission is a theorem that *breaks* when the withdrawal block is added | LC1.15 | `ListQueuedBlocks_cancel_free` |
| LC1.17 | The CC-5 contention chain threaded through `InformationFlow/FineLockFlow.lean`: the delay bound, its wall-clock composition, both mode instances, the alphabet bound, the inventory tie-in, the run predicate, and both typed evidence arms | LC1.12 | `lockContention_delay_bounded`, `lockContentionRun` |
| LC1.18 | Anchors, suites, the lock inventory and its four count sites, the phase-theorem manifest, the documentation sync, and the version cut | LC1.17 | Tier 0-3 green; `check_lock_ffi_symmetry.sh` |

## 4. LC2 — the deployed cancel

**Acceptance**: `QueuedRwLock::cancel` withdraws a **mid-queue** ticket without
stalling the lock or admitting two cores; the ticket-FIFO refinement relates it
to `RwLockOp.cancel`; loom is decisive against two relation-breaking mutations;
and the Tier-5 oracle exercises the new letter in both languages.

| ID | Sub-task | Consumes | Evidence |
|----|----------|----------|----------|
| LC2.1 | The tombstoned ledger: `Nat × Option CoreId`, the live-entry projection, and the well-formedness conjunct that every withdrawn ticket was issued | — | `QueuedTicketWf` elaborates with the contiguity conjunct unchanged |
| LC2.2 | The withdrawal instruction in the concrete operation type, its `applyOp` arm, and the `QueuedTicketWf.preserved` case | LC2.1 | `QueuedTicketWf.preserved` |
| LC2.3 | The simulation relation's holder-column conjunct restated over live entries, and the three consequences that read it | LC2.2 | `queuedSim_waiter_ticket`, `queuedSim_outstanding` |
| LC2.4 | Generalise the stutter prefix to a **skip** prefix, so a turn-pass may step past a withdrawn head — the piece that made this phase separable from the abstract one | LC2.3 | `queued_await_turn_terminates` survives |
| LC2.5 | The withdrawal block in the queued block relation and its preservation arm; the cancel-free restriction theorem is deleted in the same commit that makes it false | LC2.4 | the block relation elaborates; the restriction theorem is gone |
| LC2.6 | The two capstones restated over live entries — a sharper claim than the old one, since admission order is still ticket order | LC2.5 | `queuedRwLock_refines_rwLockSpec`, `queuedRwLock_admits_in_spec_order` |
| LC2.7 | The Rust protocol: the per-core withdrawal slot array, `cancel()` with publish-then-check, and the bounded skip loop in `pass_turn` with compare-and-swap arbitration | LC2.6 | `cargo test`; the build script's protocol needles still hold |
| LC2.8 | Loom models: mutual exclusion under a mid-queue withdrawal, the ticket interval closing when a withdrawn ticket is skipped, a withdrawal racing a turn-pass from both sides, and a withdrawal of an already-served ticket | LC2.7 | `scripts/test_loom_queued_rw_lock.sh` |
| LC2.9 | Gate decisiveness by **relation-breaking** mutation, per the project's own rule: keep the withdrawal call and move its publish *after* the head check; keep the skip loop and delete only the arbitration. Each must fail a model | LC2.8 | both mutations red |
| LC2.10 | Unit tests and miri under strict provenance, at the iteration counts the existing harness scales | LC2.9 | `scripts/test_miri_queued_rw_lock.sh` |
| LC2.11 | Tier-5: widen both oracles' alphabet in the same commit, and **re-derive** the ticket-interval check rather than patching its constant — with tombstones the outstanding count is no longer a function of the writer bit | LC2.10 | `scripts/test_tier5_cross_language.sh` |
| LC2.12 | Expose the withdrawal across the foreign-function bridge, since the unwind's caller is on the Lean side and a Lean-only operation would be unreachable from the runtime | LC2.11 | `check_lock_ffi_symmetry.sh` |
| LC2.13 | Anchors, inventory, documentation sync, and the version cut | LC2.12 | Tier 0-3 green; cross build green |

## 5. LC3 — the two-phase-locking consumers

**Acceptance**: a refused revalidated entry withdraws every request its growing
phase queued, `withLockSet`'s shrinking phase is release-or-withdraw on every
member, the strict two-phase-locking and serializability results are re-proved
over the new fold, and the golden trace is byte-identical.

| ID | Sub-task | Consumes | Evidence |
|----|----------|----------|----------|
| LC3.1 | `AccessMode.toCancelOp` beside its acquire and release siblings, and the `cancelAll` fold over a reversed acquisition sequence | — | the two definitions and their unfold lemmas |
| LC3.2 | The revalidated entry's refusal path becomes a full unwind; the "what released does and does not mean" caveat is deleted and replaced by the theorem that makes it true | LC3.1 | the refusal releases *and* withdraws |
| LC3.3 | The typed evidence arm for the refusal claim re-proved over the new outcome, and the non-holder release theorem's docstring corrected — the theorem stays, its statement about the tree changes | LC3.2 | `fineLockClaimEvidence` elaborates |
| LC3.4 | `withLockSet`'s shrinking phase becomes release-or-withdraw on each member, keeping the bracket projection-invisible | LC3.3 | `withLockSet_unfold` |
| LC3.5 | The strict two-phase-locking results re-proved over the new fold | LC3.4 | `strictly_2pl_preserved` |
| LC3.6 | The serializability results re-proved over the new fold | LC3.5 | the conflict-serializability capstones |
| LC3.7 | The dynamic chain extension swept the same way, since it uses the same folds | LC3.6 | `withDynamicChainExtension` elaborates |
| LC3.8 | Suites and the golden trace: the bracket is invisible to the projection, so the fixture must be **byte-identical**, not regenerated | LC3.7 | `tests/fixtures/main_trace_smoke.expected` unchanged |
| LC3.9 | Anchors, inventory, documentation sync, and the version cut | LC3.8 | Tier 0-3 green |

## 6. LC4 — SM2.C-T, the timed execution

**Acceptance**: `RwLockExecution` carries a per-step cost with no default; the
CC-5 contention bound has a cycle-denominated form that instantiates to the
existing step bound at unit cost; the release budget has a stated conversion to
hardware ticks; and no docstring in the tree still says the bound is available
only per lock operation.

| ID | Sub-task | Consumes | Evidence |
|----|----------|----------|----------|
| LC4.1 | The `stepCost` field with no default, every construction site declaring its cost model, and an early check that the decidable fairness fixtures still reduce with a function field present | — | one fixture verified before the rest are touched |
| LC4.2 | Elapsed time across a step interval and the bounded-critical-section predicate, as Props about the field rather than structure invariants | LC4.1 | the two definitions |
| LC4.3 | The writer's cycle-denominated capstone, derived from the existing step bound | LC4.2 | the capstone instantiates to the step bound at unit cost |
| LC4.4 | The mode-generic twin, which must move with the writer form or the definitional bridge between the two wait depths breaks | LC4.3 | both elaborate |
| LC4.5 | The release budget's unit made explicit, with the counter-to-tick conversions built on the existing timer model so the placeholder gains a real hardware meaning | LC4.4 | the conversion lemmas |
| LC4.6 | The wall-clock contention bound reads the execution's own cost rather than taking one as an argument; the generic form is kept as the general statement, and the debt comment block is replaced by the result | LC4.5 | `lockContention_wallClock_bounded` |
| LC4.7 | The two docstrings that say the figure is per lock operation and not per unit time, corrected — the per-unit-time form now exists | LC4.6 | no such sentence remains |
| LC4.8 | The two typed evidence arms that inline full statements, updated with the theorems | LC4.7 | `fineLockClaimEvidence` elaborates |
| LC4.9 | The lock inventory's unit-bearing description strings and any entries whose denomination changed | LC4.8 | `check_lock_ffi_symmetry.sh` |
| LC4.10 | Closure: both debt rows out of table C, the workstream registry row added, and the status index and standing constraints updated to stop naming the two residuals as open | LC4.9 | `docs/REGISTERED_DEBT.md` |
| LC4.11 | Anchors, documentation sync, the regenerated maps, and the version cut | LC4.10 | Tier 0-3 green |

## 7. Verification

Per phase, in this order:

```bash
source ~/.elan/env && lake build <each edited module>   # mandatory pre-commit
./scripts/test_full.sh                                  # Tier 0-3
./scripts/test_rust.sh                                  # host build/tests/fmt/clippy
./scripts/test_aarch64_cross_build.sh                   # any rust/ change
./scripts/test_tier5_cross_language.sh                  # both oracles
./scripts/test_loom_queued_rw_lock.sh                   # LC2
./scripts/test_miri_queued_rw_lock.sh                   # LC2
bash scripts/check_lock_ffi_symmetry.sh
python3 scripts/check_workstream_plan.py
python3 scripts/generate_smp_theorem_manifest.py --check
git add -A && python3 scripts/check_identifier_naming.py
./scripts/bump_version.sh <x.y.z>                       # + CHANGELOG entry
```

## 8. Risks

| Risk | Mitigation |
|---|---|
| The largest liveness proof cannot absorb the withdrawal case | Attempt it first inside LC1, before the cheaper sites, so the design is revisited while little is spent |
| The Rust withdrawal race is subtle | Loom is written before the implementation is called correct, and its decisiveness is proved by mutation rather than asserted |
| A function field breaks the decidable fixtures on the execution type | LC4.1 verifies this on one fixture before the rest are touched |
| The ticket-interval check is silently weakened rather than re-derived | LC2.11 requires re-derivation from the tombstoned invariant; a patched constant is a review failure |
