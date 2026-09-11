# WS-RM — seL4's `reply_remove` on the reply path

> **Status**: PLANNED — registered at `v0.35.4`.  Opens immediately after that
> cut lands and **before** WS-RR RR8; no sub-task has started.
> **Predecessor finding**: the reply-path residual recorded in
> [`../REGISTERED_DEBT.md`](../REGISTERED_DEBT.md) §A, found while auditing the
> `v0.35.4` reply-stack cut.
> **Sub-task count**: 26 across 6 phases (RM1..RM6), each phase numbered in the
> order it is to be implemented

## 1. Phase goal

`v0.35.4` replaced the single-linked reply stack with seL4's doubly-linked one,
so a frame can be taken out of the *middle* of a stack in `O(1)` by repairing its
two neighbours.  That closed the object-pinning defect on the **cancellation**
path, where `cancelIpcBlocking`'s reply arm runs `detachCancelledCallerFrame`
immediately before `consumeReplyLink`.

The **reply** path did not get the same treatment.  `endpointReplyOnCore` runs
`SystemState.consumeCallerReply` with no detach, and `Reply.consumed` clears both
links on any frame that is not a stack head — so when the answered frame has a
frame above it, the consume falsifies
`donationChainWellFormed.prevLinkReciprocal` at that frame.

This workstream makes the reply path do what seL4's `reply_remove` does and what
the cancellation path already does: take the frame off its stack before the
caller link is consumed.

## 2. The defect

### 2.1 Why the state is reachable

`endpointReplyOnCore`'s own docstring records the authority model: authority to
reply flows from *holding the reply capability*, and a copied or minted reply
capability held by a different server is legitimate delegated authority
(seL4-MCS reply capabilities are delegatable).  On a chain `C1 → C2 → S`:

1. `C1` calls `C2`, pushing `R1` (C1's reply object) as the stack head.
2. `C2` delegates a copy of `R1`'s reply capability to `X`, then calls `S`,
   pushing `R2` above `R1` (`R2.prev = R1`, `R1.next = .frame R2`).
3. `X` replies to `C1` **out of order**.  `R1` is consumed and cleared, while
   `R2.prev` still names it.

### 2.2 What breaks, and what does not

The consequence is **fail-closed**, not a corruption.  When `S` later replies to
`C2`, the pop of the head runs `replyStackOuterCaller?`, whose reciprocity test
finds the stale link and returns `.error .invalidArgument`.  Nothing is written,
and the same test refuses a *re-linked* `R1`, so there is no confused deputy and
no privilege escalation.

The cost is a **wedge**: that reply fails permanently, `C2` stays blocked, and
the scheduling context stays with `S`.  A denial of service against the threads
in one call chain and one reservation, available to a party that already holds
delegated reply authority over that chain.  Severity **Medium**, availability
only.  Before `v0.35.4` the same input produced the object-pinning leak that cut
was opened to fix, so this is the same defect in its remaining shape rather than
a new exposure class.

It is recorded in `Reply.consumed`'s own docstring as a stated precondition.

## 3. Design

### 3.1 Sequence the detach; do not fold it into the consume

`consumeCallerReply_objects_frame` is a **two-key** statement, and the tree's
`consumeCallerReply` surface — 53 theorems, 215 mentions in
`DualQueueMembership.lean` alone — rests on it.  Folding a third write into
`consumeCallerReply` falsifies that statement outright.  Running
`detachReplyFrameAbove` *before* it leaves every one of those theorems untouched,
and is also what seL4 does: `reply_remove` clears the frame above's `replyPrev`
and then calls `reply_unlink`.

### 3.2 The detach is invisible to everything that matters

None of `ipcInvariantFull`'s twenty conjuncts reads `Reply.prev` or `Reply.next`;
the two that read `Reply.caller` (`replyCallerLinkage`,
`pendingReceiveReplyWellFormed`) are untouched by a `prev`-only write at a third
key.  And `detachReplyFrameAbove_preserves_projection` is already
*unconditional*, because `projectKernelObject` erases `prev` — so the
information-flow cost is one rewrite and no new hypothesis.

### 3.3 The blast radius funnels through two theorems

`endpointReplyOnCore_state_eq` is `rcases`d by all eighteen downstream results in
`EndpointReplyInvariant.lean`, and `endpointReplyOnCore_post_agrees` pins the
cross-core post-state to the single-core one at **every** object key
(`OffSchedulerAgrees.objects`).  The second is why the cross-core and single-core
spines cannot move apart, and why RM4 is one cut rather than two.

### 3.4 The head case is a transient the pop discharges

A *head* frame keeps its links when its caller is consumed, deliberately: the pop
that removes it runs in the same transition, right after the reply leg, and
validates the head by that very link (plan §3.3 of WS-OD).  So the reply leg's
chain preservation is stated with the head relaxed, and the **composite**
(`endpointReplyCrossCoreDispatch`) is where the head case is discharged — the
same shape `ipcInvariantFullExceptDonationOwner` has against the bare reply.

### 3.5 What the footprint costs

The detach writes a Reply the reply footprints do not name, so both gain a member
in **write** mode.  `lockSet_replyRecv` goes 16 → 17 members, which moves
`maxLockSetSize` to 17: the RPi5 tick then admits **19 µs** per lock
(`1000 / 51`) and the uniform 60 µs envelope is **3060 µs**.

The cost is **parametric only**, and that is stated rather than left to be
re-derived: the new member is `some` exactly when the answered frame is *not* a
head, and every donation-return member is `some` exactly when it *is*, so the two
are mutually exclusive and no *reachable* footprint grows.
`lockSet_endpointReplyRecvOnCore_size_le_fifteen` is unmoved.

## 4. Sequencing

Phases run in order.  **RM4 is one cut**: `post_agrees` relates the two spines at
every object key, so they cannot change in separate PRs — the numbering rule's
"when splitting is impossible, merge the rows".  RM1–RM3 are inert and each must
leave the whole tree building unchanged, which is their own acceptance test.

No phase may run in parallel with another: RM3 and RM4 both edit the reply
footprints and their consumers.

## 5. Phase map

| Phase | Scope | Sub-tasks |
|-------|-------|-----------|
| RM1 | One removal step, shared by both paths (inert) | 5 |
| RM2 | The chain preservation (inert) | 3 |
| RM3 | The footprint member and the ceiling (declared ahead of the code) | 6 |
| RM4 | The reply path goes live (both spines in one cut) | 5 |
| RM5 | The composite payoff and the dispatchers | 3 |
| RM6 | Witnesses, anchors, documentation, closure | 4 |

## 6. Sub-tasks

Estimates: **S** small (<½ day) · **M** medium (1–2 days) · **L** large (3–5 days)

### RM1 — One removal step, shared by both paths (5 sub-tasks)

Inert: nothing calls the new step, so the whole tree must still build unchanged.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| RM1.1 | Re-home and rename `detachCancelledCallerFrame` as `detachFrameAboveThreadReply`, beside the primitive it wraps.  The old name says *when* it is called; internal-first naming wants *what it does*, and the reply path is about to call it too.  The cancellation arm reads the new name | `SeLe4n/Kernel/IPC/Operations/Endpoint.lean`, `SeLe4n/Kernel/Lifecycle/Suspend.lean` | S |
| RM1.2 | `removeCallerReplyFrame (caller) (rid) : Kernel Unit` — seL4's `reply_remove` non-head branch then `reply_unlink`: the detach folded to identity on error (a non-reciprocating upward link means "nothing above me on my stack", which the chain relation permits by design since it is stated downward), then `SystemState.consumeCallerReply`.  Ships with `removeCallerReplyFrame_eq_consume_of_no_frame_above`, the definitional equality that makes every later repair a case split whose `none` branch is the existing proof verbatim | `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` | M |
| RM1.3 | Its read/write algebra, each entry a composition of `detachReplyFrameAbove`'s existing fifteen lemmas with `consumeCallerReply`'s: `_isOk`, `_objects_frame` (three keys), `_nonTcbNonReply_agree`, `_tcb_forward` / `_tcb_backward`, the `getReply?` readings, `_scheduler_eq`, `_machine_eq`, `_cdt_eq`, `_preserves_objects_invExt`.  No new argument is invented — both halves already carry every lemma this needs | `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` | M |
| RM1.4 | `removeCallerReplyFrame_preserves_projection` and its per-core wrapper: one rewrite over the unconditional `detachReplyFrameAbove_preserves_projection` and the existing consume lemma.  No observability hypothesis is added, because the only field the detach writes is erased by `projectKernelObject_reply_prev_invariant` | `SeLe4n/Kernel/InformationFlow/Invariant/Helpers.lean`, `SeLe4n/Kernel/IPC/CrossCore/EndpointCallNiPerCore.lean` | S |
| RM1.5 | `removeCallerReplyFrame_preserves_ipcInvariantFull` — the existing consume theorem plus a `prev`-only transport at a third key.  Cheap by construction (§3.2): no conjunct reads `prev` or `next`, and the two that read `caller` are untouched | `SeLe4n/Kernel/IPC/Invariant/Structural/DualQueueMembership.lean` | M |

**Acceptance**: `lake build` is byte-for-byte unaffected outside the new
declarations, and `removeCallerReplyFrame_eq_consume_of_no_frame_above` holds by
`rfl`.

### RM2 — The chain preservation (3 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| RM2.1 | `detachReplyFrameAbove_unreferencedAfter` — the reply-path twin of `detachCancelledCallerFrame_unreferenced`: after the detach, no stored Reply's `prev` names the detached frame.  This is the producer for the consume's `hUnreferenced` obligation, and it is why the detach must run **first** rather than alongside | `SeLe4n/Kernel/Lifecycle/Invariant/CancellationReplyShape.lean` | M |
| RM2.2 | `removeCallerReplyFrame_preserves_donationChainWellFormed` under `invExt`, the chain invariant and `hNotHead` only — `hUnreferenced` discharged by RM2.1, exactly as the cancellation path discharges it.  Mirrors `consumeReplyLink_preserves_donationChainWellFormed` clause for clause | same | L |
| RM2.3 | The head case stated rather than hidden: the "except at the consumed head" form, with `Reply.wellFormed` relaxed at that one key (§3.4).  It stands to the reply leg as `ipcInvariantFullExceptDonationOwner` stands to the bare reply.  The composite that discharges it is stated where it binds, in the phase that proves it | same | M |

**Acceptance**: the reply leg's effect on the chain is a stated theorem in both
cases — non-head preserved, head relaxed at one key — with no case left silent.

### RM3 — The footprint member and the ceiling (6 sub-tasks)

Declared ahead of the code, which is the order the numbering rule requires: a
live transition may not write an object its footprint does not name, and
over-declaring is sound.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| RM3.1 | `answeredReplyFrameAbove?` — derived from the same `(st.getTcb? target).bind (·.replyObject)` expression the arm's existing reply member is resolved from, so the footprint and the transition cannot disagree about which frame is answered | `SeLe4n/Kernel/IPC/CrossCore/EndpointReply.lean` | S |
| RM3.2 | `lockSet_endpointReply` gains the member in **write** mode: 9 → 10 parameters, base 3 plus 8 options.  Restate at full arity the size bound, `lockSet_consistent_reply`, the five write-membership lemmas, the `lockSetTransitions_within_bound` conjunct, both atomicity lemmas, `lockSet_endpointReply_donation_extension`, and the resolver `lockSet_endpointReplyOnCore`.  `size_le_8` and `lockSet_consistent_base_plus_eight_opts` already exist | `SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean`, `SeLe4n/Kernel/Concurrency/Locks/Deadlock.lean`, `SeLe4n/Kernel/IPC/CrossCore/EndpointReply.lean` | L |
| RM3.3 | `lockSet_replyRecv` gains it too: 16 → 17 parameters, base 4 plus 13 options.  Restate the four size bounds, the consistency lemma, the twelve write-membership lemmas, the bound conjunct, `KernelOperation.ofReplyRecv`, both atomicity lemmas, `lockSet_replyRecv_no_caps`, `capsCarryingIpcArms_footprints_share_serialization`, and the resolver.  `size_le_13` and `lockSet_consistent_base_plus_thirteen_opts` already exist, so no new combinator is needed | same | L |
| RM3.4 | `maxLockSetSize` 16 → 17 and every figure derived from it (§3.5).  Rewrite the canonical sentence at all five sites `scripts/check_lock_ceiling_figures.py` requires, plus the `PerCoreWcrt.lean` docstrings and `rpi5Tick_refuses_sixty_micro_sections` | `SeLe4n/Kernel/Concurrency/Locks/LockSet.lean`, `SeLe4n/Kernel/Scheduler/Operations/PerCoreWcrt.lean`, `CLAUDE.md`, `AGENTS.md`, `docs/spec/SELE4N_SPEC.md`, `docs/gitbook/12-proof-and-invariant-map.md` | M |
| RM3.5 | `lockSetForSyscall`'s thirteen reply and replyRecv theorems, and the two resolved bounds.  **Add the sharp bound that characterises the cost**: the new member and the donation-return members are mutually exclusive, so no reachable footprint grows and `lockSet_endpointReplyRecvOnCore_size_le_fifteen` is unmoved.  Consumes RM3.3 | `SeLe4n/Kernel/Concurrency/Locks/LockSetForSyscall.lean`, `SeLe4n/Kernel/Concurrency/Locks/ResolvedFootprintBounds.lean` | M |
| RM3.6 | The figure-bearing suites and anchors: `DeadlockFreedomSuite` (about 39 sites, several positional 16-argument applications), `LockSetSuite`, `SmpWcrtSuite` (divisor 48 → 51, envelope 2880 → 3060), `SmpSchedulerSuite`, and the Tier 3 ceiling anchors including the negative that refuses the previous value | `tests/DeadlockFreedomSuite.lean`, `tests/LockSetSuite.lean`, `tests/SmpWcrtSuite.lean`, `tests/SmpSchedulerSuite.lean`, `scripts/test_tier3_invariant_surface.sh` | M |

**Acceptance**: `SeLe4n.Testing.LockFootprintBoundCensus` builds — it refuses a
size bound left at the old arity — and `check_lock_ceiling_figures.py` passes
with no stale figure in any tracked prose.

### RM4 — The reply path goes live (5 sub-tasks)

One cut: `endpointReplyOnCore_post_agrees` relates the cross-core post-state to
the single-core one at every object key, so the two spines cannot move apart.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| RM4.1 | `endpointReplyOnCore`, and the single-core `endpointReply` / `endpointReplyRecv`, all call `removeCallerReplyFrame` | `SeLe4n/Kernel/IPC/CrossCore/EndpointReply.lean`, `SeLe4n/Kernel/IPC/DualQueue/Transport.lean` | M |
| RM4.2 | `endpointReplyOnCore_state_eq` gains its third component, and `post_agrees` is re-proved with the single-core side carrying the same step.  Consumes RM4.1 | `SeLe4n/Kernel/IPC/CrossCore/EndpointReplyInvariant.lean` | L |
| RM4.3 | The seven success reductions and three failure reductions in `EndpointReply.lean`.  Each repair is a case split on `answeredReplyFrameAbove?` whose `none` branch is the existing proof verbatim, by RM1.2 | `SeLe4n/Kernel/IPC/CrossCore/EndpointReply.lean` | M |
| RM4.4 | The eighteen results that `rcases` on `state_eq`, plus the single-core bundle theorems.  Consumes RM4.2 | `SeLe4n/Kernel/IPC/CrossCore/EndpointReplyInvariant.lean`, `SeLe4n/Kernel/IPC/Invariant/Structural/DualQueueMembership.lean`, `SeLe4n/Kernel/IPC/Invariant/PerCoreBundlePreservation.lean` | L |
| RM4.5 | The information-flow surface: the cross-core non-interference proofs, the reply-path NI lemmas, and the single-core projection results.  Each gains one rewrite and no hypothesis, by RM1.4 | `SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean`, `SeLe4n/Kernel/IPC/CrossCore/EndpointReplyNI.lean`, `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean` | L |

**Acceptance**: every reply path takes the answered frame off its stack before
consuming its caller link, and the single-core and cross-core spines still agree
at every object key.

### RM5 — The composite payoff and the dispatchers (3 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| RM5.1 | `endpointReplyCrossCoreDispatch_preserves_donationChainWellFormed` — **the theorem the workstream exists for**.  The reply leg's head transient from RM2.3 is discharged by the donation pop that follows it in the same transition, exactly as `returnDonatedSchedContext` discharges the relaxed donation-owner conjunct today | `SeLe4n/Kernel/IPC/CrossCore/EndpointReplyDispatchInvariant.lean` | L |
| RM5.2 | `replyRecvBody` and the results that consume the reply leg's post-state: the staged dispatch payoff, the dispatch invariant's `hStackValid` hypotheses, and the fault-reply preservation | `SeLe4n/Kernel/API.lean`, `SeLe4n/Kernel/IPC/Invariant/DispatchPayoff.lean`, `SeLe4n/Kernel/IPC/CrossCore/EndpointReplyDispatchInvariant.lean`, `SeLe4n/Kernel/IPC/Invariant/FaultPreservation.lean` | L |
| RM5.3 | The closure statement, **derived rather than listed**: a Tier 1 census over the elaborated environment that collects every transition reaching a write of reply-stack data and requires each to name a preservation theorem, reconciled in both directions against a registry.  This is what makes "every transition preserves the chain" checkable, and what stops a future consume site from silently omitting the detach.  Consumes RM5.1 | `SeLe4n/Testing/` (new census module), `scripts/test_tier1_build.sh` | M |

**Acceptance**: `donationChainWellFormed` is preserved by every kernel
transition, and that claim is machine-checked rather than asserted.

### RM6 — Witnesses, anchors, documentation, closure (4 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| RM6.1 | Runtime witnesses for the defect and its fix: build a depth-2 chain, answer the inner caller out of order through a delegated reply capability, assert the frame above has its `prev` cleared, then assert the in-order reply **succeeds** — the wedge is gone.  A fixture exercising only the in-order path would pass before and after | `tests/SmpIpcSuite.lean` | M |
| RM6.2 | Unit checks that the step is inert on the in-order path (the answered frame is the head, so the detach is the identity) and that it fires exactly once otherwise — both directions, so neither reads as coverage without asserting anything | `tests/SmpCrossCoreReplySuite.lean` | S |
| RM6.3 | Tier 3 anchors: both spines call the composite; a negative refuses a bare `consumeCallerReply` in either; the detach precedes the consume in the composite's own body; and the updated ceiling figures with a negative on the previous value.  Each negative mutation-tested in both directions — silent on a clean tree, firing on a mutation that keeps the token and moves it | `scripts/test_tier3_invariant_surface.sh` | M |
| RM6.4 | Documentation and closure: drop the registered-gap paragraph from `Reply.consumed`; correct `donationChainFrame`'s docstring, which names the reply path as its one exception; update the spec's reply-stack section and GitBook 12; add the claim-evidence rows; close the debt row; update the standing constraints in `CLAUDE.md` and `AGENTS.md`; add the **WS-RM** row to the workstream registry, which `scripts/check_identifier_naming.py` reads for its family grammar; bump the version and add the CHANGELOG entry | `SeLe4n/Model/Object/Reply.lean`, `SeLe4n/Kernel/IPC/Invariant/Defs.lean`, `docs/spec/SELE4N_SPEC.md`, `docs/gitbook/12-proof-and-invariant-map.md`, `docs/CLAIM_EVIDENCE_INDEX.md`, `docs/REGISTERED_DEBT.md`, `CLAUDE.md`, `AGENTS.md`, `CHANGELOG.md` | M |

## 7. What every cut in this workstream must run, in order

```bash
source ~/.elan/env
lake build                                  # production closure
lake build SeLe4n.Platform.Staged           # staged modules CI builds
./scripts/test_smoke.sh --continue          # tiers 0-2 + rust + docs sync
./scripts/test_full.sh --continue           # adds tier 3 invariant surface
```

Per-phase, beyond the tiers:

- **RM1–RM2**: `lake build SeLe4n.Kernel.IPC.Operations.Endpoint` and
  `lake build SeLe4n.Kernel.Lifecycle.Invariant.CancellationReplyShape`.
- **RM3**: `lake build SeLe4n.Testing.LockFootprintBoundCensus`,
  `python3 scripts/check_lock_ceiling_figures.py`, then
  `lake exe deadlock_freedom_suite`, `lake exe lock_set_suite`,
  `lake exe smp_wcrt_suite`, `lake exe smp_scheduler_suite`.
- **RM4–RM5**: `lake exe smp_cross_core_reply_suite`, `lake exe smp_ipc_suite`,
  `lake exe smp_information_flow_suite`, `lake exe fault_handling_suite`.
- **RM6**: `python3 scripts/check_workstream_plan.py`,
  `python3 scripts/check_claim_evidence_citations.py`,
  `./scripts/bump_version.sh <version>`, `./scripts/test_docs_sync.sh`.

## 8. Acceptance gate

Every box is ticked by a machine-checked artefact or an executed run, never by a
document existing.

1. `removeCallerReplyFrame` is the only spelling of "take the frame off its stack
   and consume the caller link" reachable from a reply path, refused otherwise by
   a Tier 3 negative (RM6.3).
2. `removeCallerReplyFrame_preserves_donationChainWellFormed` holds for a
   non-head frame with no side condition beyond `invExt` and the chain invariant
   (RM2.2).
3. `endpointReplyCrossCoreDispatch_preserves_donationChainWellFormed` holds
   unconditionally, head case included (RM5.1).
4. The Tier 1 census reports every reply-stack writer as carrying a preservation
   theorem, reconciled in both directions (RM5.3).
5. An executed run answers a middle caller out of order and then completes the
   in-order reply that used to fail with `.invalidArgument` (RM6.1).
6. No footprint exceeds `maxLockSetSize`, and the sharp resolved bound shows no
   reachable footprint grew (RM3.5).
7. `Reply.consumed`'s docstring no longer states a precondition the tree does not
   meet, and `donationChainFrame`'s no longer names the reply path as its
   exception (RM6.4).

## 9. What this plan deliberately does not do

- **It does not reverse the reply-then-pop ordering.**  Running the pop before
  the reply leg would remove the head transient entirely, but that ordering was
  chosen deliberately (WS-OD plan §3.3) and is why `returnDonatedSchedContext`
  takes its new owner as an argument.  RM2.3 states the transient and RM5.1
  discharges it instead.
- **It does not collapse the two consume spellings.**  `consumeCallerReply` and
  `consumeReplyLink` perform the same two writes in opposite orders through
  different helpers — one question with two answers, and pre-existing.  It is
  registered as a follow-on row rather than absorbed into a 215-mention
  refactor here.
- **It does not refuse the out-of-order reply.**  A fail-closed `.illegalState`
  guard would have been far cheaper, and it was measured and rejected: delegated
  reply capabilities are documented as legitimate, seL4 supports answering a
  non-head frame, and refusing would trade a wedge for a lost capability.
