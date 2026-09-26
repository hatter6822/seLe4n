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

Since `v0.35.190` (WS-RR RR8.16) a thread can actually *reach* that machinery:
`seL4_CNode_Revoke` has a dispatch arm (`SyscallId.cspaceRevoke`), which routes
`cspaceRevokeCdt` — the variant that walks the derivation tree across arbitrary
CSpaces, not the local `cspaceRevoke` that reaches only the invoked CNode.
Before it, the whole family was verified and unreachable.  Since `v0.36.1` the
walk is also all the revocation does: the shared scaffold no longer opens with
the local same-target sweep, which had destroyed capabilities the source never
derived, so a revocation destroys exactly the source's CDT descendants — seL4's
`cteRevoke` — as the canonical spec's §8.11.1 records.  The arm carries the
capability-only dispatch payoff (`cspaceRevokeCdt_preserves_ipcInvariantFull`),
whose scaffold and fold arguments are stated **predicate-free** beside their
definitions (`revokeCdtScaffold_ok_decompose`, `revokeCdtFold_induct`) so this
bundle's argument and `ipcInvariantFull`'s are one induction rather than two.
See `SELE4N_SPEC.md` §8.11.1 for the ABI, the authority and the two boundary
statements the arm needed (no static lock footprint; a content-tracked field
written with no tracked content moved).

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
bound on a post-state across all **199** statements in the family, with the
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
carries `donateSchedContext_preserves_donationChainWellFormed`. The **splice**
(`v0.35.4`, a sever until WS-HP HP6.3) is the third writer: it takes a frame out
of the *middle* of a stack in `O(1)` by reconnecting the frames either side of it
(clearing the frame above's `prev` at a bottom frame, where nothing lies below),
which is what the upward link exists for and what stops a cancelled middle
caller's frame from being left on a stack with its caller gone — pinning its Reply
and its SchedContext against every retype.
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
the removal into the **cancellation** path and left the **reply** path relying on
the answered frame being the head — which every reply of the nested Call pattern
satisfies and a *delegated* reply capability answering out of order does not.
`removeCallerReplyFrame` is the one removal step, called by
`endpointReplyOnCore` and by both single-core spines; `.reply` and `.replyRecv`
declare the frame it writes (`answeredReplyFrameAbove?`, resolved from the same
expression the arm's existing reply member comes from), which takes the declared
lock-set ceiling to **22** -- with that member proved a declared *write* rather
than merely declared (`lockSet_endpointReplyOnCore_covers_splicedFrameAbove` and
its `.replyRecv` twin, the reply-path siblings of the cancellation path's own);
the reply leg's head case is stated as `donationChainWellFormedExcept` and
discharged by the donation pop that follows it in the same transition
(`endpointReplyCrossCoreDispatch_preserves_donationChainWellFormed`, with the
fault reply and the reply *transfer* composing it, under one pre-state local
coherence fact -- `answeredHeadContextIsServerDonation` until WS-HP HP4
(`v0.35.38`) made the pop read the very frame the relaxation sits at, which
retires it for the strictly weaker `replyFrameHeadIsBound` and which HP7
(`v0.35.46`) followed by **deleting** that predicate and the two other stated
coherence facts outright, their content having become theorems of the trigger, on
the frozen mirror
as well as on the live spines -- `frozenEndpointReplyWithDonationReturn` reads
`frozenReplyFrameHeadHolder?` and the binding-driven frozen resolver is deleted,
because the coverage table's `frozenBranchOperationChecked` claims the two are run
beside each other and two readings of one question is what that claim forbids --
and since HP8 (`v0.35.47`) that mirror's *removal* splices too, with the sever's
`frozenDetach…` names deleted and `FO-043`, a three-frame stack whose middle frame
the reply answers, as the witness: every shallower scenario agrees under both
policies, so the suite was green before the flip);
and `.replyRecv`'s pop moved
**between** the legs, which is seL4-MCS's own `doReplyTransfer` → `reply_remove`
→ `receiveIPC` order and which the receive leg's re-link requires, since
`Reply.isFree` reads both stack links.  What keeps the surface closed is derived
rather than listed: `ReplyStackWriteCensus` (Tier 1) collects every definition
that writes reply-stack data from the elaborated environment and requires each to
name a chain result, or to be recorded as a half-step of the composite that does,
or — on the frozen execution surface, which has no chain predicate of its own —
as mirroring a live site that states one — with the primitive list it starts from
held to the code by a second, independent derivation, since `storeObject` takes a
whole object and a record update can rewrite a stack link without naming any
helper.  The frozen surface joined at `v0.35.12`: it was then reached by neither
library root, so the closure held everywhere except one module that writes the
live `Reply` record, and the frozen reply was clearing a caller's Reply bare —
this workstream's own defect, on the surface nothing was looking at.  The cost was
stated with the fix: removing a caller from the *middle* of a chain did not preserve
the donation accounting, so a delegate answering an owner out of order left that
owner `.unbound` and the context settled on the intermediate caller.  That was
**seL4-MCS's cost too, not a divergence from it** — re-verified at `v0.35.40`
against upstream source at master, 13.0.0, 12.1.0, 12.0.0 and 11.0.0, where
`reply_remove`'s non-head branch writes zero into the frame above under the comment
*"not the head, remove from middle - break the chain"*; `v0.35.14` claimed the
reverse and cited a line that is in no release, so the chain-preserving removal is
an **improvement on** upstream rather than parity with it — and it is pinned by
`tests/SmpIpcSuite.lean` **§3.22**, the depth-three witness: §3.20's depth-two one
structurally cannot show it, because a two-frame stack's lower frame is its bottom
and both policies then write the same value there.

**WS-HP recovered it at depth ≥ 3, and `v0.35.45` is where it landed.**  HP4
(`v0.35.38`) moved the pop's trigger to the answered frame's head-ness on both the
live and the frozen reply surfaces, and HP5 (`v0.35.39`) did the same for the
**cancellation** reclaim — forced rather than symmetric, because after the splice a
frame becomes the head whose recorded reply target is gone, and a binding-driven
reclaim declines there and leaves a `.donated` binding naming a `.ready` owner.  HP5
retired WS-RR RR7.22's `donationHolderIsReplyTarget` for the head-keyed
`donatedContextIsOwnerFrameHead`, turned two footprint docstring claims into
theorems the binding reading could not have stated (the head the pop clears **is**
the victim's own reply object; a reclaim excludes both removal members), and gave
the reclaim its **first** runtime witness — before it, every `.blockedOnReply`
fixture in the tree held a Reply whose `next` was unset, so the arm declined under
both readings.

**HP6 then turned the sever into the splice** (`cancelledMiddleCallerPolicy =
.spliceOutTheCut`): the frame above a cut takes the cut frame's own downward link,
the frame below links back up at it, and the cut frame's own `prev` is cleared —
seL4's `reply_unlink` downward half, and what makes `donationChainWellFormed`
survive the removal outright rather than transiently.
`donationAccountingPreserved_atCallDepthThree` is the payoff: at depth ≥ 3 the
reservation leaves the cut **owed outward** and the pop that answers the bottom
frame delivers it home.  §3.22 inverted from a COST witness to a PAYOFF witness in
the same cut and now measures that second pop.  The below side **degenerates** to
the sever rather than refusing, so the removal's refusal set is exactly the
pre-WS-HP one, a stale upward link is still reachable, and the reciprocity checks
stay load-bearing.  **Depth 2 was not closed by the splice** — both policies write
`none` into the frame above a bottom frame — and that §3.20's depth-two halves and
the golden trace passed byte-identically across the flip is the measurement that
that change was confined to depth ≥ 3.  Closing depth 2 needed the reservation's
*origin* on the `SchedContext` rather than stack reachability, which is HP10 and
which landed at `v0.35.53` (below).

**HP9 (`v0.35.48`) showed the splice COMPOSES**, which depth 3 cannot.  The splice
writes the frame below's `next` and leaves its own `prev` untouched, so on a
three-frame stack “the frame above reconnects” and “the frames below survive” are
the same statement; depth **4** is the shallowest stack with *two* frames below a
cut, and `tests/SmpIpcSuite.lean` §3.23 builds one, cuts its third frame, asserts
the frame below the cut untouched, and runs **three** successive
`returnDonatedSchedContextResolved` pops that end with the reservation `.bound` on
the original owner — the transitive form of
`donationAccountingPreserved_atCallDepthThree`.  What the cut *measured* changes what
§3.23 is evidence for: a token-preserving mutation of the splice's **store shape**
does not fail the suite, it **fails to elaborate**, because
`spliceReplyFrameStores_cases` pins the three stores as a theorem.  So the shape needs
no witness and §3.23's subject is the composition; the witness says so rather than
implying a mutation-verification that is not available.  HP9 also moved the three
upstream facts this workstream rests on — the non-head branch's write, the pop's
trigger, and `reply_pop`'s `tcbSchedContext == NULL` guard — to
`donationRecipientAcceptable`'s own docstring, each with the revisions it was read at,
which is what `v0.35.40`'s retraction-of-a-retraction cost.  **Depth 2 was HP10's**,
and the register row was closed at `v0.35.54` on both halves being earned — was
**re-opened at `v0.35.141`** on the depth-2 half, and is **closed again at
`v0.35.157`**, see the correction below.

**HP10.9 (`v0.35.53`) addressed depth 2**, which the splice provably could not reach:
the frame a depth-2 removal takes off the stack *is* the bottom, so nothing sits
below it to reconnect and either policy writes the same `none` above it
(`removeCallerReplyFrame_clears_prev_of_bottom_frame`).
`donationAccountingPreserved_atCallDepthTwo` is the payoff — with the reservation's
origin recorded on the `SchedContext` and read in place of stack reachability, a
delegate answering the client out of order no longer costs that client its
reservation.  Upstream has the same loss at this depth (`reply_pop` donates to the
answered frame's own `replyTCB`), so this is an improvement on seL4-MCS too.  The
theorem **derives** the reachability answer from the removal and, since `v0.35.157`,
the owner's rebindability too (the removal cleared its `replyObject`), and
**hypothesises** the recipient guard.

**And that guard was a PROXY, so the depth-2 claim was retracted — and restored**
(PR #897's review, `v0.35.141`; closed `v0.35.157`).  Until `v0.35.157`
`donationOriginRebindable` read the origin's `ipcState` alone, standing in for
"some live `.donated _ origin` binding names it".  A client woken by the
out-of-order reply is an ordinary runnable thread: its next Call is `.unbound`, so
it donates nothing and no binding names it, while putting it `.blockedOnReply`
again — and the proxy refused it.  The pop then fell back to the answered caller
and **transferred** the reservation to the intermediate caller, clearing
`donationOrigin`.  The guard is now `schedContextBind`'s own admissibility, asked
of the origin — its reply frame is on no **live** stack (`replyFrameOnLiveStack`,
on both surfaces) — which admits the re-called client and refuses a frame that
heads a context or sits inside a live stack; its soundness is the binding → head
fact `donatedContextIsOwnerFrameHead`, relocated upstream and carried by the reply
path as `redirectedOriginFrameCoherent`.  Measured on the live pop at
`tests/SmpIpcSuite.lean` §3.25's PAYOFF group, with the retired proxy computed
beside the live guard so the assertions discriminate.  The accounting holds at
every reply-stack depth.
§3.20's accounting halves inverted from COST to PAYOFF and now drive the live
`.reply` spine rather than `returnDonatedSchedContextResolved`, which was an
accurate proxy for the pop while nothing redirected and omits the redirect since
HP10.7.  **No mutation of the production code is available** — every relevant
definition is pinned as a theorem, so a mutation fails to *elaborate*, exactly as
§3.23 records for the splice's stores — so the decisive comparison is a differential
within the suite: one function applied to a chain that recorded an origin and to one
that predates the field, a single field apart and opposite outcomes.  The same cut
gave HP10.4's production write its first measurement, running the live push twice
and asserting both directions.  §3.22, §3.23 and the golden trace are
byte-identical, which is *structural* rather than lucky: at depth ≥ 3 the pop sits
at a `some` arm, where `replyDonationRecipient_eq_of_outer_some` makes the redirect
the identity by theorem.

See [`SELE4N_SPEC.md`](../spec/SELE4N_SPEC.md) §8.12.8 for the canonical text,
§8.12.9 for the head-driven reply pop, §8.12.10 for the cancellation reclaim,
§8.12.11 for the splice, §8.12.14 for its composition at depth 4 and §8.12.15 for
the depth-two payoff.

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
one site at a time.  Two invariants follow the read.
`effectiveParamsMatchRunQueue{,OnCore}` says a run-queue member's recorded bucket
is that thread's own base priority — at *every* binding since `v0.35.133`, its
three-armed case analysis having collapsed when `TCB.priority` became the base's
one home; its `.bound` arm's `| _ => True` fallback went with it, so a bound
thread whose reservation does not resolve is no longer excused from the claim.
And `boundThreadPriorityConsistent` ranges over `.bound` alone, where quantified
over every binding **the donation falsified it** whenever the donor's and the
donee's base priorities differed — the reservation's `priority` had to equal one
before the hand-off and the other after, and the hand-off writes neither field.
It is load-bearing for no read now and is kept as the statement that
`schedContextBind` and `schedContextConfigureBoundPropagate` propagated the band
a reservation configures.  Budget,
period and deadline stay the reservation's at every depth, and the five budget
predicates keep their merged arm — pinned as such, so the split cannot leak into
the budget question.  `schedContextConfigureBoundPropagate` gates both
propagations on the bound thread **owning** the reservation, through one
predicate both halves consult so they cannot diverge, and `effectiveSchedParams` reports a donee's own
domain, since every live domain filter reads `tcb.domain`.  `maxLockSetSize` is
unmoved at **14**.

### 3.4 Lifecycle — `SeLe4n/Kernel/Lifecycle/Invariant/`

`lifecycleInvariantBundle` is the identity/aliasing invariant — the
object-type metadata is exact for every object id — preserved across retype,
suspend, resume and cleanup.  (The stale-reference and capability-reference
layers it once conjoined were retired at v0.35.78: every predicate in them was
stated over a reader that read the object store, so each was a tautology.)
Retype is the sharp edge: `retypeFromUntyped` must not overlap an existing
region (`untypedRegionsDisjoint`, §3.5), and `lifecycleRevokeDeleteRetype`
revokes every capability naming the object before it is retyped, so no slot
carries authority over the consumed object into its successor (the
capability layer's revoke theorems, §3.2).

**The cancellation reply arm's bundle statement is taken at the pair, not at
either half** (WS-RR RR8.7, `v0.35.80`).  Two theorems about the reply-link
teardown used to ask for `ipcInvariantFull` of the state they run on *together
with* that state's answered caller not being `.blockedOnReply` — and
`replyCallerLinkage`'s second direction refutes exactly that pairing, since a
stored Reply naming a caller obliges that caller to be reply-blocked.  Their
premises therefore held on **no state**: they asserted nothing while their names
read, in a bundle search, like coverage.  `replyCallerLinkage_refutes_woken_linked_caller`
is that reading as a theorem (the two premises derive `False`) and is kept as a
permanent pin so the spelling cannot return.

The honest pre-state is `ipcInvariantFullExceptReplyLinkage st woken` — the twenty
conjuncts with reciprocity relaxed at **one** thread, and relaxed as narrowly as
possible: the reciprocal pair is still required to exist at the woken thread and
only the blocking clause is dropped, as a disjunct rather than by excusing the
thread from the clause (the pair is what the teardown reads).  It stands to
`replyCallerLinkage` as `ipcInvariantFullExceptDonationOwner` stands to
`donationOwnerValid`.  The **unit** is the restore-and-teardown pair: the restore
wakes the victim and so breaks reciprocity, the teardown consumes the link that
wake left dangling, and each is the other's repair — so `restoredAndConsumed` is
what carries the full bundle end to end.

**And the removal's own statement landed at `v0.35.188`** (WS-RR RR8.16), which
that cut had left owed: `removeCallerReplyFrame` — the splice then the consume —
now carries the relaxed bundle to the full one
(`removeCallerReplyFrame_establishes_ipcInvariantFull_of_exceptReplyLinkage`).
What it needed was a **unit** rather than an argument.  The relaxed predicate was
written flat, and a `replyLinkageFrame` transports the reciprocal *pair*, so there
was nothing for the frame to carry and the splice would have had to re-run the
full store's case analysis; split as `replyCallerLinkage` is —
`replyCallerLinkageReciprocalExcept ∧ blockedOnReplyHasReplyObject` — the
transport is its full sibling one strength down.  Two collapses rode along, each
one question given one owner: everything but the reciprocal pair is proved once
and assembled twice, and the splice's store chain is one transport over any
predicate a caller-preserving Reply store carries, rather than a copy per bundle.
See `SELE4N_SPEC.md` §8.12.16.

**And the object-domain donation members follow the donation's own guard**
(WS-RR RR8.16, `v0.35.189`; register row 56).  WS-RR RR8.12 Cut C1 narrowed the
`.receive` *replenish* segment onto `callDonationSchedContext?` and registered
that the two **object**-domain members had its gaps one lock domain over:
`endpointCallDonatedSc?` read the caller's own effective context with no test
that a receiver was waiting or that it was passive, and
`receiveRendezvousDonatedSc?` read the queued sender's through it — so a plain
`Send`, and a `Call` to a receiver that already holds a reservation, each
declared a SchedContext write lock for a migration that provably does not happen.
Sound, and not free: lock contention is SM8.D's CC-5 channel.  Each member now
resolves the *other* party and asks the transition's own guard of the pair, and
the soundness half is proved in the one direction a footprint needs — *the
transition migrates ⟹ the footprint declares*, which is post-state `some` ⟹
pre-state `some` (`endpointCallDonatedSc?_some_of_post`,
`receiveRendezvousDonatedSc?_some_of_post`, each through Cut C1's backward
binding frame).  `receiveRendezvousDonatedSc?_isSome_iff_donatingSender` then says
the object member and the scheduler segment declare on exactly the same
rendezvous, because a shared spelling is not that fact.  Landing it moved
`callDonationSchedContext?` down to the layer both askers reach and three binding
frames out of the staged call-chain invariant surface into production.
`maxLockSetSize` is unmoved and the golden trace is byte-identical.
See [`SELE4N_SPEC.md`](../spec/SELE4N_SPEC.md) §8.12.7.

**And with the arm keystone, all three cancellation arms carry the bundle**
(WS-RR RR8.7, `v0.35.82`): the blocked-on-endpoint arm since `v0.34.95`, the
notification arm since `v0.34.96`, and the reply arm at `v0.35.82`
(`cancelIpcBlocking_replyArm_preserves_ipcInvariantFull`).  Only the composite
over all five arms lifted to `cancelIpcBlockingOnCore` is still owed.

The reply arm needed a different shape because it is a **four-step composition**
rather than one sweep — reclaim, splice, restore, teardown, pinned to exactly
that by `rfl` (`cancelIpcBlocking_reply_arm_eq`), so a step inserted or reordered
fails to elaborate rather than escaping the keystone.  No two steps carry the
bundle for the same reason: the reclaim composes the holder abort with the
donation pop's carriage at the *relaxed donation-owner* bundle, the splice is
three `.reply` stack-link stores, and the restore and teardown carry it only as
the pair above.

Its hypothesis set is larger than its siblings', and the load-bearing part is
that it takes **both directions** of one local coherence fact:
`replyFrameHeadHolderDonation` at the victim's reply object (head → binding,
which the pop's carriage is stated over) and `donatedContextIsOwnerFrameHead`
(binding → head, which the no-donation payoff quantifies over).  Neither entails
the other and `ipcInvariantFull` entails neither — `donationOwnerValid` relates a
donation to no reply object, and `donationChainWellFormed` carries no binding
clause at all.  Two facts it deliberately does **not** take: the abort's "not
blocked on reply" premise, which is *false* of a general holder and so is derived
inside each aborting branch rather than hypothesised; and a caller-supplied
holder, since the reclaim resolves its own from the victim's reply frame.

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
> pre-receive return are mutually exclusive on the send queue.  WS-HP HP6.2
> (`v0.35.44`) retired the sharper seventeen and made this one unconditional; the
> canonical account is `SELE4N_SPEC.md` §8.12.6.
>
> WS-HP HP10.6 (`v0.35.50`) moved the ceiling 23 → 24 for the TCB a
> bottom-of-stack pop will redirect a reservation to, and that eighteen **did not
> move**: the origin member is live only where the pop is at the bottom of its
> stack, and there the two below-head members are both absent
> (`replyStackBelowHead?_of_originRecipient`), so a reachable footprint trades two
> members for one.  `tests/LockSetSuite.lean` exhibits the redirecting shape at
> seventeen, one *narrower* than the popping shape measured at the same operands.
>
> At HEAD, the declared lock-set ceiling is **24**, the RPi5 tick admits **13 µs** per lock, and the uniform 60 µs envelope is **4320 µs** —
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

> **The frozen execute phase reads the same priority, and the same field
> clear** (`v0.35.134`). PR #897's review reported the frozen waiter fold as
> reading a different priority from the live one; it did against `v0.35.132`,
> and `v0.35.133`'s one-home collapse closed it while leaving nothing in the
> tree saying so. `effectiveSchedParams_fst_eq_boostedPriority` and
> `frozenComputeMaxWaiterPriority_eq_live_reading` are the two halves of saying
> it, the second quantified over every live state because the reading reads
> none of it. Sweeping the same question found `frozenResumeThread` reading the
> wrong priority in three places — a four-field-short restore, no `pipBoost`
> recompute, and a preemption test on the two **bases** rather than the
> effective priorities, so the surfaces disagreed both ways whenever either
> thread carried an inherited boost. The live field clear is now
> `TCB.restoredToReady`, called by both surfaces: it had been spelled inline
> inside `updateTcb`'s lambda, so the mirror could only copy its field list.
> Canonical: [`CLAUDE.md`](../../CLAUDE.md) and
> [`SELE4N_SPEC.md`](../spec/SELE4N_SPEC.md) §R5.D.

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
