# WS-HP — the head-driven donation pop, and the chain-preserving removal

> **Status**: **PLANNED** — registered `v0.35.16`. No sub-task has started.
> **Predecessor finding**: [`../REGISTERED_DEBT.md`](../REGISTERED_DEBT.md)
> table C, registered `v0.35.14` — the removal does not preserve the donation
> accounting at reply-stack depth ≥ 3.
> **Sub-task count**: 55 across 10 phases (HP1..HP10), each phase numbered in the
> order it is to be implemented.

## Context — why this exists

`v0.35.14` registered this divergence and corrected the documentation that
described it wrongly, and stopped there. That is half of what this project's
**implement-the-improvement rule** requires: where the optimal implementation is
out of scope for a cut, the audit "must split the work into the proper sequence
of PRs … rather than treating documentation surgery as a substitute for the code
change." The debt row is the bookkeeping; this plan is the sequence.

**The defect.** `spliceReplyFrameOut` writes `above.prev := none`, so every
frame *below* a cut leaves the context's reply stack (`severAtCut`). The later
pop then reads the frame above the cut as the bottom and binds that caller
`.bound scId`. On a three-frame stack the reservation settles on a thread
strictly *inside* the chain and its owner is left `.unbound` for good — so a
callee that delegates its caller's reply capability to a confederate, or anyone
holding a suspend right over a middle caller, can permanently capture that
caller's CBS reservation. Measured on a live stack in `tests/SmpIpcSuite.lean`
§3.22.

**seL4-MCS severs too — corrected at `v0.35.40`.** `reply_remove`'s non-head
branch, read at upstream master, 13.0.0, 12.1.0, 12.0.0 and 11.0.0 (every release
that has the function), is

```c
if (next_ptr) {
    /* not the head, remove from middle - break the chain */
    REPLY_PTR(next_ptr)->replyPrev = call_stack_new(0, false);
}
if (prev_ptr) {
    REPLY_PTR(prev_ptr)->replyNext = call_stack_new(0, false);
}
```

It writes **zero** into the frame above, which is `severAtCut`. `v0.35.14` claimed
the opposite and cited
`REPLY_PTR(call_stack_get_callStackPtr(reply->replyNext))->replyPrev =
reply->replyPrev` as the evidence; that line is in no release.

**This does not weaken the plan — it reclassifies it.** The defect above is real
and measured, and upstream has it too, so the chain-preserving removal is an
**improvement on seL4-MCS** rather than parity with it. Everything the phases do
is unchanged; what changes is the attribution and the claim set (see §8 and §9).
Two things upstream *does* confirm, and both are already landed: `reply_pop`'s
trigger is `call_stack_get_isHead(reply->replyNext)` — head-driven, HP4 and HP5 —
and it donates only `if (tcb->tcbSchedContext == NULL)`, which is HP4.6's
`donationRecipientAcceptable` with upstream's own reason ("only give the SC back if
our SC is NULL").

**Why the splice alone does not work here, and what actually has to change.**
This kernel decides whether a reply pops a donation from the **recorded
server's binding** (`endpointReplyServerDonation?` → `recordedReplyServer?`),
not from whether the answered frame heads a context. `severAtCut` is exactly
what keeps those two facts equivalent. Splice under the current trigger and a
frame gets re-headed whose recorded server is by then gone and `.unbound`:
answering it runs no pop, `Reply.consumed` keeps a head's links, and the result
is a consumed frame heading a context — the object-pinning state `v0.35.4`
closed and `replyStackOuterCaller?_of_consumed_frame` refuses.

So the correction is **two changes in a forced order**: move the pop's trigger
to head-ness and its source to `SchedContext.boundThread` (HP4, HP5), then
replace the sever with the splice (HP6). Doing them in the other order is
unsound, and HP2.3 makes that a machine-checked fact rather than a note.

**Intended outcome.** A completed call chain returns the client's reservation
to the client at any depth; the three pre-state coherence hypotheses the reply
path carries today become derivable rather than assumed; and v1.0.0 can claim a
reply-stack removal that preserves the donation accounting — a property seL4-MCS
does not have. (The claim v1.0.0 must *stop* being blocked from making is the
accounting one; "seL4-MCS reply-stack removal semantics" is already true, since
`severAtCut` is what upstream writes.)

## 1. Phase goal

`returnDonatedSchedContext` fires exactly when the answered frame heads a
scheduling context, takes that context from the frame's own `.head` link and
its current holder from `SchedContext.boundThread`, and a non-head removal
splices rather than severs. `donationAccountingPreserved_atCallDepthThree` is
the payoff: on the depth-3 witness, the reservation reaches its owner.

## 2. What is wrong today, precisely

Three facts, each checkable in the tree:

1. **The trigger is the wrong fact.** `endpointReplyCrossCoreDispatch`
   (`SeLe4n/Kernel/IPC/CrossCore/EndpointReplyDispatch.lean`) resolves
   `recordedReplyServer? st target`, then `endpointReplyDonation?` on that
   server. Nothing reads the answered frame's `next`.
2. **The removal drops the tail.** `spliceReplyFrameOut`
   (`SeLe4n/Kernel/IPC/Operations/Endpoint.lean`) stores
   `{ a with prev := none }` and never writes the frame below.
3. **The equivalence that licenses (1) is unstated.**
   `replyStackHeadIsAnsweredReply`, `replyDonationOwnerIsAnsweredCaller`
   (`SeLe4n/Kernel/Concurrency/Locks/ResolvedFootprintBounds.lean`) and
   `answeredHeadContextIsServerDonation`
   (`SeLe4n/Kernel/IPC/CrossCore/EndpointReplyDispatchInvariant.lean`) are
   carried as *stated* pre-state hypotheses. No invariant entails them.

## 3. Design

### 3.1 The trigger becomes a property of the frame

`answeredFrameHeadContext? st target : Option (SchedContextId × ThreadId)` —
the context the answered frame heads, paired with that context's
`boundThread`. Resolved from the **same**
`(st.getTcb? target).bind (·.replyObject)` expression the arm's existing reply
member and `answeredReplyFrameAbove?` already come from, so the footprint, the
transition and the trigger cannot disagree about which frame is answered.

`donationHeadOf?` already validates `r.next = some (.head scId)` given a
`scId`; the new resolver reads the `scId` *off* the link instead. Its
fail-closed arms are `donationHeadOf?`'s: a head that resolves to no Reply, or
to a context that does not name it back, is a refusal and not an empty stack.

### 3.2 The recipient is the answered caller, and the holder is read from the context

`returnDonatedSchedContext st serverTid scId originalOwner newOwner?` keeps its
shape. What changes is where three of its four arguments come from:

| argument | today | after HP4 |
|---|---|---|
| `scId` | the recorded server's `.donated` binding | the answered frame's `.head` link |
| `serverTid` | the recorded server | `sc.boundThread` |
| `originalOwner` | the binding's recorded owner | `target`, the answered caller |
| `newOwner?` | `replyStackOuterCaller?` | unchanged |

The existing `boundThread` guard (`sc.boundThread != some serverTid → error`)
becomes trivially satisfied rather than defence in depth, which is the honest
direction: the operation now reads the fact it used to check.

### 3.3 The recipient is guarded, and that guard is this kernel's, not upstream's

`returnDonatedSchedContext` writes `donationReturnBinding scId newOwner?` at
`originalOwner` unconditionally. Under the new trigger `originalOwner` is the
answered caller, which may have acquired a context of its own while blocked
(`schedContextBind` binds a blocked thread). Overwriting would strand it. So the
pop refuses a recipient that is not `.unbound` — the same fail-closed posture
`outerCallerAcceptable` already takes for the outer caller.

This is required by **this** kernel's typing (`.bound` / `.donated` /
`.unbound`) whichever way upstream answers, so it is not a branch point. **And
upstream answers the same way** — resolved at `v0.35.40`, so HP9.4's open question
is closed: `reply_pop` guards its `schedContext_donate` with
`if (tcb->tcbSchedContext == NULL)`, under the comment *"only give the SC back if
our SC is NULL. This prevents strange behaviour when a thread is bound to an sc
while it is in the BlockedOnReply state"* — which is HP4.6's reason in upstream's
own words. HP9.4 records the answer rather than asking the question.

### 3.4 The splice, and why it must come second

`spliceReplyFrameOut st rid` writes **two** Reply objects: `above.prev :=
cut.prev` and `below.next := cut.next`. Fail-closed on either neighbour failing
to reciprocate, exactly as the detach is today.

It is sound only under the head-driven trigger (§Context). HP2.3 states the
equivalence that `severAtCut` maintains and the splice breaks, so the ordering
is forced by a theorem: a cut that reorders HP6 before HP4 has to make HP2.3
false.

**It also cannot be built ahead of its caller, and that is a second forced
ordering — one this plan originally got wrong.** The splice was scheduled as
as three HP1 sub-tasks, "inert beside the detach", on the reasoning that a definition
nothing calls changes no behaviour. It was written that way, it built, and
`SeLe4n/Testing/ReplyStackWriteCensus.lean` refused it. The census derives the
reply-stack write-site set from the elaborated environment and demands a chain
result of every site, and a splice **on its own** has none: what it does to
`donationChainWellFormed` is break `prevLinkReciprocal` at the cut frame, and
that is repaired by the consume which follows it inside `reply_remove`. So the
only true statement is the *composite's*, and the composite is HP6's. Landing
the splice earlier meant either a `states` entry whose theorem says the chain is
broken — gaming a gate — or a `halfStep` naming a composite that does not exist
yet. The splice is therefore HP6.1–HP6.3, and it is the *write* that is
constrained, not the declaration: `replyFrameBelow?` reads nothing and stays in
HP1, and the footprint member it feeds stays in HP3, because a footprint may be
declared ahead of the write it covers (§3.6) and a write may not be declared
ahead of its proof.

The distinction is worth stating because "inert" has two meanings and only one of
them is free. A definition with no caller changes no *behaviour*; it still enters
the *environment*, and a gate whose domain is derived from the environment sees
it. Inertness buys nothing against a gate that asks what a declaration owes.

### 3.5 The depth-≤ 2 case is unchanged, definitionally

`spliceReplyFrameOut_eq_sever_of_no_frame_below` is the load-bearing lemma of
the workstream: where the cut frame is the bottom of its stack — every stack of
depth two, and every reply in a tree with no donation — the splice **is** the
sever. Every later repair is then a case split whose `none` branch is the
pre-HP proof verbatim, which is the shape `removeCallerReplyFrame_eq_consume_of_no_frame_above`
gave WS-RM and the reason that workstream landed in one cut.

### 3.6 What the footprint costs

The splice writes the frame below, which no footprint names. It is **not**
mutually exclusive with `answeredReplyFrameAbove?` — a mid-stack removal writes
both — so this is a genuine `+1`:

- `maxLockSetSize` **22 → 23**
- `admissibleCriticalSection` on the 1 ms RPi5 tick **15 µs → 14 µs**
- the uniform 60 µs envelope **3960 → 4140 µs**

All three are derived from the constant and move with it;
`scripts/check_lock_ceiling_figures.py` holds every prose copy. Read the cost
against the alternative: a footprint that omits a written object is *false*.

**The *reachable* bound is expected to be unmoved, and HP3.5 must state which.**
The below member fires exactly on a mid-stack removal, and the donation-return
members fire exactly on a head — mutually exclusive, the same argument by which
WS-RM's frame-above member left
`lockSet_endpointReplyRecvOnCore_size_le_eighteen` alone. Twenty-three is what
the *definition* can produce, which is what `boundedWait_under_2pl` and the WCRT
surface must consume; the sharp bound is what a reachable `.replyRecv` declares.
If that exclusion turns out not to hold, the sharp bound moves too and HP3.5
says so rather than quoting the ceiling as though it were the reachable figure.

**LANDED, and the exclusion holds.** The unconditional `.replyRecv` figure
absorbed the member (`lockSet_endpointReplyRecvOnCore_size_le_nineteen` →
`…_size_le_twenty`) and both reachable ones are byte-for-byte where WS-RM left
them, at **eighteen** and **seventeen**. Two separate exclusions do it, and only
one of them needs a coherence fact: `answeredReplyFrameBelow?` resolves *through*
`answeredReplyFrameAbove?`, so a frame with nothing above it declares no
below-member with no invariant at all, and the head-exclusion
(`replyStackHead?_none_of_answeredFrameAbove`) does the rest. The cancellation
family moved the same way — `lockSet_cancelIpcBlockingOnCore_size_le_twelve` →
`…_size_le_thirteen` and the suspend pipeline
`lockSet_tcbSuspendOnCore_size_le_sixteen` → `…_size_le_seventeen` — with its
reachable reply-arm figure still ten, because a caller owed a reclaim is the
innermost live caller and so has nothing above its frame.

**One half of HP3.4's row is retired rather than done, and this is the reason.**
`lockSet_cancelDonationOnCore` needs **no** below-member: `cancelDonation`'s
donated arm is `cleanupDonatedSchedContext` → `returnDonatedSchedContextResolved`,
which is the reply-stack **pop**, and HP6 makes a *removal* a splice, not a pop.
The frame a pop re-heads is already declared, as `belowHeadReplyId`, and has been
since `v0.35.4`. Declaring a second one would put a write lock on a Reply the
operation never touches — sound, and not free, since lock contention is an
observable channel (SM8.D's CC-5), so a footprint wider than its operation
carries contention that says nothing about the operation. The coverage layer
HP3.4 asks that family for already exists: WS-RM's post-landing audit added
`lockSet_cancelDonationOnCore_covers_victim` and its five siblings.

### 3.7 What this buys, beyond the accounting

The three stated coherence hypotheses become **derivable**:
`replyStackHeadIsAnsweredReply` is definitional under the new trigger (the pop
fires only where the answered frame is the head, and `headLinkResolves` supplies
the converse); `answeredHeadContextIsServerDonation` is definitional (the holder
is read from `sc.boundThread`); `replyDonationOwnerIsAnsweredCaller` is by
construction (the recipient *is* `target`). HP7 retires them from every
consumer's hypothesis list.

**Landed at `v0.35.46`, with one correction to this paragraph.**  All three are
gone, and so are HP2's own equivalence and refutation, the scaffolding that consumed
them and the binding-driven resolver itself: nine declarations.  What this paragraph
does not mention, and HP7 found, is a **fourth** stated fact —
`replyFrameHeadHolderDonation`, HP4.2's rename of `answeredHeadHolderDonation` — which
is **live** and stays stated: the trigger answers `(context, holder)` off a `.head`
link and says nothing about `holder`'s *binding*, so the one thing it does not
witness is exactly the fact that keeps that predicate load-bearing.  Its own
docstring, and four others across `API.lean`, `DispatchPayoff.lean`,
`DonationPreservation.lean` and `Endpoint.lean`, claimed HP7 retires it; that claim
is corrected rather than acted on.

### 3.8 HP4 in full: what flips, what does not, and the two ways to get it wrong

HP4 is the largest cut in this workstream and the only one that changes what the
live kernel does. This section is its implementation plan; §6's HP4 rows are the
schedule and this is the design they execute.

#### 3.8.1 The measurement

| symbol | references | files |
|---|---|---|
| `applyReplyDonation` | 172 | 23 |
| `endpointReplyCrossCoreDispatch` | 135 | 20 |
| `applyReplyDonationOnCore` | 99 | 12 |
| `recordedReplyServer?` | 91 | 17 |
| `replyDonationReturn?` | 61 | 9 |
| `endpointReplyServerDonation?` | 32 | 6 |
| `replyDonationOwnerHome` | 8 | 4 |

Four definitions are re-keyed **in place** rather than duplicated:
`applyReplyDonation`, `applyReplyDonationOnCore`, `replyDonationReturn?` and
`endpointReplyServerDonation?`. A second spelling of each would be this project's
one-question-two-answers hazard on the tree's most-travelled IPC path, and the
`_post_agrees` result that relates the single-core and per-core spines would then
be relating four things rather than two.

`recordedReplyServer?` **stays and keeps every consumer it has outside the
donation pop.** It answers "which thread did this caller record as its reply
server", which the reply *leg* needs (it is what `endpointReply`'s authority gate
reads, and what `replyTransferOnCore` branches on) and which the arm's footprint
declares a lock for. Only the *pop* stops asking it.

#### 3.8.2 The hazard: two resolvers, one type, opposite meanings

```
endpointReplyServerDonation? st target : Option (SchedContextId × ThreadId)
                                                                 ^ originalOwner — who GAINS the context
answeredFrameHeadContext?     st target : Option (SchedContextId × ThreadId)
                                                                 ^ holder — who LOSES it
```

The types are identical and the second components are opposites. A substitution
that replaces one call with the other typechecks, and under the flip the pair
also moves from argument 4 to argument 2 of `returnDonatedSchedContextResolved`.
So the flip is done **by name and position, deliberately, one call site at a
time**, and never by a mechanical rewrite. Three things enforce that:

1. `answeredFrameHeadContext?`'s components are destructured into `let scId` and
   `let holder` at every use, never passed positionally out of a `some (a, b)`
   pattern whose binder names could be read either way.
2. A Tier 3 negative refuses `returnDonatedSchedContextResolved` applied with a
   pair pattern bound from `answeredFrameHeadContext?` in the argument position
   the *owner* occupies — token-preserving, since it keeps both the resolver and
   the call and changes only which component reaches which parameter.
3. `answeredFrameHeadContext?_boundThread` is the theorem that the second
   component **is** `sc.boundThread`; a proof that needs the owner there fails.

#### 3.8.3 The four arguments, and where each comes from after the flip

`returnDonatedSchedContext st serverTid scId originalOwner newOwner?` keeps its
shape (§3.2). After HP4:

- `scId` — `answeredFrameHeadContext?`'s first component, read off the answered
  frame's `.head` link.
- `serverTid` — its second component, `sc.boundThread`: the thread that loses the
  context and is set `.unbound`.
- `originalOwner` — `target`, the answered caller: the thread that gains it, and
  `donationReturnBinding scId newOwner?` is written there.
- `newOwner?` — unchanged, `replyStackOuterCaller?` on the pop's pre-state.

Two consequences to state rather than discover:

**The `boundThread` guard becomes vacuous, and that is the honest direction.**
`if sc.boundThread != some serverTid then .error .invalidArgument` was RR2.8's
symmetry with `donateSchedContext`'s donor check; with `serverTid` *read from*
`sc.boundThread` it cannot fire. Keep it — deleting it would make the operation
depend on its caller having resolved the server the one correct way — and restate
`returnDonatedSchedContext_ok_implies_sc_bound` as the triviality it becomes. The
SM5.H migration's source core stays derivable: it is that same `boundThread`'s
home, now read directly instead of through a guard.

**`outerCallerAcceptable st serverTid originalOwner newOwner?` is re-examined at
its new arguments, not assumed to carry.** Its first argument is the thread
losing the context and its second the thread gaining it; both change identity
under the flip even where they change nothing on the nested-Call path. HP4.6's
recipient guard is the other half of the same question.

#### 3.8.4 The signature change, and why it is a narrowing

`applyReplyDonation` and `applyReplyDonationOnCore` take the recorded server and
resolve its `.donated` binding **inside their own bodies**. That is the trigger,
and it is what flips. They take `target` after HP4 and resolve
`answeredFrameHeadContext? st target` themselves.

This is the *parameter is a place for a caller to be wrong* rule: the footprint
resolves its members from `target` and the operation now resolves its pop from
the same argument, so the two cannot name different contexts.

It also settles what happens to the two migration-home arguments, and the answer
is not "internalise both because internalising is good". `replierHome` and
`ownerHome` feed `migrateSchedContextReplenishment`, which moves a SchedContext's
replenishments from its outgoing bound thread's home core to its incoming one.
Both are `determineTargetCore` of threads the operation will hold after the flip,
so both *could* be computed inside — and `determineTargetCore` is the **right**
resolver here, unlike the deschedule's: the replenish queue is keyed by affinity
(`replenishQueueAffinityConsistentOnCore`), not by placement, so there is no proxy
to remove. Internalising them is therefore a readability change with a large
restatement cost and no correctness content, and HP4 does **not** do it.

What HP4 does retire is `replyDonationOwnerHome`, and for a different reason: it
is a *second* resolver for "which core does the owner's replenish queue live on",
computed from `replyDonationReturn?` at the call site while the operation resolves
the same owner internally. That is one question with two answers, and after the
flip the two answers come from different triggers — the call site's from the
binding and the operation's from the frame — so they can disagree on exactly the
orphan-head state HP4 exists for. It goes; the caller passes
`determineTargetCore st` of the component the resolver hands back.

It does **not** remove the core parameter this cut's sibling finding is about (the
`v0.35.36` deschedule proxy, `docs/REGISTERED_DEBT.md` table A). That fix and
this flip touch the same five lines and must not be interleaved: the proxy fix
lands first, on the pre-flip spine, so that the flip's `_post_agrees` re-proof has
one moving part rather than two.

**The resolver has to move down the import chain first, and HP1 put it in the
wrong module for HP4.** `answeredFrameHeadContext?` was declared in
`IPC/CrossCore/EndpointReply.lean`, which is right for HP1 — its consumers there
are the footprint and the dispatch — and is **not** in
`IPC/Operations/Donation/Primitives.lean`'s import closure, which imports
`IPC/Operations/Endpoint.lean` alone. So the single-core `applyReplyDonation`
cannot call it as written.

The fix is a relocation, not a second spelling: `answeredReplyObject?` and
`answeredFrameHeadContext?` move down beside `replyFrameHeadContext?` in
`Endpoint.lean`, where every expression they need is already in scope
(`SystemState.getTcb?`, `getSchedContext?`, `SchedContext.boundThread`) and where
`returnDonatedSchedContext` — the operation the trigger decides for — already
lives. Everything that reads them today reads them through a module that imports
`Endpoint.lean`, so nothing else changes. Declaring a second thread-level
resolver in the lower module instead would be the hazard §3.8.2 is about, with
the two spellings free to drift in exactly the component whose meaning is easy to
get wrong.

Do the relocation first and build `Donation.Primitives` before touching anything
else; a flip that discovers the import problem only when it re-keys the
single-core spine has already rewritten the characterisation that 172 references
run through.

#### 3.8.5 What HP4 must *not* change

- **The priority-inheritance walk does not move.** `propagatePipChainCrossCore`
  keys on waiters (`TCB.blockingServer?`), not on donations, so it is unaffected
  by which resolver decides the pop. Its argument stays `expected`, which is
  `recordedReplyServer?` — a Tier 3 negative refuses re-keying it on the holder,
  because a chain walk from the context's `boundThread` would start at the wrong
  thread whenever the two differ, which is exactly the delegated case.
- **The `.replyCapInvalid` arm stays, and stays unreachable.** "No recorded
  server" and "no head context" are different facts and must remain
  distinguishable: the first is a malformed reply and the second is an ordinary
  reply with no donation to return. Collapsing them would turn every
  donation-free reply into an error.
- **The two pre-receive cleanups keep the binding-driven resolver** (HP4.6).
  `cleanupPreReceiveDonation` asks "does this receiver still hold a donation",
  which is a question about a *binding* and not about a frame. A Tier 3 negative
  pins that they do.
- **Behaviour is preserved on every state the tree reaches today.** HP2.1 is the
  statement; the golden trace being byte-identical is the measurement. The two
  triggers diverge only at an orphan head, which `severAtCut` provably never
  leaves (`severAtCut_pop_leaves_no_head`) — so the divergence is unreachable
  until HP6 creates it, which is why HP4 is a refactor and HP6 is the semantic
  change.

#### 3.8.6 Order of work inside the cut

One PR, in this order, because each step is the previous step's only consumer:

1. `replyDonationReturn?` and `endpointReplyServerDonation?` re-keyed, with
   `_eq_answeredFrameHeadContext?` stated on each so every existing theorem about
   them has a bridge rather than a rewrite.
2. `applyReplyDonation` re-keyed and `applyReplyDonation_characterisation`
   restated — that characterisation is what every reply-side invariant proof runs
   on, so it is the single point through which 172 references move.
3. `applyReplyDonationOnCore` re-keyed, `applyReplyDonationOnCore_eq_single` /
   `_post_agrees` re-proved.
4. `endpointReplyCrossCoreDispatch`'s body, and the footprint's resolver
   arguments repointed to match.
5. HP4.6's recipient guard, with `returnDonatedSchedContext_rejects_bound_recipient`.
6. The two Tier 3 negatives of §3.8.2 and §3.8.5, each mutation-tested in both
   directions: silent on the clean tree, firing on a mutation that keeps every
   token and swaps the component or the key.

The acceptance measurement is in §6's HP4 row and it is the golden trace, not a
build: a flip that compiles and changes a dispatch outcome is exactly the failure
this ordering exists to catch.

#### 3.8.7 What implementing it corrected

Five things the design above got wrong, recorded here because the plan is the
canonical source for this phase's design and a plan that still describes the
superseded shape is worse than no plan.

**The pop cannot resolve its own trigger, and §3.8.4 assumed it could.**
`answeredReplyObject?` is the answered caller's own forward link — the one
`linkCallerReply` wrote and `consumeCallerReply` **clears** — and the donation pop
runs *after* the reply leg, which is seL4-MCS's `doReplyTransfer` order and the
one this kernel keeps because the server needs the returned budget while it
replies. So `answeredFrameHeadContext? st1 target` is `none` on every state the
pop ever sees. HP1's own docstring had said so ("every one of those sites must
read it from the **pre**-state") and §3.8.4 did not read it.

The fix is a split, not a passed pair: `replyFrameHeadHolder? st rid` is the
frame-keyed resolver and `answeredFrameHeadContext?` is its composition with
`answeredReplyObject?`. The pop takes the **reply id**, resolved on the pre-state
through the one expression the footprint members also come from, and resolves the
context and its holder itself at the state it runs on. Passing the resolved
*pair* instead would have made both a pre-state read and put
`returnDonatedSchedContext`'s `boundThread` guard back to work, which is the shape
HP4 exists to retire — so the split is what keeps §3.8.3's second consequence
true.

**`replyDonationReturn?` is not re-keyed, and §3.8.6 step 1 was wrong to say it
would be.** Its argument means the thread that *holds* a donated context; the
trigger's means the thread whose reply is being *answered*. Re-keying it in place
would have changed its argument's meaning at 57 call sites while every one of
them still typechecked — the §3.8.2 hazard at its worst, because there the two
spellings are not even the same resolver. It stays as the binding-driven
"does this thread hold a donated context" resolver, which is a question the tree
still asks (the two pre-receive cleanups, the cancellation reclaim, the witnesses);
what moved to the trigger is the *characterisation* of `applyReplyDonation`.

**One coherence hypothesis survives, and it is not one of the three.** The chain
composite loses `answeredHeadContextIsServerDonation` outright — the pop and the
relaxation name one frame by construction now — and gains `replyFrameHeadIsBound`:
a scheduling context that heads a reply stack is bound to a thread. It is strictly
weaker (the retired one implies it through `donationOwnerValid`), it is vacuous on
every reply whose frame heads nothing, and it is what rules out the arm
`replyFrameHeadHolder?` declines on — a frame heading a context bound to nobody,
where the pop would be the identity while the leg had already relaxed the chain
there. `answeredFrameHeadContext?`'s docstring argues that arm is unreachable, and
that argument is about *reachability*: `donationChainWellFormed` carries no binding
clause. HP7 is where it becomes one.

**The pop's conditions are stated at the state the pop runs on.** The bundle
payoff's `hDonationReturned` was a pre-state fact transported across the reply leg
through `endpointReplyOnCore_sameSchedContextBindings`; its head-driven form is
about the reply *stack*, which the leg does rewrite, so there is no free
transport. All three pop-side conditions therefore follow `hStackValid`'s
existing convention in that same signature — stated at
`(endpointReplyOnCore … st).1`, a pre-state-computable expression, so the
de-threading discipline is respected and no transport lemma stands between what a
caller discharges and what the pop consumes. The *frame* stays on the genuine
pre-state, for the reason above.

**And "this reply returns no donation" became two facts.** `hNoDonationOwnedBy`
(nothing is donated by the answered caller) made the relaxation empty and, under
the binding-driven trigger, also made the pop the identity. It no longer does: a
frame heading a context held by a thread whose binding names some *other* owner
satisfies the first and not the second. `endpointReplyCrossCoreDispatch_preserves_ipcInvariantFull`
takes both, and on a reachable state they coincide.

*A note for HP7*: `replyDonationReturn?` reads the thread through `lookupTcb`
(which refuses a reserved id) while `endpointReplyDonation?` reads it through
`getTcb?`. The two therefore answer differently on a reserved thread — fail-closed
on the `lookupTcb` side — which is one question with two answers. HP4 retires
neither, because the pop now asks neither; giving the question one answer belongs
with the retirement of the resolver that survives.

#### 3.8.8 Why the frozen mirror's trigger flips inside HP4, not inside HP8

HP8 as written puts the frozen surface's whole catch-up after HP6, on the
reasoning that `FrozenOps` mirrors *transitions* and the transitions settle
there. That is right for the **splice** and wrong for the **trigger**, and the
difference is which cut creates the divergence.

`frozenEndpointReplyWithDonationReturn` is the mirror of the live `.reply`
*operation*, and `frozenBranchOperationChecked .endpointReplyToBlockedCaller =
true` is a machine-checked claim that the two are run beside each other. HP4
makes the live operation head-driven. From that instant a binding-driven mirror
is answering the pop question a second way — `CLAUDE.md`'s *one question answered
in two places will diverge*, with the divergence already on this plan's own
schedule at HP6 — and the coverage row's `true` is a claim about an agreement
that no longer holds on states HP6 makes reachable. Registering that as debt
would be documenting an asymmetry between two paths, which this project's
implement-the-improvement rule forbids where making them symmetric is available.
It is available: the frozen composite is *handed* `replyId`, and
`frozenEndpointReply` refuses it unless the target's own `replyObject` names it,
so the frozen arm needs no resolver relocation at all — it asks the head question
of exactly the frame the live operation recovers through `answeredReplyObject?`.

So **HP4.7** flips it, and HP8.2 narrows to the splice half. Two things fell out
of doing it, and both are findings rather than bookkeeping.

1. **The frozen binding-driven resolver is deleted, not left beside the new
   one.** `frozenEndpointReplyServerDonation?` existed solely as this composite's
   trigger; keeping it would leave two readings on the surface whose entire
   purpose is to have one. A pin on a symbol nothing reads is a tautology.

2. **`FO-041` never fired the pop on either side.** Through review rounds 13, 14,
   15 and 22 that scenario grew halves for delegation, a stale boost and a
   missing guard, and not one of them gave the recorded server a `.donated`
   binding — so the donation return *round 13 added to this surface* was compared
   on neither side, and the operation-level claim that round 15 built to stop
   exactly this substitution was resting on it. `FO-042` is the fix: one half
   where the frame heads a real context so both sides pop, with the post-state
   asserted on the live side so agreement is agreement with a pop; and one half
   where the two candidate triggers **disagree** — the server holds the donation
   and the answered frame heads nothing — where the retired reading would pop,
   the live operation does not, and the mirror must not. That second half is the
   mutation that decides the flip: reverting the frozen trigger to the binding
   reading fails it and leaves all ten of its neighbours passing, which is the
   token-preserving shape this project requires of a witness.

3. **The frozen pop was missing HP4.6's recipient guard** — found by asking the
   question the flip raises rather than reported. It carried two of the live
   pop's three guards under a docstring saying *"both of the live guards come
   with it"*, a sentence that was true when written and false from HP4.6 onward.
   The guard is head-driven-specific, which is why it could not have been missing
   earlier: under the binding reading the recipient *is* the binding's recorded
   owner, which the operation has already seen hold nothing. `FO-042`'s third
   half is its witness, and reverting to the genuine pre-fix behaviour (no frozen
   guard) fails exactly that assertion while every neighbour — *including* "the
   live pop REFUSES to overwrite it" — still passes.

4. **...and the live pop's ID promotion was missing as well.**
   `applyReplyDonation` refuses a holder `ThreadId.toValid?` will not promote;
   the mirror went straight to the return, so a SchedContext bound to the
   sentinel thread took a different arm on each surface. The refusal sits at the
   unit the live code puts it and is spelled `holder.isReserved`, because this
   surface uses `toValid?` nowhere — `frozenLookupTcb` is its "is this id
   usable" and *is* `isReserved`, which is exactly `= sentinel`. Importing
   `toValid?` would have been a second validity convention where the surface has
   one, which is the reasoning it already gives for declining `scThreadIndex`; a
   Tier 3 negative keeps `toValid?` out of both frozen modules.

## 4. Sequencing

Phases run in order. **No phase may run in parallel with another** — HP3, HP4,
HP5 and HP6 all edit the reply footprints and their consumers.

Three orderings are forced and each is forced by a theorem rather than a note:

- **HP1–HP2 before HP4** — the numbering rule's semantic half. A live
  transition may not change its trigger ahead of the equivalence that says the
  change is behaviour-preserving on every state the tree reaches today.
- **HP4 and HP5 before HP6.** The splice is unsound under a binding-driven
  trigger (§Context). HP2.3 is what makes this checkable. The splice also
  *cannot* be built before HP6 at all, for a second and independent reason
  (§3.4): `ReplyStackWriteCensus` demands a chain result of every reply-stack
  write site and a bare splice has none to give, so the definition and the
  composite that makes its statement sayable land in one cut.
- **HP5 is not optional, and the reason is derived rather than assumed.** After
  the splice, a frame becomes the head whose recorded reply target is gone, so
  *cancelling* that frame's caller resolves `cancelledCallerDonation?` through
  a thread that may not exist, the reclaim declines, and the holder is left
  `.donated` naming an owner that is now `.ready` — `donationOwnerValid`
  violated. The cancellation trigger therefore flips with the reply trigger.

**HP4, HP5 and HP6 are each one cut.** Within HP4 the two spines are related by
`endpointReplyOnCore_post_agrees` at every object key and cannot change in
separate PRs — the numbering rule's "when splitting is impossible, merge the
rows".

HP1, HP2 and HP3 are **inert**: nothing calls the new definitions, and the whole
tree must still build unchanged. That is their own acceptance test — and it is an
acceptance test about behaviour, not about gates. A declaration with no caller is
still in the environment, so a census whose domain is derived from the
environment judges it; §3.4 records the instance that taught this plan the
difference.

## 5. Phase map

| Phase | Scope | Sub-tasks |
|-------|-------|-----------|
| HP1 | The trigger's resolvers, inert | 2 |
| HP2 | The equivalence and the derivable coherence facts, inert | 4 |
| HP3 | The footprint member and the ceiling, declared ahead of the code | 5 |
| HP4 | The reply path's trigger flips (one cut) | 7 |
| HP5 | The cancellation path's trigger flips (one cut) | 5 |
| HP6 | The splice replaces the sever — **COMPLETE** (HP6.1 `v0.35.41`, HP6.2 `v0.35.44`, HP6.3–HP6.9 one cut at `v0.35.45`) | 9 |
| HP7 | The three stated hypotheses retire — **COMPLETE** (`v0.35.46`; HP7.1 verified already done at HP4.4, HP7.4 measured out vacuous) | 4 |
| HP8 | The frozen mirror — **COMPLETE** (`v0.35.47`; HP8.4 added while implementing: the depth-3 witness the phase turns on) | 4 |
| HP9 | Witnesses, anchors, documentation, closure — **COMPLETE** (`v0.35.48`; HP9.2 largely verification, HP9.3's own premise corrected, acceptance box 10 struck as wrong) | 5 |
| HP10 | The reservation's origin, so the return does not depend on chain connectivity | 10 |

## 6. Sub-tasks

Estimates: **S** small (<½ day) · **M** medium (1–2 days) · **L** large (3–5 days)

### HP1 — The trigger's resolvers, inert (2 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| HP1.1 | `answeredFrameHeadContext?` (§3.1) — resolved from the same `(st.getTcb? target).bind (·.replyObject)` expression as `answeredReplyFrameAbove?`, reading `scId` off the frame's `.head` link and the holder from that context's `boundThread`; fail-closed on an unresolvable head or one that does not name the frame back | `SeLe4n/Kernel/IPC/CrossCore/EndpointReply.lean` | M |
| HP1.2 | Its read algebra: `_of_no_reply`, `_of_not_head`, `_some_iff`, `_eq_of_getTcb?`, and the frame lemma over a step writing no chain object — the shape `donationHeadOf?` already carries | same | M |

**Acceptance**: `lake build` is unaffected outside the new declarations, and
`SeLe4n.Testing.ReplyStackWriteCensus` builds — the resolvers write nothing, so
the census's site count must be exactly what it was.

**The splice moved to HP6 at `v0.35.36`, and the move is not a schedule slip —
it is this plan's own numbering rule, enforced by a gate.**  The splice was
written here, inert, with its whole algebra derived through one shared store step
so the second store cost the bundle and projection surfaces nothing; it built and
the algebra was right.  `SeLe4n/Testing/ReplyStackWriteCensus.lean` then refused
it: the census derives the reply-stack write-site set from the elaborated
environment and demands a chain result of every site, and a *bare* splice has
none to give — what it does to `donationChainWellFormed` is break
`prevLinkReciprocal` at the cut frame, repaired by the consume that follows it
inside `reply_remove`, so the only true statement about it is the composite's.
The two ways to satisfy the census here were a `states` entry whose theorem says
the chain is broken, which is gaming the gate, and a `halfStep` naming a
composite that does not exist until HP6.  So the splice is HP6.1–HP6.3, where
`removeCallerReplyFrame` supplies the caller that makes the statement sayable.
`replyFrameBelow?` and the footprint member it feeds stay in HP1/HP3, because a
*footprint* may be declared ahead of the write and a *write* may not be declared
ahead of its proof.

### HP2 — The equivalence and the derivable coherence facts, inert (4 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| HP2.1 | `answeredFrameHeadContext?_eq_serverDonation` — under `donationChainWellFormed` and the three coherence facts, the two triggers agree on every reachable state. The safety net that makes HP4 a refactor rather than a behaviour change. Consumes HP1.2 | `SeLe4n/Kernel/IPC/CrossCore/EndpointReplyDispatchInvariant.lean` | L |
| HP2.2 | The converse — a recorded server holding `.donated scId owner` implies the answered frame heads `scId` — through `headLinkResolves` and the push's own freshness. Without it HP4 could narrow the set of states that pop | same | L |
| HP2.3 | **`severAtCut_maintains_triggerEquivalence`** and its negative twin: the splice falsifies HP2.1's hypothesis set, stated against `cancelledMiddleCallerPolicy` so a cut that reorders HP6 before HP4 has to make it false (§3.4). Consumes HP2.1 | `SeLe4n/Kernel/IPC/Invariant/Defs.lean` | M |
| HP2.4 | The three coherence facts stated as *theorems* of the new resolver (§3.7) — not yet retired from consumers, which is HP7. Consumes HP2.1, HP2.2 | `SeLe4n/Kernel/Concurrency/Locks/ResolvedFootprintBounds.lean`, `SeLe4n/Kernel/IPC/CrossCore/EndpointReplyDispatchInvariant.lean` | M |

**Acceptance**: the two triggers are proved equal on every state satisfying the
chain invariant and the three coherence facts, and the theorem that the splice
breaks that equality exists and is cited by HP6's row.

### HP3 — The footprint member and the ceiling (5 sub-tasks)

Declared ahead of the code, which is the order the numbering rule requires: a
live transition may not write an object its footprint does not name, and
over-declaring is sound.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| HP3.1 | `answeredReplyFrameBelow?` — derived from the same expression as `answeredReplyFrameAbove?` composed with the cut frame's own `prev`, so the footprint and the splice cannot disagree | `SeLe4n/Kernel/IPC/CrossCore/EndpointReply.lean` | S |
| HP3.2 | `lockSet_endpointReply` gains it in **write** mode. Restate at full arity: the size bound, `lockSet_consistent_reply`, the write-membership lemmas, the `lockSetTransitions_within_bound` conjunct, both atomicity lemmas, and the resolver `lockSet_endpointReplyOnCore` | `SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean`, `SeLe4n/Kernel/Concurrency/Locks/Deadlock.lean`, `SeLe4n/Kernel/IPC/CrossCore/EndpointReply.lean` | L |
| HP3.3 | `lockSet_replyRecv` gains it, same restatement list, plus `KernelOperation.ofReplyRecv`, `lockSet_replyRecv_no_caps` and `capsCarryingIpcArms_footprints_share_serialization`. Consumes HP3.2 | same | L |
| HP3.4 | The cancellation footprints gain it — `lockSet_cancelIpcBlockingOnCore` and `lockSet_cancelDonationOnCore`, each with the resolved coverage theorem its family carries (`…_covers_splicedFrameBelow`). Consumes HP3.1 | `SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean`, `SeLe4n/Kernel/Concurrency/Locks/ResolvedFootprintBounds.lean` | L |
| HP3.5 | `maxLockSetSize` 22 → 23 and every figure derived from it (§3.6): the canonical sentence at all five sites `check_lock_ceiling_figures.py` requires, `PerCoreWcrt.lean`'s docstrings, `rpi5Tick_refuses_sixty_micro_sections`, and the figure-bearing suites (`DeadlockFreedomSuite`, `LockSetSuite`, `SmpWcrtSuite`, `SmpSchedulerSuite`) with the Tier 3 ceiling anchors including the negative that refuses 22. Consumes HP3.2, HP3.3, HP3.4 | `SeLe4n/Kernel/Concurrency/Locks/LockSet.lean`, `SeLe4n/Kernel/Scheduler/Operations/PerCoreWcrt.lean`, `CLAUDE.md`, `AGENTS.md`, `docs/spec/SELE4N_SPEC.md`, `docs/gitbook/12-proof-and-invariant-map.md`, `tests/`, `scripts/test_tier3_invariant_surface.sh` | M |

**Acceptance**: `SeLe4n.Testing.LockFootprintBoundCensus` builds — it refuses a
size bound left at the old arity — and `check_lock_ceiling_figures.py` passes
with no stale figure in any tracked prose.

### HP4 — The reply path's trigger flips (7 sub-tasks)

One cut: `endpointReplyOnCore_post_agrees` relates the two spines at every
object key. Behaviour-preserving on every reachable state by HP2.1, which is
what makes it a refactor rather than a semantic change. §3.8 is the design;
these rows are its schedule, and the order inside the cut is §3.8.6's because
each step is the previous step's only consumer.

**The `v0.35.36` deschedule-proxy fix (`docs/REGISTERED_DEBT.md` table A) lands
before HP4.1, not inside it.** It rewrites the same five lines of
`endpointReplyCrossCoreDispatch` that HP4.4 does, and interleaving the two would
leave `_post_agrees` with two moving parts and no way to attribute a failure.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| HP4.1 | **First** relocate `answeredReplyObject?` and `answeredFrameHeadContext?` from `IPC/CrossCore/EndpointReply.lean` down beside `replyFrameHeadContext?` in `IPC/Operations/Endpoint.lean`: HP1 put them where their HP1 consumers are, and `Donation/Primitives.lean` — the module the single-core spine lives in — imports `Endpoint.lean` alone, so as written that spine cannot call the resolver (§3.8.4). A relocation, never a second spelling. Then **split the resolver at the reply object**: `replyFrameHeadHolder? st rid` is the frame-keyed form the pop reads and `answeredFrameHeadContext?` becomes its composition, because the reply leg clears the answered caller's link to its frame before the pop runs (§3.8.7). `replyDonationReturn?` and `endpointReplyServerDonation?` are **not** re-keyed — their argument means the *holder*, the trigger's means the answered *caller*, so re-keying in place would have changed the meaning at 57 typechecking call sites (§3.8.7). `recordedReplyServer?` is untouched and keeps every consumer outside the pop. Consumes HP2.1 | `SeLe4n/Kernel/IPC/Operations/Endpoint.lean`, `SeLe4n/Kernel/IPC/CrossCore/EndpointReply.lean` | M |
| HP4.2 | `applyReplyDonation` re-keyed: it takes the answered **frame** (resolved on the pre-state through the same `answeredReplyObject?` expression the footprint's members come from) and the answered **caller**, and resolves the context and its holder itself at the state it runs on — the `a parameter is a place for a caller to be wrong` rule, applied to everything the pop can still ask its own state (§3.8.4, §3.8.7). `applyReplyDonation_characterisation` restated — it is what every reply-side invariant proof runs on, so it is the single point through which 172 references move. Also `answeredHeadHolderDonation` → `replyFrameHeadHolderDonation`: the one binding fact the trigger does not witness, named once so HP7 has one symbol to delete. Consumes HP4.1 | `SeLe4n/Kernel/IPC/Operations/Donation/Primitives.lean`, `SeLe4n/Kernel/IPC/Operations/Donation.lean` | L |
| HP4.3 | `applyReplyDonationOnCore` re-keyed the same way, which **retires `replyDonationOwnerHome`**: it resolves the owner's home from the *binding* at the call site while the operation resolves the same owner from the *frame*, so after the flip the two answers can disagree on exactly the orphan-head state HP4 exists for (§3.8.4). The two migration-home arguments themselves **stay** parameters — `determineTargetCore` is the correct resolver for a replenish queue, which is keyed by affinity rather than placement, so there is no proxy there to remove and internalising them would be restatement with no correctness content. `applyReplyDonationOnCore_eq_single` and `_post_agrees` re-proved. Consumes HP4.2 | `SeLe4n/Kernel/IPC/CrossCore/EndpointReplyDispatch.lean` | L |
| HP4.4 | `endpointReplyCrossCoreDispatch`'s body, which resolves the answered frame on the pre-state and threads it to the pop. The **PIP walk does not move** — it keys on waiters, so its argument stays `recordedReplyServer?` — and the `.replyCapInvalid` arm stays, because "no recorded server" and "no head context" are different facts (§3.8.5). The two footprints keep their binding-driven resolvers and gain `lockSet_endpointReplyOnCore_covers_headDrivenPop` instead, because repointing them belongs to the phase that makes the divergence reachable and would otherwise make the two sharp bounds depend on a coherence fact HP7 deletes (§3.8.7). The row that does it names this one. Consumes HP4.3 | `SeLe4n/Kernel/IPC/CrossCore/EndpointReplyDispatch.lean`, `SeLe4n/Kernel/IPC/CrossCore/EndpointReplyDispatchInvariant.lean`, `SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean` | L |
| HP4.5 | `.replyRecv`'s `replyRecvPopDonation` — between the legs, where WS-RM put it — re-keyed on the frame the reply capability names and the caller it answers; on this arm the frame needs no resolving, because `rid` **is** the capability. Its three preservation theorems, the two total accessors, the NI confinement and the dispatch payoff's `replyRecvStage` fields all restated. Consumes HP4.4 | `SeLe4n/Kernel/API.lean`, `SeLe4n/Kernel/IPC/Invariant/DispatchPayoff.lean`, `SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean` | L |
| HP4.6 | The **recipient guard** (§3.3): `donationRecipientAcceptable` refuses an `originalOwner` that is not `.unbound`, with `returnDonatedSchedContext_rejects_bound_recipient` proving the refusal commits nothing and `_ok_recipient_unbound` the fact a successful pop witnesses; `outerCallerAcceptable` re-examined at its new arguments rather than assumed to carry (§3.8.3). Plus the Tier 3 negatives §3.8.2 and §3.8.5 call for — the component swap, the PIP re-keying, the pre-state frame resolution, and the two pre-receive cleanups keeping their binding-driven resolver — each token-preserving. Consumes HP4.5 | `SeLe4n/Kernel/IPC/Operations/Endpoint.lean`, `scripts/test_tier3_invariant_surface.sh` | M |
| HP4.7 | **The frozen mirror's trigger, in the same cut** (§3.8.8): `frozenReplyFrameHeadContext?` / `frozenReplyFrameHeadHolder?` beside the frozen detach, and `frozenEndpointReplyWithDonationReturn` re-keyed on them — the frozen arm needs no resolver relocation, because `replyId` **is** the presented capability and `frozenEndpointReply` refuses it unless the target's `replyObject` names it. `frozenEndpointReplyServerDonation?` is deleted rather than left beside the new reading, and `frozenApplyReplyDonation`'s first parameter is renamed `holder` (it was `replier` and denoted the recorded server). And the frozen pop gains HP4.6's **recipient guard** (`frozenDonationRecipientAcceptable`), which it was missing under a docstring claiming it carried every live guard — the direction that matters, since a mirror missing a guard succeeds where the kernel refuses — and the live step's **ID promotion**, spelled in this surface's own `isReserved` vocabulary. `FO-042` fires the pop on both sides — which `FO-041` never did in four review rounds — and its second half is the state where the two candidate triggers disagree. Consumes HP4.6 | `SeLe4n/Kernel/FrozenOps/Core.lean`, `SeLe4n/Kernel/FrozenOps/Operations.lean`, `tests/FrozenOpsSuite.lean`, `scripts/test_tier3_invariant_surface.sh` | M |

**Acceptance**: every existing reply theorem holds unchanged, `smp_ipc_suite`
and `smp_cross_core_reply_suite` pass with no fixture edit, and the golden trace
is byte-identical — the measurement that the flip is behaviour-preserving. A flip
that builds and changes a dispatch outcome is the failure §3.8.6's ordering
exists to catch, and only the trace can see it.

### HP5 — The cancellation path's trigger flips (5 sub-tasks)

Forced by §4: after HP6 a frame becomes the head whose recorded reply target is
gone, and a binding-driven reclaim would leave a `.donated` binding naming a
`.ready` owner.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| HP5.1 | `cancelledCallerDonation?` reads the victim's own frame's `.head` link and that context's `boundThread`, derived from `replyFrameHeadHolder?` — the frame-keyed resolver both reply spines read since HP4.1 — rather than spelled a second time. `_independent_of_victim` pins that the victim's id is no longer consulted (the binding reading's `owner == tid` check is what the structure replaces) and `_eq_answeredFrameHeadContext?` ties it to the reply path's own resolver | `SeLe4n/Kernel/Lifecycle/Suspend.lean` | M |
| HP5.2 | `returnDonationToCancelledCaller` re-proved over the new resolver. Two things the head reading forces, neither foreseen: **`returnDonatedSchedContext_ok_under_invariants` generalises** into `_ok_of_boundAndRecipient`, which takes the context, its bound thread and the recipient's `.unbound` as *arguments* (the head reading supplies the first two and has no binding to read the third from), with the binding-keyed form as its instance — "derive both answers from one" rather than a second success proof; and the payoff's case split moves onto **the pop's own result**, because the recipient fact is available only in the refused branch, where `hTcb` *is* a pre-state binding and `donationOwnerValid` reads the victim's `.unbound` off it. Plus `returnDonatedSchedContext_ok_server_not_reserved` and `abortHolderPendingIpc_eq_self_of_lookup_none`: the head reading names a `boundThread` no invariant ties to a stored TCB, so what rules that out is the pop declining. Consumes HP5.1 | `SeLe4n/Kernel/IPC/Invariant/Defs.lean`, `SeLe4n/Kernel/IPC/Operations/Endpoint.lean`, `SeLe4n/Kernel/Lifecycle/Invariant/SuspendPreservation.lean`, `SeLe4n/Kernel/Lifecycle/Invariant/CancellationReplyShape.lean` | L |
| HP5.3 | The coherence fact **re-keyed with the resolver**: `donatedContextIsOwnerFrameHead` replaces WS-RR RR7.22's `donationHolderIsReplyTarget`, which is deleted rather than left beside it — the resolver no longer reads a recorded reply target, so the old fact would have no consumer. `cancelIpcBlocking_reply_no_donation_to_victim` and `passiveServerIdle` preservation carry across unchanged in *statement*; `cancelledCallerDonation?_none_below_the_cut` and `…_some_of_immediate_donee` restate on the **stack** (a frame with a frame above it heads nothing), which drops their binding hypotheses altogether — the second is renamed `…_some_of_frame_head` for what it now says. Consumes HP5.2 | `SeLe4n/Kernel/Lifecycle/Invariant/CancellationReplyShape.lean` | L |
| HP5.4 | The wake and the scheduler footprint. **They needed no re-resolution**: `cancelAbortedHolderWake?`, `cancelAbortedHolderWakeCore?`, `cancelBelowHeadReads?` and `cancelReclaimHead?` are all *derived from* `cancelledCallerDonation?`, so HP5.1 flows through them — which is the payoff of the derivation discipline, measured rather than assumed. What the row does own is the two claims the flip turns from fixture observations into **theorems**: `cancelReclaimHead?_eq_replyObject` (the head the pop clears **is** the victim's own reply object — `replyStackHeadIsAnsweredReply`'s content seen from the cancellation end) and `cancelDetachedFrameAbove?_of_donation` / `cancelSplicedFrameBelow?_of_donation` (a reclaim excludes both removal members, so the reachable footprint stays below the ceiling they raise). Both were sentences about reachable states that the binding reading could not have stated at all. Consumes HP5.3 | `SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean` | M |
| HP5.5 | **The runtime witness**, which the tree did not have: nothing exercised the reply-arm reclaim at all, so the flip would have landed untested. `tests/SmpCancellationSuite.lean` §3.20 fires it on two shapes — the seL4-MCS one where both readings agree, and the **orphan head** where they differ, with both answers computed side by side (the retired reading spelled in the suite, nowhere else) so the assertions are known to discriminate. The second is the state HP6's splice creates and the reason HP5 precedes it: the binding-driven reclaim declines there and leaves `.donated scId victim` live across a cancellation that made the victim `.ready`, which is exactly the `donationOwnerValid` break RR7.22 was written to close. Consumes HP5.4 | `tests/SmpCancellationSuite.lean`, `scripts/test_tier3_invariant_surface.sh` | M |

**Acceptance**: `smp_cancellation_suite` passes unchanged, and
`cancelIpcBlocking` preserves `donationOwnerValid` and `passiveServerIdle` on
every arm with no new hypothesis.

**The fixture sweep HP4 owes this phase, already run.** A hand-built `.donated`
binding is only as reachable as the invariants nobody was checking, and HP4 paid
for that five times — three golden-trace fixtures and `SyscallDispatchSuite`'s
`sd052b` / `sd052c`, each carrying a donation with **no frame on the context's
reply stack** (unreachable since WS-OD OD4.1 made `donateSchedContext` a push that
is fail-closed on the donor's `replyObject`) and a donor left `.bound` on the
context it had donated away (which HP4.6's recipient guard refuses). So the tree
was swept for every remaining one, and exactly one is this phase's:

**And the note above was itself the defect it warns about.** It named three files,
and a sweep over a named list is *a recognised set standing in for a derived one* —
this project's own rule, in the paragraph that exists to prevent this class. Running
the named three found nothing to correct; the **golden trace** then failed, because
`SeLe4n/Testing/MainTraceHarness.lean` is not one of the three. The derived set is
every tracked test or harness file mentioning `.donated` — thirteen of them — and it
found **two** live fixture defects:

- `SeLe4n/Testing/MainTraceHarness.lean`'s `SCO-020b/c/d` (the WS-OD OD1.4/OD1.5/OD1.7
  reclaim scenarios) built a `.donated` binding with **no Reply object at all**: no
  victim `replyObject`, no `scReply` on the context. The reclaim became the identity
  and all three lines flipped to `false`. **Corrected** by giving the fixture the
  stack a live `Call` builds, which keeps `main_trace_smoke.expected`
  byte-identical — the strongest available statement that behaviour is restored
  exactly, and the measurement that those three lines *discriminate*: a reclaim that
  stops firing is visible in every field.
- `tests/SmpIpcSuite.lean`'s OD5.2 pair was passing **vacuously**. Its store's
  `pushOuter` carried no `replyObject` though `pushOuterReply.caller` named it back —
  a state `replyCallerLinkage` forbids — and both assertions handed the resolver a
  TCB without the field, so "the reclaim fires" and "the reclaim declines below the
  cut" declined for the *same* reason and the pair discriminated nothing. Corrected
  at the store (one `pushOuterBlockedTcb`, retiring two local re-spellings, one of
  which carried a note asserting no check read that field) and both assertions
  restated on the stack, the declining one on the state the **live push** produces.

- `tests/SmpCancellationSuite.lean`'s `stDonated` (Scenario F) needed **nothing**, and
  the prediction that it would was wrong about which resolver it drives:
  `cancelDonationOnCore` reads the *victim's own* binding (`cancelBindingSc?` /
  `cancelDonatedOwner?` — "this thread holds a donated context, give it back"), a
  different question HP5 does not re-key.
- `tests/SuspendResumeSuite.lean`'s `sr023`, `tests/NegativeStateSuite.lean`'s
  `.donated ⟨8888⟩ ⟨9999⟩`, `tests/LockSetSuite.lean`'s two `cancelDonation` size
  assertions, `tests/PriorityManagementSuite.lean`'s seven binding-classification
  checks and `SeLe4n/Testing/InvariantChecks.lean`'s binding walk need **nothing**:
  arm-selection negatives, footprint arity over explicit `Option` arguments, and
  reads of `ownScId?` / `scId?` — none reaches a pop.

Two things to carry forward. **A suite's assertions can pass vacuously; an exact
golden trace cannot** — which is why the trace found what the suites hid, and why a
flip's sweep should run the trace early rather than last. And the real gap the sweep
surfaced is HP5.5: before it, **nothing in the tree fired the reply-arm reclaim with
the head reading available** — the cancellation suite's `.blockedOnReply` fixtures
hold Replies whose `next` is unset, so the arm declined under both readings. A sweep
for fixtures that would *break* is not a sweep for fixtures that would *exercise*,
and only the second measures a flip. Each new fixture takes a pre-state assertion
that the trigger resolves, as `sd052b_pre_donation_frame_heads_the_context` does —
without one, a frame heading nothing makes the pop the identity and every downstream
check measures the fixture instead of the arm.

### HP6 — The splice replaces the sever — COMPLETE (9 sub-tasks; HP6.1 `v0.35.41`, HP6.2 `v0.35.44`, HP6.3–HP6.9 one cut at `v0.35.45`)

One cut: both removal paths call one step, and `removeCallerReplyFrame`'s
algebra is stated over it.

**The splice itself is built here, not in HP1**, and HP1's acceptance note says
why: `ReplyStackWriteCensus` demands a chain result of every reply-stack write
site, and a bare splice has none — it breaks `prevLinkReciprocal` at the cut
frame until the consume that follows repairs it.  The composite is what can make
the statement, so the splice and its caller land together.  That is why HP6.1–3
sit below HP4 and HP5 in the numbering rather than above them: the splice cannot
be landed earlier, and HP6.4 was always going to need HP4 and HP5 anyway (§4).

**Three measurements taken before writing code reshaped these rows** (`v0.35.41`);
each is a correction to this section rather than a discovery about the kernel.

1. **"Beside, then repoint" is the wrong shape.**  The rows used to add a second
   primitive *beside* the existing one and repoint the two callers.  Measured over
   the code view: the removal family has **388** references (254 of them its
   `OrSelf` fold), `removeCallerReplyFrame` **380**, and
   `DualQueueMembership.lean` alone holds 89 + 142.  A second primitive would
   leave ~37 lemmas and ~254 references watching a definition nothing reaches —
   the tautological-pin shape this project retires.  So the definition changes
   **in place**, under the final names, and the rename comes first because it
   carries no semantics and gives a green checkpoint either side of it.
2. **The below side must not refuse** — §3.4 said "fail-closed on either
   neighbour failing to reciprocate, exactly as the detach is today", and that
   breaks `spliceReplyFrameOutOrSelf`'s soundness: the fold's whole
   justification is that a *refusal* means nothing links down to the cut frame
   (`_unreferenced`, consumed by the `consumeCallerReply` after it).  A below-side
   refusal folded to the identity leaves a reciprocating frame above still naming
   the cut frame while the caller clears its links — the wedge WS-RM exists to
   prevent.  So the link below is an `Option`: not resolving, not reciprocating,
   or naming the frame above means *not followed*, and the removal degenerates to
   `severAtCut` there.  That is fail-closed on its own terms (writing
   `above.prev := some below` on a stale link stops a later walk mid-chain, since
   every walk validates reciprocity) and it keeps this operation's refusal set
   **exactly** the detach's, so every refusal theorem carries verbatim.
3. **One composed store step, because that keeps the case analysis two-way.**  37
   of the 47 sites that destructure `_cases` are inside `Endpoint.lean` itself and
   only 10 are outside; a three-way split changes the pattern at all 47, where a
   composed `spliceReplyFrameStores` leaves the arity alone and proves the
   two-store analysis once.  Statement-level changes are then five lemmas with
   ~15 callers in total — `_cases`, `_objects_ne`, `_decision`,
   `_objects_rewrite` and `replyFrameAbove?_of_detach_store` — while
   `_reply_rewrite` needs none, because `replyStackRewrite` is already general
   over both links and transitive.

4. **The footprint repoint must come BEFORE the splice, and was numbered last.**
   The two reply footprints resolve their donation members through
   `endpointReplyServerDonation?` while the pop reads `replyFrameHeadHolder?`.
   Under `severAtCut` those agree — `severAtCut_pop_leaves_no_head` (HP2.3) is
   exactly that statement — which is why HP4 could safely leave them and hold the
   gap with `lockSet_endpointReplyOnCore_covers_headDrivenPop`.  **The splice is
   the change that makes them disagree.**  So in any window where the splice has
   landed and the repoint has not, the footprint can omit a SchedContext and a TCB
   the pop writes, which is a *false* footprint — and this project rates that worse
   than a wide one.  That is the numbering rule's semantic half (*a transition goes
   live only after the declarations that cover it*), and the row is now **HP6.2**.
   It is landable there because under the sever the two resolvers agree, so the
   repoint is behaviour-preserving, and the 18 → 17 merge becomes definitional
   under the head-driven trigger HP4 already landed.  Renumbering was free: no
   HP6 sub-task ID had reached a `CHANGELOG.md` entry.

**And the claim that HP6 closes BOTH surviving divergences from upstream was
wrong, twice over — retracted at `v0.35.45`, measured rather than reasoned.**  The
paragraph this replaces said the splice closes the first divergence *and* that
`consumeCallerReply` falsifies `prevLinkReciprocal` on a non-head frame, making
HP6.7 a strengthening.  What is actually true:

1. **The first divergence is genuinely closed, and by construction.**  Upstream
   clears the frame below's upward link; `severAtCut` left it stale.  The splice
   *writes* it, so the pair either side of the cut reciprocates.
   `removeCallerReplyFrame_splices_reciprocally` (HP6.7) is the statement, and it
   is at the *removal* rather than at the splice because the consume that follows
   could in principle disturb the pair it just built.
2. **The second divergence is about HEADS, which HP6 does not touch.**  "Upstream
   clears the removed frame's own links; `Reply.consumed` keeps them" is true only
   on a frame that *heads* a context — `Reply.consumed`'s non-head branch already
   clears both, and since HP6.3 the splice clears the cut frame's `prev` itself
   (seL4's `reply_unlink` downward half).  A head keeps its links **deliberately**,
   because the pop that follows in the same transition validates the head by them,
   and nothing in HP6 changes that.  So the residue survives HP6 and is correctly
   still recorded as such.
3. **HP6.7 is a restatement, not a strengthening, for the theorem it names.**
   Measured on the pre-splice tree: `removeCallerReplyFrame_preserves_donationChainWellFormed`
   held on non-heads at `v0.35.44` with no side condition beyond `invExt` and the
   chain, because `spliceReplyFrameOutOrSelf_unreferenced` discharges exactly the
   precondition `Reply.consumed`'s docstring states.  The consume only falsifies
   `prevLinkReciprocal` when called **bare** — the WS-RM defect, which the census
   now refuses.  What HP6.7 *adds* is the reciprocity fact in (1), which the sever
   could not state at all.

**The post-HP6 position, stated accurately.**  Upstream parity on the removal's
*fail-closed* behaviour, a **divergence in this kernel's favour** on the frame
below's link, an accounting property at depth ≥ 3 **neither kernel has**, and one
residue — the depth-**two** loss the splice provably cannot reach, since both
policies write `none` into the frame above a bottom frame.  That last is WS-HP
HP10's, registered with a closure target.  The correction matters for what v1.0.0
may claim: not "seL4-MCS reply-stack semantics", which understates it, and not
"completing a call chain returns a client's reservation", which HP10 has not yet
earned.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| HP6.1 | **The family renamed, with no semantic change**  **LANDED v0.35.41**: `detachReplyFrameAbove` → `spliceReplyFrameOut` (which covers the `OrSelf` fold and every `_*` lemma by prefix), `detachFrameAboveThreadReply` → `spliceThreadReplyFrameOut`, `cancelDetachedFrameAbove?` → `cancelSplicedFrameAbove?` (pairing it with HP1's `cancelSplicedFrameBelow?`), `detachedFrame{Above,Below}` → `splicedFrame…` in the four footprint coverage theorems and the footprint parameter, `replyFrameAbove?_of_detach_store` → `_of_splice_store`, and the three test-side names (`runFrameDetachChecks`, `runMiddleCallerDetachChecks`, one `let` binder).  **545 occurrences over 593 lines in 27 modules**, plus 17 Tier 3 anchors and five live documents — the row said "~500 across 42 modules" from a code-view count that double-counted the overlay; the landed figure is measured.  A green build and four green suites either side: the checkpoint that separates rename breakage from semantic breakage, and what lets the ~37 proof rewrites the splice's algebra needs happen once, under the final names.  Three things this row decided rather than inherited.  (1) The **name is one cut ahead of the body** until the splice lands, so `spliceReplyFrameOut`'s docstring states what it writes today, names the row that completes it, and separates the two facts that say which semantics is live: `cancelledMiddleCallerPolicy` is the declared policy and `spliceReplyFrameOutOrSelf_store_cases` is the body's write, stated as `{ a with prev := none }`, so this row's successor cannot change the body without changing that lemma.  It also records that `cancelledMiddleCaller_severs_at_cut` is **not** that pin — its policy conjunct is `rfl` and its cut shape is a hypothesis — which is a claim this cut nearly shipped the other way round.  (2) The **English word** "detach" in prose describing what the operation does is left alone: it is accurate at this version, and prose follows behaviour when the body changes rather than the name here.  (3) The **frozen** family (`frozenDetachReplyFrameAbove{,OrSelf}`) is not renamed — it still severs, and HP8 renames it in the cut that makes it splice.  **And the rename found a dead citation**: WS-RM RM1.1 retired `detachCancelledCallerFrame` at `v0.35.6`, and four *live* claims still named it (`CLAUDE.md`/`AGENTS.md`'s WS-OD "what new code must respect" item 5, and `SELE4N_SPEC.md` §8.12.7 twice) — the dead-symbol shape this project calls a tautology, in prose rather than in an anchor | 27 modules; `scripts/test_tier3_invariant_surface.sh`; `CLAUDE.md`, `AGENTS.md`, `docs/spec/SELE4N_SPEC.md`, `docs/CLAIM_EVIDENCE_INDEX.md`, `docs/gitbook/12-proof-and-invariant-map.md` | M |
| HP6.2 | **The two reply footprints repointed onto the head-driven trigger**  **LANDED v0.35.44** — moved ahead of the splice, see the preamble's finding 4.  `lockSet_endpointReplyOnCore` / `lockSet_endpointReplyRecvOnCore` resolve their donation members through `answeredFrameHeadContext?`, the expression the pop reads, so the footprint and the transition cannot disagree about which objects are written; `lockSet_endpointReplyOnCore_covers_headDrivenPop` — HP4.4's stand-in — is **deleted**, replaced by the hypothesis-free pair `lockSet_endpointReply{,Recv}OnCore_covers_donationPop`, so it consumes HP4.4.  Sound today (under `severAtCut` the two resolvers agree), so the row is behaviour-preserving and verifiable on its own.  **Five things it landed that the row did not predict.**  (1) The slot's *meaning* changes, so the parameter does: `donatedOriginalOwnerTid` → `donatedScHolderTid` on both parametric footprints, since the head reading's second component is the thread the pop **unbinds** and the recipient needs no member at all (it is `replyTargetTid`).  (2) **Three write-membership lemmas had to be added** — the second donation member had none on *either* footprint and `lockSet_replyRecv`'s SchedContext member had none either, so nothing could state that the objects the pop writes carried declared write locks; the stand-in had routed around the gap through `callerTid`'s lemma.  (3) The 18 → 17 claim in the `v0.35.43` correction was still wrong in one direction: `…_size_le_eighteen` becomes **unconditional** (a frame heading a context provably has no frame above it, so the exclusion is structural where it took `donationChainWellFormed` and `replyStackHeadIsAnsweredReply`).  (4) And `…_size_le_seventeen` is **retired**: its merge was owner = answered caller, and the head reading's second component runs *on* the context while the answered caller is `.blockedOnReply`, so the coincidence occurs on no reachable state — false rather than unproved.  One unit of slack traded for two hypotheses and a figure that survives the splice.  (5) Both coherence facts therefore have **no consumer**, which is the verification the retirement row later in this phase-group asks for, recorded at each predicate.  The fixture sweep found one more instance of HP5's own lesson: `tests/SmpCrossCoreReplySuite.lean`'s delegated-reply state carried a `.donated` binding and **no reply stack**, so it declared nothing and its assertions would have passed vacuously; it carries the stack a live `Call` leaves, and a new **orphan-head** witness — a holder that is not the recorded server — is the shape on which the two resolvers name different threads.  A behavioural revert never reaches that witness: it fails the coverage theorem first.  Consumes HP6.1, HP4.4 | `SeLe4n/Kernel/IPC/CrossCore/EndpointReply.lean`, `SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean`, `SeLe4n/Kernel/Concurrency/Locks/ResolvedFootprintBounds.lean`, `SeLe4n/Kernel/Concurrency/Locks/LockSet.lean`, `SeLe4n/Kernel/IPC/CrossCore/EndpointReplyDispatchInvariant.lean`, `tests/SmpCrossCoreReplySuite.lean`, `tests/LockSetSuite.lean` | L |
| HP6.3 | **The splice's primitives.**  **LANDED v0.35.45**: `spliceFrameBelow?` (validated, `Option`-valued — preamble finding 2), `spliceReplyFrameStores` (one composed step — finding 3), `spliceReplyFrameOut`'s body, and `spliceReplyFrameOut_eq_sever_of_no_frame_below`, the definitional equality that makes every repair below a case split whose `none` branch is the pre-WS-HP proof verbatim.  Resolution and validation of the frame **above** are unchanged, so this operation's refusal set is exactly the sever's and every refusal theorem — including `spliceReplyFrameOutOrSelf`'s fold soundness — carries verbatim.  **THREE stores, not two, and the third is what the row did not predict.**  The two-store splice (`above.prev := some below`, `below.next := some (.frame above)`) leaves the *cut* frame with `prev = some below` while nothing below names it back, which falsifies `prevLinkReciprocal` at the cut frame — so the bare splice would have owed a relaxed predicate (`…Except rid`) and `ReplyStackWriteCensus` would have had to accept a half-step where the sever stated its result outright.  The third store is `rid.prev := none`, which is seL4's `reply_unlink` **downward half**, and with it `donationChainWellFormed` is preserved **outright** across the splice: no transient, no new predicate, and `spliceReplyFrameOut_preserves_donationChainWellFormed` keeps the shape it had.  Measured before choosing: the cut frame's lock is **already** a declared write member on both removal paths (the reply footprints' `replyId?` / the cancellation's victim reply), so the third store costs **no** footprint change and `maxLockSetSize` stays at HP3.5's 23.  Consumes HP6.2 | `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` | M |
| HP6.4 | **The algebra.**  **LANDED v0.35.45**: `spliceReplyFrameStores_*` proved once by a two-way split on `spliceFrameBelow?`, `_cases` restated at **today's arity** so the 47 destructuring sites are one-symbol swaps, and the statement-changing lemmas with their callers (`_objects_ne`, `_decision`, `_objects_rewrite`, `replyFrameAbove?_of_splice_store`).  `_reply_rewrite` needed no statement change, because `replyStackRewrite` is already general over both links and transitive.  `spliceReplyFrameOutOrSelf_unreferenced` is re-proved rather than inherited: in the splice branch `rid`, `above` and `below` are pairwise distinct, so the written `prev` is not `some rid` and reciprocity rules out any other frame naming it.  **Four things the row did not predict.**  (1) `_objects_ne` gained **two** exclusions rather than one — the frame below *and* the cut frame — and the cut-frame exclusion is unconditional, which propagated to `removeCallerReplyFrame_objects_frame` (its write set is **four** keys now) and to both `spliceReplyFrameOutOrSelf` forms.  (2) `spliceReplyFrameOutOrSelf_reply_next` could not be restated: the splice moves a `next` from one `.frame` link to another, so its old conclusion (`rq.next = rp.next`) is false.  It is **renamed** `spliceReplyFrameOutOrSelf_preserves_reply_caller_and_headLink` and weakened to a disjunction, which is still exactly what its one consumer needs — that no reply's `next` acquires a `.head` link, so `hNotHead` may be read on the pre-state.  (3) `spliceReplyFrameOutOrSelf_store_cases` is a **three-step existential** rather than a named relation, deliberately: a `Prop`-valued relation whose body mentions `storeObject` is reported by `ReplyStackWriteCensus`'s store frontier, and registering a relation as a write site is not an option because it writes nothing — which is the census decision the registration row below asks for, taken here.  (Named by artefact rather than by row number: a forward *citation* of a sibling is read as a forward *dependency* by `scripts/check_workstream_plan.py`, correctly, since no scanner can tell a narrative mention from a consumption.)  (4) The information-flow half needed `hSetInv` threaded to three theorems, because the frame below is written at the *intermediate* state and its index membership is read there.  Consumes HP6.3 | same, plus `SeLe4n/Kernel/IPC/Invariant/Defs.lean` (a new simultaneous-induction walk lemma: the existing one cannot express a *redirect*) | L |
| HP6.5 | **LANDED v0.35.45**: `spliceReplyFrameOut_preserves_projection` and `_preserves_ipcInvariantFull` — one extra `.reply` store at a third key, cheap by construction: no conjunct reads `prev` or `next`, and `projectKernelObject` erases both.  The bundle proof was **extracted** rather than copied: `storeObject_reply_stackLinks_preserves_ipcInvariantFull` states the 80-line argument once over one store and the splice composes it once or three times, so the removal gaining a write costs an iteration and no new argument — the same treatment the index-set pair and the dual-queue invariant got.  **The census decision the composed store step forces, taken.**  The row offered two exits and a third turned out to be right: the three steps are spelled out as an **existential**, so no `Prop`-valued name mentions a store and the frontier has nothing to report — no `isPredicate` patch, no exemption.  `spliceReplyFrameStores` itself *is* a write site and is registered `.halfStep spliceReplyFrameOut`, exactly as `storeDonationHeadClear` and `storeReplyReHead` are half-steps of `storeDonationHeadPop`, and added to `chainWritePrimitives` so a transition reaching for it directly is a site too.  It cannot state a chain result of its own: given only `above` and the two records, nothing says the frame above is the one whose `prev` names `rid`, and the three reciprocal links are coherent only under the resolution `spliceReplyFrameOut` performs.  Consumes HP6.4 | `SeLe4n/Kernel/InformationFlow/Invariant/Helpers.lean`, `SeLe4n/Kernel/IPC/Invariant/Structural/DualQueueMembership.lean`, `SeLe4n/Kernel/IPC/Invariant/Structural/QueueNextTransport.lean`, `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean`, `SeLe4n/Kernel/IPC/Invariant/LookupCongruence.lean`, `SeLe4n/Kernel/IPC/CrossCore/CancellationNI.lean`, `SeLe4n/Testing/ReplyStackWriteCensus.lean` | L |
| HP6.6 | **The callers, and the pin that ties the written key to the declared lock.**  **LANDED v0.35.45**: `removeCallerReplyFrame` and `spliceThreadReplyFrameOut` call the fold and so need no body change — verified rather than assumed, by reading both bodies — and `spliceFrameBelow?_mem_replyFrameBelow?` with its `answered…` and `cancel…` liftings states the containment the four footprint coverage theorems rest on and which nothing said: the footprint's resolver stops at "there is a frame above, and this is the cut frame's `prev`" while the operation additionally refuses a `prev` naming the frame above and one whose own `next` does not link back, so the operation's answer is **contained** in the declaration's.  `replyFrameBelow?_eq_prev_of_frame_above` states the other direction — the declaration is the cut frame's `prev` *whatever the operation decides*, so on either refusal the footprint declares a lock the splice never uses, which is the sound direction and is not free (SM8.D's CC-5 makes contention observable), which is why the excess is bounded to one member and named.  Consumes HP6.5, HP4, HP5 | `SeLe4n/Kernel/IPC/Operations/Endpoint.lean`, `SeLe4n/Kernel/IPC/CrossCore/EndpointReply.lean`, `SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean` | M |
| HP6.7 | **LANDED v0.35.45**, and the row's own claim corrected — see the preamble's retraction.  `removeCallerReplyFrame_preserves_donationChainWellFormed` over the splice is a **restatement**: it held on non-heads at `v0.35.44` too, because `spliceReplyFrameOutOrSelf_unreferenced` discharges the precondition `Reply.consumed`'s docstring states, and the consume only falsifies `prevLinkReciprocal` when called *bare*.  On a head the splice is the identity and the state is the `…Except rid` transient the composite already discharges, unchanged.  **What this row actually delivers is the fact the sever could not state**: `removeCallerReplyFrame_splices_reciprocally` — after a middle removal the frame above names the frame below and the frame below names the frame above.  Stated at the *removal* rather than at the splice, because the consume that follows clears the cut frame's remaining link and a claim about the splice alone would say nothing about whether that clear disturbs the pair; and with **no** key-distinctness hypothesis, derived instead from the store's contents (a key at which the post-splice state holds a `.reply` is one at which the consume's own TCB lookup fails), because `ReplyId.toObjId` and `ThreadId.toObjId` are two wrappers over one `ObjId` and a collision is representable.  It lives in `DualQueueMembership.lean` beside the removal's other read/write algebra rather than in `CancellationReplyShape.lean`, which the depth-three payoff below cannot import.  Consumes HP6.6 | `SeLe4n/Kernel/Lifecycle/Invariant/CancellationReplyShape.lean`, `SeLe4n/Kernel/IPC/Invariant/Structural/DualQueueMembership.lean` | L |
| HP6.8 | **LANDED v0.35.45**: `cancelledMiddleCallerPolicy := .spliceOutTheCut`, with `cancelledMiddleCaller_splices_at_cut` replacing `…_severs_at_cut` — the target's new binding is `.donated scId outer`, owed outward, where the sever's was `.bound scId` — and `replyStackOuterCaller?_follows_policy` restated from `hCut : r.prev = none ⟹ .ok none` to the frame below and `.ok (some outer)`.  **HP2.3's pin `severAtCut_pop_leaves_no_head` is DELETED, not retired-in-place**: its first conjunct was the policy constant at the old value, so a theorem whose conclusion has become false can only be deleted, and a tombstone comment beside the HP2.3 banner records what replaced it — a reader arriving from any of the five prose citations needs to find that out.  Its **negative twin** `answeredHeadContextIsServerDonation_false_of_orphan_head` is **kept** rather than retired as the row said: what it says has changed from a *prohibition* (why HP6 may not precede HP4) into a *fact about reachable states* (the coherence predicate is false on states the live removal now produces), which together with the predicate having no consumer (HP6.2) is exactly the warrant HP7 deletes it on.  Also swept: `cancelledCallerDonation?_none_below_the_cut`'s policy conjunct, the three constructor and constant docstrings, and the four prose citations of the deleted name.  Consumes HP6.7 | `SeLe4n/Kernel/IPC/Invariant/Defs.lean`, `SeLe4n/Kernel/IPC/Invariant/DonationPreservation.lean`, `SeLe4n/Kernel/Lifecycle/Invariant/CancellationReplyShape.lean`, `SeLe4n/Kernel/IPC/CrossCore/EndpointReplyDispatchInvariant.lean`, `SeLe4n/Kernel/IPC/CrossCore/EndpointReply.lean`, `tests/SmpCancellationSuite.lean` | M |
| HP6.9 | **The payoff.  LANDED v0.35.45**: `donationAccountingPreserved_atCallDepthThree` — on a three-frame stack a middle removal leaves the reservation owed outward and the pop that follows delivers it to the caller the surviving stack names.  `outer` is read off the **pre-state** frame below the cut, so no hypothesis hands the conclusion over; the head is resolved on the *post-removal* state against the pre-state `SchedContext`, which needs `removeCallerReplyFrame_getSchedContext?_eq` — a new framing lemma, stated with no distinctness hypothesis for the same reason HP6.7's is.  `tests/SmpIpcSuite.lean` §3.22 inverts from a COST witness to a PAYOFF witness in the same cut, keeping the in-order half — restated as an **AGREEMENT** rather than a contrast, since the two now coincide and that coincidence is the defect's closure — and gaining two **negatives** that spell the retired sever's values, so the assertions are known to discriminate rather than merely to pass (HP5.5's lesson).  It also measures the **second** pop: one pop leaves the reservation owed, the pop that answers the bottom frame delivers it `.bound` to its owner, which the sever could not reach at all.  §3.20's depth-two halves pass **byte-identically** and the golden trace is byte-identical, which is the measurement that the change is confined to depth ≥ 3.  Consumes HP6.8 | `SeLe4n/Kernel/IPC/Invariant/DonationPreservation.lean`, `SeLe4n/Kernel/IPC/Invariant/Structural/DualQueueMembership.lean`, `tests/SmpIpcSuite.lean` | L |

**Acceptance**: §3.22's assertions read the owner receiving its reservation, the
in-order contrast is unchanged, and §3.20's depth-2 halves pass byte-identically
— the measurement that the change is confined to depth ≥ 3.

### HP7 — The three stated hypotheses retire (4 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| HP7.1 | **LANDED v0.35.46, and it had already happened.**  HP4.4 (`v0.35.38`) took `answeredHeadContextIsServerDonation` out of the chain composite and its two fault-path composites in the cut that flipped the trigger, replacing it with the strictly weaker `replyFrameHeadIsBound` — so this row's own work was done three phases early, and verifying that is what it delivers: the predicate's remaining occurrences were its own definition, its two vacuity discharges, HP2.1's equivalence and prose.  The verification is the useful half rather than a formality, because a row that *reads* as outstanding is what makes a later reader re-derive it: `rg` over the comment-free code view puts the hypothesis in no theorem statement anywhere in the tree.  What this cut therefore does is **delete** it — the row below says on what warrant | `SeLe4n/Kernel/IPC/CrossCore/EndpointReplyDispatchInvariant.lean` | M |
| HP7.2 | **LANDED v0.35.46**: the verification the row asks for, run rather than reasoned, and it came back clean in both directions.  `replyDonationOwnerIsAnsweredCaller` has **no consumer** — HP6.2 (`v0.35.44`) retired `lockSet_endpointReplyRecvOnCore_size_le_seventeen`, its only one, because the merge that bound it (*the returned donation's owner is the answered caller*) occurs on **no** state the head-driven trigger reaches: the pair's second component is the thread the pop *unbinds*, which is running on the context while the answered caller is `.blockedOnReply`.  And `lockSet_endpointReplyRecvOnCore_size_le_eighteen` is already **unconditional**, HP6.2 having derived its exclusion structurally (`answeredReplyFrameAbove?_none_of_headContext`) where it used to take two of these facts as hypotheses.  Two things the row did not predict.  (1) **The sweep is where the work is**, and it is not "every other citation": a naive dead-symbol sweep over reference counts would have deleted eleven **live** `lockSet_*_size_le` bounds, which have zero textual consumers and are required *by name* by the Tier 1 `LockFootprintBoundCensus` and by Tier 3 anchors — so "unused" is measured over `scripts/lean_code_view.py --overlay` **minus what a gate consults**, which is now a project rule in `CLAUDE.md`.  (2) The sweep found a **Tier 0 gate red at HEAD**: `scripts/check_workstream_plan.py` had been failing since HP6 on two of this plan's own landing notes, which cite a later sibling narratively (`HP6.5`, `HP6.9`) where the gate — correctly, since no scanner can tell a mention from a consumption — reads a forward dependency.  Fixed by naming the artefact instead of the row, which is this project's own identifier rule one artefact over.  Consumes HP7.1, HP6.8 | `SeLe4n/Kernel/Concurrency/Locks/ResolvedFootprintBounds.lean`, `docs/planning/DONATION_POP_TRIGGER_PLAN.md` | M |
| HP7.3 | **LANDED v0.35.46**, and the row's arithmetic corrected: **nine** declarations are deleted, not three, and one of the "three facts" is not retired at all.  Deleted: the three stated coherence predicates (`replyDonationOwnerIsAnsweredCaller`, `replyStackHeadIsAnsweredReply`, `answeredHeadContextIsServerDonation`), the two vacuity discharges of the third, the scaffolding that consumed them (`replyStackHead?_none_of_answeredFrameAbove`, `donatedContextHeadsStack` with its vacuity lemma, HP2.2's `serverDonation_implies_answeredFrameHeadContext?`), HP2.1's `answeredFrameHeadContext?_implies_serverDonation`, HP2.3's orphan-head pair, and the binding-driven resolver `endpointReplyServerDonation?` itself.  **The fourth stated fact is LIVE**: `replyFrameHeadHolderDonation` (HP4.2's rename of `answeredHeadHolderDonation`) has twelve-plus consumers and is the one binding fact the trigger does not witness — its docstring claimed HP7 retires it, and that claim is corrected here rather than acted on.  So of the row's premise, two facts are *eliminated* (their content became HP2.4's derivations, which are anchored in Tier 3 precisely so a derivation nothing consults does not read like one nobody checked) and one is *migrated*.  **Three things the deletions cost**, each now a project rule in `CLAUDE.md`: a positive Tier 3 anchor on a deleted symbol must become a **negative** (a positive fails outright; worse, a `run_negative_check` on a deleted symbol passes forever, which is the tautological pin this project already retires), the *retired reading a witness needs* moves into that witness as a `private def` and nowhere else (`bindingDrivenReplyServerDonation?` in `tests/SmpCrossCoreReplySuite.lean`, beside HP5.5's `bindingDrivenCancelledCallerDonation?` and `FrozenOpsSuite`'s `FO-042`), and every deletion leaves a **tombstone** naming what replaced it, because a reader arriving from a citation the sweep missed needs somewhere to land.  `answeredHeadContextIsServerDonation_false_of_orphan_head` is deleted with the predicate it negates — HP6.8's row kept it as "the warrant HP7 deletes it on", which is exactly what this cut spends it on.  Consumes HP7.2 | same, plus `SeLe4n/Kernel/IPC/CrossCore/EndpointReply.lean`, `SeLe4n/Kernel/IPC/CrossCore/EndpointReplyDispatchInvariant.lean`, `tests/SmpCrossCoreReplySuite.lean`, `scripts/test_tier3_invariant_surface.sh` | M |
| HP7.4 | **VACUOUS, verified v0.35.46** — and recorded as vacuous rather than closed, because the two read differently to the next person.  Neither pack ever carried one of the three facts as a field: `syscallDispatchQuiescence` has eleven (`reachable`, `capOnly`, `callerShape`, `mintBadgeValid`, `sendStage`, `callStage`, `callNotSelfRendezvous`, `recvStage`, `replyStage`, `signalNoBoundTarget`, `replyRecvStage`) and `checkedSyscallDispatchQuiescence` two (`base`, `declassifySignalNoBoundTarget`), and what the two reply-stage fields carry are the **live** facts — `replyFrameHeadHolder?`, `replyFrameHeadHolderDonation`, `passiveServerIdleAllowed`, `replyStackOuterCallerValid`, `objects.invExt`.  HP4.2/HP4.4 re-keyed those conjuncts onto the head-driven reading **in the cut that flipped the trigger**, which is the correct place for them (a pack field stated at a state its own step no longer runs on is a claim about a different state), so there is nothing left here to shed and the inhabitation witnesses need no re-run.  The phase's acceptance criterion is corrected accordingly: the hypothesis count fell at HP4, not here, so the checkable claim is the *dethreading gate's* — zero post-state conjuncts, bundle count 177, every prose site holding it updated — which this cut re-ran green.  Consumes HP7.3 | — (no change required) | L |

**Acceptance** (corrected at `v0.35.46`, when HP7.4 measured out vacuous):
`check_ipc_invariant_dethreading.py` reports zero post-state conjuncts with its
bundle count updated in every prose site it holds; the three retired predicates
occur in **no theorem statement** anywhere in the comment-free code view; and
each retired symbol's Tier 3 anchor is a **negative** rather than a positive, so
a reintroduction fails rather than a deleted pin reporting PASS over nothing.
The row's original criterion — *the dispatch payoff's hypothesis count falls* —
was not met and could not be: HP4 re-keyed those pack fields in the cut that
flipped the trigger, which is where the count fell.  Recording that rather than
restating the criterion is the point: a criterion nothing can satisfy reads, to
the next person, exactly like one nobody checked.

### HP8 — The frozen mirror (4 sub-tasks)

`FrozenOps` is reached by neither library root and must stay in step (PR #895
review, `v0.35.12`).

**The trigger half already landed, as HP4.7.** §3.8.8 says why: HP4 is the cut
that makes the live `.reply` operation head-driven, so that is the cut in which a
binding-driven mirror of it becomes a second answer to one question. What remains
here is the **splice**, whose divergence HP6 creates.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| HP8.1 | **LANDED v0.35.47**, and *replacing* the frozen detach rather than sitting beside it — the row said "beside", which would have been two readings of one question with the answers already known to differ, the shape HP4.7 rejected for the trigger.  `frozenSpliceFrameBelow?`, `frozenSpliceReplyFrameStores` (three stores), `frozenSpliceReplyFrameOut` and `…OrSelf`, each clause for clause with its live counterpart; `frozenDetachReplyFrameAbove{,OrSelf}` are **deleted**, which is HP6.1's rule discharged (the name and the body move together, so a `frozenDetach…` whose body splices reads as a drift where the sever's name read as the schedule).  `frozenSpliceReplyFrameStores_eq_sever_of_no_frame_below` is the definitional equality that makes every pre-HP8 scenario answer as it did | `SeLe4n/Kernel/FrozenOps/Core.lean` | M |
| HP8.2 | **LANDED v0.35.47**: `frozenEndpointReply` runs `frozenSpliceReplyFrameOutOrSelf`, before the consume, in the order the live spine uses.  Its pop was already head-driven (HP4.7).  Consumes HP8.1, HP6.4 | `SeLe4n/Kernel/FrozenOps/Operations.lean` | M |
| HP8.3 | **LANDED v0.35.47**: the registry carries **three** frozen splice entries where the sever had two — the store step is registered on its own, as the live `spliceReplyFrameStores` is, because it performs the writes with none of the removal's resolution or validation.  Each is a `.mirrors` entry naming the live counterpart of the same shape, so the store step's chain terminates in a stating entry two hops out (through the live `.halfStep`) rather than one, which the registry's own closure check follows.  The census reports **24** write sites, 6 frozen mirrors.  Consumes HP8.2 | `SeLe4n/Testing/ReplyStackWriteCensus.lean` | M |
| HP8.4 | **The witness, added while implementing — LANDED v0.35.47.**  Not in the row list, and it is what the phase turns on: every scenario this surface carried passed **byte-identically** when the splice landed, because FO-031 and FO-041/042 all sit on stacks of depth ≤ 2, where a two-frame stack's lower frame is its bottom and both policies write the same value.  That is HP5.5's lesson on this surface — *a sweep for fixtures that would break is not a sweep for fixtures that would exercise* — so HP8 would have landed untested on its own green suite.  `FO-043` is a three-frame stack with the answered caller holding the **middle** frame, and it is mutation-verified in both directions: the pre-HP8 sever fails it while every control still passes.  Two things it measured rather than assumed.  The splice's **third** store (`rid.prev := none`) is **not observable through the composite** — with it deleted the whole suite still passes, because the `Reply.consumed` that follows clears the same field on a frame heading nothing — so a composite assertion about the cut frame's `prev` tests `consumed`, not the splice, and reads as coverage while asserting nothing.  The last half therefore drives `frozenSpliceReplyFrameOut` **directly**, beside the live primitive, which is the only place that store's deletion fails.  And the store stays load-bearing regardless: it is seL4's `reply_unlink` downward half, and it becomes observable the moment `consumed` changes | `tests/FrozenOpsSuite.lean`, `scripts/test_tier3_invariant_surface.sh` | M |

**Acceptance** (corrected at `v0.35.47`): `lake exe frozen_ops_suite` passes all
differential scenarios — **and at least one of them must be a stack of depth ≥ 3**,
because every shallower shape agrees under both removal policies, so a green suite
over depth ≤ 2 is evidence about the fixtures rather than about the flip.  The row
list's original criterion ("passes all differential scenarios, including the
agreement between the frozen reply and the live one") was met by the suite
*before* HP8 landed, which is what makes it the wrong criterion.

### HP9 — Witnesses, anchors, documentation, closure (5 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| HP9.1 | **LANDED v0.35.48**: `tests/SmpIpcSuite.lean` §3.23, a four-frame stack built by a third live `donateSchedContext`, with the cut at the **third** frame from the bottom — cutting the second would leave one frame below and measure §3.22 again.  Three things it establishes.  (1) **The transitive half**: the splice writes `above.prev := some below` and leaves `below`'s *own* `prev` alone, so at depth 3 "the stack reconnects" and "the frame beneath the reconnection survives" are one statement and §3.22 cannot separate them; at depth 4 the untouched bottom frame is a proposition of its own.  (2) **Three pops**, where §3.22 needs two: the reservation travels holder → second frame's caller → bottom frame's caller → `.bound` on its owner, with every intermediate caller left unbound.  (3) **What the witness does NOT catch, measured rather than claimed**: a code mutation of the splice's *stores* never reaches it, because `spliceReplyFrameStores_cases` states the three stores exactly and both candidate mutations — the full sever, and a reconnection that clobbers the frame below's own downward link — fail to **elaborate** (four errors each).  So the store shape is pinned by a theorem and this scenario's subject is the composition, which no theorem states; the docstring says so, rather than letting a reader infer a mutation story the cut does not have | `tests/SmpIpcSuite.lean` | M |
| HP9.2 | **LANDED v0.35.48, and mostly as verification** — the anchors this row asks for went in with the cuts they belong to rather than being deferred here, which is the right place for them: HP6.5 pinned all three splice stores positively, the policy constant in **both** directions, `removeCallerReplyFrame_splices_reciprocally` and the depth-3 payoff; HP7 replaced the binding-driven trigger's per-definition negatives with one tree-wide over `SeLe4n/`, since the resolver is deleted; HP8 added the frozen family's, including a negative refusing the sever's names tree-wide; and the recipient guard already carried a positive *and* a token-preserving negative (`serverTid` substituted for `originalOwner`).  Adding parallel anchors here would be the duplication this project retires, so what this row contributes is the depth-4 witness's own anchors — and one it **retired after writing it**: a standalone check that the scenario is *called* duplicated the WS-OD contiguous-run anchor, which names every runner of that group **in order** and which is what caught this insertion, exactly as its own comment says it caught OD3.1's and OD4.1's.  A witness defined and never run is the tautological pin one artefact over, and that relation was already owned; a new scenario in the group extends that anchor rather than adding a sibling.  The cut also repaired an anchor of its own that never matched: `HOME .bound. to` reads the backtick with its `.` and then needs a literal `bound`, so the assertion it names begins `.bound` and the pattern was a **broken** anchor, not a passing one — found by running it rather than by reading it | `scripts/test_tier3_invariant_surface.sh` | M |
| HP9.3 | **LANDED v0.35.48, with this row's own premise corrected.**  It said "table C row closed, and its closing paragraph restored now that the exception is gone" — written before `v0.35.42` found the **depth-2** loss, so it is false: the row cannot close while the defect it names is live, and closing it would corrupt exactly the artefact RR8.4's hand-off check reads.  The row stays **open** with HP10 as owner and its depth-≥ 3 half recorded as earned.  The rest of the documentation landed incrementally with HP6, HP7 and HP8 rather than in one sweep at the end — each cut swept its own citations, which is what kept the dead-citation classes from accumulating — so what this row does is verify that and add HP9's own: §3.23 in the spec, the acceptance boxes marked MET, and box 10 struck through rather than deleted, because a reader arriving from the old text needs to find out why | as listed | M |
| HP9.4 | **LANDED v0.35.48**: the three verified upstream facts are recorded **beside the code they justify** (`donationRecipientAcceptable`'s docstring) rather than only in a plan — `reply_pop` donates only under `if (tcb->tcbSchedContext == NULL)`, the pop's trigger is `call_stack_get_isHead(reply->replyNext)`, and `reply_remove`'s non-head branch writes **zero** into the frame above, so upstream severs and this kernel's splice is an *improvement on* it.  Each names the revisions read (`master`, `13.0.0`, `12.1.0`, `12.0.0`, `11.0.0`), because `v0.35.14` asserted the opposite, quoted a line that exists in no release, and swept that error across nine prose sites and three docstrings that had been right | `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` | S |
| HP9.5 | **LANDED v0.35.48**: `check_workstream_plan.py`, `check_claim_evidence_citations.py`, `check_lock_ceiling_figures.py`, the version bump, the `CHANGELOG.md` entry and `test_docs_sync.sh`.  Consumes HP9.1–HP9.4 | `scripts/`, `CHANGELOG.md` | S |

**Acceptance**: see §8 — where **box 10 is struck through as wrong** rather than
ticked, for the reason HP9.3 records.

### HP10 — The reservation's origin, so the return does not depend on chain connectivity (10 sub-tasks)

**Why this phase exists, and why the splice does not subsume it.**  HP6 fixes the
accounting at reply-stack depth >= 3 and **provably cannot** fix depth 2:
`severAtCut` writes `above.prev := none`, `spliceOutTheCut` writes
`above.prev := rid.prev` — the *cut* frame's own downward link — and when the cut
frame is the **bottom** of its stack its `prev` is `none`, so the two policies
write the same value.  That is exactly what HP6.9's "§3.20's depth-two halves pass
byte-identically" measured, and it passed.  So after HP6 a client that
delegates its reply capability to a confederate still loses its reservation at
depth 2: the delegate answers the client out of order, the client's frame leaves
the stack, and the later in-order pop finds the remaining frame at the bottom and
binds the reservation to the **intermediate** caller.

**The debt register understates the defect, and HP10.2 fixes that first.**  The
`REGISTERED_DEBT.md` table C row is headed "at reply-stack depth >= 3", and
`tests/SmpIpcSuite.lean` §3.22 measures that case.  §3.20 exercises the depth-2
*structural* outcome — the frame above loses its `prev`, the answered frame goes
free — and asserts nothing about where the reservation ends up, so the depth-2
accounting loss is in the tree's reach and in neither its witnesses nor its
register.  A reader of the row today would conclude HP6 closes the defect.  It
does not.

**The cause is not MCS and not the removal policy.**  It is that the recipient is
derived from **stack reachability**, so removing a frame changes who the kernel
believes owns the context.  seL4-MCS derives it the same way — `reply_pop` donates
to the answered frame's own `replyTCB` — so it has the same loss at depth 2 and no
remedy for it; this phase is therefore an improvement on upstream at every depth
rather than parity at any.

**The fix is one field and one arm.**  `SchedContext.donationOrigin : Option
ThreadId` records the thread that owned the reservation when it first left, and
the pop's bottom-of-stack arm binds *that* thread when it is an acceptable
recipient, the answered caller otherwise.  In every in-order unwind the two are
the same thread, so nothing that holds today changes; they differ exactly when
frames left the stack, which is the loss, at any depth.

**Five things this phase decides rather than inherits.**

1. **The origin is history, not an invariant.**  No `donationChainWellFormed`
   clause relates it to the stack: "the origin is the bottom frame's thread, or a
   thread whose frame was removed" has an unstateable second disjunct, and a
   clause carrying only the first would be *false* on precisely the states this
   phase exists for.  What makes acting on it safe is the pop's own guard
   (`donationRecipientAcceptable`), so the field is a hint the kernel validates
   rather than a fact it trusts — stated in the docstring, with a Tier 3 negative
   refusing a chain conjunct over it.
2. **Thread-id reuse is the one real hazard, and it is closed structurally.**  The
   kernel writes the origin from the donor's own identity, so it can never name a
   thread that did not own the reservation — *unless* that thread is destroyed and
   its id reused, after which a stale origin would hand a reservation to an
   unrelated thread.  `lifecyclePreRetypeCleanup` therefore clears the origin of
   any context naming the retyped thread, exactly as it already refuses a context
   that still heads a stack.  HP10.5 owns it and is ordered **before** the arm
   that reads the field, which is this project's rule that a transition goes live
   only after the proofs and guards that cover it.
3. **The footprint grows and the ceiling moves.**  Redirecting the recipient
   changes *which* TCB the pop writes, and the resolver can answer either thread,
   so both reply footprints must declare the origin's TCB as well as the answered
   caller's: `maxLockSetSize` 23 -> 24, with the RPi5 per-lock
   `admissibleCriticalSection` and the uniform envelope moving with it.  A
   footprint that omits a written object is false, and this project rates that
   worse than a wide one — but the cost is stated in the row rather than
   discovered in it.
4. **It is a strengthening with no state on which it is worse than today.**  The
   fallback is the current recipient, so `_eq_legacy_of_no_origin` makes every
   existing result a case split whose `none` branch is the pre-HP10 proof
   verbatim, and a stale or unacceptable origin degrades rather than clobbers.
5. **It lands in WS-HP, not WS-CB.**  WS-CB restructures what a `SchedContext`
   *is* (a server containing members) and will add fields of its own, so folding
   this in looks economical.  Two things decide against it: WS-CB is PLANNED with
   no sub-task started, so folding a depth-2 correctness fix into it defers the
   fix indefinitely; and WS-CB's own plan requires every generalising cut after
   CB1 to carry "the model is unchanged on states without servers", which a
   flat-model fix landing first is strictly easier to satisfy than one entangled
   with servers.  WS-CB inherits the field.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| HP10.1 | **LANDED v0.35.49 — the measurement, and it re-cut the phase.**  Measured over `scripts/lean_code_view.py --overlay`, OD2's `scReply` precedent is **198 occurrences across 27 modules** (458 / 60 over the raw tree, which counts docstrings); this row's own registration text said *264 references across 34 files*, which matches neither figure at neither scale, so the precedent is **re-stated** rather than cited.  Most of it is the chain machinery `scReply` enabled, not the field: the surfaces a *new* `SchedContext` field must actually touch are **six**, and two of them refuse it structurally — `bootSafeSchedContextCheck` and `schedContextReferencesReservedIdleSlot` both destructure the constructor, so they fail to elaborate until the field is classified, which is the PR #889 round-8 pin working for us.  The four that must be extended by hand are `BEq SchedContext` (field-wise `beq`), `projectKernelObject`'s `.schedContext` arm, and the two reply footprints, whose arities go 11 → 12 and 23 → 24.  **The freeze half is vacuous**: `freezeObject` on `.schedContext` is a pass-through by `rfl` (`freezeObject_schedContext_passthrough`) and `FrozenKernelObject.schedContext` carries the live record, so the field row's "`Model.freeze` mirror" clause has no subject — recorded here rather than discovered in that row, the treatment HP7.4 got.  **And the measurement found a row this phase did not have**, which is what the row exists for — the frozen reply composite's own arm, which has its own row below | this plan | S |
| HP10.2 | **LANDED v0.35.49, and this row's premise was overtaken too.**  It said §3.20 *gains* the accounting halves it lacks; measured at HEAD it already had both — `COST: the original owner is left unbound, having lost its reservation` and `COST (contrast): an IN-ORDER unwind leaves it owed outward, not owned`, both passing, added when the depth-2 loss was found at `v0.35.42` rather than deferred to this phase.  So the loss was already measured before anything is built to fix it, which is what this row exists to guarantee.  What it *did* find is a **labelling** defect of the kind this project treats as a claim at the wrong unit: the assertion that the pop settles the context on `pushDonor` — a thread strictly **inside** the chain — was labelled `PAYOFF` alone, because as WS-RM's payoff the pop succeeding is the whole point, while as HP10's cost the *thread it names* is.  One expression, two facts, and a reader taking the label at face value reads half of it.  Relabelled `PAYOFF/COST`, with the two roles stated — not duplicated under a second label, which would be the shape this file retires.  What HP10 inverts is the thread that row names, not whether the pop succeeds | `tests/SmpIpcSuite.lean` | M |
| HP10.3 | **LANDED v0.35.49 — the field, inert.**  `SchedContext.donationOrigin : Option ThreadId` (it lives in `SeLe4n/Kernel/SchedContext/Types.lean`, not `Model/Object/Structures.lean` as this row guessed), erased by `projectKernelObject` in the same cut and pinned by `projectKernelObject_schedContext_donationOrigin_invariant`; refused on a boot SchedContext by `bootSafeSchedContextCheck`, with the soundness bridge's clause and `schedContextReferencesReservedIdleSlot` both extended — the second because the origin is a `ThreadId` and so can name a reserved idle thread.  **Both boot arms refused to elaborate until the field was classified**, which is the PR #889 round-8 constructor-arity pin working exactly as intended and is why HP10.1 counted them as *structural* rather than as work.  `BEq SchedContext` carries it too, so a record or clear is visible to every `==` comparison, the frozen differential included.  **The `Model.freeze` half is vacuous, as HP10.1 measured**: `freezeObject` on `.schedContext` is a pass-through by `rfl` and `FrozenKernelObject.schedContext` carries the live record, so there was nothing to mirror.  Consumes HP10.1 | `SeLe4n/Kernel/SchedContext/Types.lean`, `SeLe4n/Kernel/InformationFlow/Projection.lean`, `SeLe4n/Platform/Boot.lean` | L |
| HP10.4 | **LANDED v0.35.49 — the write, the clears, and two loan-enders this row did not name.**  `donateSchedContext` records `donationOrigin := some clientTid` on a **first** push only, through `donationFirstPush` — a *named* definition rather than an inline test, because the operation branches on it and `_ok_storeChain` (the only description of the operation) must name the same question.  An onward push leaves the field, which is what makes it the origin rather than the immediate donor; the immediate donor is already `.donated scId owner`, and a field recording it would be the duplicate this project retires.  **The row named three loan-enders and the tree has five**: the pop's bottom arm (`newOwner?.isNone` — exactly where `donationReturnBinding` yields `.bound`), `schedContextBind`, `schedContextUnbind`, **and `cancelBoundDonation` / `cancelBoundDonationOnCore`**, the suspend path's unbind, which asks the identical question ("this context stops being owned") and would have diverged from `schedContextUnbind` by a field.  The two are `rfl`-bridged at the boot core, so they could not have differed in any case — but the single-core spelling is reached from `suspendThread`, and an origin surviving a suspend would be carried into whatever binds the context next.  Three mechanical consequences: the push's and the pop's projection hops are **one** three-field lemma (`projectKernelObject_schedContext_donationWrite_invariant`, widened rather than duplicated — a `…PushWrite…` sibling would have been the shape this project retires); the chain-preservation lemmas take the origin as a **parameter**, in the same position and for the same reason as `serverTid` / `originalOwner`, since those proofs read `scReply` and nothing else; and `returnDonatedSchedContext_eq_legacy_of_none` gains `hNoOrigin` as a hypothesis rather than growing its right-hand side, which is the precedent HP4.6 set in that theorem's own docstring.  The golden trace is **byte-identical** and all four donation suites are green, which is the measurement that the write is inert: nothing reads the field yet.  Consumes HP10.3 | `SeLe4n/Kernel/IPC/Operations/Endpoint.lean`, `SeLe4n/Kernel/SchedContext/Operations.lean`, `SeLe4n/Kernel/Lifecycle/Suspend.lean`, `SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean` | L |
| HP10.5 | **LANDED v0.35.49 — the id-reuse closure, and it cost a pack clause.**  `clearDonationOriginReferences` (in `Lifecycle/Operations/Cleanup.lean`, not `ScrubAndUntyped.lean` as this row guessed) is a write-set-honest fold in the shape `removeFromAllEndpointQueues` uses, and it is wired as `cleanupTcbReferences`'s **fourth sweep** rather than beside the donation return in `lifecyclePreRetypeCleanup`: a stale origin *is* a dangling reference to a destroyed thread, which is what that function is for, and unlike the donation return it needs no error channel — there is nothing to refuse.  §3.24 is the witness, with **two** negatives: scrubbing a *different* thread must leave the origin standing, because a sweep that cleared unconditionally would satisfy every payoff and destroy the field's whole purpose.  **What the row did not predict is the obligation**: `cleanupTcbReferences` is claimed to be an *identity* under `retypeTargetDetached`, and that claim is now false unless the pack says no context records the target as an origin — which its other clauses do **not** imply, and must not: a thread that lent its reservation and had its frame removed is still the recorded origin while it is suspended and destroyed, which is exactly the state the sweep exists for.  So `tcbNotDonationOrigin` joins the pack as a caller obligation in the class of `notSc` and `tcbNotDonated` — the revoke-and-suspend-before-retype contract, one field further — and the runtime sweep is what makes a *violation* safe rather than what makes the clause redundant.  Ordered before the arm that reads the field, per this project's rule that a transition goes live only after the guards that cover it.  Consumes HP10.4 | `SeLe4n/Kernel/Lifecycle/Operations/Cleanup.lean`, `SeLe4n/Kernel/Lifecycle/Operations/CleanupPreservation.lean`, `SeLe4n/Kernel/IPC/Invariant/DispatchArmPreservation.lean`, `tests/SmpIpcSuite.lean` | M |
| HP10.6 | **LANDED v0.35.50 — the footprint member and the ceiling, declared ahead of the arm, and the row found seven dead bounds.**  `donationOriginRecipient?` is the resolver — the pop's own bottom arm (`replyStackOuterCaller? = .ok none`), the context's recorded origin, and HP4.6's recipient guard applied to the **candidate** so a stale origin falls back rather than refusing — and both reply footprints declare it in write mode, with `_originRecipient_write_mem` at full arity and `lockSet_endpointReply{,Recv}OnCore_covers_originRecipient` resolved, because declaring a member is not proving the transition writes it.  `maxLockSetSize` **23 → 24**, so the RPi5 tick admits **13 µs** per lock and the uniform 60 µs envelope is **4320 µs**; the canonical sentence moved at all five pinned sites and `check_lock_ceiling_figures.py` derived every one of them.  **The reachable figures did not move**, and that is a theorem rather than a hope: the origin member is live only where the pop is at the bottom of its stack, and there the two below-head members are both absent (`replyStackBelowHead?_of_originRecipient`), so a reachable footprint trades two members for one — `…_size_le_twenty` and `…_size_le_eighteen` are unchanged, now by a case split on the redirect, and `tests/LockSetSuite.lean` exhibits the redirecting shape at **seventeen**, one *narrower* than the popping one.  **The member is live, not absent**, and that had to be corrected in this row's own first draft: HP10.4 records an origin on every first push, so a *depth-1* donating reply resolves it to `some` — and there the recorded origin **is** the answered caller, so `insertOrMerge` collapses it and the declaration is unchanged, which is the honest form of "inert".  It is a distinct key exactly on the out-of-order removal this phase exists for, which is the state the flip's pop writes a different TCB on; `tests/DeadlockFreedomSuite.lean` asserts the depth-1 equality and the negative that the merge is a property of *that* coincidence rather than of the member.  **What the row did not predict is the deletion**: HP6.2 retired the resolved seventeen and left **seven** parametric feeders orphaned — the five `_of_owner_eq_target` bounds, whose merge HP6.2 established is *false* on every state the arm reaches, and the two `_of_no_donation` corners — with no consumer in the tree.  A sharp figure resting on a refuted hypothesis is worse than no figure, so they are deleted with a tombstone, and Tier 3's positive anchor on `_size_le_twentytwo_of_owner_eq_target` is now a tree-wide negative.  Consumes HP10.5 | `SeLe4n/Kernel/IPC/Operations/Endpoint.lean`, `SeLe4n/Kernel/IPC/CrossCore/EndpointReply.lean`, `SeLe4n/Kernel/Concurrency/Locks/{LockSet,LockSetTransitions,Deadlock,ResolvedFootprintBounds}.lean`, `SeLe4n/Kernel/Scheduler/Operations/PerCoreWcrt.lean` | L |
| HP10.7 | **LANDED v0.35.51 — the arm flips, and the guard was not sufficient.**  `replyDonationRecipient` is the one definition all three reply-path pops read: the recorded origin where HP10.6's resolver answers one, the answered caller otherwise, and the identity wherever the resolver is silent (`replyDonationRecipient_eq_of_no_origin`), so every pre-flip result carries across as a case split whose `none` branch is the old proof verbatim.  The SCOPE constraint the row was given held: the redirect is in `applyReplyDonation`, `applyReplyDonationOnCore` and `replyRecvPopDonation` and **not** in the shared `returnDonatedSchedContextResolved`.  **What the row did not predict is that HP10.6's guard is not sufficient**, and this is the cut's substantive finding rather than a tightening: `donationOwnerValid` requires the owner of every live `.donated` binding to be `.unbound` **and** `.blockedOnReply`, so a thread can pass `donationRecipientAcceptable` while another thread's binding names it as the owner it waits on — and writing `.bound scId` there falsifies that clause.  Reachable with ordinary syscalls: a client answered out of order is woken `.ready` and `.unbound`, and nothing stops it binding a second reservation and Calling with it while the first is still parked on a server whose stack records it as the origin.  `donationOriginRebindable` is the O(1) contrapositive — a thread not reply-blocked is named as owner by none (`donationOriginRebindable_no_owner`) — and a still-blocked origin falls back rather than refusing, which is why HP10.6 put the guard on the *candidate*.  **The bundle needed the recipient split from the binding's recorded owner**: one thread used to play three roles, and exactly one conjunct argument cared, so `…_of_except_redirected` is where `hNoOwner` lands — supplied by the new guard, which is the measurement that it is the right guard.  **And the migration's DESTINATION moved with the recipient**: `ownerHome` was the answered caller's home, so redirecting the reservation without redirecting the replenish queue would have left `replenishQueueAffinityConsistentOnCore` false from the instant it committed; `replyDonationRecipientHome` mirrors HP4.3's source resolver, all three readers take it, and `hOwnerHome` is quantified over the trigger's answer as `hHolderHome` is.  Witness `tests/SmpIpcSuite.lean` §3.25: a different thread on a different core, each guard's negative paired with a control that the *other* guard admits that state.  The golden trace is byte-identical.  Consumes HP10.6 | `SeLe4n/Kernel/IPC/Operations/Endpoint.lean`, `SeLe4n/Kernel/IPC/Operations/Donation/Primitives.lean`, `SeLe4n/Kernel/IPC/CrossCore/EndpointReplyDispatch.lean`, `SeLe4n/Kernel/IPC/Invariant/{Defs,DonationPreservation}.lean`, `SeLe4n/Kernel/API.lean` | L |
| HP10.8 | **LANDED v0.35.52 — the frozen arm flips, and running it beside the live one found two defects.**  `frozenReplyDonationRecipient` mirrors the live redirect clause for clause, over `frozenDonationOriginRecipient?` and `frozenDonationOriginRebindable`; the frozen store carries the live `SchedContext` record, so there was no field to add.  **The row's *same cut* requirement was missed and then honoured**: HP10.7 landed alone at `v0.35.51`, which opened exactly the window the row names — `frozenBranchOperationChecked .endpointReplyToBlockedCaller = true` claims the two programs are run beside each other, and for one cut they disagreed on the states this phase exists for — and closing it was the first thing this cut did.  **Defect one, found by FO-044 and not by a review**: the frozen return did not clear `donationOrigin` on the bottom arm, because HP10.4 landed the field's clears on the live side only.  A field added to a *shared* record is a sweep of both surfaces; nothing could see the gap until a frozen scenario recorded an origin at all.  **Defect two is a retracted claim**: HP10.6 said this member is live at depth 1, and it is not — the footprint resolves on the syscall's pre-state, where the answered caller is `.blockedOnReply`, so HP10.7's rebindability guard refuses it there.  That is behaviourally sound (the transition then redirects to the answered caller, whose TCB the footprint declares unconditionally) and it leaves the footprint and the transition resolving at **different states**, which is registered rather than assumed away.  FO-044's two halves are an origin that differs from the answered caller and one that does not; the second is decisive because the resolver *declines* there and the fallback lands on the same thread, so a selector firing unconditionally passes every outcome assertion and fails the resolver one.  Consumes HP10.7 | `SeLe4n/Kernel/FrozenOps/{Core,Operations}.lean`, `tests/FrozenOpsSuite.lean` | L |
| HP10.9 | **LANDED v0.35.53 — the payoff, and the decisive comparison is not a mutation.**  `donationAccountingPreserved_atCallDepthTwo` derives the reachability answer from the removal (`replyStackOuterCaller? st' scId = .ok none` is a *conclusion*, through the new sever-direction sibling `removeCallerReplyFrame_clears_prev_of_bottom_frame`) and hypothesises the two guards, because one of them **cannot** be derived: `donationOriginRebindable` is *false* at the pre-state — the owner is `.blockedOnReply` on exactly the reply being answered — and becomes true at the wake `endpointReplyOnCore` performs before the removal.  Tier 3 negatives refuse hypothesising either derived fact, and the sibling's `above ≠ rid` is derived from bottom-ness rather than assumed.  §3.20's halves inverted from COST to PAYOFF and now measure the **live `.reply` spine**: they measured `returnDonatedSchedContextResolved` directly, which was an accurate proxy for the pop while nothing redirected and is a proxy that *omits* the redirect since HP10.7.  **What the row did not predict is that no mutation is available**: every mutation of the production code — the origin write, the resolver, the three pops, the dispatch's recipient — fails to **elaborate** rather than failing the suite, which is §3.23's situation with the splice's store shape.  So `replyRemovalOutcome` takes the chain as a *parameter* and is applied twice, to a chain whose first push recorded an origin and to `pushStore`'s, which predates HP10.4 and records none: one function, two chains differing in exactly one field, opposite outcomes.  **And it found that HP10.4's production write had never been measured** — every fixture that carried an origin set the field by hand, so `pushOwnerStore` is `pushStore` with the first push undone and `replyRemovalChain` runs the live push *twice*, asserting both directions (a FIRST push records, an ONWARD push preserves) and that the first push reproduces `pushStore`'s own shape.  The depth-three payoff (§3.22, §3.23) is byte-identical and so is the golden trace, which is the measurement that this phase is confined to the reachability gap — *structurally* rather than luckily, since at depth ≥ 3 the pop sits at a `some` arm where `replyDonationRecipient_eq_of_outer_some` makes the redirect the identity by theorem.  One mechanical note: a Tier 3 anchor in this cut lost the closing quote of its `bash -lc '…'` argument, so it swallowed the following lines and **never decided**; `bash -n` passes and the gate prints PASS, the mutation harness reported it as a negative that would not fire, and `check_anchor_consistency.py` refuses it by name for its own stated reason.  Consumes HP10.8, HP10.2 | `SeLe4n/Kernel/IPC/Invariant/DonationPreservation.lean`, `SeLe4n/Kernel/IPC/Invariant/Structural/DualQueueMembership.lean`, `tests/SmpIpcSuite.lean` | L |
| HP10.10 | **Closure**: the debt row retires and the claim-set constraint lifts in full — a completed call chain returns the client's reservation at *every* depth, which is a claim neither this kernel nor seL4-MCS can make today — with the spec, the claim index and the GitBook mirror saying so.  Consumes HP10.9 | `docs/REGISTERED_DEBT.md`, `docs/spec/SELE4N_SPEC.md`, `docs/CLAIM_EVIDENCE_INDEX.md`, `docs/gitbook/12-proof-and-invariant-map.md`, `CLAUDE.md`, `AGENTS.md` | M |

## 7. What every cut in this workstream must run, in order

```bash
source ~/.elan/env
lake build                                  # production closure
lake build SeLe4n.Platform.Staged           # staged modules CI builds
./scripts/test_smoke.sh --continue          # tiers 0-2 + rust + docs sync
./scripts/test_full.sh --continue           # adds tier 3 invariant surface
```

Per-phase, beyond the tiers:

- **HP1–HP2**: `lake build SeLe4n.Kernel.IPC.Operations.Endpoint`,
  `lake build SeLe4n.Kernel.IPC.CrossCore.EndpointReplyDispatchInvariant`.
- **HP3**: `lake build SeLe4n.Testing.LockFootprintBoundCensus`,
  `python3 scripts/check_lock_ceiling_figures.py`, then
  `lake exe deadlock_freedom_suite`, `lake exe lock_set_suite`,
  `lake exe smp_wcrt_suite`, `lake exe smp_scheduler_suite`.
- **HP4–HP6**: `lake exe smp_cross_core_reply_suite`, `lake exe smp_ipc_suite`,
  `lake exe smp_cancellation_suite`, `lake exe smp_information_flow_suite`,
  `lake exe fault_handling_suite`; and the golden trace compared byte for byte.
- **HP7**: `python3 scripts/check_ipc_invariant_dethreading.py`.
- **HP8**: `lake exe frozen_ops_suite`,
  `lake build SeLe4n.Testing.ReplyStackWriteCensus`.
- **HP9**: `python3 scripts/check_workstream_plan.py`,
  `python3 scripts/check_claim_evidence_citations.py`,
  `./scripts/bump_version.sh <version>`, `./scripts/test_docs_sync.sh`.

## 8. Acceptance gate

Every box is ticked by a machine-checked artefact or an executed run, never by
a document existing.

1. The reply path's pop fires on **head-ness of the answered frame**, and a
   Tier 3 negative refuses the binding-driven spelling in either spine (HP4.1,
   HP9.2).  **MET** at `v0.35.38`, and strengthened at `v0.35.46`: HP7 deleted
   `endpointReplyServerDonation?` outright, so the negative is tree-wide over
   `SeLe4n/` rather than per definition — there is no binding-driven spelling left
   to refuse in one spine and miss in the other.
2. `spliceReplyFrameOut_eq_sever_of_no_frame_below` holds definitionally, so
   every depth-≤ 2 result is the pre-HP proof verbatim (HP6.3).  **MET** at
   `v0.35.45`; the row number was HP6.2, which is the footprint repoint.
3. The two triggers are proved equivalent on every state satisfying the chain
   invariant, and the theorem that the splice breaks that equivalence exists —
   so HP6's position after HP4 is machine-checked rather than asserted
   (HP2.1, HP2.3).  **MET** at `v0.35.36`, and **its artefacts are now gone —
   deliberately.**  Read at `v0.35.48`, every name this box cites survives only as a
   tombstone comment: HP6.8 deleted `severAtCut_pop_leaves_no_head` because its first
   conjunct was the policy constant at the old value, and HP7 deleted HP2.1's
   equivalence with the binding-driven resolver it was stated over.  That is the
   intended lifecycle of an **ordering pin**: it existed to make the sequence HP4 →
   HP6 a machine-checked fact *while the ordering was still ahead*, and once the
   ordering was taken its subject no longer exists — a theorem whose conclusion has
   become false, and an equivalence over a deleted definition, can only be retired.
   So this box is not re-verifiable by grep at HEAD, and saying so is the point: the
   evidence is the two cuts at `v0.35.36`, and the tombstones name what replaced each
   (the HP2.4 derivation family, and the splice's own `…_cases`).  A box whose
   artefacts a later phase consumes must record that, or it reads exactly like a box
   nobody checked.
4. **`donationAccountingPreserved_atCallDepthThree`**: on the depth-3 witness a
   middle removal leaves the reservation owed outward and the later pop
   delivers it to its owner (HP6.9 — the row number was HP6.7, which is the
   reciprocity fact it rests on).  **MET** at `v0.35.45`, with §3.22 inverted from
   COST to PAYOFF, the second pop measured, and the golden trace byte-identical.
   This box also said *§3.20's depth-2 halves are unchanged*, and that clause is
   **superseded at `v0.35.53`** rather than false: it was HP6.9's own measurement
   that the policy flip is confined to depth ≥ 3, and HP10.9 is the phase whose
   whole content is changing those halves.  What carries the criterion forward is
   box 11's mirror of it — §3.22 and §3.23 byte-identical — so read the
   confinement claim there.  *An acceptance box is a present-tense claim, so a
   later phase that supersedes its artefacts must sweep it.*
5. A depth-4 executed run shows the splice composing — two frames below a cut,
   both still reachable from the head (HP9.1).  **MET** at `v0.35.48`
   (`tests/SmpIpcSuite.lean` §3.23), and the run measures more than reachability:
   **three** successive pops carry the reservation from the innermost holder to its
   owner, where §3.22 needs two.  One thing the cut established rather than
   assumed — a code mutation of the splice's *stores* never reaches this witness,
   because `spliceReplyFrameStores_cases` states the three stores exactly and both
   candidate mutations (the full sever; a reconnection that clobbers the frame
   below's own downward link) fail to **elaborate**.  So the store shape is pinned
   by a theorem and this witness's subject is the *composition*, which no theorem
   states.
6. All three stated coherence hypotheses are **gone**, not merely unused: no
   consumer names them and the definitions are deleted (HP7.3).  **MET** at
   `v0.35.46` — nine declarations, with the binding-driven resolver among them, and
   a **fourth** stated fact found live (`replyFrameHeadHolderDonation`, which the
   trigger does not witness) rather than deleted with them.
7. No footprint exceeds `maxLockSetSize`, the ceiling and every figure derived
   from it are consistent under `check_lock_ceiling_figures.py`, and the cost
   (22 → 23; 15 → 14 µs) is stated in the canonical sentence rather than
   described (HP3.5).  **MET** at `v0.35.37` and re-checked at every cut since,
   including HP6.3's third splice store — which is **free**, the cut frame's lock
   being a declared write member on both removal paths already — and HP6.2's
   footprint repoint, which retired the sharper reachable seventeen rather than
   moving the ceiling.
8. `cancelIpcBlocking` preserves `donationOwnerValid` and `passiveServerIdle`
   on every arm with no hypothesis it did not carry before (HP5.3).  **MET** at
   `v0.35.39`, and the precise reading is *one stated fact swapped for one*, not
   *none added*: WS-RR RR7.22's `donationHolderIsReplyTarget` is deleted and
   `donatedContextIsOwnerFrameHead` takes its place, keyed on the frame the reclaim
   now reads.  Its builder `…_of_donationOwnerValid` measures what that costs — every
   clause but the frame-head link and the holder's promotability comes out of
   `donationOwnerValid` — so the arm carries no *additional* obligation and the two
   payoffs (`cancelIpcBlocking_preserves_passiveServerIdle`,
   `cancelIpcBlocking_reply_no_donation_to_victim`) are live at HEAD.
9. The frozen mirror runs the same removal and the same trigger, reconciled in
   both directions by the Tier 1 census (HP8.3).  **MET** at `v0.35.47` (trigger
   at `v0.35.38`, HP4.7).  The census reports 24 write sites with six frozen
   mirrors; `FO-043` is the depth-3 witness the flip needed, because every
   scenario that surface carried sits at depth ≤ 2 and passed byte-identically
   when the splice landed.
10. ~~`docs/REGISTERED_DEBT.md` table C's donation-accounting row is closed~~ —
    **this box is WRONG and is corrected at `v0.35.48` rather than acted on.**  It
    was written before `v0.35.42` found the **depth-2** loss, and the row cannot
    close at HP9: at depth 2 the removal takes the client's frame off the *bottom*
    of its stack, both policies write `none` into the frame above a bottom frame,
    and the splice therefore **provably cannot** reach it.  What HP9 closes is the
    depth-≥ 3 half, which HP6 earned; the row stays open with HP10 as its owner,
    and at HP9 v1.0.0 could still not claim that completing a call chain returns a
    client's reservation *unconditionally*.  **HP10.9 (`v0.35.53`) earned that
    claim** — see box 11 — so what keeps the row open at HEAD is its own retirement
    (HP10.10) rather than a live defect.  Closing a register row while the
    defect it names is live would be the worst available outcome here, because the
    row is what RR8.4's hand-off check reads.  The *upstream-parity* half of
    `v0.35.14`'s qualification was separately withdrawn at `v0.35.40`, since
    `severAtCut` is what upstream writes.
11. **`donationAccountingPreserved_atCallDepthTwo`**: on a depth-2 chain whose
    bottom frame the removal takes off the stack, the live `.reply` spine settles
    the reservation on the thread that **owned** it rather than on the thread
    reachability names (HP10.9).  **MET** at `v0.35.53`, with §3.20's accounting
    halves inverted from COST to PAYOFF, and §3.22, §3.23 and the golden trace
    byte-identical — which is the confinement measurement box 4 used to carry in
    the other direction, and which is *structural* rather than lucky: at depth ≥ 3
    the pop sits at a `some` arm, where `replyDonationRecipient_eq_of_outer_some`
    makes the redirect the identity by theorem.  Three things this box records that
    its row did not predict.  **No mutation of the production code is available** —
    the origin write, the resolver, the three pops and the dispatch's recipient are
    each pinned as theorems, so a mutation fails to *elaborate* rather than failing
    the suite, exactly as box 5 records for the splice's stores — so the decisive
    comparison is a differential *within* the suite: `replyRemovalOutcome` applied
    to a chain with a recorded origin and to `pushStore`'s without one, one field
    apart and opposite outcomes.  **HP10.4's production write had never been
    measured**, every fixture that carried an origin having set it by hand, so this
    cut runs the live push twice from `pushOwnerStore` and asserts both directions.
    And the theorem **derives** the reachability answer while **hypothesising** the
    two guards, because one of them cannot be derived at all: the owner is
    `.blockedOnReply` on exactly the reply being answered until the reply leg's
    wake.  Tier 3 negatives refuse hypothesising either derived fact.

## 9. What this plan deliberately does not do

- **It does not change when the cancellation reclaim happens, and it must not.**
  Upstream returns a donated context on **reply-capability revocation**
  (`finaliseCap` → `reply_remove` → `reply_pop` — the Reference Manual's documented
  behaviour) and *not* on `cancelIPC`, which runs `reply_remove_tcb` and donates
  nothing, leaving the context with the server until an SC-capability holder
  rebinds it. `returnDonationToCancelledCaller` applies the `reply_remove`
  semantics at the cancellation point instead, because this kernel's binding typing
  forces it: `.donated scId owner` names its owner, so `donationOwnerValid` is false
  the instant that owner stops being reply-blocked, where upstream's flat
  `tcbSchedContext` pointer carries no such obligation. Verified at `v0.35.40`
  against master, 13.0.0, 12.1.0, 12.0.0 and 11.0.0; before that `Suspend.lean`'s
  docstring named `reply_remove` where the call site's own comment named
  `reply_remove_tcb`, and the first correction over-generalised the `cancelIPC` path
  to the whole kernel. HP5 changes only which *fact* selects the reclaim, never
  whether or when the reclaim happens.
- **It does not reverse the reply-then-pop ordering.** The reply leg still runs
  first and the head transient is still discharged by the composite, exactly as
  WS-RM left it. What changes is which fact the composite reads.
- **It does not touch the push.** `donateSchedContext` already records the
  context on the head frame alone, which is what makes a mid-stack removal an
  `O(1)` repair of two neighbours. Nothing about the splice needs the push to
  change.
- **It does not remove the recipient guard in favour of matching upstream** —
  and upstream has the guard anyway (§3.3, resolved at `v0.35.40`):
  `reply_pop` donates only `if (tcb->tcbSchedContext == NULL)`. HP9.4 records the
  answer rather than asking the question.
- **It does not widen `Reply`.** Every fact the new trigger reads already
  exists in the record; the workstream is a change of *which* fact is read, not
  of what is stored.

## 10. Open questions carried into implementation

1. **HP2.2's converse may need a reachability witness.** "A recorded server
   holding a donation implies the answered frame heads that context" is true of
   states the push and the pop construct; whether it is derivable from
   `donationChainWellFormed` alone, or needs an `ipcReachable` conjunct, is
   settled by attempting HP2.2 and is the one place the phase could grow.
2. **Whether `.replyRecv`'s receive leg needs a second trigger read.** Its two
   legs run on different states; HP4.5 states the pop's fields at the post-pop
   state, and if the receive leg turns out to need its own resolution that is a
   seventh sub-task in HP4, not a later phase.
3. **The upstream `reply_pop` guard** — HP9.4.
