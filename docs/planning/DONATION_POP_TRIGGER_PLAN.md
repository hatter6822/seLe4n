# WS-HP — the head-driven donation pop, and seL4's splice

> **Status**: **PLANNED** — registered `v0.35.16`. No sub-task has started.
> **Predecessor finding**: [`../REGISTERED_DEBT.md`](../REGISTERED_DEBT.md)
> table C, registered `v0.35.14` — the removal does not preserve the donation
> accounting at reply-stack depth ≥ 3.
> **Sub-task count**: 43 across 9 phases (HP1..HP9), each phase numbered in the
> order it is to be implemented.

## Context — why this exists

`v0.35.14` registered this divergence and corrected the documentation that
described it wrongly, and stopped there. That is half of what this project's
**implement-the-improvement rule** requires: where the optimal implementation is
out of scope for a cut, the audit "must split the work into the proper sequence
of PRs … rather than treating documentation surgery as a substitute for the code
change." The debt row is the bookkeeping; this plan is the sequence.

**The defect.** `detachReplyFrameAbove` writes `above.prev := none`, so every
frame *below* a cut leaves the context's reply stack (`severAtCut`). The later
pop then reads the frame above the cut as the bottom and binds that caller
`.bound scId`. On a three-frame stack the reservation settles on a thread
strictly *inside* the chain and its owner is left `.unbound` for good — so a
callee that delegates its caller's reply capability to a confederate, or anyone
holding a suspend right over a middle caller, can permanently capture that
caller's CBS reservation. Measured on a live stack in `tests/SmpIpcSuite.lean`
§3.22.

**seL4-MCS splices**, confirmed against upstream source:
`REPLY_PTR(call_stack_get_callStackPtr(reply->replyNext))->replyPrev =
reply->replyPrev`, with the link orientation this tree assumes confirmed to
match. So the frames below a cut stay reachable from the head there, and the
reservation goes on travelling outward.

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
path carries today become derivable rather than assumed; and v1.0.0 can claim
seL4-MCS reply-stack semantics.

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
2. **The removal drops the tail.** `detachReplyFrameAbove`
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
`.unbound`) whichever way upstream answers, so it is not a branch point. Whether
seL4's `reply_pop` guards its `schedContext_donate` with
`if (tcb->tcbSchedContext == NULL)` is an open question recorded in HP9.4; the
answer changes a docstring, not the design.

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

`spliceReplyFrameOut_eq_detach_of_no_frame_below` is the load-bearing lemma of
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
| HP6 | The splice replaces the sever (one cut) | 8 |
| HP7 | The three stated hypotheses retire | 4 |
| HP8 | The frozen mirror | 3 |
| HP9 | Witnesses, anchors, documentation, closure | 5 |

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

### HP6 — The splice replaces the sever (8 sub-tasks)

One cut: both removal paths call one step, and `removeCallerReplyFrame`'s
algebra is stated over it.

**The splice itself is built here, not in HP1**, and HP1's acceptance note says
why: `ReplyStackWriteCensus` demands a chain result of every reply-stack write
site, and a bare splice has none — it breaks `prevLinkReciprocal` at the cut
frame until the consume that follows repairs it.  The composite is what can make
the statement, so the splice and its caller land together.  That is why HP6.1–3
sit below HP4 and HP5 in the numbering rather than above them: the splice cannot
be landed earlier, and HP6.4 was always going to need HP4 and HP5 anyway (§4).

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| HP6.1 | `spliceReplyFrameOut` beside `detachReplyFrameAbove` (§3.4): two Reply stores, fail-closed on either neighbour not reciprocating, plus the `…OrSelf` fold both removal paths need | `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` | M |
| HP6.2 | **`spliceReplyFrameOut_eq_detach_of_no_frame_below`** (§3.5) and the full read/write algebra — `_cases`, `_objects_frame` (three keys), `_tcb_eq`, `_reply_rewrite`, `_scheduler_eq`, `_machine_eq`, `_cdt_eq`, `_preserves_objects_invExt`. Each entry composes `detachReplyFrameAbove`'s existing fifteen with one extra store through **one** shared store step, so the case analysis is not doubled; no new argument is invented. Consumes HP6.1 | same | L |
| HP6.3 | `spliceReplyFrameOut_preserves_projection` and `_preserves_ipcInvariantFull` — one extra `.reply` store at a third key, cheap by construction: no conjunct reads `prev` or `next`, and `projectKernelObject` erases both. **Plus the census decision the shared store step forces**: a `Prop`-valued *relation* that mentions a store and constructs a chain record is reported by `recordConstructingStoreCandidates`, because the loop's `Meta.isProp` asks whether the declaration is a *proof* and a predicate is not one. `isDefinitionShaped`'s docstring states that over-report as deliberate and fail-closed, and asks for "an explicit decision, not a silent pass" — so make one here, where the subject exists: either state the relation without a `Prop`-valued name, or apply the census's own pure `isPredicate` at both frontiers with a token-preserving witness (a relation keeping the store and the constructor, differing only in its result type). Registering a relation as a write site is not an option — it writes nothing, and the entry would be false. Consumes HP6.2 | `SeLe4n/Kernel/InformationFlow/Invariant/Helpers.lean`, `SeLe4n/Kernel/IPC/Invariant/Structural/DualQueueMembership.lean`, `SeLe4n/Testing/ReplyStackWriteCensus.lean` | L |
| HP6.4 | `removeCallerReplyFrame` and `detachFrameAboveThreadReply` call `spliceReplyFrameOutOrSelf`. Every repair is the case split HP6.2 set up: the `no_frame_below` branch is the pre-HP proof verbatim. Consumes HP6.3, HP4, HP5 | `SeLe4n/Kernel/IPC/Operations/Endpoint.lean`, `SeLe4n/Kernel/Lifecycle/Suspend.lean` | L |
| HP6.5 | `removeCallerReplyFrame_preserves_donationChainWellFormed` over the splice — reciprocity is *maintained* rather than vacated, so the argument is shorter than the sever's: `above.prev = some below` and `below.next = .frame above` are written together. Consumes HP6.4 | `SeLe4n/Kernel/Lifecycle/Invariant/CancellationReplyShape.lean` | L |
| HP6.6 | `cancelledMiddleCallerPolicy := .spliceOutTheCut`, with `cancelledMiddleCaller_splices_at_cut` replacing `…_severs_at_cut`, and `replyStackOuterCaller?_follows_policy` restated. HP2.3's negative twin is retired *here*, in the cut that earns it. Consumes HP6.5 | `SeLe4n/Kernel/IPC/Invariant/Defs.lean`, `SeLe4n/Kernel/IPC/Invariant/DonationPreservation.lean` | M |
| HP6.7 | **The payoff**: `donationAccountingPreserved_atCallDepthThree` — on the depth-3 witness, a middle removal leaves the reservation owed outward and the later pop delivers it to its owner. `tests/SmpIpcSuite.lean` §3.22 inverts from a COST witness to a PAYOFF witness in the same cut, keeping the in-order contrast. Consumes HP6.6 | `SeLe4n/Kernel/IPC/Invariant/DonationPreservation.lean`, `tests/SmpIpcSuite.lean` | L |
| HP6.8 | **The two reply footprints repointed onto the head-driven trigger**, which HP4 deliberately left (§3.8.7): `lockSet_endpointReplyOnCore` / `lockSet_endpointReplyRecvOnCore` resolve their donation members through `endpointReplyServerDonation?` while the pop reads `replyFrameHeadHolder?`, and this is the cut that makes the two disagree on a reachable state — `spliceOutTheCut` can leave an orphan head, which `severAtCut` provably cannot. The theorem HP4.4 left in its place — `lockSet_endpointReplyOnCore_covers_headDrivenPop` — is what holds the gap closed until here and is **deleted** by this row, since the members then come from the trigger itself; this row therefore consumes HP4.4 as well as HP6.7. The two sharp bounds re-proved: the `owner = target` merge the head-driven footprint no longer has becomes the `holder = recorded server` one, which is why this row could not land before HP7 retires the coherence facts it would otherwise depend on. Consumes HP6.7 | `SeLe4n/Kernel/IPC/CrossCore/EndpointReply.lean`, `SeLe4n/Kernel/Concurrency/Locks/ResolvedFootprintBounds.lean`, `SeLe4n/Kernel/IPC/CrossCore/EndpointReplyDispatchInvariant.lean` | L |

**Acceptance**: §3.22's assertions read the owner receiving its reservation, the
in-order contrast is unchanged, and §3.20's depth-2 halves pass byte-identically
— the measurement that the change is confined to depth ≥ 3.

### HP7 — The three stated hypotheses retire (4 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| HP7.1 | `answeredHeadContextIsServerDonation` removed from `endpointReplyCrossCoreDispatch_preserves_donationChainWellFormed` and its two composites, discharged by HP2.4 | `SeLe4n/Kernel/IPC/CrossCore/EndpointReplyDispatchInvariant.lean` | M |
| HP7.2 | `replyDonationOwnerIsAnsweredCaller` removed from `lockSet_endpointReplyRecvOnCore_size_le_*`; the sharp bound becomes unconditional. Consumes HP7.1 | `SeLe4n/Kernel/Concurrency/Locks/ResolvedFootprintBounds.lean` | M |
| HP7.3 | `replyStackHeadIsAnsweredReply` removed from its consumers; the three definitions are deleted rather than left as unused predicates, since a stated fact nothing consumes is the shape this project retires. Consumes HP7.2 | same, plus consumers | M |
| HP7.4 | `syscallDispatchQuiescence` / `checkedSyscallDispatchQuiescence` shed the corresponding pack fields, with the inhabitation witnesses re-run. Consumes HP7.3 | `SeLe4n/Kernel/IPC/Invariant/DispatchPayoff.lean` | L |

**Acceptance**: the dispatch payoff's hypothesis count falls, and
`check_ipc_invariant_dethreading.py` still reports zero post-state conjuncts
with its bundle count updated in every prose site it holds.

### HP8 — The frozen mirror (3 sub-tasks)

`FrozenOps` is reached by neither library root and must stay in step (PR #895
review, `v0.35.12`).

**The trigger half already landed, as HP4.7.** §3.8.8 says why: HP4 is the cut
that makes the live `.reply` operation head-driven, so that is the cut in which a
binding-driven mirror of it becomes a second answer to one question. What remains
here is the **splice**, whose divergence HP6 creates.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| HP8.1 | `frozenSpliceReplyFrameOut` beside the frozen detach, mirroring HP6.1 | `SeLe4n/Kernel/FrozenOps/Core.lean` | M |
| HP8.2 | `frozenEndpointReply` runs the frozen **splice**; its pop is already head-driven (HP4.7). Consumes HP8.1, HP6.4 | `SeLe4n/Kernel/FrozenOps/Operations.lean` | M |
| HP8.3 | `SeLe4n/Testing/ReplyStackWriteCensus.lean`'s registry updated — the new sites recorded, the frozen ones as `mirrors` entries naming their live twins. Consumes HP8.2 | `SeLe4n/Testing/ReplyStackWriteCensus.lean` | M |

**Acceptance**: `lake exe frozen_ops_suite` passes all differential scenarios,
including the agreement between the frozen reply and the live one.

### HP9 — Witnesses, anchors, documentation, closure (5 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| HP9.1 | A **depth-4** witness — the shallowest stack on which two frames sit below a cut — so the splice's transitivity is measured rather than inferred from depth 3 | `tests/SmpIpcSuite.lean` | M |
| HP9.2 | Tier 3 anchors: positives for the splice's two writes and the head-driven trigger; negatives refusing the sever spelling, the binding-driven trigger on the reply path, and an unguarded recipient. Each mutation-tested in **both** directions — silent on a clean tree, firing on a token-preserving mutation that keeps the name and moves the relation | `scripts/test_tier3_invariant_surface.sh` | M |
| HP9.3 | The canonical documentation: `CLAUDE.md` + `AGENTS.md` (the WS-RM and WS-OD sections, whose current text states the divergence this workstream closes), `docs/spec/SELE4N_SPEC.md` §7, `docs/REGISTERED_DEBT.md` (table C row closed, and its closing paragraph restored now that the exception is gone), `docs/CLAIM_EVIDENCE_INDEX.md`, the GitBook mirrors | as listed | M |
| HP9.4 | Confirm against upstream source whether `reply_pop` guards its donate with `if (tcb->tcbSchedContext == NULL)` (§3.3) and record the answer beside the recipient guard — a docstring either way, since this kernel's typing requires the guard regardless | `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` | S |
| HP9.5 | Closure: `check_workstream_plan.py`, `check_claim_evidence_citations.py`, the version bump and `CHANGELOG.md` entry, `test_docs_sync.sh`. Consumes HP9.1–HP9.4 | `scripts/`, `CHANGELOG.md` | S |

**Acceptance**: see §8.

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
   HP9.2).
2. `spliceReplyFrameOut_eq_detach_of_no_frame_below` holds by `rfl`, so every
   depth-≤ 2 result is the pre-HP proof verbatim (HP6.2).
3. The two triggers are proved equivalent on every state satisfying the chain
   invariant, and the theorem that the splice breaks that equivalence exists —
   so HP6's position after HP4 is machine-checked rather than asserted
   (HP2.1, HP2.3).
4. **`donationAccountingPreserved_atCallDepthThree`**: on the depth-3 witness a
   middle removal leaves the reservation owed outward and the later pop
   delivers it to its owner (HP6.7). §3.20's depth-2 halves are unchanged.
5. A depth-4 executed run shows the splice composing — two frames below a cut,
   both still reachable from the head (HP9.1).
6. All three stated coherence hypotheses are **gone**, not merely unused: no
   consumer names them and the definitions are deleted (HP7.3).
7. No footprint exceeds `maxLockSetSize`, the ceiling and every figure derived
   from it are consistent under `check_lock_ceiling_figures.py`, and the cost
   (22 → 23; 15 → 14 µs) is stated in the canonical sentence rather than
   described (HP3.5).
8. `cancelIpcBlocking` preserves `donationOwnerValid` and `passiveServerIdle`
   on every arm with no hypothesis it did not carry before (HP5.3).
9. The frozen mirror runs the same removal and the same trigger, reconciled in
   both directions by the Tier 1 census (HP8.3).
10. `docs/REGISTERED_DEBT.md` table C's donation-accounting row is closed, and
    that table's closing claim — which `v0.35.14` had to qualify for this row —
    is restored (HP9.3).

## 9. What this plan deliberately does not do

- **It does not adopt seL4's cancellation semantics.** seL4's `cancelIPC` runs
  `reply_remove` and never donates the context back to the cancelled caller;
  this kernel does (`returnDonationToCancelledCaller`), deliberately, and
  `Suspend.lean` records that as a divergence with its reason. HP5 changes only
  which *fact* selects the reclaim, never whether the reclaim happens.
- **It does not reverse the reply-then-pop ordering.** The reply leg still runs
  first and the head transient is still discharged by the composite, exactly as
  WS-RM left it. What changes is which fact the composite reads.
- **It does not touch the push.** `donateSchedContext` already records the
  context on the head frame alone, which is what makes a mid-stack removal an
  `O(1)` repair of two neighbours. Nothing about the splice needs the push to
  change.
- **It does not remove the recipient guard in favour of matching upstream.**
  §3.3: this kernel's binding typing requires it whichever way seL4 answers, so
  HP9.4 records the answer rather than acting on it.
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
