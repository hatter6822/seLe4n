# WS-HP — the head-driven donation pop, and seL4's splice

> **Status**: **PLANNED** — registered `v0.35.16`. No sub-task has started.
> **Predecessor finding**: [`../REGISTERED_DEBT.md`](../REGISTERED_DEBT.md)
> table C, registered `v0.35.14` — the removal does not preserve the donation
> accounting at reply-stack depth ≥ 3.
> **Sub-task count**: 40 across 9 phases (HP1..HP9), each phase numbered in the
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
| HP4 | The reply path's trigger flips (one cut) | 6 |
| HP5 | The cancellation path's trigger flips (one cut) | 4 |
| HP6 | The splice replaces the sever (one cut) | 7 |
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

### HP4 — The reply path's trigger flips (6 sub-tasks)

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
| HP4.1 | **First** relocate `answeredReplyObject?` and `answeredFrameHeadContext?` from `IPC/CrossCore/EndpointReply.lean` down beside `replyFrameHeadContext?` in `IPC/Operations/Endpoint.lean`: HP1 put them where their HP1 consumers are, and `Donation/Primitives.lean` — the module the single-core spine lives in — imports `Endpoint.lean` alone, so as written that spine cannot call the resolver (§3.8.4). A relocation, never a second spelling. Then `replyDonationReturn?` and `endpointReplyServerDonation?` re-keyed onto it, **in place** — a second spelling of either would be the one-question-two-answers hazard on the hottest IPC path (§3.8.1). Each gets an `_eq_answeredFrameHeadContext?` bridge so the theorems about it move by rewrite rather than by re-proof. `recordedReplyServer?` is untouched and keeps every consumer outside the pop. Consumes HP2.1 | `SeLe4n/Kernel/IPC/Operations/Endpoint.lean`, `SeLe4n/Kernel/IPC/Operations/Donation.lean`, `SeLe4n/Kernel/IPC/CrossCore/EndpointReply.lean` | M |
| HP4.2 | `applyReplyDonation` re-keyed: it takes `target` and resolves the pop from the same expression the footprint resolves its members from, which is the `a parameter is a place for a caller to be wrong` rule (§3.8.4). `applyReplyDonation_characterisation` restated — it is what every reply-side invariant proof runs on, so it is the single point through which 172 references move. Consumes HP4.1 | `SeLe4n/Kernel/IPC/Operations/Donation/Primitives.lean`, `SeLe4n/Kernel/IPC/Operations/Donation.lean` | L |
| HP4.3 | `applyReplyDonationOnCore` re-keyed the same way, which **retires `replyDonationOwnerHome`**: it resolves the owner's home from the *binding* at the call site while the operation resolves the same owner from the *frame*, so after the flip the two answers can disagree on exactly the orphan-head state HP4 exists for (§3.8.4). The two migration-home arguments themselves **stay** parameters — `determineTargetCore` is the correct resolver for a replenish queue, which is keyed by affinity rather than placement, so there is no proxy there to remove and internalising them would be restatement with no correctness content. `applyReplyDonationOnCore_eq_single` and `_post_agrees` re-proved. Consumes HP4.2 | `SeLe4n/Kernel/IPC/CrossCore/EndpointReplyDispatch.lean` | L |
| HP4.4 | `endpointReplyCrossCoreDispatch`'s body, and `lockSet_endpointReplyOnCore` / `lockSet_endpointReplyRecvOnCore` repointed so every member is resolved from the same `target` the pop is. The **PIP walk does not move** — it keys on waiters, so its argument stays `recordedReplyServer?` — and the `.replyCapInvalid` arm stays, because "no recorded server" and "no head context" are different facts (§3.8.5). Consumes HP4.3 | `SeLe4n/Kernel/IPC/CrossCore/EndpointReplyDispatch.lean`, `SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean` | L |
| HP4.5 | `.replyRecv`'s `replyRecvPopDonation` — between the legs, where WS-RM put it — and the dispatch payoff's `replyRecvStage` fields restated at the post-pop state. Consumes HP4.4 | `SeLe4n/Kernel/IPC/Invariant/DispatchPayoff.lean`, `SeLe4n/Kernel/API.lean` | L |
| HP4.6 | The **recipient guard** (§3.3): the pop refuses an `originalOwner` that is not `.unbound`, with `returnDonatedSchedContext_rejects_bound_recipient` proving the refusal commits nothing, and `outerCallerAcceptable` re-examined at its new arguments rather than assumed to carry (§3.8.3). Plus the three Tier 3 negatives §3.8.2 and §3.8.5 call for — the component swap, the PIP re-keying, and the two pre-receive cleanups keeping their binding-driven resolver — each mutation-tested in both directions. Consumes HP4.5 | `SeLe4n/Kernel/IPC/Operations/Endpoint.lean`, `scripts/test_tier3_invariant_surface.sh` | M |

**Acceptance**: every existing reply theorem holds unchanged, `smp_ipc_suite`
and `smp_cross_core_reply_suite` pass with no fixture edit, and the golden trace
is byte-identical — the measurement that the flip is behaviour-preserving. A flip
that builds and changes a dispatch outcome is the failure §3.8.6's ordering
exists to catch, and only the trace can see it.

### HP5 — The cancellation path's trigger flips (4 sub-tasks)

Forced by §4: after HP6 a frame becomes the head whose recorded reply target is
gone, and a binding-driven reclaim would leave a `.donated` binding naming a
`.ready` owner.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| HP5.1 | `cancelledCallerDonation?` reads the victim's own frame's `.head` link and that context's `boundThread`, derived from `answeredFrameHeadContext?` rather than spelled a second time | `SeLe4n/Kernel/Lifecycle/Suspend.lean` | M |
| HP5.2 | `returnDonationToCancelledCaller` and the abort prefix `abortHolderPendingIpc` re-proved over the new resolver — `_eq_self_of_getTcb?_none`, the binding frames, `abortHolderPendingIpc_preserves_donationOwnerValid`. Consumes HP5.1 | `SeLe4n/Kernel/Lifecycle/Invariant/CancellationReplyShape.lean` | L |
| HP5.3 | `cancelIpcBlocking_reply_no_donation_to_victim`, `passiveServerIdle` preservation on all arms, and `cancelledCallerDonation?_none_below_the_cut` restated — below the cut the reclaim still declines, now because the victim's frame is not a head. Consumes HP5.2 | `SeLe4n/Kernel/Lifecycle/Invariant/CancellationReplyShape.lean`, `SeLe4n/Kernel/IPC/Invariant/DonationPreservation.lean` | L |
| HP5.4 | The wake and the scheduler footprint — `cancelAbortedHolderWake?`, `enqueueAbortedHolderOnCore`, `cancelIpcBlockingOnCoreSchedLockSet` — re-resolved from the new holder. Consumes HP5.3 | `SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean` | M |

**Acceptance**: `smp_cancellation_suite` passes unchanged, and
`cancelIpcBlocking` preserves `donationOwnerValid` and `passiveServerIdle` on
every arm with no new hypothesis.

### HP6 — The splice replaces the sever (7 sub-tasks)

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

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| HP8.1 | `frozenSpliceReplyFrameOut` beside the frozen detach, mirroring HP6.1 | `SeLe4n/Kernel/FrozenOps/Core.lean` | M |
| HP8.2 | `frozenEndpointReply` runs the frozen splice and the head-driven pop. Consumes HP8.1, HP6.4 | `SeLe4n/Kernel/FrozenOps/Operations.lean` | M |
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
