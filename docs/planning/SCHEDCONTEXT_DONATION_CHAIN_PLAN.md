# WS-OD — SchedContext donation chains (onward donation)

> **Status**: IN FLIGHT — registered at `v0.34.98`; OD1.1 landed at `v0.34.100`,
> OD1.2 at `v0.34.101`, OD1.3 at `v0.34.103`, OD1.4 at `v0.34.104`, OD1.5 at
> `v0.34.105`, OD1.6 at `v0.34.106`, OD1.7 at `v0.34.108` — **OD1 is closed**.
> **OD2 is closed** at `v0.34.125`: OD2.1–OD2.7 landed in one cut, because the
> phase is additive and its rows do not compile apart — the field, its projection
> erasure and the two exhaustive positional patterns are one arity change, and
> the predicate, its frames and the pack conjunct are one elaboration.
> **Opens**: beside WS-RR RR7, and must close **before RR8 closes** — RR8 is the
> closure phase and cannot close over open work.
> **Predecessor findings**: the two Medium-severity model/specification gaps
> recorded in [`../REGISTERED_DEBT.md`](../REGISTERED_DEBT.md) §A, reported while
> proving the WS-RR RR7.22 residual at `v0.34.97` and `v0.34.98`.
> **Sub-task count**: 41 across 6 phases (OD1..OD6), each phase numbered in the
> order it is to be implemented

## 1. Phase goal

`applyCallDonation` donates a SchedContext **only when the caller's binding is
`.bound scId`**.  A caller already holding `.donated scId owner` falls through to
its `| _ => .ok st` arm, and `donateSchedContext` is the only operational
construction site of a `.donated` binding, so nothing else can donate either.
seL4-MCS's `receiveIPC` → `maybeDonateSchedContext` reads
`sender->tcbSchedContext`, which is set for bound **and** donated holders, so
seL4 passes the context down the call chain and this kernel stops it at the first
server.

This workstream makes donation transitive with seL4-MCS's reply-stack structure,
and closes the `passiveServerIdle` hole the flat model left behind.

## 2. The two defects

### 2.1 A passive server at call depth ≥ 2 can never run

`docs/spec/SELE4N_SPEC.md` §8.12.7 states that donation "enables **passive
servers**".  At depth ≥ 2 the callee stays `.unbound`, receives no budget and is
never selected, so the claim is false there.  Under `CLAUDE.md`'s
implement-the-improvement rule the code becomes what the specification describes;
the specification is not weakened to match the code.

Severity **Medium**: availability plus a false-assurance gap, not memory safety
or confidentiality; not exploitable, because nothing boots and the SVC seam halts
before SM10.1.

### 2.2 The `v0.34.97` reclaim can leave an unbound thread blocked on a call

This one was **live on HEAD at registration, at depth 1, with no chain
involved** — closed by OD1 (`v0.34.104`–`v0.34.108`; the plan header records
the phase) — and was introduced by the RR7.22 remediation itself:

1. `D0` (`.bound sc`) Calls `ep1` with server `S` waiting → `S := .donated sc D0`,
   `D0` `.unbound` ∧ `.blockedOnReply ep1 (some S)`.
2. `S` Calls `ep2` with **no** receiver waiting.  `endpointCallOnCore`'s
   no-receiver arm enqueues `S` `.blockedOnCall ep2`; there is no rendezvous, so
   no donation, and `S` keeps `.donated sc D0`.
3. `.tcbSuspend D0` → `cancelledCallerDonation?` resolves the holder to `S` with
   `.donated sc D0` and `owner == D0`, so the reclaim fires and leaves `S`
   `.unbound` while still `.blockedOnCall ep2`.

`S` is then unbound, off every run queue, and in a state `passiveServerIdleAllowed`
excludes.  **No theorem is unsound** — nothing claims `passiveServerIdle` across
`cancelIpcBlocking`, exactly as the register says of `donationOwnerValid` before
`v0.34.97` — but the conjunct is false of a state a live syscall reaches, which is
the false-assurance shape this workstream exists to remove.

**Onward donation does not close this half.**  seL4 reaches the same state and
permits it, because seL4 has no such invariant.  It is therefore OD1, ahead of
every reply-stack row, so that no later phase does bundle work over a surface
carrying a known-false conjunct.

## 3. Design

### 3.1 The chain lives in the Reply objects and one SchedContext field the docstrings already name

`Reply` (`SeLe4n/Model/Object/Reply.lean`) carries
`donatedSc : Option SchedContextId` and `prev : Option ReplyId`, **both declared
and never written to `some`**.  `Reply.wellFormed` is `True` with a docstring
saying it is "strengthened when the reply-stack and donation linkage land — 
`donatedSc` resolves, `prev` is acyclic, and **`donatedSc.scReply` agrees with
this reply**".  `SchedContext.scReply` **does not exist**.  That is the
implement-the-improvement case in its plainest form: the documentation describes a
better state than the code, so the field is built rather than designed around.

Building it is also what keeps the footprints inside `maxLockSetSize`.  Without
it the push must compute `prev` by reading the *owner's* `replyObject`, which adds
the owner's TCB read lock and the outer reply's read lock to
`lockSet_endpointCall` — already eight members at full resolution — for ten
against a ceiling of nine.  Raising the ceiling widens the published
covert-channel bound `maxLockSetSize · (numCores − 1) · tCs`, so it is not a free
move.  With `scReply`, `prev := sc.scReply` reads an object the call footprint
**already write-locks**, and the footprint does not grow at all.

* **Push**, inside `donateSchedContext`.  On a Call from donor `D` (holding `sc`)
  to receiver `R`, `D` is already `.blockedOnReply` with `D.replyObject = some Rd`
  — both reply-link sites run strictly before the dispatch-layer donation, so the
  link is always there.  Set `Rd.donatedSc := some sc`, `Rd.prev := sc.scReply`,
  `sc.scReply := some Rd`, then the three writes the operation already performs,
  with `R := .donated sc D`.
* **Pop**, inside `returnDonatedSchedContext`.  The new owner is **passed in**,
  not read from the post-state — see §3.3.  The operation validates the head
  (`Rt.donatedSc = some scId`), clears `Rt.donatedSc` / `Rt.prev`, and pops
  `sc.scReply`.

**The binding's `owner` stays the immediate donor**, which is what
`donateSchedContext` already writes, and that is what keeps all five donation
conjuncts true at depth `n` **with their current definitions**.  In a chain
`D0 → D1 → D2`: `D2` is `.donated sc D1`, `D1` is `.unbound` ∧ `.blockedOnReply`,
`D0` likewise.  `donationOwnerValid` holds at `D2`; only `D2` names `D1`, so
`donationOwnerUnique` holds; only `D2` has `scId? = some sc`, so
`donationBudgetTransfer` holds; and the *binding* graph still never has a chain of
length ≥ 2, so `donationOwnerValid_implies_donationChainAcyclic` stays true — the
chain lives entirely in the reply stack.  Only the prose beside
`donationChainAcyclic` needs a clarifying edit.

### 3.2 The pop lands before the push, and lands inert

If the push landed first, a depth-2 chain would become reachable while the return
is still the old one.  When `D2` replies to `D1`, the old return writes
`D1 := .bound sc` — `D1` permanently acquires `D0`'s SchedContext — and `D1`'s
own reply to `D0` then hits `applyReplyDonation`'s no-op arm, so `D0` wakes
`.unbound` and never runs again.  **That state breaks no conjunct**: no `.donated`
binding exists, `D0` is `.unbound` ∧ `.blockedOnReply`, and one holder has the
context.  The bundles stay green while a live transition moves a scheduling
context across a domain boundary — precisely the failure `CLAUDE.md`'s numbering
rule names.

So the pop goes first, and goes in **inert**: with no reply ever carrying a
`prev`, its new branch is provably dead
(`returnDonatedSchedContext_eq_legacy_of_none`), and OD4 is the only phase that
changes behaviour.

### 3.3 The pop cannot read the target's reply link — it is already consumed

`endpointReplyOnCore` folds `consumeCallerReply target rid` into the reply leg,
clearing `target.replyObject` and the reply's `caller`, and only then does
`endpointReplyCrossCoreDispatch` run the donation return.  `.replyRecv` has the
same shape.  Reordering is not available: it would break `replyCallerLinkage` and
re-derive the whole reply-leg surface.

The tree already answers this twice, in the same file: `recordedReplyServer?` and
`replyDonationOwnerHome` are both resolved from the **pre-state** and passed into
the dispatch.  The pop follows that discipline — `returnDonatedSchedContext` gains
a `newOwner? : Option ThreadId` parameter, and `replyStackOuterCaller?` is the
pre-state resolver that computes it.

### 3.4 A stale `prev` over a reusable Reply is a confused deputy

`Reply` has `prev` but no `next`, so a cancelled middle caller cannot be spliced
out by a backward scan the way seL4's doubly-linked `reply_remove` does.  Reply
objects are then **re-linked to new callers** — that is what `replyIdEstablishFresh`
exists for.  A stale `prev` naming a reused Reply would make the pop read the new
caller and hand the original thread's SchedContext to an unrelated thread, in
another domain, driven by object reuse.

Severity **High in the design**; not exploitable, because no code exists yet.
The remedy is cheap and load-bearing in both directions: the pop **validates**
`p.donatedSc = some scId` before accepting `p.caller`, and every freshening and
reply consumption clears `donatedSc` / `prev`.  That also gives `donatedSc` an
operational reader — without it the field would be written and never read, which
is the unwired-structure shape the implement-the-improvement rule names.

What a cancelled **middle** caller's context should do is a genuine decision, not
a detail, and OD5.2 is the row that makes it: either the pop falls back to
`.bound sc` at the target (seL4's non-head branch, but it transfers the cancelled
thread's budget to its callee), or the reclaim reaches the real holder in O(1)
through `sc.scReply` / `sc.boundThread` and returns the context to the cancelled
thread (consistent with the head case, but a deliberate divergence from seL4).
The row states both, picks one, and proves the choice — it does not inherit one by
omission.

### 3.5 `passiveServerIdle` is closed by the reclaim, and not with `timeoutThread` itself

`timeoutThread` writes the **scheduler**: its last step re-enqueues the thread.
`returnDonationToCancelledCaller`'s own docstring states that it writes `objects`
and nothing else, which is what keeps `cancelIpcBlocking_scheduler_eq` true — and
three cross-core results consume that theorem.  `timeoutThread` also returns
`Except`, while `cancelIpcBlocking` is total.

So the reclaim uses `timeoutThread`'s **object-only prefix**: the endpoint-queue
removal plus the timeout TCB rewrite (`.ready`, `timedOut := true`, the staged
timeout frame, cleared `pendingMessage` / `timeoutBudget` / `pendingReceiveReply`),
with **no** run-queue write.  The resulting thread is `.unbound` ∧ `.ready` ∧
off-queue, which is a legitimate passive-server shape and the correct one — an
unbound thread is unschedulable anyway.  Semantically this is what a timeout
*means* in MCS: the budget the operation was issued on has been revoked.

### 3.6 `donationChainWellFormed` stands beside the bundle — and is preserved, not assumed

The chain invariant is **not** added to `ipcInvariantFull`.  That bundle has
exactly twenty conjuncts and 166 theorems in its family, and the figure is
machine-checked against prose by a Tier-0 gate; widening it is a change of a
different size.  The predicate joins `ipcReachable` and the two dispatch packs
instead.

The saving is real but it is not free, and the plan prices it honestly: adding a
conjunct to `ipcReachable` re-opens `ipcReachable_default`, two further
reachability witnesses and **seventeen** `syscallDispatchQuiescence_inhabited*`
witnesses — twenty discharges, against 166 bundles.  More importantly, a pack
field that no transition is proven to preserve is a hypothesis wearing an
invariant's name, so OD2.5 builds the frame family and OD3.6 / OD4.4 / OD5.6
supply the per-transition preservation.

Weakening `passiveServerIdle` instead is not an escape either: `ThreadIpcState`
has six constructors and `passiveServerIdleAllowed` admits four, so admitting the
other two makes the conjunct vacuous and it should then be deleted — nineteen
conjuncts and all 166 bundles.  The cheap-looking option is the expensive one.

### 3.7 What this unblocks

The open WS-RR RR7.22 residual — the cancellation reply arm's `ipcInvariantFull`
and the five-arm composite over `cancelIpcBlockingOnCore` — is blocked on §2.2:
without OD1 its keystone would have to take the holder's state as a named
hypothesis.  **OD1 unblocks it**, so the residual can land immediately after OD1
rather than waiting for the whole workstream.  The endpoint and notification arms
(`v0.34.95`, `v0.34.96`) are unaffected.

## 4. Sequencing

Phases run **sequentially and may not overlap**: OD1, OD3, OD4 and OD5 all edit
`SeLe4n/Kernel/IPC/Operations/Endpoint.lean` and
`SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean`.  Within a phase, an operation
change and the theorems that unfold it land in **one** sub-task — those theorems
case-analyse the literal `storeObject` chain, so a fourth store makes them
non-compiling rather than merely unproven, and neither half compiles alone.

Every cut that adds a `*_preserves_ipcInvariantFull` statement also updates the
family-size figure in `CLAUDE.md`, `AGENTS.md` and `docs/spec/SELE4N_SPEC.md` in
the same commit; the Tier-0 de-threading gate holds those three sites to its own
measurement.

| Phase | Scope (one line) | Subs | Est |
|-------|------------------|------|-----|
| OD1 | The reclaim's `passiveServerIdle` hole — a live `v0.34.97` defect, independent of the reply stack | 7 | L |
| OD2 | Inert structure: `SchedContext.scReply`, `Reply.wellFormed`, the chain predicate and its frames | 7 | M |
| OD3 | The pop, generalised and behaviourally inert — signature, head validation, pre-state resolver, and the footprint split its growth needs | 7 | XL |
| OD4 | The push — `applyCallDonation` accepts a `.donated` caller; the chain goes live; the call sites thread the resolver | 8 | XL |
| OD5 | Chain-aware teardown and reply reuse — cancellation, retype, `.replyRecv`, freshening | 6 | L |
| OD6 | Payoff, footprint census, tests, documentation, closure | 6 | M |

## 5. Sub-tasks

Estimates: **S** small (<½ day) · **M** medium (1–2 days) · **L** large (3–5 days)
· **XL** extra large (>5 days)

### OD1 — the reclaim's `passiveServerIdle` hole

Provable against today's tree, with no reply-stack work.  It runs first because it
removes a conjunct that is false of a reachable state, which every later phase's
bundle work would otherwise inherit, and because its footprint restructuring is the
precondition for every later lock-set change.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| OD1.1 | **The live stranding defect.**  The tree has two endpoint-queue removals.  `endpointQueueRemoveDual`, which every other path uses, gives the successor the removed thread's own `queuePPrev` and *requires* that field to agree with `queuePrev`; `endpointQueueRemove`, whose only kernel-side caller is `timeoutThread`, patches `queuePrev` and leaves `queuePPrev` naming the removed thread — so a timeout strands its successor, which no later dual-queue removal can dequeue, and no conjunct reads the field so nothing catches it.  The fix is to make the two **agree**: `endpointQueueRemove` gives the successor `tcb.queuePPrev`, which is the right value in both the head case (`.endpointHead` is inherited) and the mid-queue case.  Moving the timeout onto the dual removal instead would import its `pprevConsistent` precondition, which **no invariant states** — the Boolean checker in `Testing/InvariantChecks.lean` checks it and the Prop-level `intrusiveQueueWellFormed` does not — and would falsify the existing argument that the timeout's error branch is dead.  Collapsing to one removal therefore waits on that invariant and is registered as debt rather than absorbed here | `SeLe4n/Kernel/IPC/DualQueue/Core.lean`, `docs/REGISTERED_DEBT.md` | M |
| OD1.2 | `abortPendingIpcOnEndpoint` — the timeout's object-only prefix: the same removal the timeout uses, now correct after OD1.1, plus the timeout TCB rewrite, with **no** run-queue write, total rather than `Except`-returning at the composite level | `SeLe4n/Kernel/IPC/Operations/Timeout.lean` | M |
| OD1.3 | Twenty-conjunct carriage for OD1.2.  The splice engine is stated over the dual removal, so this row builds the single removal's carriage on the same shape — the four conditional inserts are the same writes in a different order, which is what OD1.1 made true | `SeLe4n/Kernel/IPC/Invariant/QueueSplicePreservation.lean` | L |
| OD1.4 | Wire OD1.2 into `returnDonationToCancelledCaller` when the holder is `.blockedOnSend` / `.blockedOnCall`, preserving totality and the objects-only frame four cross-core results consume.  **The abort runs before the return**, for the reason `v0.34.97` put the return before the restore: with the return first the intermediate state has the holder `.unbound` while still blocked on a call, which is the very violation being closed; with the abort first every intermediate state satisfies the conjunct, since a `.donated` holder is outside `passiveServerIdle`'s reach.  The donation is resolved once, before either step, and the resolution survives the abort because the abort writes no binding | `SeLe4n/Kernel/Lifecycle/Suspend.lean` | M |
| OD1.5 | `cancelIpcBlocking_preserves_passiveServerIdle` — the theorem that does not exist — with footprint membership for the abort's writes and the size bound.  **The abort adds three members, not one**: it splices, so the holder's two queue neighbours join its endpoint — an arithmetic correction this row could not make before OD1.4 landed.  Summed, the footprint is eleven of nine; the bound holds by case analysis, because the donation-derived members and the victim's own blocked-object members both key on `tcb.ipcState` and are therefore mutually exclusive.  The reply arm is then **nine of nine**, with no headroom — see the footprint-budget risk below for where that is recovered | `SeLe4n/Kernel/Lifecycle/Invariant/SuspendPreservation.lean`, `SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean` | L |
| OD1.6 | The two exact-text Tier-3 anchors updated for the rewritten arm, a negative for the pre-OD1 shape and one for the single-queue removal, suite cases for the stranding defect and the abort, the family-size figure, version and CHANGELOG | `scripts/test_tier3_invariant_surface.sh`, `tests/SmpCancellationSuite.lean`, `tests/SmpIpcSuite.lean`, `CLAUDE.md`, `AGENTS.md`, `docs/spec/SELE4N_SPEC.md` | M |
| OD1.7 | **The aborted holder is placed, not merely unblocked.**  OD1.2–OD1.6 end the holder's send or call and leave it `.ready`, spliced off its endpoint and on **no** run queue — and every recovery path is closed: `resumeThreadOnCore` demands `threadState = .Inactive` and the abort leaves `.Ready`; `schedContextBind` re-buckets only a thread already queued; `chooseThreadOnCore` never scans ready TCBs.  So the reclaim stranded the server permanently, a denial of service reachable from an ordinary `.tcbSuspend` on the caller.  The premise the omission rested on — OD1.2's "an unbound thread is unschedulable anyway" — is false in this model (`resolveEffectivePrioDeadline`'s `.unbound` arm returns the legacy TCB priority), and `schedContextUnbind`'s own H2 step records having fixed the identical defect.  The wake goes at the **cross-core** layer, where the composite already writes the scheduler, so `cancelIpcBlocking_scheduler_eq` and its four consumers stand; it is a *scheduler-only* insert, because the abort already wrote `.ready`, which keeps every object-level and information-flow result about the composite true verbatim.  The declared scheduler footprint gains the woken core's run-queue write lock — the holder's home core is neither the victim's nor the executing core — and the per-core locality clause names that core as its second stated exclusion.  Reported as a security finding, not folded in silently | `SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean`, `SeLe4n/Kernel/IPC/CrossCore/CancellationNI.lean`, `SeLe4n/Testing/MainTraceHarness.lean` | L |

**Acceptance** — **MET at `v0.34.106`**: `passiveServerIdle` is preserved by
`cancelIpcBlocking` on every arm, machine-checked
(`cancelIpcBlocking_preserves_passiveServerIdle`), with no footprint exceeding
`maxLockSetSize` (`lockSet_cancelIpcBlockingOnCore_size_le`, nine of nine on the
reply arm — see §8a).  Exhibited by an executed run as well as by a theorem:
`[SCO-020b]` reports `holder_ready=true holder_unbound=true caller_rebound=true
holder_spliced=true`, and `[SCO-020c]` reports that a holder in a state the
conjunct permits is left untouched — the executed half of the bound on the
abort's reach.

### OD2 — inert structure and the chain predicate

No operational behaviour changes in this phase; every row is additive.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| OD2.1 | `SchedContext.scReply : Option ReplyId := none` — the field `Reply.wellFormed`'s docstring already names.  Update the structural comparator, the two exhaustive positional patterns and the boot-safety check | `SeLe4n/Kernel/SchedContext/Types.lean`, `SeLe4n/Platform/Boot.lean` | M |
| OD2.2 | Erase `scReply` in the projection's SchedContext arm, and state the erasure theorem beside the existing `boundThread` one — in the same cut as OD2.1, or the push becomes observable | `SeLe4n/Kernel/InformationFlow/Projection.lean` | S |
| OD2.3 | Replace `Reply.wellFormed`'s `True` with the property its own docstring states: `donatedSc` resolves, `prev` is acyclic, and the context's head agrees with this reply | `SeLe4n/Model/Object/Reply.lean` | M |
| OD2.4 | `donationChainWellFormed` — fuel-bounded `prev`-walk termination, every member naming the same context, each `prev` **validated** by its own `donatedSc` rather than by having a caller, and the context's head being the chain head | `SeLe4n/Kernel/IPC/Invariant/Defs.lean` | L |
| OD2.5 | The frame family: an objects-equality frame, a no-Reply-write frame, and single-`storeObject` frames for the TCB, SchedContext and Reply kinds, on the shape the passive-server frame already uses | `SeLe4n/Kernel/IPC/Invariant/Defs.lean` | L |
| OD2.6 | Conjoin into `ipcReachable` and re-discharge the twenty inhabitation witnesses (the default state, two reachability witnesses and seventeen dispatch-pack ones).  Consumes OD2.4 and OD2.5 | `SeLe4n/Kernel/IPC/Invariant/Reachability.lean`, `SeLe4n/Kernel/IPC/Invariant/DispatchPayoff.lean` | XL |
| OD2.7 | Tier-3 anchors for the new definitions; correct the acyclicity prose that reads as forbidding what OD4 builds; version and CHANGELOG | `scripts/test_tier3_invariant_surface.sh`, `SeLe4n/Kernel/IPC/Invariant/Defs.lean`, `CHANGELOG.md` | S |

**Acceptance** — **MET at `v0.34.125`**: the tree builds (default target and
`SeLe4n.Platform.Staged`) with the field, the predicate and the pack conjunct
present, and the predicate is vacuously true of every reachable state because
nothing writes `prev` — witnessed both ways.  By *theorem*:
`donationChainWellFormed_of_no_donations` discharges all three conjuncts from
"no reply carries a donation and no context heads a stack", and it is what
`ipcReachable_default` and the two dispatch-pack witnesses use.  And the predicate *decides* rather than
refuses: `donationChainWitness_wellFormed` proves the whole predicate — the
completeness clause included — of the store a depth-2 Call chain leaves, which is
what keeps a conjunct discharged only vacuously from hiding an over-strong
obligation.  By *executed
run*: `smp_ipc_suite` §3.15 walks a hand-built depth-2 chain and reports
`some [head, outer]`, refuses the same chain one step short of fuel, and refuses
four token-preserving mutations — a `prev` naming a live reply that donates a
*different* context, one that donates nothing, a self-linked head, and a link to
no object at all — while §3.9 reports that a live donating call and its return
leave all three fields at `none`.

Two things the phase decided beyond the row list.  **The boot admission was
tightened**: `bootSafeObjectCheck` refuses a config SchedContext that heads a
stack, because every admissible boot Reply is inert, so a config-supplied head
could only dangle — a `donationChainWellFormed` violation installed before the
first instruction runs.  And **`Reply.wellFormed` states only its local half**:
`Model.Object.Reply` is imported *by* `KernelObject`, so a `Reply → Prop` has no
store, and the docstring's two store-level clauses (`donatedSc` resolves; the
context's head agrees) are stated in `donationChainWellFormed`, which carries the
local predicate as its own first conjunct — nothing of the SM6.D promise is
dropped, and `donationChainWellFormed.replyWellFormedAt` is the bridge.

### OD3 — the pop, generalised and inert

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| OD3.1 | `returnDonatedSchedContext` gains `newOwner?`, the head validation (fail-closed, symmetric with RR2.8's `boundThread` guard), the Reply clear and the head pop — a four-store chain.  The six theorems that case-analyse the literal store sequence re-derive **in this row**, because a fourth store makes them non-compiling and neither half compiles alone | `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` | XL |
| OD3.2 | Re-base the remaining thirty-five attached theorems.  **Three** change *statement*, not only proof: the one asserting the return touches no Reply becomes a Reply **frame**; the binding trichotomy widens at the target; and the two reusable frames that asserted whole-object Reply identity (`replyLinkageFrame.replyAgree`, `donationReadAgreement.otherKind`) drop to the `caller` projection the conjunct they serve actually reads.  Consumes OD3.1 | `SeLe4n/Kernel/IPC/Operations/Endpoint.lean`, `SeLe4n/Kernel/IPC/Invariant/DonationPreservation.lean`, `SeLe4n/Kernel/IPC/Invariant/Defs.lean` | XL |
| OD3.3 | `returnDonatedSchedContext_eq_legacy_of_none` — at `newOwner? = none` the new definition **is** the old one.  This is the row that makes the phase inert and leaves OD4 as the only behaviour change | `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` | S |
| OD3.4 | `replyStackOuterCaller?` — the pre-state resolver and its correctness lemma, required because the reply leg consumes the target's link before the donation return runs (§3.3), on the same discipline as the two resolvers already beside it.  **Placement corrected at OD3.1**: it goes in `Endpoint.lean` beside `donationHeadOf?`, not in `EndpointReplyDispatch.lean`, because three of the six call sites that must resolve it (`cleanupDonatedSchedContext`, `applyReplyDonation`, `returnDonationToCancelledCaller`) are **upstream** of that module and none of them imports it | `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` | M |
| OD3.5 | **The arm-selected cancellation footprint.**  Split the summed `Option` arguments into footprints chosen by the victim's `ipcState`: the arms are mutually exclusive, but the bound census measures at full arity, so the summed form reaches nine before the next row adds a member.  Every later footprint change consumes this one.  **Also recovers the `.replyRecv` headroom** (PR #892 review round 6): a *delegated* reply — one answered by a thread other than the one the Reply records as its server — needs that server's own TCB lock, and the arm is already at nine of nine, so `lockSetForSyscall` answers `none` there and the delegated case keeps the coarser serialisation.  With the arms selected rather than summed, declare it | `SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean`, `SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean` | L |
| OD3.6 | Footprints: the reply, replyRecv and cancellation-reply-arm sets gain the previous reply's **read**; re-prove the bound at full arity on each.  If any exceeds the ceiling, stop and escalate — raising it widens the published covert-channel bound | `SeLe4n/Kernel/IPC/CrossCore/EndpointReply.lean`, `SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean`, `SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean` | L |
| OD3.7 | Chain preservation for the pop; the projection result re-derived through the added store; the two Tier-3 name anchors; the family-size figure; version | `SeLe4n/Kernel/IPC/Invariant/DonationPreservation.lean`, `scripts/test_tier3_invariant_surface.sh`, `CLAUDE.md`, `AGENTS.md`, `docs/spec/SELE4N_SPEC.md` | L |

**Acceptance**: every call site passes `none`, and OD3.3 witnesses that the tree's
behaviour is bit-identical to pre-OD3.

**Landed OD3.4 at `v0.34.127`, and moved the threading row into OD4.**  Two
things this row records rather than inherits.  (1) **The resolver validates the
frame it follows**, which §3.4 assigns to OD5.1: a live resolver whose
safety check lands two phases later is the ordering this plan's own numbering
rule forbids, so the confused-deputy check is built in here and OD5.1 keeps the
other half (the clears at freshening and consumption).  (2) **The pop validates
its donee.**  `donateSchedContext` checks its donor before minting a `.donated`
binding; the pop mints one too and checked nothing, so every consumer carried the
donor shape as a hypothesis — and on the reply path, where the answered caller is
already `.ready`, no consumer could discharge it.  `outerCallerAcceptable` is an
O(1) fail-closed check, so three of `donationReturnOuterValid`'s four clauses are
now consequences of the operation succeeding.  The fourth (`outerUnowned`) is
whole-store quantified and stays a caller obligation.

**And the threading row moved to OD4.4 for a reason worth stating.**  It was
attempted at all six call sites and reverted at all six: each site's invariant
surface runs through `returnDonatedSchedContext_preserves_ipcInvariantFull`,
which OD3.2 states under `hBottom : newOwner? = none` and which OD4.3
generalises.  The numbers ascended and the proofs still arrived after the
transition that needed them — the *semantic* half of the numbering rule, which
the numeric half does not imply.

**Landed OD3.1–OD3.3 at `v0.34.126`.**  Two decisions the rows record rather than
inherit.  (1) **The depth-≥ 2 conjunct obligations are stated in OD3.2, not
deferred to OD4**: `donationReturnOuterValid` names what the pop owes
`donationOwnerValid` when it hands the context to a thread that is itself a
donor, and `donationOwnerValid`, `donationOwnerUnique` and
`donationBudgetTransfer` are general under it — so OD4.3 does not reopen them and
no live transition is ever ahead of its own proof.  (2) **The one exception says
so**: `returnDonatedSchedContext_establishes_ipcInvariantFull_of_except` takes
`hBottom : newOwner? = none`, because its case analysis discharges the target's
arm by `cases` on a `.bound` binding at four places; **OD4.3 removes it**, in the
row whose subject is exactly the five conjunct preservations under the widened
arm.  The arm it excludes is unreachable until OD4.1 writes a reply stack.

### OD4 — the push; the chain goes live

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| OD4.1 | `donateSchedContext` writes the reply's `donatedSc` and `prev` and pushes the context's head — `prev` read from an object the footprint already write-locks.  Four-store chain; the four theorems that unfold it re-derive in this row | `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` | XL |
| OD4.2 | `applyCallDonation` accepts a `.donated` caller; the footprint resolver follows; the three characterisation theorems re-derive here, because they **are** the guard being widened | `SeLe4n/Kernel/IPC/Operations/Donation/Primitives.lean`, `SeLe4n/Kernel/IPC/Operations/Donation.lean` | L |
| OD4.3 | The five conjunct preservations under the new arm.  The caller-blocked and receiver-not-owner hypotheses already exist, so the shape carries; the new obligation is that the intermediate donor is `.unbound` ∧ `.blockedOnReply` at the donation site, which the dispatch's prior write supplies | `SeLe4n/Kernel/IPC/Invariant/DonationPreservation.lean` | XL |
| OD4.4 | **Thread `newOwner?` through all six call sites**, each resolving from its own pre-state.  Moved here from OD3 at `v0.34.127`: every site's invariant surface runs through `returnDonatedSchedContext_preserves_ipcInvariantFull`, which OD3.2 states under `hBottom : newOwner? = none`, so a site that resolves its argument cannot use it until the row above generalises it.  Attempted at all six sites and reverted at all six for that one reason — the plan's numbering ascended while the proofs still arrived after the transition that needed them.  Consumes OD3.4 and OD4.3 | `SeLe4n/Kernel/IPC/Operations/Donation/Primitives.lean`, `SeLe4n/Kernel/IPC/Operations/Endpoint.lean`, `SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean`, `SeLe4n/Kernel/Lifecycle/Suspend.lean`, `SeLe4n/Kernel/API.lean` | XL |
| OD4.5 | Chain preservation for the push — the row that closes the loop OD2.4 opened.  Consumes OD2.4 and OD4.1 | `SeLe4n/Kernel/IPC/Invariant/DonationPreservation.lean` | L |
| OD4.6 | The cross-core call donation and its replenishment migration at depth ≥ 2: the source core is the **intermediate** donor's home, which the dispatch already passes.  Proved rather than inherited | `SeLe4n/Kernel/IPC/CrossCore/EndpointCall.lean`, `SeLe4n/Kernel/IPC/CrossCore/EndpointCallDispatch.lean` | L |
| OD4.7 | Prove the call footprint does **not** grow: the head is read under the SchedContext write lock the set already declares, and the reply under the reply write lock it already declares | `SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean`, `SeLe4n/Kernel/IPC/CrossCore/EndpointCallInvariant.lean` | M |
| OD4.8 | The `.call` and `.replyRecv` dispatch-arm bundles under the generalised push; the donation primitive's own projection result through the two added stores; Tier-3 anchors; the family-size figure; version | `SeLe4n/Kernel/IPC/Invariant/DispatchArmPreservation.lean`, `SeLe4n/Kernel/InformationFlow/Projection.lean`, `scripts/test_tier3_invariant_surface.sh`, `CLAUDE.md`, `AGENTS.md`, `docs/spec/SELE4N_SPEC.md` | XL |

**Acceptance**: a depth-2 Call donates, and both `ipcInvariantFull` and the chain
invariant hold across it.

### OD5 — chain-aware teardown and reply reuse

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| OD5.1 | **Closes the §3.4 confused deputy.**  Reply freshening and the reply consumption clear `donatedSc` and `prev`, and the pop validates the previous reply's own `donatedSc` before accepting its caller.  Without this a reused Reply redirects a SchedContext to an unrelated thread | `SeLe4n/Kernel/IPC/CrossCore/EndpointReply.lean`, `SeLe4n/Model/State.lean`, `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` | L |
| OD5.2 | The cancelled **middle** caller: state both candidate answers of §3.4, pick one, and prove it — the seL4-shaped fallback at the target, or the O(1) reclaim to the cancelled thread through the context's head.  Whichever is chosen, `.tcbSuspend` preservation at depth ≥ 2 lands with it.  Consumes OD5.1 | `SeLe4n/Kernel/IPC/Invariant/Defs.lean`, `SeLe4n/Kernel/Lifecycle/Invariant/CancellationReplyShape.lean` | XL |
| OD5.3 | The **double pop**: cancelling a middle caller makes the donated-donation teardown reachable inside the same suspend, so two replenishment migrations run where the suspend's scheduler-domain footprint declares one pair.  Add the third core and re-prove the ladder and the bound | `SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean` | L |
| OD5.4 | Retype and revoke must not leave a live `prev` naming a deleted Reply, and must pop the context's head | `SeLe4n/Kernel/Lifecycle/Operations/CleanupPreservation.lean`, `SeLe4n/Kernel/Lifecycle/Operations/RetypeWrappers.lean` | M |
| OD5.5 | `.replyRecv` at depth ≥ 2 — the third live push site: its return leg uses OD3.4's resolver, and its re-donation fires when the next thread is itself `.donated` | `SeLe4n/Kernel/API.lean`, `SeLe4n/Kernel/IPC/CrossCore/EndpointReplyDispatch.lean` | L |
| OD5.6 | Bundles for the teardown paths; chain preservation for each; Tier-3 anchors; the family-size figure; version | `SeLe4n/Kernel/IPC/Invariant/DispatchArmPreservation.lean`, `scripts/test_tier3_invariant_surface.sh`, `CLAUDE.md`, `AGENTS.md`, `docs/spec/SELE4N_SPEC.md` | L |

### OD6 — payoff, census, tests, closure

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| OD6.1 | The defect's own closure theorem: a passive server reached at call depth ≥ 2 holds a SchedContext whose bound thread is itself.  The statement the workstream exists to make true, not merely the preservation of what was already true | `SeLe4n/Kernel/IPC/Invariant/DonationPreservation.lean` | L |
| OD6.2 | Re-run the footprint bound census over every touched set; record the worst case, and if the ceiling moved, the recomputed covert-channel headline | `SeLe4n/Testing/LockFootprintBoundCensus.lean`, `SeLe4n/Kernel/InformationFlow/FineLockFlow.lean` | M |
| OD6.3 | Tests: depth-2 donation and depth-2 reply; middle-caller and outer-caller cancellation; reply-reuse-after-cancel as a **negative** that keeps the link and breaks the relation rather than deleting it; the new footprints | `tests/SmpIpcSuite.lean`, `tests/SmpCancellationSuite.lean`, `tests/LockSetSuite.lean`, `tests/SuspendResumeSuite.lean` | L |
| OD6.4 | Trace harness: a depth-2 donation scenario and a cancel-at-depth-2 scenario, registered and re-baselined with rationale.  **Regenerate the fixture's `.sha256` companion in the same step** — every `.expected` has one, the Tier-2 drift check compares against it, and no other tier does, so a fixture updated without its hash passes Tier 0, Tier 1 and Tier 3 and fails only the full suite | `SeLe4n/Testing/MainTraceHarness.lean`, `tests/fixtures/scenario_registry.yaml`, `tests/fixtures/main_trace_smoke.expected` | M |
| OD6.5 | Documentation: the specification's donation section, the GitBook chapters carrying the conjunct count, the claim-evidence index, the two register rows closed with their versions, the codebase map regenerated | `docs/spec/SELE4N_SPEC.md`, `docs/gitbook/`, `docs/CLAIM_EVIDENCE_INDEX.md`, `docs/REGISTERED_DEBT.md`, `docs/codebase_map.json` | M |
| OD6.6 | Full-gate run and closure audit: the tier scripts, the de-threading report, the workstream-plan gate, the registry row, version | `scripts/`, `CHANGELOG.md`, `lakefile.toml` | S |

## 6. What every cut in this workstream must run, in order

Learned the expensive way on OD1.1, where three separate runs each caught a
different derived artefact the previous one had not reached.  Assembling
individual tiers is **not** a substitute for the whole suite: each of these is
checked by exactly one gate, and a cut that skips the step passes every other
tier.

1. Build each touched module (`lake build <Module.Path>`), then the default
   target **and** `SeLe4n.Platform.Staged` — a staged proof that quotes an
   operation's store chain literally breaks without appearing in the default
   build.
2. If the trace output changed: regenerate `tests/fixtures/main_trace_smoke.expected`
   **and its `.sha256` companion**.  Only the Tier-2 drift check compares the
   hash; Tier 0, Tier 1 and Tier 3 all pass without it.
3. If **any** `.lean` source changed: regenerate `docs/codebase_map.json`, then
   `./scripts/sync_readme_from_codebase_map.sh`, then
   `./scripts/sync_translated_metrics.py`.  The map feeds the README and spec
   metrics, which feed the eleven translated READMEs and the GitBook chapters;
   only `test_docs_sync.sh` compares them, and it runs after the tiers.
4. `./scripts/bump_version.sh <x.y.z>` and the `CHANGELOG.md` entry.
5. `./scripts/test_full.sh` **to completion**, and read the suite's own exit
   line rather than a wrapper's.

## 7. Acceptance gate

The workstream closes when **all nine** hold and each is checkable:

1. **The defect is gone, positively.**  `applyCallDonation` donates from a
   `.donated` caller, and OD6.1's theorem states that a passive server at call
   depth ≥ 2 holds a SchedContext bound to itself.  Not "no bundle regressed" —
   the improvement is stated as a theorem.
2. **`Reply.donatedSc` and `Reply.prev` are both written and both read on live
   paths**, and `SchedContext.scReply` names the head.  A search for a write with
   no operational read comes back empty.
3. **The chain invariant is preserved, not assumed.**  It is a conjunct of
   `ipcReachable`, every transition that writes a Reply has a preservation
   theorem, all twenty inhabitation witnesses are re-discharged, and no theorem
   takes it as a post-state hypothesis.
4. **`passiveServerIdle` is preserved by `cancelIpcBlocking` on every arm**, and
   no reachable state has an `.unbound` thread `.blockedOnSend` / `.blockedOnCall`.
   The conjunct is not weakened, and `ipcInvariantFull` still has exactly twenty.
5. **No footprint exceeds `maxLockSetSize` at full arity**, measured by the bound
   census.  If the constant moved, the covert-channel headline is recomputed and
   stated in the spec rather than absorbed.
6. **The de-threading gate reports zero threaded statements and zero post-state
   bindings**, and the family size it measures equals the figure at every prose
   site — which the gate enforces, so it is a consequence rather than a checklist
   item.
7. **A reused Reply object cannot redirect a donation.**  A negative test builds
   cancel-then-reuse-then-reply and asserts the context does not reach the new
   caller.  Per the mutation rule it must **keep the token and break the
   relation** — a live `prev` naming a live reply whose `donatedSc` is a
   *different* context — not merely delete the link.
8. **Projection stability is witnessed for all four new writes** — the reply's two
   fields, the context's head, and the pop's clear — and the head is in the
   projection's SchedContext erasure.
9. **`test_full.sh` green and the workstream-plan gate green**; every `OD` citation
   in the canonical index resolves; both register rows are closed with a version
   rather than a note.

## 8. Registration

* This plan is named from `README.md`, `CLAUDE.md` and `AGENTS.md`, the canonical
  index every plan must appear in.  It is not website-linked, so
  `scripts/website_link_manifest.txt` is unchanged.
* **WS-OD** has a row in the workstream registry of
  [`../REGISTERED_DEBT.md`](../REGISTERED_DEBT.md); that table is machine-read by
  `scripts/check_identifier_naming.py`, so the family is covered by the naming
  gate from the moment it is registered.
* Every cut bumps the patch version through `./scripts/bump_version.sh` with a
  matching `CHANGELOG.md` entry.

## 8a. The footprint budget, after OD1.5

`lockSet_cancelIpcBlockingOnCore` reaches **nine of nine** on the reply arm at
`v0.34.105`: the victim's TCB, its consumed reply, the returned SchedContext, the
donation holder, the victim's two splice neighbours, and the holder's endpoint
plus *its* two splice neighbours.  Summed over all arms the parametric form
carries eleven optional members; the bound holds only because the
donation-derived members and the victim's own blocked-object members are
mutually exclusive, both keying on `tcb.ipcState`.

So there is **no headroom left**, and two rows below depend on that being
recovered before they run:

* **OD3.5** is the arm-selected split — the footprints chosen by the victim's
  `ipcState` rather than summed.  On the reply arm it drops the victim's two
  neighbour members, which are vacuous there (that arm performs no victim
  splice), taking the reply arm from nine to seven.
* **OD3.6** adds the previous reply's *read* to the reply, replyRecv and
  cancellation-reply-arm footprints, and is the row that would exceed the ceiling
  without OD3.5.

The narrowing was deliberately **not** pulled forward into OD1.5.  It ripples
into `SeLe4n/Kernel/InformationFlow/FineLockFlow.lean` and
`SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean`, and doing it in the row
that *adds* members would put a footprint restructuring ahead of the row that
owns it.  If OD3.6 nevertheless exceeds the ceiling, stop and escalate: raising
`maxLockSetSize` widens the published covert-channel bound.

## 9. Two things this plan deliberately does not fix

* **Priority authority through a donation.**  `getCurrentPriority` and
  `updatePrioritySource` treat `.bound` and `.donated` identically, so writing a
  `.donated` thread's priority writes the *donor's* SchedContext.  That is already
  true at depth 1; chains widen the blast radius to a third domain but do not
  create the behaviour.  Recorded here so it is a known constraint rather than an
  inherited surprise; it belongs with WS-CB's MCP-authority work.
* **`scThreadIndexConsistent` is prose only.**  The object-store index that tracks
  which threads reference a SchedContext has a documented consistency property and
  no Lean definition.  The push and pop maintain the index correctly at depth ≥ 2
  — the donor is cleared either way — but nothing states it.  A separate
  implement-the-improvement candidate, registered rather than absorbed.
