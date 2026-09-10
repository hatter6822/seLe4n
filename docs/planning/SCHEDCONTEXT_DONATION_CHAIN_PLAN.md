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
> **Sub-task count**: 53 across 6 phases (OD1..OD6), each phase numbered in the
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
omission.  Until it lands, the answer the tree gives is **stated, not inherited**
(PR audit of OD3, `v0.34.138`): `replyStackOuterCaller?_of_consumed_frame`
proves that the resolver answers `none` on a validated frame whose caller has
been consumed — the seL4-shaped fallback, the target bound outright with the
consumed frame still heading the stack — and `tests/SmpIpcSuite.lean` pins both
the resolver's answer and the pop's result.  Before that theorem the same
behaviour fell out of `Reply.caller`'s pass-through while the resolver's
docstring presented `.ok none` as the bottom of the stack alone, which is exactly
the inheritance this paragraph forbids.  OD5.2 therefore changes a theorem and a
witness, whichever answer it picks.

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
invariant's name, so OD2.5 builds the frame family and OD3.7 / OD4.4 / OD5.6
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
| OD3 | The pop, generalised and behaviourally inert — signature, head validation, pre-state resolver, and the footprint split its growth needs | 19 | XL |
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
| OD3.6 | **seL4-MCS's `maybeDonateSchedContext`: the receive side donates.**  Unscheduled when this plan was written and found while threading OD3.5's resolvers: `.receive` performed *no* SchedContext donation at all, so a passive server taking its **first** request with `seL4_Recv` ran on no reservation while the same server taking its later requests with `seL4_ReplyRecv` was charged correctly — a budget-enforcement bypass, reported before being fixed.  One shared step (`applyReceiveRendezvousDonation`) called by both `.receive` arms **and** by `replyRecvReturnDonation`, whose inlined copy is retired; the guard discharges the donation's caller-blocked obligation, leaving only `hReceiverNotOwner` as a `recvStage` pack conjunct; `lockSet_endpointReceive` gains the donated SchedContext and a **disjunctive** state-level member (conditioning it on `installsCaps` alone omits it on exactly the passive-server path).  Bound restated at the new arity: `3 + 4 = 7 ≤ 11`  **LANDED v0.34.129** | `SeLe4n/Kernel/IPC/Operations/Donation.lean`, `SeLe4n/Kernel/API.lean`, `SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean` | L |
| OD3.7 | Footprints: the reply, replyRecv and cancellation-reply-arm sets gain the previous reply's **read**; re-prove the bound at full arity on each.  If any exceeds the ceiling, stop and escalate — raising it widens the published covert-channel bound.  **LANDED v0.34.130**, and the row named *one* read where the operation performs **two**: `replyStackOuterCaller?` reads the Reply one frame below the head, and `outerCallerAcceptable` then reads that frame's caller's TCB to validate it before the pop binds a context to it — a validate-then-commit, so an unlocked read is a time-of-check/time-of-use window.  Both are declared through one resolver (`replyStackBelowHeadReads?`), in **read** mode, and both are `none` on every state this tree reaches.  The escalation fired and was answered: **`maxLockSetSize` 11 → 13**, `admissibleCriticalSection` 30 µs → 25 µs, the envelope 1980 → 2340 µs.  Only `.replyRecv` needed it — the reply arm reaches nine and the cancellation reply arm ten, both asserted rather than described.  The pop stays **O(1)** at any chain depth, so this is a constant `+2`, not `O(depth)` | `SeLe4n/Kernel/IPC/Operations/Endpoint.lean`, `SeLe4n/Kernel/IPC/CrossCore/EndpointReply.lean`, `SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean`, `SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean` | L |
| OD3.8 | Chain preservation for the pop; the projection result re-derived through the added store; the two Tier-3 name anchors; the family-size figure; version.  **LANDED v0.34.132.**  Two of the five deliverables were already discharged and are recorded rather than redone: the projection re-derivation landed at OD3.1/OD3.2, where the fourth store made every copy of the case analysis stop compiling, and the de-threading family size does not move — `_preserves_donationChainWellFormed` is not an `ipcInvariantFull` bundle, so the gate's own `len(bundles)` is unchanged at 170.  What the row actually cost is the **acyclicity** argument the plan did not name: clearing the popped head's links is sound only if no frame below links back to it, which is *termination* read as acyclicity (`donationChainFrom_head_not_mem_tail`, over a suffix-walk and a determinism lemma), and only if the head is on no other context's chain, which is `not_mem_donationChainFrom_of_not_donating`.  No conjunct was added to the predicate to obtain either — a `NoDup` field would have been an enumeration standing in for a derivation, and a Tier-3 negative refuses one.  The congruence the proof consumes is **chain-scoped** (`donationChainFrom_congr_on_chain`), since the whole-store `donationChainFrom_congr` is false of a step that rewrites a key's links.  Exercised on the `some` arm via the OD2.4 witness (`donationChainWitness_pop_wellFormed`, `_pop_chain`), because a theorem discharged only where the context heads no stack is indistinguishable from one whose writing arm is wrong | `SeLe4n/Kernel/IPC/Invariant/Defs.lean`, `SeLe4n/Kernel/IPC/Invariant/DonationPreservation.lean`, `SeLe4n/Kernel/IPC/Invariant/Reachability.lean`, `SeLe4n/Kernel/IPC/Operations/Endpoint.lean`, `tests/SmpCrossCoreCallSuite.lean`, `scripts/test_tier3_invariant_surface.sh`, `CLAUDE.md`, `AGENTS.md`, `docs/spec/SELE4N_SPEC.md` | L |

**Acceptance**: every call site passes `none`, and OD3.3 witnesses that the tree's
behaviour is bit-identical to pre-OD3.

**Landed OD3.5 at `v0.34.128`, and the row's second deliverable inverted.**  The
arm-selected split went in as written — `cancelArmSpliceNeighbors?`, derived from
`cancelBlockedEndpoint?` so the arm question is asked once, taking the widest
cancellation arm from ten members to eight.  What the row planned as "recover the
headroom so the delegated `.replyRecv` can declare" turned out to rest on a false
premise: the arm was short a member on *every* case, not only the delegated one.
`replyRecvReturnDonation` performs two SchedContext hand-offs and declared one,
so the passive-server steady state wrote a kernel object under no declared lock.
See §8.1 for the full account and the numbers it supersedes.  **OD3.7 then moved
them again**, for the two objects the donation return reads below the reply-stack
head: `maxLockSetSize` is **13**, `admissibleCriticalSection` for the 1 ms tick is
25 µs — **23 µs** since OD3.13 raised the ceiling to 14 — and the uniform
envelope is 2520 µs.  Every later row measures against
those.  The escalation clause this row's own text carries fired at OD3.7 and was
answered by the maintainer in favour of the raise, against the alternative of
refusing to declare `.replyRecv` at call depth ≥ 2 — the pattern OD3.5 had just
retired for the delegated reply.

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

| OD3.9 | **The third endpoint-queue removal.**  Unscheduled when this plan was written and found while sweeping every declared arm for undeclared queue-structure TCB writes: `spliceOutMidQueueNode` — the removal `.tcbSuspend` and thread destruction run — patched its successor's `queuePrev` and **not** its `queuePPrev`, so the successor was left naming the removed thread and failed `endpointQueueRemoveDual`'s `pprevConsistent` check in every case it had a successor at all.  It could then never leave the endpoint queue, and every later bound-notification delivery to it returned `.illegalState`: suspending the thread *ahead* of a passive server was an authority-crossing denial of service on that server.  Identical to the defect WS-OD OD1.1 closed in `endpointQueueRemove` at `v0.34.100`, live for eight further cuts because OD1.1 fixed the copy it was shown and asserted the dual removal was "the removal every other kernel path uses" — the sweep rule failing in the way `CLAUDE.md` describes.  Reported before being fixed.  One definition of what unlinking writes (`queueUnlinkPredecessor` / `queueUnlinkSuccessor`, beside the fields they maintain), used by both removals that spell their patches, and the third tied to it by a theorem about the object it stores.  **LANDED v0.34.134** | `SeLe4n/Model/Object/Types.lean`, `SeLe4n/Kernel/Lifecycle/Operations/Cleanup.lean`, `SeLe4n/Kernel/IPC/DualQueue/Core.lean`, `SeLe4n/Kernel/IPC/Invariant/QueueSplicePreservation.lean`, `SeLe4n/Kernel/Lifecycle/Operations/CleanupPreservation.lean`, `SeLe4n/Kernel/Lifecycle/Invariant/CancellationQueueShape.lean`, `tests/SmpCancellationSuite.lean`, `scripts/test_tier3_invariant_surface.sh` | M |
| OD3.10 | **`.notificationSignal` declares the two TCBs its dequeue relinks.**  The first of the arms the OD3.9 sweep found undeclared: the bound-delivery path runs `endpointQueueRemoveDual`, which writes the removed thread's predecessor and successor TCBs, and `lockSet_notificationSignal` named neither — so a `.notificationSignal` on one core and a `.tcbSuspend` of a queue-mate on another had provably disjoint footprints while both writing the same TCB.  Latent rather than live (SM5.I's global entry lock serialises every entry, and nothing boots), so a verification defect: the statements built on `lockSetForSyscall` were *silent* about those objects rather than conservative.  The resolver is derived twice over — its arm gate from `boundDeliveryTarget?`, its neighbour identities from `queueSpliceNeighbors?`, which is `cancelSpliceNeighbors?` given its neutral name and moved beside the link fields, since adding a second reader without unifying it would be OD3.9's divergence one level up.  Every statement about the footprint restated at the new full arity; `maxLockSetSize` unmoved at `3 + 5 = 8`.  **LANDED v0.34.135** | `SeLe4n/Model/Object/Types.lean`, `SeLe4n/Kernel/IPC/CrossCore/NotificationSignal.lean`, `SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean`, `SeLe4n/Kernel/Concurrency/Locks/LockSetForSyscall.lean`, `SeLe4n/Kernel/Concurrency/Locks/Deadlock.lean`, `tests/SmpCrossCoreNotificationSuite.lean`, `scripts/test_tier3_invariant_surface.sh` | M |
| OD3.11 | **`.send` and `.call` declare the queue-structure neighbour.**  The shape that covers four of the arms the OD3.9 sweep found: every rendezvous-or-block either pops the head of one endpoint queue -- relinking the popped thread's successor into the head -- or enqueues the caller on the other, relinking that queue's old tail.  Exactly one TCB, and no footprint named either, so a rendezvous on one core and a `.tcbSuspend` of the affected neighbour on another had provably disjoint footprints while both writing it.  One definition (`endpointQueueStructureNeighbor?`), an `Option` rather than a pair because the two cases are mutually exclusive, with the branch decided by the resolver the arm's receiver/sender member already comes from.  Every statement about both footprints restated at the new arity -- RR7.18's census caught both size bounds the moment they were left at the default; `maxLockSetSize` unmoved at `3 + 4 = 7` and `3 + 6 = 9`.  `.receive` and `.replyRecv` are the next row.  **LANDED v0.34.136** | `SeLe4n/Kernel/IPC/DualQueue/Transport.lean`, `SeLe4n/Kernel/IPC/CrossCore/EndpointCall.lean`, `SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean`, `SeLe4n/Kernel/Concurrency/Locks/LockSetForSyscall.lean`, `SeLe4n/Kernel/Concurrency/Locks/Deadlock.lean`, `SeLe4n/Kernel/Concurrency/Locks/ResolvedFootprintBounds.lean`, `tests/SmpCrossCoreCallSuite.lean`, `scripts/test_tier3_invariant_surface.sh` | M |
| OD3.12 | **`.receive` declares the queue-structure neighbour.**  The same shape as OD3.11 with the queues exchanged: this arm pops the **send** queue and blocks on the **receive** queue, through the same two primitives, so it writes the same one neighbour TCB.  Threaded through `receiveSideQueueStructureNeighbor?`, derived from `receiveRendezvousSender?` — the resolver the arm's sender member, its caps flag and its donation member already read, so all four agree about the branch.  Fits at `3 + 5 = 8`; no ceiling change.  **LANDED v0.34.137** | `SeLe4n/Kernel/IPC/DualQueue/Transport.lean`, `SeLe4n/Kernel/IPC/CrossCore/EndpointReply.lean`, `SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean`, `SeLe4n/Kernel/Concurrency/Locks/LockSetForSyscall.lean`, `SeLe4n/Kernel/Concurrency/Locks/Deadlock.lean` | M |
| OD3.13 | **`.replyRecv` declares it, and `maxLockSetSize` moves 13 → 14.**  Its receive leg *is* `.receive`'s transition, so it writes the same neighbour — but the arm was at 13 of 13 and had nowhere to put it.  The escalation the plan requires fired and was answered: raise, and state the cost.  `admissibleCriticalSection` for the 1 ms tick 25 → **23 µs**, the uniform envelope 2340 → 2520 µs, the sharp reachable `.replyRecv` bound 12 → 13; the *gap* between ceiling and sharp bound is unchanged at one.  Read against the alternative: a footprint that omits a written object is **false**, and every statement built on `lockSetForSyscall` was silent about that TCB rather than conservative.  With this row all eight declared arms name every object they write and the OD3.9 sweep closes.  **LANDED v0.34.137** | `SeLe4n/Kernel/Concurrency/Locks/LockSet.lean`, `SeLe4n/Kernel/Scheduler/Operations/PerCoreWcrt.lean`, `SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean`, `SeLe4n/Kernel/Concurrency/Locks/Deadlock.lean`, `SeLe4n/Kernel/Concurrency/Locks/ResolvedFootprintBounds.lean`, `SeLe4n/Kernel/IPC/CrossCore/EndpointReply.lean`, `SeLe4n/Kernel/Concurrency/Locks/LockSetForSyscall.lean`, `scripts/test_tier3_invariant_surface.sh` | L |
| OD3.14 | **The receive rendezvous' PRIORITY hand-off.**  Unscheduled when this plan was written and reported by review on the OD3 cut: OD3.6's donation carries a queued caller's scheduling context, hence its *base* priority, and `resolveEffectivePrioDeadline` is `max basePrio pipBoost` — so the inherited **boost** travelled by no route at all on the `.receive` arm, which ran no `propagatePipChainCrossCore` while `.call` and `.replyRecv` both did.  A chain `D → C → S` (`D` blocked on `C`, `C` dequeued into `.blockedOnReply` on the passive server `S`) left `D`'s priority stopping dead at `C`: unbounded priority inversion, and it bites with **no** donation too, since `applyCallDonation` is the identity for an already-`.bound` receiver that still gains the waiter.  Pre-existing rather than introduced by OD3.6 — the base branch read the rendezvous straight into staging — and reported as a possible vulnerability before being fixed.  One shared action (`applyReceiverPipHandoff`); the `.receive` pair (`applyReceiveRendezvousHandoff`) reads the rendezvous guard **once, from the pre-state**, so the donation and the boost provably fire on the same states.  The sweep found the same defect at a sibling: `.replyRecv` walks from the *recorded server*, which is the receiver only on a non-delegated reply, so `applyReceiveLegPipHandoff` adds the receiver's walk gated on the equality that makes the first walk **be** it.  `replyRecvBodyWriteSet` gains a fourth leg, and the SM3.C walker's obligation list grows with the *walks* — `pipChainStart_endpointReceive` and `pipChainStart_replyRecvReceiveLeg`, with the reply leg's own marker corrected to name the recorded server it actually walks from.  `maxLockSetSize` does not move: the chain's locks are the scheduler domain's, declared through the `pipChainStart_<τ>` hints rather than through `lockSet_<τ>`, which is what keeps the static footprint honest.  **LANDED v0.34.141** | `SeLe4n/Kernel/IPC/Operations/Donation.lean`, `SeLe4n/Kernel/IPC/Invariant/DonationPreservation.lean`, `SeLe4n/Kernel/IPC/Invariant/DispatchPayoff.lean`, `SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean`, `SeLe4n/Kernel/API.lean`, `SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean`, `SeLe4n/Kernel/Concurrency/Locks/LockSetInventory.lean`, `SeLe4n/Kernel/Concurrency/Locks/DynamicChainExtension.lean`, `SeLe4n/Kernel/Concurrency/PhaseTheoremManifest.lean`, `tests/SmpIpcSuite.lean`, `tests/LockSetSuite.lean`, `scripts/test_tier3_invariant_surface.sh` | L |
| OD3.15 | **The ceiling's derived figures stop being hand-maintained.**  `maxLockSetSize` is the WCRT headline's first factor and two published figures are functions of it — the per-lock critical section the 1 ms tick allows, and the contention envelope at a uniform cost — so every raise in this phase (OD3.5, OD3.7, OD3.13) left a stale copy of one of them somewhere in the prose, and **four consecutive review rounds each found one the previous round's sweep had missed**; the OD3.14 cut alone hand-fixed three more.  That is the enumeration-standing-in-for-a-derivation shape at the scale of a document set, and this repo already had the remedy: WS-RR RR7.28 holds the de-threading bundle count to its census and caught 170 → 172 on the cut that made it stale.  `scripts/check_lock_ceiling_figures.py` (Tier 0) is the same mechanism for the ceiling — both axes derived (the three constants **and** `admissibleCriticalSection`'s formula read out of the Lean sources; the sites the tracked tree), the live claim given a **canonical spelling** so narrative naming a superseded value stays free, a near-miss reported as a gate defect rather than skipped, and five documents pinned to carry the statement so deleting the sentence does not satisfy it.  Fifteen self-test cases, and the harness refuses a check whose only rejecting fixture deletes a token.  **LANDED v0.34.142** | `scripts/check_lock_ceiling_figures.py`, `scripts/test_tier0_hygiene.sh`, `SeLe4n/Kernel/Concurrency/Locks/LockSet.lean`, `SeLe4n/Kernel/Scheduler/Operations/PerCoreWcrt.lean`, `CLAUDE.md`, `AGENTS.md`, `docs/spec/SELE4N_SPEC.md`, `docs/gitbook/12-proof-and-invariant-map.md` | M |
| OD3.16 | **The raw-match scan reads the discriminator's own line.**  Reported by review round 4 on the OD3.14 cut, and the round-2 finding one line over: the rule matching a `match … .objects[…]` ended in `next`, so the four-line window opened *after* the discriminator and a `match st.objects[id]? with | some (.tcb t) => …` — which Lean accepts — recorded no `RAW_SITE` at all.  Not a lost row but a lost **site**: `RAW_MATCH_TOTAL` is derived from those rows, so such a read is absent from every enforced metric and moves only the diagnostic-only `RAW_MATCH_UNCLASSIFIED` — it passes Tier 0 in silence.  Round 2 widened the window to its *end* and never asked whether it *began* in the right place, which is the sweep rule failing at the smallest possible distance.  `scan_arms` now runs on the discriminator line without consuming a window slot, so the four following lines are scanned exactly as before and **no tree figure moves** — which is why the fix is evidenced by a fixture rather than by a recomputation.  The scanner also becomes ONE program shared by the real run and a new self-test (five Lean fixtures, the one-line discriminator among them), wired into Tier 0 beside the monotonic gate: that gate's own self-test synthesizes *baseline files*, so it exercises the comparison and never the measurement — a scanner that under-reaches simply produced lower floors and both gates reported PASS.  **LANDED v0.34.143** | `scripts/ak7_cascade_baseline.sh`, `scripts/test_tier0_hygiene.sh` | S |
| OD3.17 | **Four review-round-5 findings, three of them in the gates written to prevent this class.**  (1) `check_lock_ceiling_figures.py`'s pin on `admissibleCriticalSection`'s body had **no end anchor**, so `budget / (maxLockSetSize * (numCores − 1)) + 1` satisfied a *prefix* of it: the gate would derive 23 while Lean computed 24, and every stale figure would pass — a presence-check-is-not-a-relation-check defect inside the pin written to enforce a relation.  (2) The same gate read the three Lean sources **raw**, so a docstring shaped like the canonical `def` could decide whether a Tier 0 gate passes — the project's own headline rule broken in a scanner written the same day; the constants and formula now come through `lean_code_view.strip` while the *claims* still come from the real text, which is that rule applied within one gate rather than around it.  (3) `RAW_MATCH_UNCLASSIFIED` subtracted a count of **variant incidences** from a count of **match lines**, so the multi-arm support OD3.16 completed made a two-arm match compute `1 − 2 = −1`; the operand is now `count_classified_match_sites`, emitted by the same awk program so the two readings cannot drift.  (4) `lockSet_replyRecv`'s contract still said *the receive phase does NOT initiate donation* — true of the single-core transition it was written for, false of `replyRecvBody` since OD3.5, and a contract that denies a hand-off its own footprint declares invites the next caller to omit the members it needs.  Self-tests grow to 18 and 9 cases respectively, each new one token-preserving.  **LANDED v0.34.144** | `scripts/check_lock_ceiling_figures.py`, `scripts/ak7_cascade_baseline.sh`, `SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean` | M |
| OD3.18 | **The header's donation inventories were a third copy of `permittedKinds`.**  Found by sweeping OD3.17's fourth finding -- *a contract that denies a hand-off its own footprint declares* -- for the other places that answer the same question, which is the rule that finding's own fix invoked and did not run.  `LockSetTransitions.lean`'s module header carries two hand-written inventories of exactly this, and **all three drifts sit in them**: `.receive` was listed under *syscalls that do NOT need donation extension*, on the reasoning OD3.6 disproved, for twelve cuts after OD3.6 gave it a `donatedScId`; `lockSet_replyRecv`'s entry repeated the very sentence OD3.17 retired at the declaration site; and `tcbSetPriority`, `tcbSetMCPriority` and `tcbSetAffinity` -- each of which writes the target's **bound SchedContext**, because priority and home core live there rather than on the TCB -- were called *TCB-only config ops*, with `tcbSetAffinity` in neither list.  **The remedy is deletion of the duplicate, not a checker over it.**  The first attempt built a Tier 1 census walking each footprint's elaborated body for `schedContextLock`; it took six corrections in a row (a name-prefix frontier a differently-named helper defeats, a tuned rather than derived bound, a skip set right for the narrow frontier and wrong for the wide one, a `getUsedConstants` that pushes per subterm) -- `unconditionalActions` again, for the reason CLAUDE.md already records.  It was deleted before it shipped, because the tree **already derives this fact and proves it**: `permittedKinds` is the declared kind inventory and the `lockSet_consistent_<arm>` family states `∀ p ∈ (lockSet_<arm> ...).pairs, p.fst.kind ∈ permittedKinds <arm>` at each footprint's FULL arity, so a member added without the kind being permitted fails to elaborate.  The lists now defer to it.  Corrected in passing: `lockSet_endpointSend`'s justification, and the PIP-chain section, which now names the `pipChainStart_<τ>` marker family OD3.14 grew to six.  **LANDED v0.34.145** | `SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean`, `scripts/test_tier3_invariant_surface.sh` | S |
| OD3.19 | **Two review-round-6 findings, both a cardinality standing in for a set.**  (1) The raw-read inventory keyed on `(file, variant)`, so hygienizing a raw read in one declaration while a fresh one appeared in another declaration of the SAME file left the row and every scalar identical -- the cross-file case OD3.5f fixed, with *file B* replaced by *declaration e*, surviving the fix for it.  **22 of the 30 rows had a count above one**, so the exposed shape was the majority.  Keyed by the enclosing declaration the inventory is 102 rows and the swap becomes a key the baseline does not name, which fails outright; `check_inventory` splits on the LAST `|` so the comparison logic needed no change.  The refinement **stops** at declaration granularity, and the docstring says why: the declaration is the unit of hygienization, so a count-preserving swap inside one is not the movement the gate exists to catch, while finer keys (lines, ordinals) churn the baseline on unrelated edits.  (2) `SmpSchedulerSuite`'s WCRT labels read `≤ RPi5 bound (1980)` -- the value at ceiling **11** -- beneath a ceiling of 14, while the assertion checked `maxLockSetSize * (3 * 60)` = 2520, so a passing line claimed a bound 540 µs tighter than the one established, under a comment citing the 8 → 9 move.  The figure is now **interpolated from the constant**, which ends the class rather than correcting an instance; and the retired `typical 4-lock syscall (720 µs) < 1 ms tick` line -- true arithmetic, and the exact framing CLAUDE.md retracts -- is replaced by the property that is actually about the declared ceiling (`admissibleCriticalSection rpi5TickBudgetMicros = 23`, and that 60 µs sections are refused).  Self-tests grow to 10 (scanner) and 7 (monotonic gate), each new case token-preserving.  **LANDED v0.35.1** | `scripts/ak7_cascade_baseline.sh`, `scripts/ak7_cascade_check_monotonic.sh`, `scripts/store_reader_hygiene_baseline.txt`, `tests/SmpSchedulerSuite.lean` | M |
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
| OD5.2 | The cancelled **middle** caller: state both candidate answers of §3.4, pick one, and prove it — the seL4-shaped fallback at the target, or the O(1) reclaim to the cancelled thread through the context's head.  Whichever is chosen, `.tcbSuspend` preservation at depth ≥ 2 lands with it.  The interim answer is stated rather than inherited — `replyStackOuterCaller?_of_consumed_frame` (the seL4-shaped fallback, `v0.34.138`) and its runtime witness — so this row changes a theorem, not an accident.  Consumes OD5.1 | `SeLe4n/Kernel/IPC/Invariant/Defs.lean`, `SeLe4n/Kernel/Lifecycle/Invariant/CancellationReplyShape.lean` | XL |
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

> **Superseded by OD3.5, OD3.7 and OD3.13.**  This section records the budget as
> it stood at `v0.34.105`.  OD3.5 made the victim's splice neighbours
> arm-selected, taking the reply arm to eight; OD3.7 added the two below-head
> reads, taking it to ten; OD3.13 took `maxLockSetSize` itself to **fourteen**
> for the queue-structure TCB `.replyRecv`'s receive leg relinks; and OD3.14
> moved it **not at all**, because a priority-inheritance chain is
> state-discovered and unbounded, so its locks are declared through the
> `pipChainStart_<τ>` markers rather than through `lockSet_<τ>`.  The live
> figures are `lockSet_cancelIpcBlockingOnCore_size_le_ten` and
> `maxLockSetSize`, never the numbers below.

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
* **OD3.7** adds the previous reply's *read* to the reply, replyRecv and
  cancellation-reply-arm footprints, and is the row that would exceed the ceiling
  without OD3.5.

The narrowing was deliberately **not** pulled forward into OD1.5.  It ripples
into `SeLe4n/Kernel/InformationFlow/FineLockFlow.lean` and
`SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean`, and doing it in the row
that *adds* members would put a footprint restructuring ahead of the row that
owns it.  If OD3.7 nevertheless exceeds the ceiling, stop and escalate: raising
`maxLockSetSize` widens the published covert-channel bound.

### 8.1 What OD3.5 actually found (landed `v0.34.128`)

The split landed as planned and the arithmetic above is superseded, because
implementing it surfaced a **false footprint** on the arm the row's second
deliverable was about.  Recorded here rather than rewritten above, so the
prediction and the outcome can be compared.

`replyRecvBody`'s third stage, `replyRecvReturnDonation`, performs **two**
SchedContext hand-offs: the recorded server's return, and then
`applyCallDonationOnCore nextThread tid` when the receive leg dequeues a queued
`Call`.  `donateSchedContext` writes the *new* caller's SchedContext, which is
provably not the returned one, and `lockSet_replyRecv` named only the returned
one — so a `.replyRecv` on one core and a `.tcbSuspend` of that queued caller on
another had provably disjoint footprints while both writing that object.  It is
the passive-server steady state, not an edge case: the receiver is `.unbound` at
that point precisely because the return just made it so.  `.call` has declared
exactly this member since SM6.A.5 and says why.

Two consequences for the numbers this section states:

* The **ceiling moved to 11**, the maintainer's decision against the alternative
  of narrowing `.replyRecv`'s declaration further on the hottest IPC path.  The
  cost is stated where it is paid: `admissibleCriticalSection` for the 1 ms tick
  falls from 37 µs to 30 µs.  The plan's "stop and escalate" clause fired one row
  early and for the opposite reason — a member that was *missing*, not one being
  added.
* The reply arm is **eight**, not seven: every donation-carrying footprint also
  gained the state-level lock, because `SystemState.scThreadIndex` is an
  `RHTable` whose insert may rehash the whole table and therefore does not
  decompose by object.  The split was still *necessary* rather than merely
  planned — with that member added, the un-narrowed reply arm would have reached
  ten against the old ceiling of nine.

The split is **licensed** rather than asserted: the four frames the tree lacked
— `endpointQueueRemove_objects_ne`, `abortPendingIpcOnEndpoint_other_tcb_eq`,
`abortHolderPendingIpc_other_tcb_eq` and
`returnDonatedSchedContext_other_tcb_eq`, each stating a step's effect *outside*
its write set — compose into `cancelIpcBlocking_replyArm_tcb_frame`, which shows
the reply arm rewrites exactly the holder, its two queue neighbours and the
cancelled caller, every one a declared member.  Building them retired the third
inlined copy of the neighbour-patch shape (`endpointQueueRemove_eq_patches` pins
it to `queueNeighbourPatch` by `rfl`).

**OD3.7 re-measures against 11 and against these shapes**, not against the
figures above.

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
