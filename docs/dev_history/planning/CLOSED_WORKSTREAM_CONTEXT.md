# Closed workstream context (archived)

> The per-workstream status sections for workstreams that have **closed**,
> moved verbatim from the "Active workstream context" section of `CLAUDE.md`
> (via `docs/agent_guide/WORKSTREAM_CONTEXT.md`); only relative link targets
> were rewritten.  Retained for traceability only.  Live workstream status is
> in `docs/REGISTERED_DEBT.md` and `docs/agent_guide/WORKSTREAM_CONTEXT.md`.

### WS-RA Syscall Return ABI — COMPLETE (v0.33.37; RA.B.5b + RA.B.8 at v0.33.38)

The kernel returns seL4's ARM64 frame exactly: `x0` = badge / primary result at
full 64-bit width, `x1` = `MessageInfo` whose label carries the kernel status in
the **top** of the 20-bit label range (`0` = success, `errorLabelBase + d` =
discriminant `d` with `errorLabelBase = 0xFFF00`; every label below the base is
a delivered message's own — a fault handler's `seL4_Fault_tag`, for one),
`x2`-`x5` = message registers.  `SYSCALL_ABI_VERSION = 3`, pinned in Lean,
`sele4n-types` and the HAL.  Version 2 carried the status as label `d + 1`
and was retired at v0.34.44 (WS-RR RR4 audit round): a delivered fault
message's tag decoded in userspace as a kernel error, so no fault handler could
be written against `sele4n-abi`.  New code must not treat a nonzero `x1`
label as an error; `ofErrorLabel?` / `decode_response` decide by range.

Return-frame *delivery* is the context restore's, and it is live since WS-BP
BP7.6 (`v0.36.19`): a blocked caller resumes with the frame the kernel later
stages into its context, and a caller that took a fault at the seam (outcome tag
2, `.faulted`) resumes its successor like any other.  What survives is the
fail-closed answer on a core where no restore was staged: a blocked caller's
frame poisoned with `blocked_resume_sentinel_regs()`, so a stale request
register can never decode as a success, and a faulted one's core halted (PR #887
review round 5) — never `eret`ed past its `SVC`.

**A forcibly unblocked thread is staged an error frame** (WS-RR RR7.14,
v0.34.67) — the other half of §9's registered obligation, and closed.  A thread
taken out of a blocking IPC has no value to receive, and both unblocking paths
staged nothing, so the context restore would have delivered its own argument
spill back as a return value.  They now stage, and they stage **different**
errors because they are different facts: `timeoutThread` stages
`Architecture.timeoutFrame` (`.ipcTimeout` — the budget expired under a
well-formed operation, which the caller may reissue), and `cancelIpcBlocking`'s
four blocked arms stage `Architecture.cancelledIpcFrame` (`.ipcCancelled`, a
new `KernelError` at discriminant **57** — the operation was destroyed, so
reissuing may be meaningless and a userspace library cannot write a correct
retry against a conflated code; `timeout_and_cancelled_frames_differ` is the
pin).  seL4 answers this by setting the thread `Restart`; this kernel has no
restart state, so the crossing ends in a distinguishable error.  Three things
new code must respect.  (1) **Two paths stage nothing, deliberately**:
`cancelIpcBlocking`'s `.ready` arm commits no write at all, and `restoreToReady`
— the *resume* spelling of the same field clear — stages nothing because
`.tcbResume` restarts a thread where it was (RR4.11's
`retirePendingFaultForResume` is the fault half of the same posture), so
overwriting `x0`-`x5` would destroy the window the restart preserves.  Both are
pinned as negatives.  (2) **One field clear, two spellings**:
`restoreToReadyStaging` takes the frame as an argument and `restoreToReady` /
`restoreToReadyCancelled` are its `none` / `some` instances, so every framing,
`invExt`, `ipcInvariant`, `tcb_lookup`, identity and projection result is stated
once and instantiated twice, and a field added to one clear and not the other
fails to elaborate (`restoreToReadyCancelled_tcb`).  (3) **The staging is
confined to the TCB**: `contextMatchesCurrentOnCore` compares a core's register
bank against its **own current thread's** saved context and reads no other
TCB's, so `objects_change_preserves_schedulerInvariantStructuralRegNodup_smp`'s
`hReg` is scoped to the current thread and
`storeObject_tcb_preserves_schedulerInvariantStructuralRegNodup_smp` takes a
disjunction (the context is unchanged **or** the thread is current on no core);
demanding the equality at every thread — as it did — is strictly stronger than
the conclusion needs and refuses this write.  The information-flow half needs no
new argument because the frame goes into the victim's *own* TCB, which holds
only because `writeReturnFrameToTcb` deliberately does not touch `machine`.

Plan: [`docs/planning/SYSCALL_RETURN_ABI_PLAN.md`](../../planning/SYSCALL_RETURN_ABI_PLAN.md).

### WS-OD SchedContext donation chains — COMPLETE (registered v0.34.98; OD1 v0.34.108, OD2 v0.34.125, OD3 v0.35.1, OD4–OD6 v0.35.2)

`applyCallDonation` donated only from a **`.bound`** caller, and
`donateSchedContext` is the only operational construction site of a `.donated`
binding — so a scheduling context stopped at the first passive server and seL4's
passive-server pattern did not work at call depth ≥ 2, where the callee stayed
`.unbound` and could never run.  seL4-MCS's `maybeDonateSchedContext` reads the
sender's *effective* context, bound or donated, and passes it down the chain; so
does this kernel since **OD4** (`v0.35.2`).  Two register rows close here: that
gap, and the `passiveServerIdle` break the `v0.34.97` reclaim introduced.
**53 sub-tasks across OD1..OD6, all closed** — OD1 `v0.34.100` → `v0.34.108`,
OD2 `v0.34.125`, OD3 `v0.34.126` → `v0.35.1`, OD4–OD6 `v0.35.2`.

**The chain is transitive, and what new code must respect** (OD4–OD6, `v0.35.2`).
Six things.  (1) **The guard is the caller's *effective* context**:
`callDonationSchedContext?` and the footprint's `endpointCallDonatedSc?` both
answer `SchedContextBinding.scId?`, so a `.donated` caller donates exactly as a
`.bound` one does, and neither the transition nor its footprint can widen without
the other.  (2) **`donateSchedContext` is a four-store *push*** whose frame is the
donor's own `replyObject`, and it is **fail-closed** on that frame
(`donationPushFrame?`: no reply object, an unresolvable one, or one that already
donates are three refusals).  A donation with no stack frame is what lets the next
pop clear an *outer* caller's frame and settle a context on the wrong thread.
(3) **The `.call` footprint does not grow**
(`lockSet_endpointCallOnCore_covers_donationPush`) and `maxLockSetSize` is
unmoved: every key the push writes is a declared write member already.  (4)
**Every pop resolves its new owner** — all six sites run
`returnDonatedSchedContextResolved`, and the obligation that carries is
`replyStackOuterCallerValid` (with `cleanupDonationStackValid` and
`cancelDonationStackValid` as its two call-shaped siblings), vacuous wherever no
context heads a stack.  (5) **A Reply that still donates cannot be freshened or
retyped, and neither can a context that still heads a stack** — `linkReply` and
`lifecyclePreRetypeCleanup` refuse rather than clear, because clearing takes a
frame off a stack the context still heads and the walk would then stop mid-chain.
(6) **A cancelled *middle* caller is SPLICED out of the stack**
(`cancelledMiddleCallerPolicy = .spliceOutTheCut` since WS-HP HP6.8, `v0.35.45`,
proved by `cancelledMiddleCaller_splices_at_cut`): the frame above the cut takes
the cut frame's own downward link and the frame below links back up at it, so the
reservation goes on travelling outward to the caller the surviving stack names
(`.donated scId outer`) and no thread below the cut is touched.  **Up to `v0.35.44`
it severed** — `cancelledMiddleCallerPolicy = .severAtCut`, the innermost live
caller keeping the context `.bound scId` and its owner left `.unbound` for good —
and that is **what seL4-MCS does**, re-verified at `v0.35.40` against upstream
source at master, 13.0.0, 12.1.0, 12.0.0 and 11.0.0: `reply_remove`'s non-head
branch writes `REPLY_PTR(next_ptr)->replyPrev = call_stack_new(0, false)` under the
comment *"not the head, remove from middle - break the chain"*.  It writes
**zero**, not the cut frame's own `replyPrev`.  `v0.35.14` asserted the reverse
here and quoted a line that exists in no release; see *the removal does not
preserve the donation accounting* below for what that retraction cost.  So the
splice is an **improvement on upstream** rather than an adoption of it, measured at
reply-stack depth three in `tests/SmpIpcSuite.lean` §3.22 and stated as
`donationAccountingPreserved_atCallDepthThree`; what it provably cannot reach is
the depth-**two** loss, where both policies write `none` into the frame above a
bottom frame, and that is closed instead by the reservation's recorded origin
(`donationAccountingPreserved_atCallDepthTwo`, WS-HP HP10.9, `v0.35.53`).
One consequence for the suspend footprint:
the teardown can rebind the victim `.donated`, and the arm selector re-reads the
*post*-teardown binding, so the pipeline pops twice at depth ≥ 2 and
`suspendThreadOnCoreSchedLockSet`'s replenish segment carries a **triple** for
G3 alone (`v0.35.170` appends G2's own migration pair beside it, which is a
different thread's home and a different state).  The payoff
is `passiveServerHoldsDonatedContext_atCallDepthTwo`.

Six things new code must respect once this lands, and each is a decision the plan
records rather than a default it inherited.  (1) **The `passiveServerIdle` hole was
OD1, not a consequence of the chain**, and is **closed**: it was live on HEAD at
depth 1 — a server that Calls an endpoint with no receiver blocks
`.blockedOnCall` keeping its donation, and the reclaim then unbound it in place —
so fixing it last would have meant every later phase doing bundle work over a
known-false conjunct.  See the two standing constraints above for what the
reclaim now does.  (2) **The pop
lands before the push, and lands inert**: with the push first, a depth-2 chain is
serviced by the flat return, which writes `.bound` at the intermediate thread and
moves a context across a domain boundary in a state that *breaks no conjunct*.
(3) **`SchedContext.scReply` is built** — done at `v0.34.125`, because
`Reply.wellFormed`'s docstring already required the context's head to agree
with this reply, of a field that did not exist, and because without it the push must
read the owner's TCB and the outer reply, taking `lockSet_endpointCall` to ten
against a ceiling of nine.  Four things OD2 fixes about the surface new code
writes against.  The field is **erased by `projectKernelObject`** in the same cut
that adds it (`projectKernelObject_schedContext_scReply_invariant`), or the OD4
push would be observable in the interval; a **boot SchedContext heads no stack**
(`bootSafeObjectCheck` refuses one, since every admissible boot Reply is inert,
so a config-supplied head could only dangle); **`Reply.wellFormed` is no longer
`True`** but "a `prev` link only on a reply that is itself on a stack", with the
two store-level clauses its docstring also promised stated in
`donationChainWellFormed`, which carries it as its own first conjunct; and the
chain invariant is a conjunct of **`ipcReachable`**, not of `ipcInvariantFull`
(twenty, unchanged), *preserved* through `donationChainFrame` rather than
assumed.  The frame is stated over the two projections the walk actually reads
(`replyStackLinks?`, `schedContextStackHead?`), so it **is** the read set rather
than an over-approximation of it, and a field the chain starts reading has to
enter a projection before any frame can be re-proved.  And the predicate is
known to **decide** rather than refuse: it is discharged vacuously everywhere
today, so `donationChainWitness_wellFormed` proves it whole — completeness
clause included — of the store a depth-2 Call chain leaves, which is what stops
an over-strong conjunct from hiding behind an obligation that never fires.
(4) **The pop's new owner is an argument**, since the reply leg consumes the
target's reply link before the donation return runs.  (5) **The pop validates the
link it follows** — Reply objects are re-linked to new callers, so a stale
`prev` over a reused Reply would hand a thread's context to an unrelated thread
in another domain.  Since `v0.34.125` that validation is *structural*:
`donationChainFrom` follows a link only after checking the target's own
**upward** link against the frame that reached it, never its `caller`, and a
Reply carrying no upward link is provably on no chain
(`not_mem_donationChainFrom_of_unlinked` — the freshness fact the push
consumes).  Relinking clears both links (`Reply.isFree`), so a reused Reply
carries no answer back and the walk stops at it.  (6) **The binding's
`owner` stays the immediate donor**, which is what keeps all five donation
conjuncts true at depth `n` unchanged and leaves the *binding* graph chain-free —
the chain lives entirely in the reply stack.

**The pop validates what it hands out** (OD3.4, `v0.34.127`).
`returnDonatedSchedContext` refuses an outer caller that is not a *waiting donor*
— a stored TCB that is `.unbound` and `.blockedOnReply`, and neither of the two
threads the pop rewrites (`outerCallerAcceptable`, O(1), fail-closed, part of
`returnDonatedSchedContext_ok_storeChain`).  `donateSchedContext` has always
checked its donor side before minting a `.donated` binding; the pop mints one too
and checked nothing, which is why the depth-≥ 2 obligation was unusable — on the
reply path the answered caller is already `.ready`, so no consumer could discharge
it.  Three of `donationReturnOuterValid`'s four clauses are now consequences of
the operation succeeding; the fourth (`outerUnowned`) is whole-store quantified
and stays a caller obligation.  `replyStackOuterCaller?` is the pre-state resolver
the call sites will use: it walks exactly one link past the stack head, answers
three ways (bottom of stack / the outer caller / a link that does not validate),
and validates the frame below the head so a re-linked Reply cannot redirect a
context.  **New code must not read the frame as fixing the resolver's answer** —
`donationChainFrame` deliberately excludes `Reply.caller`, so it transports
resolvability only.  **All six call sites thread the resolver since OD4.4**
(`v0.35.2`): each runs `returnDonatedSchedContextResolved` on its own pre-state,
and the obligation that carries is `replyStackOuterCallerValid` — with
`cleanupDonationStackValid` and `cancelDonationStackValid` as its two
call-shaped siblings.  A site that passes a literal `none` is a site that has
not been threaded; OD3's `hBottom` condition on
`returnDonatedSchedContext_preserves_ipcInvariantFull` was removed by OD4.3,
which is what made the threading possible.

**And a receive rendezvous hands over the caller's *priority*, not only its
budget** (OD3.14, `v0.34.141`).  `resolveEffectivePrioDeadline` is
`max basePrio pipBoost`, and the inherited **boost** travelled by no route at
all on the `.receive` arm, which ran no `propagatePipChainCrossCore` while
`.call` and `.replyRecv` both did.  (At OD3.14 this row also read OD3.6's
donation as moving the caller's *base* priority to the donee.  It no longer
does: since `v0.35.3` a donee runs on the donor's budget, deadline and domain at
**its own** priority, so the chain walk described here is the **only** priority
route between a client and the server it calls — which makes this row
load-bearing rather than a second-order correction.)  A chain `D → C → S` — `D` blocked on `C`,
`C` dequeued into `.blockedOnReply` on the passive server `S` — therefore left
`D`'s priority stopping dead at `C`: unbounded priority inversion, on the arm a
passive server takes its *first* request with.  It bites with **no** donation
too, since `applyCallDonation` is the identity for an already-`.bound` receiver
that still gains the waiter.  Pre-existing rather than introduced by OD3.6, and
reported as a possible vulnerability before being fixed.  Five things new code
must respect.  (1) **The guard is read once, from the pre-state**:
`applyReceiveRendezvousHandoff` is OD3.6's donation and the walk under a single
`if`, so the two provably fire on the same states — a second reading on the
post-donation state would owe an `ipcState` frame lemma, and a Tier 3 negative
refuses it.  (2) **The walk starts at the receiver**, which is `.call`'s own
start point (`endpointCallCrossCoreDispatch`) and the one `.replyRecv` reaches
when its reply is not delegated.  (3) **The sibling gap closed in the same cut**:
`.replyRecv` walks from the *recorded server*, which is the receiver only on a
non-delegated reply, so `applyReceiveLegPipHandoff` adds the receiver's walk
**gated on the equality that makes the first walk be it** — the non-delegated
arm is unchanged, byte for byte.  (4) **The write set grew**: a chain walk
re-buckets run queues on the members' home cores, so `replyRecvBodyWriteSet`
carries a fourth leg (`receiveLegPipHandoffWriteSet`, read at the state that leg
runs at) and `.receive` declares `receiveRendezvousHandoffWriteSet`, whose chain
leg is a *parameter* because it runs at the post-donation state.  (5)
**`maxLockSetSize` does not move, and that is a decision**: a chain is
state-discovered and unbounded, so its locks are declared through the
`pipChainStart_<τ>` markers the SM3.C walker consumes rather than through
`lockSet_<τ>`, which is what keeps the static footprint honest.  The marker
family grows with the *walks*, not the syscalls — `pipChainStart_endpointReceive`
and `pipChainStart_replyRecvReceiveLeg`, with the reply leg's own marker
corrected to name the recorded server it actually walks from rather than the
caller the retired single-core transition walked from.

**And the receive-side arms declare it too, at the cost of the ceiling** (OD3.12
and OD3.13, `v0.34.137`).  `.receive` and `.replyRecv` pop the endpoint's **send**
queue or block on its **receive** queue -- the same two primitives, the same one
neighbour TCB -- and `.replyRecv`'s receive leg *is* `.receive`'s transition, so
one resolver (`receiveSideQueueStructureNeighbor?`) serves both.  `.replyRecv` was
at 13 of 13, so **`maxLockSetSize` is 14**: `admissibleCriticalSection` for the
1 ms tick falls 25 → **23 µs**, the uniform 60 µs envelope moves 2340 → 2520 µs,
and the sharp reachable `.replyRecv` bound goes 12 → 13 (the *gap* between
ceiling and sharp bound is unchanged at one).  Every one of those figures is
derived from the constant and moves with it, which is why they are theorems
rather than paragraphs.  Read the cost against the alternative: a footprint that
omits a written object is **false**, and every statement built on
`lockSetForSyscall` -- the 2PL serialisation results,
`boundedWait_under_2pl`, the CC-5 bound -- was *silent* about that TCB rather
than conservative.  **With this cut all eight declared syscall arms name every
object they write**, and the sweep that began at OD3.9 is closed.  Two mechanical
notes: the sharp bounds are *renamed*, not weakened -- OD3.13 spelled them
`lockSet_replyRecv_size_le_thirteen_of_owner_eq_target` and
`lockSet_endpointReplyRecvOnCore_size_le_thirteen`, and **neither name is live**:
the first was deleted at `v0.35.50` with the rest of the `_of_owner_eq_target`
family, whose merge HP6.2 refuted, and the reachable `.replyRecv` bound is
`lockSet_endpointReplyRecvOnCore_size_le_eighteen` -- and a new cut that widens a
footprint pays at `admissibleCriticalSection_rpi5Tick`, visibly.

**And `.send` / `.call` declare the queue-structure neighbour** (OD3.11,
`v0.34.136`).  Every `.send` / `.call` / `.receive` / `.replyRecv` either **pops**
the head of one endpoint queue or **enqueues** the caller on the other, and each
writes exactly one TCB besides the operation's two principals: the pop relinks the
popped thread's successor into the head, the enqueue relinks the queue's old tail.
No footprint named either.  Four things new code must respect.  (1) **One
definition** -- `endpointQueueStructureNeighbor?`, with the branch decided by the
same resolver the arm's receiver/sender member already comes from
(`endpointCallReceiver?` / `receiveRendezvousSender?`), so the footprint and the
transition cannot disagree about which branch a call takes; a Tier 3 negative
refuses re-reading the queue head at the instance.  (2) **An `Option`, not a
pair**: the two cases are mutually exclusive, so each arm grows by one member.
(3) **Restated at full arity everywhere** -- both size bounds, both
kind-consistency proofs, the four write-membership lemmas, the
`lockSetTransitions_within_bound` conjuncts, `KernelOperation.ofCall`, and the
WithCaps footprint, which *is* the base at `some destCnodeObjId`.  (4)
**`lockSet_endpointCallOnCore_capless` carries the resolver**: "capless" is a
property of the *message*, and a call carrying no capabilities still pops or
enqueues, so fixing the member at `none` there would describe a footprint the
transition does not declare.  `maxLockSetSize` is unmoved (`3 + 4 = 7`,
`3 + 6 = 9`).  `.receive` and `.replyRecv` are the same shape and not yet
declared.

**And `.notificationSignal` declares the two TCBs its dequeue relinks** (OD3.10,
`v0.34.135`).  The bound-delivery path runs `endpointQueueRemoveDual`, which writes
the removed thread's predecessor and successor TCBs, and `lockSet_notificationSignal`
named neither -- so a `.notificationSignal` on one core and a `.tcbSuspend` of a
queue-mate on another had provably disjoint footprints while both writing the same
TCB.  Latent rather than live (SM5.I's global entry lock serialises every kernel
entry, and nothing boots yet), which makes it a *verification* defect: everything
built on `lockSetForSyscall` was silent about those two objects rather than
conservative.  Four things new code must respect.  (1) **The resolver is derived
twice over**: `notificationSignalSpliceNeighbors?` takes its arm gate from
`boundDeliveryTarget?` -- the resolver the arm's other two members already come
from -- and its neighbour identities from `queueSpliceNeighbors?`, so neither the
footprint and the transition nor the two footprint families can disagree.  A Tier 3
negative refuses the inlined pair.  (2) **`cancelSpliceNeighbors?` is now
`queueSpliceNeighbors?`**, beside the link fields it reads: it was one family's
private spelling of a fact that is not cancellation-specific, and adding a second
reader without unifying it would have been OD3.9's divergence one level up.  Arm
*selection* stays per arm -- which thread is spliced is an arm question, who its
neighbours are is not.  (3) **Every statement about the footprint is restated at
the new full arity** -- the size bound, the kind-consistency proof, the three
write-membership lemmas and the `lockSetTransitions_within_bound` conjunct; a
bound left at a new argument's default is a different proposition, which RR7.18's
census refuses for sizes and which nothing covers for the others.  (4)
**`maxLockSetSize` does not move**: the shape is `3 + 5 = 8`, so
`admissibleCriticalSection` stays at 23 µs and the published contention bound is
unchanged.  The remaining arms the same sweep found -- `.send`, `.call`,
`.receive` and `.replyRecv`, each writing one queue-structure TCB (the new head
on a rendezvous, the old tail on a block) -- are the rows after this one.

**The three endpoint-queue removals write one definition** (OD3.9, `v0.34.134`).
`spliceOutMidQueueNode` -- the removal `.tcbSuspend` and thread destruction run --
patched its successor's `queuePrev` and not its `queuePPrev`, leaving it naming
the removed thread.  That is the field `endpointQueueRemoveDual` validates
(`pprevConsistent`), and after the splice it fails in *every* case there was a
successor: as the new head because it **is** the head, as an interior node
because its `queuePrev` now names its new predecessor.  So the successor could
never again be dequeued by the dual removal and every later bound-notification
delivery to it returned `.illegalState` -- reachable by suspending the thread
merely *ahead* of a passive server, over which the caller holds no authority, and
single-core logic rather than a race, so SM5.I's global entry lock does not mask
it.  Four things new code must respect.  (1) **What unlinking writes is
`queueUnlinkPredecessor` / `queueUnlinkSuccessor`** (`Model/Object/Types.lean`,
beside the fields they maintain), and the successor's carries both link fields;
a new removal calls them rather than spelling a record update.  (2) **The third
removal is tied to them by a theorem, not by a name**:
`endpointQueueRemoveDual_stores_queueUnlinkSuccessor` / `…Predecessor` are about
the object the operation *stores*, since that one spells its write through
`storeTcbQueueLinks`.  (3) **No `ipcInvariantFull` conjunct reads `queuePPrev`**,
which is why nothing caught either instance; the sharp pointwise readings
(`spliceOutMidQueueNode_tcb_value`, `sweptAndRestored_tcb_value`) now state the
field, so a reading that omits it is a statement about a different operation.
(4) **`endpointQueueRemove`'s comment claiming the dual removal is "the removal
every other kernel path uses" was false when OD1.1 wrote it** -- this is that
finding's third copy, and it survived eight cuts because the fix was applied to
the copy the finding named.  A removal added later is a fourth: sweep, do not
patch.
**...and the agreement between the two link fields is an INVARIANT, not a
per-site obligation** (WS-RR RR8.3, `v0.35.57`).  `queuePPrev` carries exactly
**one bit** beyond `queuePrev` — whether the node is linked into a queue at all —
and every other bit of it must agree: `.endpointHead` iff there is no
predecessor, `.tcbNext p` iff the predecessor is `p`.  Nothing stated that, and
that is *why* OD1.1 and OD3.9 each found a removal writing `queuePrev` alone: no
`ipcInvariantFull` conjunct read the field, so a stranded successor — one that can
never leave its endpoint queue again — was invisible to the proofs and to the
harness alike.  Six things new code must respect.

(1) **`queuePPrevAgreesWithPrev` is `dualQueueSystemInvariant`'s fourth
conjunct**, so `ipcInvariantFull` still has twenty and the bundle family is
untouched — and since `v0.35.99` its `none` arm says **`queuePrev = none`**
rather than nothing.  It read `True`, on the stated ground that
`tcbQueueLinkIntegrity` forbids a dangling `queuePrev`; that conjunct forbids a
`queuePrev` whose target does not point back and never mentions `queuePPrev`, so
a *queued* interior node carrying no back-pointer satisfied every conjunct while
the dual removal — whose guard takes a `QueuePPrev`, not an `Option` — refused it
outright and could never dequeue it.  The field was weaker than the one bit it is
documented to carry.  A new writer therefore states both back-pointers, which
every existing one already wrote: the strengthening cost six discharge sites and
changed no operation, no queue and no fixture — but every transition in the tree now carries it, and a new one must.
The cheap route is `queuePPrevAgreesWithPrev_of_frame` (every surviving TCB keeps
its two link fields) or, for a queue writer, the per-primitive siblings
`storeTcbQueueLinks_preserves_queuePPrevAgreesWithPrev` and
`storeObject_tcb_preserves_queuePPrevAgreesWithPrev`.  The bundle has **named
accessors** (`.endpointsWellFormed` / `.linkIntegrity` / `.chainAcyclic` /
`.pprevAgrees` / `.headDisjoint`) so the fifth conjunct `v0.35.106` added did not
shift a single projection path, and a positional `.2.2` into it is now a statement
about a pair.

(2) **The dual removal's precondition is a named definition the transition
reads.**  `dualQueueRemovalGuard` *is* `endpointQueueRemoveDual`'s
`pprevConsistent`, which was an anonymous `let` — which is why no caller could
state that it had established it.  A Tier 3 negative refuses the inlined spelling
coming back beside the named one, and eight proofs `unfold` the name, so deleting
it is a build failure rather than a silent pass.

(3) **The guard factors, and only one factor is the invariant's.**
`dualQueueRemovalGuard_eq_position_and_pair` splits it into
`queuePPrevHeadPositionAgrees` and `queueLinkPairAgrees`;
`dualQueueRemovalGuardHolds` discharges the second from the conjunct and the first
from **membership**, which stays a hypothesis because no invariant entails it — a
thread on *no* queue also has `queuePrev = none`, so `.endpointHead` alone cannot
say which queue's head it names.  Measured rather than asserted: a detached thread
carrying `(none, .endpointHead, none)` satisfies the pairing and fails the guard
(`tests/NegativeStateSuite.lean`).  Membership is spelled the way this tree
already spells it — the head itself, or reachable from it — and
`QueueNextPath.lastEdge` is what turns reachability into a predecessor, the
sibling `firstEdge` had lacked because the inductive is written forwards.
`dualQueueRemovalGuardHolds_of_dualQueueSystemInvariant` is the same discharge in
the shape callers hold, taking the endpoint rather than the queue.

(4) **The retype replacement is pristine in `queuePPrev` too, and that is not
derivable from `queuePrev = none` beside it**: a replacement carrying `.tcbNext p`
with no `queuePrev` *refutes* the pairing rather than satisfying it vacuously.  It
sits next to `queuePrev` in `retypeReplacementFresh`, because the two are one
back-pointer, at the cost of shifting twelve positional destructurings — which is
the price of keeping the pair together and was paid deliberately.

(5) **The unlink updates are where the pair is shown to travel together.**
`TCB.queuePPrevAgreesWithPrev_queueUnlinkSuccessor` (the successor inherits the
*removed* thread's own pair) and `…_queueUnlinkPredecessor` (only `queueNext`
moves) are the machine-checked form of the OD1.1/OD3.9 finding, composed by
`queueNeighbourPatch_preserves_queuePPrevAgreesWithPrev` into
`spliceOutMidQueueNode_preserves_queuePPrevAgreesWithPrev` — the third removal's
own statement, which the cancellation composite then consumes rather than
re-deriving.

(6) **The conjunct is checked at runtime, not only proved.**
`queuePPrevAgreesWithPrevChecks` is part of `stateInvariantChecksFor`, so every
harness state asserts it; the golden trace's `[PIP-005]` count moved 27 → 28,
which is the measurement that it runs.  Its witness is decisive in both
directions, and the mutation that decides **keeps every queue and every
`queueNext` chain and corrupts one back-pointer**.

**...and the head's back-pointer is the QUEUE's fact, not the TCB's — so it needed
a fifth conjunct** (PR #897 review, `v0.35.106`).  RR8.3 closed *present but wrong*
and `v0.35.99` closed *absent on an interior node*; what both left open is the
**head**.  `queuePrev = none` is what a detached thread carries **and** what a
queue's head carries, so `queuePPrevAgreesWithPrev` — a pointwise predicate over
one TCB — structurally cannot distinguish them, whatever its `none` arm is
strengthened to.  A queue whose sole member carried `(none, none, none)` therefore
satisfied every conjunct of the bundle while `endpointQueueRemoveDual` refused it
with `.endpointQueueEmpty`: the OD1.1 / OD3.9 stranding class a **fourth** time, and
this time on a queue that is not empty.  **And the tree had already decided it in
the other artefact**: `intrusiveQueueWellFormedB`, the check every harness state is
asserted against, has required `headTcb.queuePPrev = some .endpointHead` since it was
written — *one question answered in two places*, with the Bool right and the Prop
wrong, and the divergence sitting exactly where the proofs are silent.  Six things
new code must respect.

(1) **The clause lives in `intrusiveQueueWellFormed`'s P2**, beside `queuePrev =
none`, because it is a fact about a *queue's head* and a pointwise TCB predicate
cannot say it.  A new queue writer states both link fields of a head it installs;
`storeTcbQueueLinks_preserves_iqwf`'s `hHeadOk` carries the pair.

(2) **`endpointQueueHeadDisjoint` is `dualQueueSystemInvariant`'s FIFTH conjunct**,
and `ipcInvariantFull` still has twenty.  It says a thread heads at most one
endpoint queue, counting send and receive as different queues — which is what a
*clearing* writer needs, since with the back-pointer in P2 it must show the thread
it clears heads none of the queues it transports, and `endpointQueueNoDup` gives
disjointness only *within* one endpoint.  The bundle's named accessors gained
`.headDisjoint`, and that RR8.3 built them "before a fifth conjunct arrives" is the
measurement that the shape paid: no projection path moved.

(3) **It is a consequence of `ipcInvariantCore`, not a new assumption.**
`queueHeadExclusive` derives it from `queueHeadBlockedConsistent` — a head's
`ipcState` names *its* endpoint and *its* queue kind, and a thread has one
`ipcState` — with `queueHeadKindExclusive` the same-endpoint corollary (which
re-derives `endpointQueueNoDup`'s disjointness clause) and
`endpointQueueHeadDisjoint_of_queueHeadBlockedConsistent` the builder.  So nothing
*assumes* exclusivity; the conjunct exists so the bundle can **transport** it
without reading an `ipcState`, which is what keeps it inside this bundle's charter.

**...and it is checked at runtime too — since `v0.35.108`, not since it was added**
(PR #897 review).  RR8.3's item (6) had recorded the rule one cut earlier ("the
conjunct is checked at runtime, not only proved") and `v0.35.106` added the conjunct
with no check, so this is that rule unswept at the very next opportunity.  The gap
was not one omitted call: **nothing** in `stateInvariantChecksFor` was
cross-endpoint — `endpointDualQueueWellFormedB` is literally the two per-queue
checks of one endpoint — and nothing tied an endpoint queue's head to its own
`ipcState`, so a state the bundle refuses passed the entire surface.  Two endpoints
each holding `{head := some t, tail := some t}` over one thread the live enqueue
left with `(none, some .endpointHead, none)` is that state, and popping either queue
then clears `t`'s links and strands the other: the OD1.1 / OD3.9 stranding class a
fourth time, on a queue that is not empty.  `endpointQueueHeadDisjointChecks` asks,
per occupied head, whether any **other** `(endpoint, kind)` claims it — so it is
robust to a repeated index entry and it names the colliding pair, which is the whole
content of a disjointness failure.  Three things its witness records.  A violating
state **cannot** be reached by live operations (every kernel queue writer maintains
disjointness by construction, which is why the conjunct is provable), so the witness
writes the second endpoint's boundary by hand through `corruptEndpointQueueHeads`,
as the RR8.3 witnesses write a corrupted back-pointer by hand.  Its claim is a
**differential** against the control rather than "the only failing check is the new
one", because `baseState`'s TCBs are unsynced and two `threadState` checks fail on
both states — a plain claim there would have been false for a reason unrelated to
the finding.  And the strand is measured rather than described: the pop is taken
with `expectOkVal`, because `expectOkSt` asserts the invariant surface on the
post-state and that post-state is the corrupt one the finding is about.  The golden
trace's `[PIP-005]` count moved 28 → 29, which is the measurement that it runs.

(4) **A writer discharges it locally, from its own guard.**
`endpointQueueHeadDisjoint_of_singleQueueUpdate` (itself derived from the general
`_of_freshHeads`) takes two obligations, and each queue writer already has them: a
pop promotes a successor, which has a predecessor
(`not_queueHead_of_queuePrev_some`); an enqueue promotes a thread its own guard
refused a back-pointer to (`not_queueHead_of_queuePPrev_none` — the strengthened P2
paying for itself); a mid-queue removal and a tail append move no head.  The two
operations that clear a *victim's* links without owning its queues — the
notification purge and the reply-path restore — take the victim's off-boundary fact
as a **stated** hypothesis (`hOffEp`), which the composite holding the whole bundle
supplies from `queueHeadBlockedConsistent`, because a thread blocked on a
notification or a reply bounds no endpoint queue.

(5) **The payoff is a retired caller obligation.**  A queue member's `queuePPrev` is
now derived rather than hypothesised — at the head from P2, at an interior node from
`tcbQueueLinkIntegrity`'s forward clause plus the pairing — so
`queuePPrev_of_queueMember` joins the halves and
`dualQueueRemovalGuardHolds_of_member` is `dualQueueRemovalGuardHolds` with `hPPrev`
discharged.  `hMem` and `hTailLast` remain, because queue connectivity and the
tail's identity are what no conjunct of this bundle entails.  Its witness is
`tests/NegativeStateSuite.lean` case (5), which reads the field off both states
directly — asserting the *field* rather than a predicate's verdict is what makes it
about P2's strengthening rather than about the pairing beside it.

**...and the BOUNDARY the removals write is one definition too — and asking the
fact rather than a proxy for it is what retires a stated hypothesis** (WS-RR
RR8.4, `v0.35.58`).  OD3.9 unified what a removal writes to the *neighbours*;
the queue's own `head` and `tail` stayed two readings, and the plan row that
scheduled this collapse said they "write the same fields to the same values
today".  They did not.  Both moved the head on `q.head = some tid`; for the tail
`endpointQueueRemove` asked `q.tail = some tid` while `endpointQueueRemoveDual`
asked `removed.queueNext = none` and derived the new tail from `queuePPrev`.
Under a connected queue the two conditions coincide, and `ipcInvariantFull`
joins a queue's boundaries **nowhere** — it constrains the head, it constrains
the tail, and nothing relates them — so on a state it admits, a queued thread
with no successor that is not the tail, they part: there the inferring form
cleared the tail and **stranded the queue's real tail**, a thread that could then
never be dequeued, which is OD3.9's own defect class arriving through the field
OD3.9 did not unify.

`queueRemoveBoundary` (`Model/Object/Types.lean`, beside `queueUnlinkPredecessor`
and `queueUnlinkSuccessor` — the third and last piece of "what does unlinking
write") is the shared definition, with the four shapes a guarded removal writes
named once (`queueRemoveBoundary_{headLast,headMore,midLast,midMore}`, read by
both the dual's invariant proofs and the `endpointQueueRemove_agrees_*` family).
Five things new code must respect.

(1) **`q.tail = some tid` is the fact and `removed.queueNext = none` is a
proxy for it**, so the shared definition asks the fact — this file's own *a proxy
is not the fact* rule, applied to a field rather than to a core.  Which reading
survives is not an arbitrary pick: the proxy's failure mode is silent (a
well-formed-looking queue with a thread missing from it) and the fact's is loud
(a head cleared without its tail, which `intrusiveQueueWellFormed` refuses), so
the fact fails closed where the proxy fails open.

(2) **Asking the fact leaves the proxy's direction to be established, and the
removal CHECKS it.**  `queueTailPairAgrees` — the queue's `tail` field and the
removed thread's `queueNext` agree about whether this thread is the tail — is the
first factor of `dualQueueRemovalGuard`, so the dual **refuses** the state on
which the two readings part rather than mishandling it, and
`dualQueueRemovalGuard_eq_position_and_pair` is restated over three factors.  One
direction is free from the bundle (a tail has no successor, so a thread with one
is not the tail — `spliceTail_ne_of_hasNext`) and the other is the missing
invariant, which is why this is a runtime guard and not a fifth conjunct.  The
biconditional is stated because "the tail question has one answer" is what it
means; refusing the free direction as well costs nothing, the bundle already
excluding it.

(3) **WS-OD OD1.3's `spliceRemovedIsTailWhenLast` is DELETED, and the deletion is
not its closure.**  Every consumer was already conditioned on the dual
succeeding (`dualRemovalEnabled`), so the guard discharges what the hypothesis
supplied: `SpliceShape`'s two no-successor branches carry `hTail` outright
instead of the weaker `tail.isSome`, and `endpointQueueRemove_agrees_with_dual`,
`endpointQueueRemove_establishes_ipcInvariantFullExceptMembership` and
`abortPendingIpcOnEndpoint_preserves_ipcInvariantFull` each shed a hypothesis —
the agreement now needs the dual's success and nothing else.  But queue
connectivity is still a **missing invariant**: the fact is now
`dualQueueRemovalGuardHolds`'s `hTailLast`, an obligation on whoever *calls* a
removal, where it is discharged from where the thread sits in the queue, rather
than one carried by every theorem *about* one.  A cut that reads the deletion as
"connectivity is now entailed" has read it backwards.

(4) **The pin is asymmetric, and measured rather than assumed.**  The dual's
boundary write is buried in a five-step program, so only a theorem can state it:
`endpointQueueRemoveDual_writes_queueRemoveBoundary`, hypothesis-free, replacing
two consumer-less WS-L3 tail theorems that specified the retired inference.  The
single's body is straight-line and its four `endpointQueueRemove_ok_*` shape
theorems already state its post-store *per branch*, so they fail if its boundary
changes — measured: a no-op mutation of its Step 3 fails four of them — and a
fifth restatement was **not** added, because that is the duplication this file
spends its length retiring.  What neither side pins is the *sharing*: an inlined
copy of the identical record would satisfy every one of those theorems, so that
is a Tier 3 negative, and its mutation keeps the values and breaks only the
sharing.

(5) **A plan row's premise is a claim, and this one was false.**  "They write the
same fields to the same values today" was written from reading both bodies'
*head* computations and generalising; the tail was where they differed and where
the defect was.  The row is corrected in place rather than quietly satisfied,
because a premise that survives a cut it motivated will be cited by the next one.

**And the boundary question had FOUR askers, not two** — the sweep rule catching
this cut's own plan row.  RR8.4's row said "the two endpoint-queue removals", and
OD3.9 four sections above had already established there are **three**: the third
(`removeFromAllEndpointQueues`) splits the work, so `spliceOutMidQueueNode` writes
only the two neighbour TCBs and its *boundary* write is `removeThreadFromQueue`
(`Lifecycle/Operations/Cleanup.lean`) — a fourth spelling of the same expression,
found by asking who else computes a queue boundary rather than by trusting the
row's enumeration.  It already asked the **fact**, so unifying it is a
de-duplication and not a behaviour change (`removeThreadFromQueue_tcb_present` is
byte-for-byte the boundary it wrote before, and
`removeThreadFromQueue_eq_queueRemoveBoundary` is the relation stated over the
shared definition).  Its `lookupTcb`-absent arm is deliberately **not** routed
through `queueRemoveBoundary`: with no TCB there is no removed thread whose links
a boundary could inherit, so that arm is the *absence* of a removal and routing it
through a synthetic link-free TCB would make the shared definition describe a case
it is not about.

**And running the sweep again found a FIFTH**, which is the whole argument for
running it rather than stating it.  `frozenQueueRemove`
(`Kernel/FrozenOps/Core.lean`) is the frozen mirror of `endpointQueueRemoveDual`
and computed the boundary itself, with `==` where the live ones use `=`.  It is
the asker a kernel-tree sweep structurally missed — until `v0.35.60` the frozen
surface was in neither library root, built only by its own test target — and it
is the **fifth** time this project paid for that (WS-RM's census at `v0.35.12`,
HP4.7's trigger at `v0.35.38`, HP8's splice at `v0.35.47`, HP10.8's origin clear
at `v0.35.52`, and this boundary).  **This paragraph said "third" for two cuts
after it was five**, in the file whose own rules retire hand-kept counts; the
root cause is closed at `v0.35.60` — see *a surface outside every derived domain
is checked by whoever remembers it* below.  Because the frozen store holds the **live** `TCB` and `IntrusiveQueue`,
a *model*-level definition applies to it directly, which is why
`queueRemoveBoundary` lives beside the two unlink updates in
`Model/Object/Types.lean` rather than in the IPC layer.  Two results worth
keeping.  The mirror already asked the **fact**, so it was **right** on the tail
question where the operation it mirrors was wrong, and nothing in the tree
compared the two on the state where they part — a differential surface can hold
the better answer and never be asked.  And its *guard* is a different matter: it
refuses only `queuePPrev.isNone` where the live removal refuses three things, so
it **succeeds where the kernel refuses**, which is the direction that matters on a
mirror; the guard family lived in the kernel layer the frozen surface deliberately
does not import, so relocating it to the model was its own cut — **taken at
`v0.35.59`**, and the next paragraph is what it measured.

**A plan row's enumeration is a recognised set**; the sweep is what makes it a
derived one — and a sweep that stops where the build roots stop is still an
enumeration.

**And a surface outside every derived domain is checked by whoever remembers it**
(`v0.35.60`, the maintainer's correction).  Every domain rule above polices one
gate's input.  This is the same defect at the scale of a **subsystem**, and it is
the one that produced most of the frozen-surface findings in this file.

`SeLe4n/Kernel/FrozenOps/` was in neither library root and in no staged
allowlist, built only by its own `lean_exe`.  Measured at `v0.35.59`: that put it
outside the *derived* domain of **five of the six** Tier 1 censuses
(`IpcDethreadingEnvironmentCensus`, `BootEntryContract`,
`ExportCommitDisciplineCensus`, `LockFootprintBoundCensus`,
`StoreReadClassificationCensus` — the sixth, `ReplyStackWriteCensus`, reaches it
only because `v0.35.12` widened it *by hand, after a defect shipped through the
hole*), and outside `check_production_staging_partition.sh` entirely, which has no
opinion on a module that is neither production nor staged.  It was executed
(Tier 2 runs `lake exe frozen_ops_suite`) and anchored in Tier 3, so it was not
unchecked — it was under-**derived**, which is the failure mode this section
spends its length retiring.

**The cost was five after-the-fact corrections**, each found by a later cut rather
than by a gate, on a surface carrying the **live** `TCB`, `Reply`, `SchedContext`
and `IntrusiveQueue` records and mirroring the reply and cancellation spines: a
caller's Reply cleared bare and a link guard reading `caller.isNone` where the
live kernel reads `Reply.isFree` (`v0.35.12`); a binding-driven trigger after the
live path went head-driven, plus a missing recipient guard and a missing ID
promotion (`v0.35.38`); still severing after the live removal spliced
(`v0.35.47`); never clearing `donationOrigin` (`v0.35.52`); and a duplicated queue
boundary followed by a guard carrying **one of four** refusals with the wrong
error code (`v0.35.58`–`v0.35.59`).

**...and a sixth, after the promotion, which is the measurement that says what the
promotion did and did not close** (PR #897 review, `v0.35.96`).
`frozenSchedContextBind` and `frozenSchedContextUnbind` were still keeping a
`donationOrigin` the live kernel erases — the `v0.35.52` correction's own class,
one operation over — and sweeping the **operation** rather than the field found
three more: the live bind refuses four things and the mirror refused one, and it
did not propagate `sc.priority` to the bound TCB, so every frozen post-bind state
falsified `boundThreadPriorityConsistent`.  Every one of those was invisible to
the promotion, because putting a module in the library root fixes which
*definitions* a gate can see and says nothing about whether a mirror **agrees**
with what it mirrors.  That second half is `docs/REGISTERED_DEBT.md` table C's
open row — a second implementation (the architecture's own *execute* phase, not a
test double) whose fidelity is checked by a hand-written scenario list — and the measurement here is what it costs: the three
missing refusals sit on an operation `frozenBranchDifferentiallyChecked` does not
name, so no `frozenRunAgrees` comparison could have reached them and none did.
**Promotion into the root is necessary and is not the fidelity check**; until the
coverage set is derived, a cut that touches a live transition with a frozen mirror
sweeps the mirror by reading both, and a cut that adds a *field* to a shared record
sweeps every writer of it on both surfaces.

**...and a seventh, where the divergence is inside ONE DECLARATION: a primitive
that guards its principal and not its neighbours** (PR #897 review, `v0.35.146`).
The three queue primitives resolve the thread they are *about* through
`frozenLookupTcb` -- which refuses a reserved id exactly as the live `lookupTcb`
does -- and read the queue's **tail**, **predecessor** and **successor** with the
bare `getTcb?` two lines below.  So a queue whose neighbour sits at
`ThreadId.sentinel` was accepted here and refused `.objectNotFound` by
`endpointQueueEnqueue` / `endpointQueueRemoveDual`.  No scenario driving the
principal could see it, and **none driving the neighbour existed** -- every fixture
on this surface exercises the thread a primitive is *about*, which is the half
that was already guarded.  Not because the states are unreachable:
`Builder.createObject` accepts a reserved `ObjId`, measured, and the cut's own
first reading had asserted the opposite and built its fixtures by hand on the
strength of it.  (`BootstrapBuilder.withObject` does refuse the slot, and
generalising from that one builder to both was the error.)  **When a declaration
resolves two threads, ask whether it resolves them the same way**; a shared name
two lines apart reads as one convention and is not -- and *a claim about what a
builder will not accept is measured, not inferred from its sibling.*

**And a MISSING WRITE is not a refusal, so no refusal-set comparison can find
it.**  The fourth site in that cut is the one no review reported and the worse
of the two kinds: `frozenQueuePopHead` wrote **no successor patch at all**, where
the live `endpointQueuePopHead` promotes the successor to head.  The thread the
pop *makes* the head went on naming the popped one, which fails
`intrusiveQueueWellFormed`'s P2 and -- through `dualQueueRemovalEnabled`'s
`queuePPrevHeadPositionAgrees` factor -- made **every later removal of it
`.illegalState`**: stranded for good, by one ordinary `frozenEndpointSend`
rendezvous into a **two**-deep receive queue, with no hand-built state anywhere.
That is WS-OD OD1.1 / OD3.9's own class -- *a removal that writes one of a node's
two back-pointers and not the other* -- arriving on the surface that has no
theorems to catch it, five cuts after this file recorded the class twice.
Every existing scenario pops from a **one**-deep queue, where there is no
successor and the two programs agree by construction: FO-043's lesson on a
different primitive, *a sweep for fixtures that would break is not a sweep for
fixtures that would exercise*.

Two things that cut records.  **The sweep found no fifth site, and saying so took
the measurement**: six other frozen definitions read `getTcb?` and are *faithful*,
each mirroring a live counterpart that reads the store raw too -- which is why the
Tier 3 negatives are **declaration-bounded** rather than file-wide, a tree-wide one
firing on a clean tree and saying nothing.  And **the two kinds of divergence need
two kinds of anchor**: a respelled read is caught by a negative forbidding the
relation, while a *deleted* store is caught only by the positive over what replaced
it -- *test a gate by breaking the relation, not by deleting the token*, read in
the direction where the defect **is** a deletion.

So: **the gates' domains nearly all key on library-root reachability, which makes
"not in a root" a silent exemption from most of this tree's defences.**  A
mirror deliberately shaped to be compared against production therefore gets the
weakest derivation precisely because it is not production.  The remedy is not a
sixth hand-widened census — that is the recognised set again — but to put the
surface **in the root**, which `SeLe4n.lean` does at `v0.35.60` with two imports
(`FrozenOps.Agreement` and `FrozenOps.Invariant` reach all five modules; the
dependency runs frozen → production and never the reverse, so no cycle closes).

Three things that promotion measured, and the first is the argument for having
done it earlier.  **The build was clean and only one gate fired**: the
content-flow coverage gate's property (C), on `frozenTaintFlow` and
`frozenTaintClear` naming the taint-writing API from outside the declared
propagation surface — because `FrozenSystemState.declassificationTaint` is the
*same* `TaintTable` as the live field.  Tier 0, Tier 2, Tier 3 and the partition
gate all passed.  That the promotion is cheap is not evidence the deferral was
harmless; it is evidence the five corrections had already paid the behavioural
price one cut at a time, and what remained was the **declaration**.

**A frozen writer is declared as a mirror, never folded into the live surface.**
Nothing in `FrozenOps` can move `SystemState.declassificationTaint` — which the
gate's property (C2) decides type-resolved — so adding the two to
`DECLARED_TAINT_WRITERS` would dilute the live one-writer fact into "one live
writer and some others".  `DECLARED_FROZEN_TAINT_WRITERS` maps each frozen
primitive to the live counterpart it reproduces, reconciled in **both**
directions (a key the probe no longer reports is a stale exemption reading as
coverage; a value outside the live surface names a counterpart that does not
exist), which is the shape `ReplyStackWriteCensus`'s `.mirrors` constructor and
`frozenBranchLiveOperation` already use for this question — *find the answer this
tree already has*.  Both directions are mutation-tested.

**And the gate that fired had already written the finding down.**
`DECLARED_TAINT_CONSUMERS`'s own note records a "frozen/live taint-layer
mismatch" that "survived until a differential scenario could start from a tagged
state".  The gate knew the frozen taint layer diverges; it could not see the
divergence, because the constants were not in its environment.  **A gate's
comment naming a hazard it cannot reach is the clearest possible signal that its
domain is too small** — and it sat there unread while five corrections landed
around it.

**And the published METRIC had been calling it production the whole time — which
is why this was reported as a documentation contradiction rather than found by a
gate** (the maintainer's correction, `v0.35.60`).  This is the sharpest part, and
it inverts how the deferral looked from outside.

`scripts/generate_codebase_map.py` computes `prod_paths` as *everything not under
`tests/`*.  So all five `SeLe4n/Kernel/FrozenOps/` modules have been inside
`readme_sync.production_files` (330) and `readme_sync.production_loc` (385,265)
since those figures existed — and those two numbers are mechanically synced into
`README.md`, `docs/spec/SELE4N_SPEC.md`, all **eleven** `docs/i18n/*/README.md`
and GitBook.  Meanwhile the source-layout line said "(experimental)", `SeLe4n.lean`
excluded it, `check_production_staging_partition.sh` had no opinion on it, and
four C.1 rows deferred "promotion into the production chain".

**Four artefacts, three answers to one question, and the artefact that reads as
authoritative was the one nobody had checked** — because it is *derived* and
published in fourteen places, where the others are hand-written prose or a build
file.  A reader who trusts the metric over the prose, which is exactly what this
file tells readers to do everywhere else, concludes FrozenOps is production; a
reader who opens `SeLe4n.lean` concludes it is not.  Both were reading correctly.

Three things follow.  **"Is this production" is one question and must have one
answer**: the import chain is now that answer, and the metric agrees with it
because the metric already did.  **A derived figure is not automatically the right
derivation** — `not under tests/` is a *path* convention standing in for a
*reachability* fact, which is this section's own `a field name is not a receiver
type` shape at the level of a build classification; it was never wrong about the
line count, only about what "production" names.  And **a contradiction between a
published metric and a build file will be reported by a person, not a gate**,
because no gate reads both: the partition gate reads the roots and the map reads
the filesystem, and nothing reconciles them.  That reconciliation is the check this
class needs, and `v0.35.60` makes it *true* rather than *checked* — the surface is
in the root, so the two agree — which is a state a later cut can silently break.

**Running that reconciliation by hand found one more, and getting the number right
took three attempts.**  Of the **331** files the metric counts as production,
**251** are in this root's closure and the rest are reached by `Platform.Staged`,
by a Tier 1 census, or by one of the 71 `lean_exe` roots — all but **one**:
`SeLe4n/Kernel/RadixTree.lean`, a re-export hub with zero in-tree consumers that
**no build target compiled**.  Its three re-exports were therefore never checked
as a unit, so a re-export naming a renamed or deleted submodule was invisible.
`SeLe4n.lean` imports the hub now; the count is zero.

  **A fourth measurement, with the roots as the criterion, found five more**
  (`v0.35.76`).  The count above accepted a `lean_exe` or a census as reach,
  and that is not the criterion the Tier 1 censuses' environments use: each
  imports `SeLe4n` and `SeLe4n.Platform.Staged`, so a module reached only by a
  test executable is outside every one of them.  The store-access census's
  domain reconciliation (below) found the first — `ChainFootprint`, whose RR7.40
  header said PRODUCTION while no root imported it — and re-measuring with the
  two roots as the criterion found five non-test modules outside both: that one,
  its `CSpaceWalkFootprint` sibling with the same RR7.41 header, the
  `FrozenOps` and `Scheduler/PriorityInheritance` re-export hubs (RadixTree's
  shape, reached by test suites alone), and `Architecture/VSpaceARMv8`, which
  §8.15.1 of the spec had recorded as *test-anchored, not production-imported*
  for thirty minor versions.  Three went into the root (both hubs, and
  `ChainFootprint` with its one staged dependency `DynamicChainExtension`, every
  import of which was already production); two are staged with a `STATUS`
  marker each — `CSpaceWalkFootprint` because its conflict theorem is stated
  against SM3.E's `ktiSharesConflictingLock`, so its chain runs through
  `Serializability` → `Deadlock`, which the RR7.18 decision keeps out of the
  image, and `VSpaceARMv8` because it is on no execution path.  A header's
  PRODUCTION is a claim the import chain decides, and two such claims stood for
  fifty-two minor versions with nothing deciding them.

The three attempts are the finding's own epilogue, and they are this section's
*a measurement can carry the defect it is sizing* rule applied to me.  The first
reported **80** orphans, because the allowlist parser ignored the trailing
` # comment` on every entry and matched none of the 67.  The second reported
**7**, because it walked only the two roots, the staged anchor and the six
censuses, and forgot the `lean_exe` targets — which build most of what was left.
The third, reading all 71 roots out of `lakefile.toml`, reported **1**.  Two of
those three numbers would have justified a much larger claim than the tree
supports, and the only reason the first was not believed is that 80 looked wrong
enough to re-derive.  **A measurement that licenses a conclusion gets checked as
hard as the conclusion** — and a domain measured by hand needs its own domain
checked, which is the rule this whole section is about, arriving one level up.

**And a shared answer must be REACHABLE from every asker, or the unreachable one
grows its own** (`v0.35.59`).  This file's most-repeated rule is *one question
answered in two places will diverge*, and its remedy has always been to give the
question one owner.  The frozen removal is the case that shows the remedy is
incomplete: `dualQueueRemovalGuard` **had** one owner, in
`SeLe4n/Kernel/IPC/DualQueue/Core.lean`, and the one surface whose whole purpose is
to be compared against the operation that reads it **could not import it** — so it
answered the question itself, with one factor, and the divergence was not a second
implementation drifting from a first but a *layer boundary* standing between an
asker and the only answer.  The two failure modes are indistinguishable in a diff
and have opposite remedies: drift is fixed by deleting a copy, and this is fixed by
**moving the original down** to the layer both askers reach.  So: when a question
has one owner and an asker that cannot see it, the owner is in the wrong layer.
`dualQueueRemovalGuard`, `queueTailPairAgrees`, `queuePPrevHeadPositionAgrees`,
`queueLinkPairAgrees` and `tcbWithQueueLinks` are in `Model/Object/Types.lean` now,
beside the records they read and beside `queueRemoveBoundary` — the predicate is
over an `IntrusiveQueue`, a `ThreadId`, a `TCB` and a `QueuePPrev`, every one a
model record, so the IPC layer never had a claim on it.  Its **discharges** stayed
in the kernel layer (`dualQueueRemovalGuardHolds`,
`queueTailPairAgrees_of_wellFormed`), because those read `ipcInvariantFull`, and
that split is the test of whether a relocation is a layering fix or a layering
violation: the *predicate* moves, the *invariants that entail it* do not.

**And moving the answer is not enough if the QUESTION was never named — a named
condition beside unnamed ones is a subset, and reaching it through a shared
definition reads like agreement.**  This is the sharper half, and it was found by
auditing the fix rather than by a review: the first attempt relocated
`dualQueueRemovalGuard` and had the mirror call it, and that mirror **still**
succeeded where the kernel refuses.  `endpointQueueRemoveDual` refuses *four*
things before it writes anything, and only one of them had a name — the one an
invariant discharges, which is why it got named.  Beside it sat an unnamed
`if q.head.isNone || q.tail.isNone`, an unnamed `prevTcb.queueNext ≠ some tid` in
the predecessor patch, and an arm answering `.endpointQueueEmpty` where the mirror
answered `.illegalState` (and `frozenRunAgrees` compares codes, so that one was
visible to the differential all along, invisible only because nothing drove both
sides to it).  A state with an **empty queue** and `pprev = .tcbNext p` passes the
guard outright — `q.head ≠ some tid` holds vacuously for `none`, the link pair
agrees, and the tail pair agrees because both sides of it are false — so the
guard-carrying mirror would have unlinked a node from a queue that has none.

So the remedy is not a better shared *answer* but a named shared **question**:
`dualQueueRemovalEnabled` is the whole store-free precondition, both removals read
it, and a condition added to it reaches both by construction.  The one factor that
needs a store lookup cannot fold in, so it is `queuePredecessorNamesSuccessor`,
named and read by both sides, each resolving its own `prevTcb`.  **A checker for
this class must ask whether the refusal SETS agree, never whether a shared name is
called** — the anchors that pin it are the two removals' conditions *and* a
negative that refuses the guard-alone spelling coming back, because that spelling
keeps every token.  Generalising: when you relocate a definition so a second asker
can reach it, enumerate what the *first* asker does that the definition does not
cover; a named condition is the one a proof needed, not the one an operation
performs.

Four things this cut recorded rather than predicted.  **The registered cost was
wrong in the cheap direction, and that is an argument, not luck**: the debt row
said the closure must pay "whatever fixture cost the newly-refused states carry",
and it carried none — the newly-refused states are states the *kernel already
refused*, so nothing in the tree was on one, `frozenRunAgrees` is unmoved and the
golden trace is byte-identical.  A guard that only ever refuses what its subject
refuses cannot cost a fixture; that is what distinguishes tightening a mirror from
tightening an operation, and it is worth checking before deferring one.  **A
relocation that repairs no proof is the evidence the layer was wrong**: 233 lines
moved and nothing needed fixing, which is exactly what one expects when a
definition had no dependency on the layer it was sitting in.  **Collapsing two
`if`s into one costs a tactic, and the tactic says where the proofs were reading
structure**: eleven proofs across five modules needed `cases pprev` moved *ahead*
of their `split`, because unfolding the enabling condition exposes the guard's own
`match pprev` inside the `if`, and `split` takes that first — a mechanical repair,
and a reminder that a proof that splits on an `if` is coupled to how many `if`s
there are.  And **the witness must be decisive about *which* refusal is new**:
`FO-045` computes the retired `isNone`-only reading beside the live guard on a
state violating the **tail** factor and no other, and `FO-046` adds one half per
remaining refusal, each on a state that passes everything the previous half checks
and is refused by exactly one more thing.  All four were mutation-tested by
reverting the refusal each is about, and the fourth mutation is the one worth
keeping: `lake env lean --run` elaborates against existing oleans, so a mutation of
a *dependency* reads as PASS until the dependency is rebuilt — the first run of M1
reported green over the reverted fix.

**The cancellation footprint is arm-selected, and `.replyRecv` declares the
hand-off it was hiding** (OD3.5, `v0.34.128`).  Two changes with one cause: a
member the code writes and the footprint does not name is *false*, and this row
found both directions of that.

**The victim's splice neighbours are declared on the arm that splices.**
`queueSpliceNeighbors?` was the one resolver in the cancellation family that
did not key on `tcb.ipcState` — every other member selects an arm and this pair
was summed over all of them — so the reply and notification arms declared two
TCB write locks for a splice they do not perform.  `cancelArmSpliceNeighbors?`
is *derived* from `cancelBlockedEndpoint?`, so the arm question is asked once,
and the widest arm drops from ten members to eight
(`lockSet_cancelIpcBlockingOnCore_size_le_ten` since OD3.7 raised it again -- that
name is not live, the bound having been re-based since to
`lockSet_cancelIpcBlockingOnCore_size_le_thirteen` -- with
`_replyArm_eq` and `_endpointArm_covers_prev` / `_next` pinning both
directions).  Over-declaring is sound and **not free**: lock contention is an
observable channel (SM8.D's CC-5), so a footprint wider than its operation
carries contention that says nothing about the operation.  What licenses the
narrowing is checked rather than read off the definition, on every arm:
`cancelIpcBlocking_notificationArm_tcb_frame`,
`cancelIpcBlocking_replyArm_noDonation_tcb_frame` and — with the reclaim live —
`cancelIpcBlocking_replyArm_tcb_frame`, which composes the four frames the tree
lacked (`endpointQueueRemove_objects_ne`,
`abortPendingIpcOnEndpoint_other_tcb_eq`, `abortHolderPendingIpc_other_tcb_eq`,
`returnDonatedSchedContext_other_tcb_eq` — each stating a step's effect *outside*
its write set).  The arm rewrites exactly the holder, its two queue neighbours
and the cancelled caller, all four declared, so the victim's own links are stale
references to threads it never touches.  Two notes for new code.  (1)
`endpointQueueRemove`'s two link patches are pinned to `queueNeighbourPatch` by
`rfl` (`endpointQueueRemove_eq_patches`), so the removal's write set is one
lemma rather than a four-deep nested match, and the tree's third inlined copy of
that shape is gone.  (2) `returnDonatedSchedContext_other_tcb_eq` and
`_tcb_rewrite` are different statements and neither implies the other — one
permits a binding change at any key, the other permits no change at these keys —
so a footprint argument must reach for the former.

**`.replyRecv` performs two SchedContext hand-offs and declared one.**
`replyRecvReturnDonation` returns the recorded server's donation and then, when
the receive leg dequeues a queued `Call`, runs
`applyCallDonationOnCore nextThread tid` — whose `donateSchedContext` writes the
**new** caller's SchedContext, provably not the returned one.  That is the
passive-server steady state, not an edge case: the receiver is `.unbound` at
that point precisely because the return just made it so.  So the tree's
most-travelled IPC path wrote a kernel object under no declared lock, and a
`.replyRecv` on one core and a `.tcbSuspend` of that queued caller on another had
provably disjoint footprints while both writing it.  Four things new code must
respect.  (1) **The member is resolved through `.call`'s own resolver**
(`receiveRendezvousDonatedSc?` over `endpointCallDonatedSc?` at the send-queue head),
because it is the same question — `.call` has declared this member since SM6.A.5
and said why.  (2) **The recorded server's TCB is declared unconditionally**, so
a *delegated* reply declares like any other: PR #892 review round 6's refusal
(`lockSetForSyscall_replyRecv_delegated`, concluding `none`) is retired and
replaced by `_delegated_declares`.  (3) **`maxLockSetSize` is 11 at this cut**, and that is
the cost: `admissibleCriticalSection` for the 1 ms tick falls from 37 µs to
30 µs, and the CC-5 bound widens in proportion.  (OD3.7 moves it again, to 13 and
25 µs — see the bullet below.)  The alternative was a narrower
declaration on the hottest path, and this project rates a footprint that omits a
written lock worse than a wide one.  (4) **`SystemState.scThreadIndex` is an
`RHTable`**, so every donation and every return takes `stateLevelLock` — an
insert may rehash and back-shift the whole table, exactly as the CDT maps do
(RR7.9/RR7.11), and no per-object member can cover it.  Declared on
`lockSet_endpointCall`, `lockSet_endpointReply`, `lockSet_replyRecv`,
`lockSet_tcbSuspend`, `lockSet_cancelIpcBlocking` and `lockSet_cancelDonation`
conditioned on each one's own SchedContext resolver, and unconditionally on
`lockSet_schedContextBind` / `_Unbind`, whose index write is not optional on the
success path.  `.schedContextConfigure` is split out of their `permittedKinds`
row rather than widened with them: it writes no index.

**...and `.receive` performs one it never declared, because it never performed
it at all** (OD3.6, `v0.34.129`).  seL4-MCS's `receiveIPC` hands a dequeued
`Call` caller's scheduling context to a passive receiver (`reply_push` →
`schedContext_donate`); `.replyRecv` did that here and `.receive` did nothing, so
a passive server taking its **first** request with `seL4_Recv` ran the client's
work charged to no reservation while the same server taking its second and later
requests with `seL4_ReplyRecv` was charged correctly.  Nothing caught it because
the server is not wedged — `resolveEffectivePrioDeadline`'s `.unbound` arm falls
back to the legacy TCB priority, so it runs, on nobody's budget.  Five things new
code must respect.  (1) **The step is one definition**
(`applyReceiveRendezvousDonation` over `applyRendezvousCallDonation` and the
guard `rendezvousDequeuedCall`, in `IPC/Operations/Donation.lean`), called by
both `.receive` arms **and** by `replyRecvReturnDonation`: a second copy of the
donation would be the same defect one level up, and a Tier 3 negative refuses the
inlined `applyCallDonationOnCore` returning.  The resolver is shared the same
way — `receiveRendezvousDonatedSc?` is derived from `receiveRendezvousSender?`,
the resolver `receiveInstallsCaps` and the `senderTid` member already use, rather
than re-reading `sendQ.head`.  (2) **The guard *is* the caller-blocked
obligation**: `rendezvousDequeuedCall_blockedOnReply` discharges
`applyCallDonationOnCore_preserves_ipcInvariantFull`'s donor hypothesis from the
predicate the arm branches on, so the two cannot disagree about which states
donate; only the whole-store `hReceiverNotOwner` survives, as a `recvStage`
conjunct of `syscallDispatchQuiescence` stated over the receive stage's committed
state — the shape `replyRecvStage` already used for the reply leg.  (3) **The
step is inert where it must not fire**: `applyCallDonation` no-ops unless the
receiver is `.unbound` **and** the donor `.bound`, and the guard is false for a
receive that blocked and for a plain `Send` rendezvous, so every result taken
before OD3.6 survives on the states it held for.  (4) **The checked arm needs no
extra gate** — the donation writes only `schedContextBinding` and
`SchedContext.boundThread`, both erased by `projectKernelObject`, and the
endpoint→receiver flow it follows is gated above it; but the delegation theorem
and the `syscallDelegates .receive` obligation both **name** the step, since a
delegation claim that omits one is a claim about a different program.  (5)
**`lockSet_endpointReceive`'s state-level member is a disjunction**, and that is
not cosmetic: conditioning it on `installsCaps` alone omits it on exactly the
passive-server path, which donates and installs nothing.  `permittedKinds
.receive` gains `.schedContext`, the size bound is restated at the new arity
(`3 + 4 = 7 ≤ 11`), and `maxLockSetSize` does not move.

**...and the pop declares the two objects it reads below the head** (OD3.7,
`v0.34.130`).  `returnDonatedSchedContext` at call depth ≥ 2 walks one link past
the reply-stack head to find the outer caller (`replyStackOuterCaller?`) and then
reads that caller's TCB to validate it (`outerCallerAcceptable`).  Neither object
is covered by another member — the head Reply *is* the answered caller's own
`replyObject`, and the outer caller is provably neither thread the pop rewrites —
so a footprint that omits them is *false* at depth ≥ 2, and the TCB read is a
**validate-then-commit**, which makes an unlocked read a time-of-check/time-of-use
window on exactly the thread about to receive a scheduling context.  Five things
new code must respect.  (1) **The pop is O(1) at any chain depth** — one frame of
lookahead, no more — so this is a constant `+2` on the footprint rather than
`O(depth)`; a pop that traversed the chain could not be given a footprint at all,
since a `LockSet` is capped at `maxLockSetSize` and a chain is not.  (2) **Both
members are read-mode**, and Tier 3 negatives refuse the write spelling.  (3)
**One resolver answers for all three arms**: `replyStackBelowHeadReads?`, with
`cancelBelowHeadReads?` deriving the cancellation arm's pair from
`cancelledCallerDonation?` — the plan row named only the first read, and the
second is derived from the operation, which is the enumeration-versus-derivation
rule applied to a footprint.  (4) **`maxLockSetSize` was 13 at this cut and is
14 since OD3.13**: `admissibleCriticalSection` for the 1 ms tick fell to 25 µs
and then to **23 µs**, and the uniform envelope moved to 2340 and then 2520 µs,
all derived from the constant.  **Only `.replyRecv`
needed the raise** — `lockSet_endpointReply` reaches nine and the cancellation
reply arm ten (`lockSet_cancelIpcBlockingOnCore_size_le_ten` at that cut; the live
bound is `lockSet_cancelIpcBlockingOnCore_size_le_thirteen`) — and that is
asserted rather than described.  (5) **Both members are `none` on every state
this tree reaches**, so no live footprint widened; this declares ahead of OD4.4's
code, which is the order the numbering rule requires.

**And how much of that ceiling is slack is stated, not left to be re-derived**
(OD3.7 sharp bound, `v0.34.131`).  Thirteen is the union over *all* argument
values; a reachable `.replyRecv` declares **twelve**
(`lockSet_endpointReplyRecvOnCore_size_le_thirteen` at that cut; the live bound is
`lockSet_endpointReplyRecvOnCore_size_le_eighteen`), because the donation a reply
returns is owned by the thread the reply answers, so two arguments name one key
and `insertOrMerge` lubs the modes without moving the cardinality.  Three things
new code must respect.  (1) **The equality is a stated hypothesis**
(`replyDonationOwnerIsAnsweredCaller`), not a consequence of the bundle:
`donationOwnerValid` says only that the owner is `.unbound` and `.blockedOnReply
epId rt` for *some* `rt`, and relates `rt` to no donation — the gap WS-RR RR7.22
met from the cancellation end and closed with `donationHolderIsReplyTarget`, which
WS-HP HP5.3 re-keyed onto the frame as `donatedContextIsOwnerFrameHead`.  (2)
**One member is the whole of the sharpening**: the recorded server merges with
the invoking thread only on a *non-delegated* reply, a case split rather than an
invariant, and the delegated case is the one OD3.5 exists to declare.  (3) **The
sharp bound is not the ceiling** — `maxLockSetSize` is what
`boundedWait_under_2pl` and the WCRT surface consume and must stay true of every
argument value, so a Tier 3 negative refuses restating it as such.

**And the pop preserves the chain, which is what makes the predicate an
obligation** (OD3.8, `v0.34.132`).  Almost every transition in the tree
discharges `donationChainWellFormed` through `donationChainFrame` — it writes no
`Reply.prev`, no `Reply.next` and no `SchedContext.scReply`, so the two
projections the walk reads are fixed — and the pop is the exception that family
was designed against.  With
`returnDonatedSchedContext_preserves_donationChainWellFormed` the pop stopped
being that exception.  **The universal it established is not the state of the
tree at HEAD**, and a reader must not take it for one: `v0.35.4` made the stack
doubly linked, so the mid-stack *splice* is a second writer of chain data (it
preserves the predicate, `spliceReplyFrameOut_preserves_donationChainWellFormed`),
and the reply path's `consumeCallerReply` falsifies `prevLinkReciprocal` on a
frame that is not a head — the WS-RM residual recorded two sections above.  New
code must not assume `donationChainWellFormed` of a state reached by replying to
a caller whose frame has a frame above it.
Five things new code must respect.  (1) **Acyclicity is derived, not assumed**:
clearing the popped head's links is sound for the rest of that context's stack
only if no frame below links back to it, and `donationChainFrom_head_not_mem_tail`
reads that off the invariant's own *termination* clause — the walk is a function
of its starting point (`donationChainFrom_deterministic`, over
`donationChainFrom_mono_le` and `donationChainFrom_suffix_walk`), so a head
appearing again below itself would make the walk from that occurrence return the
whole chain, strictly longer than the suffix it must equal.  A `NoDup` conjunct
would have been an enumeration standing in for a derivation, and a Tier 3
negative refuses one.  (2) **The other half is freshness, and it already existed**:
`not_mem_donationChainFrom_of_not_donating` says the popped head, which donates
*this* context, is on no other context's chain — the same lemma OD4's push
consumes from the other side.  (3) **The congruence is chain-scoped**:
`donationChainFrom_congr` asks agreement at *every* key and is false of a step
that rewrites one, so `donationChainFrom_congr_on_chain` asks it only at the
chain's own members, which is exactly what the walk reads.  (4) **Unconditional in
`newOwner?`** — the pop's TCB stores write `schedContextBinding`, which is not
chain data at any depth, so unlike the `ipcInvariantFull` composite nothing here
is `hBottom`-conditioned.  (5) **Exercised on the `some` arm**: a theorem
discharged only where the context heads no stack is indistinguishable from one
whose writing arm is wrong, so OD2.4's depth-2 witness is popped
(`donationChainWitness_pop_wellFormed`) and the state the pop leaves is shown to
head exactly the *tail* of the stack it started with
(`donationChainWitness_pop_chain`).  At the time of that cut the predicate was
still vacuous on every state this tree reaches — the pop's writing arm needed a
stack nothing yet constructed — and the prose that said "no transition writes"
the three fields was corrected wherever it appeared.  **OD4.1 (`v0.35.2`) ends
the vacuity**: a depth-2 Call builds a two-frame stack, so the pop's `some` arm
is reachable and the exercised witness is the live shape rather than a
construction.

**The pop is live and inert** (OD3.1–OD3.3, `v0.34.126`).
`returnDonatedSchedContext` takes a `newOwner? : Option ThreadId` and is four
object writes — the SchedContext rebind **and** stack pop as one store, the pop
itself (`storeDonationHeadPop`: the head's links cleared, then the frame below
**re-headed** to this context), the target's
`donationReturnBinding scId newOwner?`, the server's `.unbound` — and
`returnDonatedSchedContext_eq_legacy_of_none` proves that at `newOwner? = none`
over a context heading no stack it **is** the pre-OD3 body.  All six call sites
thread OD3.4's resolver since OD4.4 (`v0.35.2`).  Six things new code must
respect.  (1) **The head validation is fail-closed**: `donationHeadOf?` refuses a
head resolving to no Reply, or to one donating a different context, rather than
reading it as an empty stack — the same posture as RR2.8's `boundThread` guard,
and what rules that arm out is `donationHeadResolves`, established either from
`donationChainWellFormed` or across any step writing no chain object
(`donationHeadResolves_of_frame`).  A theorem asserting the return **succeeds**
therefore states it.  (2) **The `_ok_storeChain` decomposition is the only
description of the operation**: `returnDonatedSchedContext_walk` is retired as
its weaker duplicate, and a new field frame is a corollary rather than a copy of
the case analysis — sixteen such copies went with the fourth store.  (3) **The
return writes a Reply**, so `_preserves_reply` is gone: `_reply_frame` says a
Reply survives with at most its stack links reset (`replyStackRewrite`), and its
`caller` — all the reply-freshness and stash invariants read — agrees exactly.
For the same reason `replyLinkageFrame.replyAgree` and
`donationReadAgreement.otherKind` state the **caller-level** correspondence;
a transition with full Reply identity supplies it through
`callerAgree_of_objectAgree`.  (4) **The binding trichotomy widens at the
target**: `_tcb_schedContextBinding_backward`'s middle clause is
`donationReturnBinding scId newOwner?`, and both its arms name the same context
(`donationReturnBinding_scId?`), so `scThreadIndex` is insensitive to stack
depth.  (5) **The depth-≥ 2 obligation is `donationReturnOuterValid`** — the
outer caller is a TCB that gave up its binding and waits on its reply, and is
neither the rebound thread nor the server — vacuous at `none`, and
`donationOwnerValid`, `donationOwnerUnique` and `donationBudgetTransfer` are
general under it.  The *composite*
`returnDonatedSchedContext_establishes_ipcInvariantFull_of_except` was not, and
said so: it took `hBottom : newOwner? = none`.  **OD4.3 (`v0.35.2`) removed
that**, before OD4.1's push made the arm reachable, so the composite now covers a
depth-≥ 2 return under `donationReturnOuterValid` like every other statement in
the family.  (6) **The return is invisible to every observer,
not merely a high one**: every field it writes is stripped by
`projectKernelObject`, so `returnDonatedSchedContext_preserves_projection` no
longer carries an observability hypothesis on the server.

**And the header's donation inventories were a third copy of `permittedKinds`**
(OD3.18, `v0.34.145`).  Found by running the sweep rule on the previous cut
rather than by a review: OD3.17 corrected a contract that denied a hand-off its
own footprint declares, and the same question was answered a second time --
wrongly, three ways -- in the same file's module header.  `.receive` sat under
*syscalls that do NOT need donation extension* for twelve cuts after OD3.6 gave
it a `donatedScId`; `lockSet_replyRecv`'s entry repeated the retired sentence
word for word; and `tcbSetPriority`, `tcbSetMCPriority` and `tcbSetAffinity` --
each writing the target's **bound SchedContext**, because priority and home core
live there -- were called *TCB-only config ops*, with `tcbSetAffinity` in neither
list.  Three things new code must respect.  (1) **`permittedKinds` is the
canonical inventory, and it is proven rather than parallel**: a footprint may
name a SchedContext lock exactly when `.schedContext ∈ permittedKinds <arm>`, and
the `lockSet_consistent_<arm>` family states `∀ p ∈ (lockSet_<arm> …).pairs,
p.fst.kind ∈ permittedKinds <arm>` at each footprint's **full arity**, so a
member added without the kind being permitted fails to elaborate.  A prose list
restating it is a copy that can drift and did.  (2) **The cut adds no checker,
deliberately.**  Its first attempt was a Tier 1 census walking each footprint's
elaborated body for `schedContextLock`; it took six corrections in a row -- a
name-prefix frontier a differently-named helper defeats, a tuned rather than
derived bound, a skip set right for the narrow frontier and wrong for the wide
one, a `getUsedConstants` that pushes per subterm -- which is
`unconditionalActions` again, for the reason recorded above: substituting `Expr`
for text moves the class down a level and does not close it.  It was deleted
before it shipped.  **Before writing a scanner, look for the fact the tree
already proves.**  (3) **The remedy for a duplicated inventory is deleting the
duplicate**, not adding a third artefact to reconcile the first two.

**And a donation moves budget, deadline and domain — never priority** (`v0.35.3`,
reported while closing this workstream).  `updatePrioritySource` classified
`.bound scId` and `.donated scId owner` identically, so `.tcbSetPriority` /
`.tcbSetMCPriority` on a thread *holding* a donated context wrote the **donor's**
`SchedContext.priority` — an authority crossing, since both arms are gated on a
TCB-write right over the *target* and the caller's MCP ceiling, and neither says
anything about the donor; the rewritten field then travelled back with
`returnDonatedSchedContext`.  The remedy is seL4-MCS's own split, not a refusal.
Five things new code must respect.  (1) **The classifier is
`SchedContextBinding.ownScId?`** — the SchedContext a thread *owns*, `some` on
`.bound` and `none` on `.unbound` and `.donated` — and it is where a *new
binding constructor* (WS-CB's hierarchical servers) must be classified.  It is
the counterpart to `scId?`, the one a thread *runs on*, and the two split a
thread's scheduling parameters: **reservation-owned** (budget, period, deadline)
read `scId?` at every binding, **thread-owned** (base priority, domain) are the
thread's, and — **at `v0.35.3`, when this was written** — were **stored in two
places** for a `.bound` thread: the TCB field and, mirrored onto it by the AK2-B
convention, `ownScId?`'s SchedContext.  Which one a *reader* took was not uniform
and that was the hazard — `threadBasePriority` read the *reservation* at `.bound`
while `TCB.boostedPriority`, which every run-queue insert is keyed by, read the
*thread* — so every writer of either had to move both, which is
`boundThreadPriorityConsistent` and which `v0.35.98` found `.tcbSetPriority` not
doing.  **The improvement named here — one home, not two kept in sync — was
taken**: `v0.35.133` for the band and `v0.35.136` for the domain, so no reader
consults a reservation for either and the standing constraint below is the live
text.  What the collapse did *not* do is retire the invariant, because the
**writes** remain two: PR #897's review found the pair falsifiable on a reachable
donation pop, which is its own table C row and which the two predicates'
docstrings now state.  `ownScId?` is a **narrowing** of `scId?`
(`ownScId?_eq_scId?_of_isSome`), so the two can never name different contexts.  (2) **The one answer is
`SystemState.threadBasePriority`**, and a new priority reader calls it rather
than matching the binding.  The three scheduler resolvers also need the
reservation's deadline or domain, so they split the arm and are tied back by
theorem — `resolveEffectivePrioDeadline_fst_eq_threadBasePriority` (new,
unconditional), `effectiveSchedParams_priority_deadline_eq_resolve`,
`effectiveBucketPriority_eq_resolveEffective`, and
`getCurrentPriority_eq_threadBasePriority` by `rfl`.  A Tier 3 negative refuses
the merged arm **per declaration**, because `hasSufficientBudget` three lines
above keeps it and a file-wide negative would fire on a clean tree; five budget
predicates are pinned as *still merged*, so the split cannot leak into the budget
question.  (3) **`boundThreadPriorityConsistent` ranges over `.bound` alone.**
Quantified over `scId?` it covered `.donated` too, and **the donation falsifies
it** whenever the donor's and the donee's base priorities differ: the
reservation's `priority` must equal the donor's before the hand-off and the
donee's after, and `donateSchedContext` writes neither field.  Nothing carries
it across either — the frame that transports it requires `schedContextBinding`
unchanged, which is precisely what the hand-off rewrites.  So it was false on
exactly the states WS-OD had just made reachable, and every result gated on it
was silent there.  (4) **The bucket invariants follow the read**: a donee's recorded
run-queue bucket is its own base priority, so `effectiveParamsMatchRunQueue`'s
`.donated` arm *is* its `.unbound` arm.  (5) **`propagatePipChainCrossCore` is
now the only priority route** between a client and the server it calls, which is
what keeps inversion bounded and what makes OD3.14's `.receive`-arm walk
load-bearing rather than a second-order correction.

**And the mirror crossing goes with it — the domain as well as the priority.**
`schedContextConfigure` propagates **both** thread-owned parameters into
`sc.boundThread`'s TCB, and after a donation `boundThread` is the **donee** — so
a capability on the *client's* reservation could rewrite the *server's* own base
priority and **migrate its scheduling domain**, permanently, since the donee
keeps both fields after the donation returns.  A domain is the partition
temporal isolation is defined over, which makes that half the more serious of
the two, and either would have been the one remaining route by which a client's
reservation sets a server's band.  Both halves maintain a `.bound`-only
invariant (`boundThreadPriorityConsistent`, `boundThreadDomainConsistent`), so
`schedContextConfigureBoundPropagate` takes the SchedContext's id and gates both
on the bound thread **owning** it, through **one** predicate
(`schedContextConfigurePropagates`) that both halves consult — so a later cut
cannot gate one and leave the other.  A reconfiguration still rewrites the
reservation itself, budget and period included: that is the object the caller
holds a capability for.  The reading side follows —
`effectiveSchedParams`'s `.donated` arm reports the donee's **own** domain,
because every live domain filter reads `tcb.domain`, so reporting `sc.domain`
described a partition the scheduler never puts a donee in; that component has no
live consumer today, which is why it had to be corrected rather than left for
the first one to inherit.  Registered debt closed;
`docs/REGISTERED_DEBT.md`'s WS-OD section records the closure.

**And the reply stack is doubly linked, so no frame is left on it with its caller
gone** (`v0.35.4`, reported while closing this workstream).  `severAtCut` was
implemented by *leaving a frame behind*: a cancelled middle caller's frame stayed
on its stack with its `caller` consumed, the later pop read it as the bottom of
the stack and bound the context outright, and that frame then **headed** the
context forever — the Reply object and the SchedContext could never be retyped,
and the Reply could never be linked to a new caller.  Reachable from an ordinary
`.tcbSuspend` on a client at call depth >= 3, with no more authority than a TCB
write right over a thread in one's own call chain.  Six things new code must
respect.  (1) **`Reply.donatedSc` is gone**; the upward link is
`Reply.next : ReplyStackLink`, a sum of `.frame above` and `.head sc`, so
"heads a context", "has a frame above" and "off every stack" are three states of
one value.  The context is recorded on the head frame **alone**, which is what
makes a mid-stack removal an `O(1)` repair of two neighbours rather than a walk
clearing a per-frame field below the cut.  (2) **`Reply.wellFormed` is
`caller = none → prev = none ∧ next = none`** — seL4's `reply_unlink` invariant —
and `Reply.isFree` is its decidable form, the one spelling of "this Reply may be
linked or retyped", shared by the link guard, the stash admission, the retype
guard and the boot check.  (3) **The walk validates reciprocity, not a donation**:
`donationChainFrom` follows a `prev` only when the target's own `next` answers the
frame that reached it, and the expectation **advances** (`.head scId` at the head,
`.frame` of the previous frame thereafter), so a frame claiming to head the
context at depth 2 is refused.  (4) **The pop writes the frame below the head**:
`storeDonationHeadPop` clears the head's links and then **re-heads** that frame,
so the below-head footprint member is a *write*, not a read.  (5) **The
cancellation path splices before it consumes** (`spliceThreadReplyFrameOut`
over `spliceReplyFrameOut`, between the reclaim and `consumeReplyLink`), and a
validated below-head frame whose caller was consumed is now an `.error`, never
the bottom of the stack.  (6) **`maxLockSetSize` went to 16 at this cut** — the
pop's new write plus the suspend pipeline's second pop; it is **21** at HEAD, and
the per-lock cost and envelope it implies are stated once, in the canonical
sentence this file carries above.

**And a delegated `.replyRecv` declares the invoking receiver's own pre-receive
return** (PR #894's review, `v0.35.5`).  That arm's receive leg **is**
`.receive`'s transition, so when the endpoint has no queued sender it runs
`cleanupPreReceiveDonationChecked` on the **invoker** — and the arm's own
donation return runs *after* the receive leg, so the invoker still carries
whatever `.donated` binding it entered with.  On a non-delegated reply the
recorded server *is* the invoker and the reply leg has just made it `.unbound`,
so that second pop is inert; **delegation is exactly what breaks the
coincidence**, and WS-OD OD3.5 had already retired the refusal
(`lockSetForSyscall_replyRecv_delegated`) that used to keep the delegated shape
out of the declared set.  Two threads cannot be bound to one scheduling context,
so the recorded server's members provably never alias the invoker's: a delegated
`.replyRecv` wrote a SchedContext, the previous owner's TCB and two Reply objects
under no declared lock, and read a third TCB it was about to hand a context to.
Four things new code must respect.  (1) **The five members are the same five
`lockSet_endpointReceive` declares**, resolved through the same two resolvers on
`replier` (`lockSet_endpointReplyRecvOnCore_covers_preReturn`); a Tier 3 negative
refuses resolving them on `target`.  (2) **The state-level member has a fourth
disjunct** — on a delegated reply whose recorded server holds no donation the
other three are all false, so without it the `scThreadIndex` write is undeclared
on exactly the shape the member exists for.  (3) **`maxLockSetSize` is 21**, and
that is the cost: `admissibleCriticalSection` falls to 15 µs on the 1 ms
tick, down from 20.  (4) **No
*reachable* state declares twenty-one**: the re-donation members fire exactly
when the endpoint has a queued sender and the pre-receive return exactly when it
does not, so `lockSet_endpointReplyRecvOnCore_size_le_eighteen` bounds every
state at **eighteen** with no hypothesis.  (The owner merge that used to take a
reachable `.replyRecv` to seventeen is retired at WS-HP HP6.2 — see below.)
Twenty-one is what the *definition* can produce,
which is what `boundedWait_under_2pl` and the WCRT surface must consume.  The
gap was excused by `lockSetForSyscall_replyRecv_refuses_donated_delegate`, **a
theorem that was never written**; it is deleted.

**And the bind guard asks reciprocity, not presence** (PR #894's review,
`v0.35.5`).  `replyFrameOnLiveStack` asked `r.next.isSome`, and `severAtCut`
deliberately leaves the frame *below* the cut with a stale upward link — so a
thread on no live stack, owed nothing, had its `schedContextBind` refused with
`.illegalState`, on a path the transition explicitly supports (it binds a
**blocked** thread).  The guard now asks the walk's own test: `.frame above`
counts only when `above.prev = some rid`, `.head sc` only when
`sc.scReply = some rid`.  It is `O(1)` and **exact** under
`donationChainWellFormed`, where `prevLinkReciprocal` and `headTerminates` make
one-step reciprocity equivalent to liveness, and a live frame still reads `true`,
so the fail-closed direction is unchanged.  In the same cut
`frozenSchedContextUnbind` gained the `isDonated` refusal its live counterpart
has carried since `v0.35.4` and its own docstring already claimed.

**The residual registered at `v0.35.4` is closed** (WS-RM, `v0.35.6`): both
removal paths run seL4's `reply_remove`, and the reply path's own section below
records what new code must respect.

Plan: [`docs/planning/SCHEDCONTEXT_DONATION_CHAIN_PLAN.md`](SCHEDCONTEXT_DONATION_CHAIN_PLAN.md).

### WS-RM seL4's `reply_remove` on the reply path — COMPLETE (registered v0.35.4; RM1–RM6 v0.35.6)

`v0.35.4` made the reply stack doubly linked and wired the removal (then a sever,
the splice since HP6.3) into the **cancellation** path, leaving the **reply** path
relying on the answered frame
being the head — which every reply of the nested Call pattern satisfies and a
*delegated* reply capability answering out of order does not.  Twenty-six
sub-tasks across six phases, all at `v0.35.6`.  Seven things new code must
respect.

(1) **One removal step, and both spines call it.**  `removeCallerReplyFrame
caller rid` is seL4's `reply_remove`: `spliceReplyFrameOutOrSelf` (the splice
folded to the identity on refusal — a non-reciprocating upward link means
"nothing above me on my stack", which the chain relation permits by design since
it is stated *downward*), then `SystemState.consumeCallerReply`.
`endpointReplyOnCore`, `endpointReply` and `endpointReplyRecv` all run it, and a
Tier 3 negative refuses a bare consume in any of the three.  **The order inside
it is the content** — the splice reads the link the consume clears — and a
second negative refuses the swap.  `removeCallerReplyFrame_eq_consume_of_no_frame_above`
is the definitional equality that makes every repair a case split whose `none`
branch is the pre-WS-RM proof verbatim.

(2) **The reply leg's head case is stated, not hidden.**  A frame that *heads* a
scheduling context keeps its links when its caller is consumed (`Reply.consumed`,
deliberately — the pop validates the head by them), so the leg's post-state
satisfies `donationChainWellFormedExcept … rid` and nothing stronger.  It stands
to the reply leg as `ipcInvariantFullExceptDonationOwner` stands to the bare
reply, and `endpointReplyCrossCoreDispatch_preserves_donationChainWellFormed` is
the composite that discharges it: the donation pop that follows in the same
transition re-heads the frame below.  `faultReplyOnCore_preserves_donationChainWellFormed`
and `replyTransferOnCore_preserves_donationChainWellFormed` (seL4's
`doReplyTransfer`) compose it; the staging writes frame the chain
(`stageDeliveredMessage_donationChainFrame` and its two siblings).

The composite carries **one** condition beyond the chain invariant, and it is a
**pre-state** fact: `answeredHeadContextIsServerDonation` — the context the
answered frame heads is the one the recorded reply server holds.  It is the
third of the tree's *local coherence facts* about a single reply, beside
`replyDonationOwnerIsAnsweredCaller` and `replyStackHeadIsAnsweredReply`, and
like them it is **stated rather than derived**: `donationOwnerValid` relates a
caller's recorded reply target to no donation, and `donationChainWellFormed`
carries no binding clause at all, by its own *what is deliberately absent*.
Vacuous wherever the answered frame heads nothing — every reply in a tree with
no donation — with both vacuity discharges named
(`answeredHeadContextIsServerDonation_of_no_caller` / `_of_no_reply`), and
`tests/SmpIpcSuite.lean` §3.21 exhibits its premises and its conclusion on a
state the live operations reach, since a hypothesis nothing exhibits is
indistinguishable from one that cannot hold.  It is at the **pre**-state exactly
as the bundle composite's `hDonationReturned` beside it is, and unlike
`hStackValid`: `replyStackOuterCallerValid`'s subject is a state the pop runs on,
whereas a `schedContextBinding` is something the reply leg provably does not
write (`endpointReplyOnCore_donationOwnerFrameExcept`), so the transport belongs
inside the proof rather than on every caller.  That is also what makes the reply
*transfer* carry the fact **once**: its two branches reply with `IpcMessage.empty`
and with `msg`, which at the post-state were two spellings differing only in a
message the question never reads.

(3) **`.reply` and `.replyRecv` declare the frame above the cut, which the splice
writes.**
`answeredReplyFrameAbove?` is resolved from the same
`(st.getTcb? target).bind (·.replyObject)` expression the arm's existing reply
member comes from, so the footprint and the transition cannot disagree about
which frame is answered.  **`maxLockSetSize` is 22** and the RPi5 per-lock cost
and envelope move with it, in the canonical sentence this file carries above.  No
*reachable* footprint grew: the new member and the donation-return members are
mutually exclusive, so `lockSet_endpointReplyRecvOnCore_size_le_eighteen` is
unmoved.  **And declaring a member is not proving the transition writes it** —
the Tier 3 anchor over each footprint's definition asks only that the resolver
*occur* there, which is a presence check.  The relation is
`lockSet_endpointReply_frameAbove_write_mem` and `lockSet_replyRecv_frameAbove_write_mem`
at full arity, with `lockSet_endpointReplyOnCore_covers_splicedFrameAbove` and
its `.replyRecv` twin resolved: the reply-path siblings of the coverage the
cancellation path has carried since `v0.35.4`
(`lockSet_cancelIpcBlockingOnCore_covers_splicedFrameAbove`), which the cut that
added the reply-path member did not sweep onto it.

**And running that sweep over every resolved footprint found one more.**
`lockSet_cancelDonationOnCore` had `_correct` and `_size_le` and no coverage
layer at all, while each of its parametric members already carried a
write-membership lemma — so nothing tied a member to the **resolver** the
resolved footprint reads it from, which is the whole content of a resolved
coverage theorem.  Neither neighbour stands in for it: `_correct` is about the
*kinds* of the members present and `_size_le` about how many there are, and
a footprint can satisfy both while naming the wrong object.  The six are
`lockSet_cancelDonationOnCore_covers_victim` (both arms of the resolution),
`…_covers_bindingSchedContext` and `…_covers_stateLevel` (through
`cancelBindingSc?`), `…_covers_donatedOwner` (through `cancelDonatedOwner?`),
`…_covers_pop` and `…_covers_outerCaller_key` (through
`cancelDonationPopMembers?`) — the last a declared **key** rather than a write,
because the pop *reads* that TCB to check it is a waiting donor, with a Tier 3
negative refusing the write spelling.  `lockSet_notificationWaitOnCore` has no
coverage layer and needs none: it resolves nothing, so its parametric lemmas are
already the statement at full arity.

(4) **`.replyRecv` pops the donation *between* its two legs**, which is
seL4-MCS's own `doReplyTransfer` → `reply_remove` → `receiveIPC` order — and it
has to be.  The receive leg re-links the very Reply `rid` the reply leg just
answered, and `Reply.isFree` reads **both** stack links, so a frame still heading
a context is not linkable: with the pop last, `linkCallerReply` and the
server-first stash both refused `.replyCapInvalid` and **no passive server whose
client had donated could ever complete a `seL4_ReplyRecv`**.  That was a live
defect on the MCS steady state, found while closing this workstream and fixed in
the same cut.  The fused `replyRecvReturnDonation` is retired and split into
`replyRecvPopDonation` (between the legs) and `replyRecvPostReceiveDonation`
(after the receive leg, taking the popped context as an argument), each with its
own bundle theorem stated at the state its own step runs on.  New code must not
read the fused name as live.

(5) **The dispatch payoff's receive-leg hypotheses are stated at the post-pop
state.**  `replyRecvPostPopState` and `replyRecvPoppedDonation` are *total*
accessors over the pop (the second was `replyRecvPoppedContext` until
`v0.35.149`, when the pop's result became the `(context, holder)` pair), so `syscallDispatchQuiescence.replyRecvStage` stays a
flat pre-state-computable pack rather than a quantification nested under the
pop's own success; the pop's two obligations (`hSrvIdle1`, `hStackValid1`) are
stated at the reply leg's committed state, which is where it runs.  Stating the
receive-leg fields at the reply leg's own state is a claim about a state the
receive leg no longer runs on.

(6) **Every reply-stack write names a chain result.**
`SeLe4n/Testing/ReplyStackWriteCensus.lean` (Tier 1) derives the write-site set
from the elaborated environment — by **two** derivations, and a site found by
either is a site: a project definition whose own body references one of the
chain-write primitives (`SystemState.consumeReply` and
`SystemState.consumeCallerReply` among them), and one that builds a `Reply` or
`SchedContext` record and stores it, which is what catches a writer that names no
helper at all.  Both are reconciled against a registry in both directions.  A
site either **states** its chain results (each named theorem must mention the
site *and* a `donationChain…` form) or is recorded as a **half-step** of the
composite that completes it, and the half-step chain must terminate in a stating
entry.  The counts are **printed by the census** and deliberately not mirrored
here: a hand-kept figure beside a derivation is the shape this file warns about,
and this one went stale the first time the frontier widened.  A new
definition that consumes a caller's Reply bare is a build failure on the day it
is written — which is the shape this workstream exists to close, and the one
level above the frontier the census deliberately stops at (composites inherit by
`donationChainFrame`'s algebra, which is a composition rather than a claim).

**And "every" meant every module either root reaches** (PR #895 review,
`v0.35.12`).  `SeLe4n/Kernel/FrozenOps/` was reached by neither, and was in no
staged allowlist: it was built only by its own `lean_exe` target
(`tests.FrozenOpsSuite`) — **the root cause closed at `v0.35.60`, which put it in
the library root** — so the closure this census claims held for every
module except one that writes the live `Reply` record — `FrozenKernelObject.reply` carries `SeLe4n.Kernel.Reply`, links and
all, and `Model.freeze` copies a live state's Reply objects verbatim, so a
frozen state taken mid-call-chain holds a real reply stack.  And the gap was not
theoretical: `frozenEndpointReply` cleared a caller's Reply **bare**, which is
WS-RM's own defect surviving on the surface nothing was looking at.  Bringing it
in cost three things.  The frozen reply now runs a frozen `reply_remove`
(the removal then the consume, in that order, since the removal reads the link the
consume clears; **WS-HP HP8.2** made that removal `frozenSpliceReplyFrameOutOrSelf`,
which splices rather than severing).  `frozenLinkCallerReply`'s guard read
`caller.isNone` where `Model.linkReply` reads `Reply.isFree` — a fifth guard
deciding one question differently, so a frame still on a live stack was linkable
there while the live kernel refuses it; it reads `isFree` now.  And the
discipline gained a third constructor, `mirrors`: `donationChainWellFormed` is a
predicate on `SystemState` and the frozen store is a `FrozenMap`, so demanding a
`donationChain…` result of a frozen site would demand a theorem that cannot be
written, while accepting no record would be the silence this census refuses.  A
`mirrors` entry names the live twin, which must itself resolve to a stating
entry — a frozen writer with no live twin is a transition the live kernel never
performs, which is a finding rather than an exemption.

(7) **`donationChainFrame_of_objects_insert` is public and lives beside the
predicate.**  It was private to the cancellation shape module; the fault-reply
path needs the same fact, and a second copy in a module the first does not import
is the one-question-two-answers shape this tree keeps paying for.

**And the removal does not preserve the donation accounting — the cost, measured,
and whose it is** (the post-landing audit, corrected at `v0.35.14`).  Taking a
caller out of the *middle* of a chain is destructive to which thread ends up
owning the scheduling context: the removal moves no context, and the later pop
donates to whatever the remaining stack says is outermost.  On
`owner → middle → server`, a delegate answering `owner` out of order leaves
`owner` **`.unbound` permanently**, and the server's in-order reply then settles
the context **`.bound` on `middle`** — which the in-order unwind would instead
have left `.donated … owner`, still owed outward.  So a callee that delegates
its caller's reply capability to a confederate can capture that caller's
reservation.  New code must not read WS-RM as accounting-preserving, and must not
read a successful pop as evidence that the context reached its owner.

**The cost is `cancelledMiddleCallerPolicy`'s, not the removal's, and a
depth-two witness cannot tell the difference.**  A two-frame stack's lower frame
is its *bottom*, so `severAtCut` (write `prev := none` into the frame above) and
the alternative `spliceOutTheCut` (write the cut frame's own `prev`) write the
same value, and §3.20 measures a shape both policies share.  §3.22 of
`tests/SmpIpcSuite.lean` is the depth-three witness where they differ: every
frame below the cut leaves the context's stack, so the reservation settles on a
thread strictly *inside* the chain and its owner is left `.unbound` two hops
outside the cut, while the same stack unwound in order delivers it outward still
owed.  Three frames is the shallowest stack on which any of that is visible.

**Why the splice was not taken at WS-RM, and the order that had to be respected.**
Up to `v0.35.37` this kernel decided whether a reply pops a donation from the
**recorded server's binding** (`endpointReplyServerDonation?`), not from whether
the answered frame heads a context; `severAtCut` is exactly what kept those two
facts equivalent, and it is what the three *stated* pre-state coherence hypotheses
(`replyStackHeadIsAnsweredReply`, `replyDonationOwnerIsAnsweredCaller`,
`answeredHeadContextIsServerDonation`) needed — no invariant in this tree entails
them.  Splicing re-heads a frame whose recorded server is gone and `.unbound`, so
under that trigger answering it would have run no pop and left a consumed frame
heading a context: the state `replyStackOuterCaller?_of_consumed_frame` refuses and
the pinning `v0.35.4` closed.  Recovering the accounting therefore meant moving the
pop's *trigger* to head-ness first, which is what **WS-HP HP4** (`v0.35.38`, the
reply path) and **HP5** (`v0.35.39`, the cancellation path) did, and only then the
sever to a splice, which is **HP6.8** (`v0.35.45`).  That ordering was enforced
rather than described: `severAtCut_pop_leaves_no_head` was HP2.3's pin on it, and
HP6.8 deleted it because its first conjunct was the policy constant at the old
value.  New code must not read this paragraph as a live reason against the splice —
the splice is the live policy and the depth-≥ 3 accounting is
`donationAccountingPreserved_atCallDepthThree`.  The depth-**two** residue the splice
provably cannot reach was WS-HP HP10's, and it is closed at `v0.35.53` by
`donationAccountingPreserved_atCallDepthTwo`, so the accounting now holds at every
depth; what the register still carries is HP10.10's documentation closure alone.

**And `severAtCut` IS seL4-MCS's removal — the `v0.35.14` retraction was itself
wrong, and how it went wrong is the finding** (re-verified at `v0.35.40`).
`reply_remove`'s non-head branch, at master, 13.0.0, 12.1.0, 12.0.0 and 11.0.0 —
every release that has the function — is

```c
if (next_ptr) {
    /* not the head, remove from middle - break the chain */
    REPLY_PTR(next_ptr)->replyPrev = call_stack_new(0, false);
}
if (prev_ptr) {
    REPLY_PTR(prev_ptr)->replyNext = call_stack_new(0, false);
}
```

It writes **zero** into the frame above, which is `severAtCut`, and upstream's own
comment says so.  `v0.35.14` claimed the opposite and cited
`REPLY_PTR(call_stack_get_callStackPtr(reply->replyNext))->replyPrev =
reply->replyPrev` as the evidence; **that line is in no release**.  So the
paragraph before this one describes the accounting cost correctly and attributes
it wrongly: the cost is seL4-MCS's too, and WS-HP's splice is an **improvement on
upstream** rather than an adoption of it.  v1.0.0 may claim seL4-MCS reply-stack
removal semantics today; what it must not claim, of either kernel, is that
completing a call chain returns a client's reservation at chain depth ≥ 3.

**Quoting is not reading.**  This file's rules all police a *scanner* substituting
a slice of text for a question about a program.  This is the same substitution with
no scanner in it: a claim about an **external artefact** was marked "checked against
upstream source ... and not assumed", in the very sentence that made it false, and
the quoted C was reconstructed from what `reply_remove` *ought* to do rather than
copied from the file.  A verbatim quotation is the strongest-looking evidence a
prose claim can carry and the easiest to fabricate without noticing, and nothing in
this tree could catch it — no gate reads seL4.  Two things follow.  **Cite the
revision, not the repository**: a claim about upstream names the tag or commit it
was read at, so the next reader can re-run the check rather than re-trust the
quotation, and this tree's upstream claims now do.  And **a retraction is a change
of claim and gets the same scrutiny as the claim**: `v0.35.14` swept a *correction*
across four files and three docstrings, and the sweep worked — it propagated the
error everywhere, in the sentence asserting it had been verified.  The three
docstrings it "fixed" had been right.

**And a claim about upstream is about a named OPERATION, not a named kernel** — the
third rule, and the one this cut paid for itself.  Its own first draft said upstream
"permanently strands a cancelled caller's reservation", which is true of `cancelIPC`
and false of the kernel: `reply_remove` returns the context and `finaliseCap` runs it
on reply-capability revocation, which is the behaviour the Reference Manual
documents.  `cancelIPC`, `reply_remove` and `reply_remove_tcb` are **three
operations**, and this tree had been treating them as one name for eight cuts — which
is how `Suspend.lean` came to carry both readings at once, the docstring naming
`reply_remove` and the inline comment at its own call site naming `reply_remove_tcb`.
So a divergence claim names the operation it diverges from, and where two upstream
operations answer differently, saying which is the whole of the claim.  The
maintainer caught this one from the manual, which is the evidence for the rule: the
error is invisible to anyone reading only the function the claim happens to name.

Two divergences survived the correction at `v0.35.40`, both smaller and both in
the direction of this kernel being the weaker one.  **The first is closed and the
direction has reversed** (WS-HP HP6.3/HP6.7, `v0.35.45`): upstream clears the frame
*below*'s upward link (`prev->replyNext = 0`), this tree used to leave it stale and
work around it by validating reciprocity at every read (`donationChainFrom`,
`replyFrameOnLiveStack`), and the splice now **writes** it —
`removeCallerReplyFrame_splices_reciprocally` — so the pair either side of the cut
reciprocates, which is stronger than clearing.  A stale upward link is still
*reachable*, because `spliceFrameBelow?` refuses a frame below that does not
reciprocate and degenerates to the sever there, so the reciprocity checks stay and
stay load-bearing.  **The second survives and is about HEADS**: upstream clears the
removed frame's own links, and `Reply.consumed` keeps them *when the frame heads a
context*, deliberately, because the pop that follows in the same transition
validates the head by them.  On a non-head `Reply.consumed` already cleared both,
and since HP6.3 the splice clears the cut frame's `prev` itself — seL4's
`reply_unlink` downward half — which is what makes `donationChainWellFormed`
survive the removal outright rather than transiently.  So the residual is the head
case alone; a claim that HP6 closes it is an over-claim, and one was retracted from
that workstream's plan at `v0.35.45`.

**And the cancellation reclaim is upstream's semantics moved earlier, not an
invention and not a permanent strand** — the maintainer's correction to this
section's first draft, which said upstream "permanently strands a cancelled
caller's reservation".  That described one of four paths and attributed it to
upstream as a whole.

**Upstream returns a donated context when the caller's Reply object is finalised,
not when the caller's IPC is cancelled** — four paths, all read at master, 13.0.0,
12.1.0, 12.0.0 and 11.0.0.  (1) The server replies: `doReplyTransfer` →
`reply_remove` → head ⇒ `reply_pop` ⇒ donate to the answered caller, guarded
`if (tcb->tcbSchedContext == NULL)`.  (2) **The reply capability is revoked** while
its caller is still `BlockedOnReply`: `finaliseCap` runs the *same*
`reply_remove`, so the context returns to the caller — the Reference Manual's "if
the reply capability is revoked while the callee currently holds the scheduling
context, the scheduling context will be automatically returned to the caller".
(3) The same revocation when the caller's frame is **not** the head, because a
deeper server holds the context: the non-head branch runs, no donation happens,
and the caller is removed from the call chain — the manual's deep-call-chain case,
and the same *break the chain* write the removal-policy correction above rests on.
(4) `cancelIPC` — a `seL4_TCB_Suspend` on the caller, an endpoint deletion, a
fault: `reply_remove_tcb` ⇒ **no** donation, and its `reply_unlink` then clears
`reply->replyTCB`, so a later revocation of that reply capability finds nothing to
do (`finaliseCap` guards on `reply->replyTCB`) and the context stays with the
server until an SC-capability holder rebinds it.

So `returnDonationToCancelledCaller` applies **upstream's `reply_remove`
semantics at the cancellation point**, where upstream defers them to Reply-object
finalisation.  The difference is *when*, not *whether* — and this kernel's binding
typing forces the earlier point: `.donated scId owner` names its owner, so
`donationOwnerValid` is false the instant that owner stops being reply-blocked,
where upstream's flat `tcbSchedContext` pointer carries no such obligation.

Two consequences for new code.  A claim that this kernel diverges from upstream on
the *cancellation* reclaim must name the operation: it diverges from `cancelIPC`
and agrees with `reply_remove`.  And "adopt seL4's cancellation semantics" is not
a licence to delete the reclaim — deleting it reaches a state
`donationOwnerValid` forbids, which is the Medium finding WS-RR RR7.22 reported.

Plan: [`docs/planning/REPLY_FRAME_REMOVAL_PLAN.md`](REPLY_FRAME_REMOVAL_PLAN.md).


### WS-HP The head-driven donation pop — COMPLETE; the depth-2 accounting re-opened at v0.35.141 and CLOSED at v0.35.157 (registered v0.35.16; HP1 v0.35.35, HP2 v0.35.36, HP3 v0.35.37, HP4 v0.35.38, HP5 v0.35.39, HP6 v0.35.41 → v0.35.45, HP7 v0.35.46, HP8 v0.35.47, HP9 v0.35.48, HP10 v0.35.49 → v0.35.54; post-landing audit v0.35.61 → v0.35.62)

The reply path decided whether to pop a donated scheduling context from the
**recorded server's binding** (`endpointReplyServerDonation?`), not from whether
the answered frame heads a context.  `severAtCut` is exactly what kept those two
facts equivalent, and the consequence was measured rather than described: at
reply-stack depth ≥ 3 a middle removal dropped the frames below the cut, the
reservation settled `.bound` on a thread strictly *inside* the chain, and its
owner was left `.unbound` for good (`tests/SmpIpcSuite.lean` §3.22; §3.20's
depth-two witness structurally cannot show it, because a two-frame stack's lower
frame is its bottom and both policies then write the same value).

**HP6 closed that at `v0.35.45`.**  Both triggers read the answered frame
(HP4, HP5), the removal splices rather than severs (HP6.3, HP6.8), and
`donationAccountingPreserved_atCallDepthThree` is the statement: at depth ≥ 3 a
middle removal leaves the reservation **owed outward** and the pop that answers the
bottom frame delivers it home.  §3.22 inverted from a COST witness to a PAYOFF
witness in the same cut.  What was left was depth two, which the splice provably
cannot reach — both policies write `none` into the frame above a bottom frame — and
which needed the reservation's *origin* on the `SchedContext` rather than stack
reachability.

**HP10 addressed that at `v0.35.53`, and the workstream's phases closed at `v0.35.54` — but the depth-2 half did not hold, and is re-opened at `v0.35.141`.**
`SchedContext.donationOrigin` records the thread that owned a reservation when it
first left, written on a **first** push and cleared by every step that ends the
loan, and `replyDonationRecipient` reads it in place of stack reachability at the
bottom of a stack.  `donationAccountingPreserved_atCallDepthTwo` is the statement,
**under its own two guard hypotheses**.  Two fragments survive the closure,
deliberately: the footprint/transition resolution asymmetry HP10.8 found keeps its
own open register row, and `CancelledMiddleCallerPolicy.severAtCut` is **kept** as
a constructor, because it names the behaviour upstream still has and an
improvement is only statable against something.

**And the depth-2 half was NOT closed at HP10 — the guard was a proxy, and its
decline was a TRANSFER** (PR #897's review, `v0.35.141`; **closed at `v0.35.157`**).
Until `v0.35.157` `donationOriginRebindable` refused an origin that is
`.blockedOnReply`, as a stand-in for "some live `.donated _ origin` binding names
it".  The two are not the same: a client answered out of order is woken `.ready`
and `.unbound`, and its next **ordinary Call donates nothing** —
`callDonationSchedContext?` reads `SchedContextBinding.scId?`, which is `none` at
`.unbound` — while putting it `.blockedOnReply` again.  No binding names it; the
proxy refused it anyway; the pop fell back to the *answered caller*, which at
depth 2 is the intermediate caller of the chain — the reservation bound to that
caller, the client left `.unbound`, `donationOrigin` erased, so the kernel could
never return it, and a callee delegating its caller's reply capability to a
confederate could arrange it.

**What closed it is the bind's own admissibility, asked of the origin.**  The
redirect *is* a bind of the reservation to its recorded owner, so
`donationOriginRebindable` now asks `schedContextBind`'s question — is the origin's
reply frame on a **live** stack (`replyFrameOnLiveStack`, one-step reciprocity,
relocated to `IPC/Operations/Endpoint.lean` because both askers read it) — on both
surfaces.  That admits the re-called client (its new frame is on no stack) and
refuses the two shapes the proxy could not tell apart from it: an origin whose
frame *heads* a context, which is a live owner, and one whose frame sits *inside*
a live stack, which is owed a pop that a binding made now would make refuse.
Four things new code must respect.  (1) **Soundness is the coherence fact, not
the `ipcState`**: `donationOriginRebindable_no_owner` derives "no live binding
names it" from the guard under `donatedContextIsOwnerFrameHead` — WS-HP HP5.2's
binding → head fact, relocated upstream to `IPC/Invariant/Defs.lean` and restated
over the reply path's own `answeredFrameHeadContext?`, with the cancellation form
its corollary (`donatedContextIsOwnerFrameHead_cancelledCallerDonation?`).  The
reply path carries it as `redirectedOriginFrameCoherent`, gated on the trigger,
the resolver and the distinctness from the answered caller — the one thread the
fact is genuinely false at in the pop's own state, its frame consumed while the
holder's binding still names it — so a reply that redirects nothing owes nothing,
and the dispatch packs' two reply stages each gained the conjunct.  (2) **The
depth-2 payoff derives its rebindability**: `donationAccountingPreserved_atCallDepthTwo`
takes `donationRecipientAcceptable` and the origin's resolution as hypotheses and
nothing else, because the removal that fires the redirect has just taken the
owner's frame off the stack (`removeCallerReplyFrame_replyObject_none`,
`donationOriginRebindable_of_no_reply`) — where the proxy was false again the
moment the owner re-Called, the structural guard stays derivable through that
window.  (3) **The witness computes the retired reading beside the live one**:
`tests/SmpIpcSuite.lean` §3.25's PAYOFF group drives the live pop on the re-called
client, with the `.blockedOnReply` proxy spelled as a `private def` in the suite
and nowhere else, and its two NEGATIVE groups plant the live owner (with the binding
that names it) and the interior frame, each with the CONTROL that the recipient
guard alone admits the thread.  (4) **The claim is lifted**: v1.0.0 **may** claim
that completing a call chain returns a client's reservation at every reply-stack
depth — the depth-≥ 3 half by HP6's chain-preserving removal, the depth-2 half by
the recorded origin under a guard that is the fact rather than a proxy for it.  The
accounting row in `docs/REGISTERED_DEBT.md` table C is **closed**.

**The splice is an improvement on seL4-MCS, not an adoption of it** (`v0.35.40`,
re-verified against upstream source at five revisions).  `reply_remove`'s non-head
branch *breaks the chain* exactly as `severAtCut` does — see the WS-RM section
above for the C and for what the `v0.35.14` retraction cost — so upstream strands
the reservation at depth ≥ 3 too.  What HP6 buys is therefore a property neither
kernel has today, and the workstream's value does not depend on the mistaken
attribution: a callee that delegates its caller's reply capability to a confederate
could capture that caller's CBS reservation at depth ≥ 3, and the chain-preserving
removal is what closed it at `v0.35.45`.  Two things upstream *does* confirm, both landed: the pop's trigger is
`call_stack_get_isHead(reply->replyNext)` (HP4, HP5), and `reply_pop` donates only
`if (tcb->tcbSchedContext == NULL)`, which is HP4.6's `donationRecipientAcceptable`
with upstream's own reason.

The correction was **two changes in a forced order**, not one: the splice alone is
unsound under a binding-driven trigger, because it re-heads a frame whose recorded
server is by then `.unbound`, so answering it would run no pop and leave a consumed
frame heading a context — the object pinning `v0.35.4` closed.  So the trigger moved
first (HP4 `v0.35.38`, HP5 `v0.35.39`), then the sever became a splice (HP6.8
`v0.35.45`), and HP2.3's `severAtCut_pop_leaves_no_head` made that ordering a
machine-checked fact rather than a note — HP6.8 deleted it, because its first
conjunct was the policy constant at the old value and a theorem whose conclusion has
become false can only be retired.  A tombstone comment beside the `WS-HP HP2.3`
banner in `IPC/Invariant/Defs.lean` records what replaced it.

| Phase | Status | Version | Scope (one line — detail in the canonical sources) |
|-------|--------|---------|----------------------------------------------------|
| HP1 | LANDED | v0.35.35 | The trigger's resolvers and the splice's below-frame resolver, both inert |
| HP2 | LANDED | v0.35.36 | The two triggers are equivalent on every coherent state, and the splice breaks it |
| HP3 | LANDED | v0.35.37 | The removal's below-frame footprint member; `maxLockSetSize` 22 → 23 |
| HP4 | LANDED | v0.35.38 | **The reply path's trigger flips** — both spines, the recipient guard, the payoff's packs, and the frozen mirror (HP4.7) |
| HP5 | LANDED | v0.35.39 | **The cancellation path's trigger flips** — the resolver, the coherence fact re-keyed, two sentences turned into theorems, and the first witness that fires the reclaim (HP5.5) |
| HP6 | LANDED | v0.35.41 → v0.35.45 | **The splice replaces the sever** — the family renamed (HP6.1), the two reply footprints repointed (HP6.2), then the primitives, the algebra, the policy flip and the depth-three payoff as one cut (HP6.3–HP6.9) |
| HP7 | LANDED | v0.35.46 | **The three stated coherence hypotheses retire** — nine declarations deleted with the binding-driven resolver, HP7.1 already done at HP4.4, HP7.4 vacuous, and the fourth stated fact found LIVE |
| HP8 | LANDED | v0.35.47 | **The frozen mirror splices** — the sever's family deleted, the census's three mirrors, and `FO-043`: the depth-3 witness every shallower scenario structurally could not be |
| HP9 | LANDED | v0.35.48 | **Witnesses, anchors, documentation, closure** — the depth-4 witness (§3.23), the upstream facts recorded at the code, and acceptance box 10 struck as wrong rather than ticked |
| HP10 | LANDED | HP10.1–HP10.5 v0.35.49, HP10.6 v0.35.50, HP10.7 v0.35.51, HP10.8 v0.35.52, HP10.9 v0.35.53, HP10.10 v0.35.54 | **The reservation's origin**, so the return does not depend on chain connectivity — the depth-2 residue the splice provably cannot reach; the redirect is live on both surfaces, **`donationAccountingPreserved_atCallDepthTwo` is the payoff**, and the debt row is closed |

**What new code must respect since HP4 (`v0.35.38`).**  Seven things.

(1) **Both reply spines pop on the FRAME, and take it as an argument.**
`applyReplyDonation st rid targetVtid`, `applyReplyDonationOnCore st rid
targetVtid holderHome ownerHome` and `replyRecvPopDonation rid target` all read
`replyFrameHeadHolder? st rid`.  The `rid` is an argument and has to be: the reply
leg's `consumeCallerReply` clears the answered caller's `replyObject`, so
`answeredFrameHeadContext?` answers `none` at every state the pop runs on.  It is
resolved on the pre-state through `answeredReplyObject?`, the one expression the
arm's footprint members also come from; `answeredFrameHeadContext?` is now that
composition rather than a second spelling.  Everything the pop *decides* — which
context the frame heads, which thread holds it, which caller is outer — is read at
the pop's own state, which is what keeps `returnDonatedSchedContext`'s
`boundThread` guard vacuous.

(2) **The pair's second component is the thread that LOSES the context**, where
`endpointReplyServerDonation?`'s was the one that gains it.  Same type, opposite
role, and under the flip the pair also moves from `returnDonatedSchedContext`'s
`originalOwner` position to its `serverTid` one.  A substitution that swaps them
typechecks; `answeredFrameHeadContext?_boundThread` is the theorem that the
component *is* `sc.boundThread`, and Tier 3 negatives refuse the swap at each
site.

(3) **`replyDonationReturn?` is NOT the trigger and was not re-keyed.**  It
answers "does this thread hold a donated context", which the two pre-receive
cleanups, the cancellation reclaim and the witnesses still ask.  Its argument
means the holder; the trigger's means the answered caller.

(4) **The pop refuses a recipient that already holds a binding**
(`donationRecipientAcceptable`).  The head-driven recipient is the answered
caller, which no binding the operation reads constrains, so without the guard a
caller that acquired a reservation while blocked would have it silently
overwritten.  Inert on every reachable state; `returnDonatedSchedContext`'s
`_ok_storeChain` carries it as a tenth component, so a consumer destructuring that
chain by position gains one `_`.

(5) **The priority-inheritance reversion still walks from `recordedReplyServer?`**,
because it keys on waiters rather than on donations — a walk from the context's
`boundThread` would start at the wrong thread on exactly a delegated reply.  And
the `.replyCapInvalid` arm still distinguishes "no recorded server" from "no head
context": collapsing them would turn every donation-free reply into an error.

(6) **The two reply footprints resolved their donation members through the
binding until HP6.2** (`v0.35.44`), with the gap held closed by
`lockSet_endpointReplyOnCore_covers_headDrivenPop` — a footprint that omits a
written object is false.  That repoint had to land *before* the splice: under the
sever the two resolvers agreed — `severAtCut_pop_leaves_no_head` was the statement,
retired with the policy at HP6.8 — and the splice is the change that makes them
disagree, so a window with the splice landed and the repoint outstanding would carry
a footprint that omits what the pop writes.  The paragraph on HP6.2 below says what
landed.

(7) **The FROZEN mirror is head-driven too, and its binding-driven resolver is
gone** (HP4.7).  `frozenEndpointReplyWithDonationReturn` reads
`frozenReplyFrameHeadHolder? st replyId` — no resolution needed on that surface,
because `replyId` *is* the presented capability and `frozenEndpointReply` refuses
it unless the target's own `replyObject` names it — and hands the context to
`targetId` rather than to a binding's recorded owner.  The flip belongs to HP4
rather than to HP8 because HP4 is the cut that makes the live operation
head-driven, and `frozenBranchOperationChecked .endpointReplyToBlockedCaller =
true` is a machine-checked claim that the two are run beside each other: a
binding-driven mirror of a head-driven operation is *one question answered in two
places* with the divergence already scheduled at HP6.
`frozenEndpointReplyServerDonation?` is deleted, not kept beside the new reading.
`FO-042` is what makes the claim a measurement — `FO-041` had never given the
recorded server a `.donated` binding, so through four review rounds the frozen
donation return was compared on neither side — and its second half is the state
where the two triggers disagree, which is the mutation that decides the flip.
Asking the question also found the frozen pop **missing HP4.6's recipient guard**
under a docstring claiming it carried every live one: `frozenDonationRecipientAcceptable`
is the counterpart, in the live position, and `FO-042`'s third half is its witness.
A mirror missing a guard *succeeds* where the kernel refuses, which is the
direction that matters on a differential surface.  The same question found the
live step's **ID promotion** missing too — `applyReplyDonation` refuses a holder
`toValid?` will not promote — added as `holder.isReserved`, because this surface
uses `toValid?` nowhere and `frozenLookupTcb` (which *is* `isReserved`, exactly
`= sentinel`) is how it already asks that question; a Tier 3 negative keeps
`toValid?` out of both frozen modules so the convention stays one.  HP8 owned
the **splice** half alone, and landed it at `v0.35.47`.

**What new code must respect since HP5 (`v0.35.39`).**  Six things.

(1) **The cancellation reclaim reads the victim's own reply FRAME.**
`cancelledCallerDonation? st _tid tcb` is `replyFrameHeadHolder? st rid` at
`tcb.replyObject` under the `.blockedOnReply` arm gate — the same frame-keyed
resolver both reply spines read since HP4.1, not a second spelling
(`cancelledCallerDonation?_eq_answeredFrameHeadContext?` ties it to the reply
path's own form).  The victim's id is **not consulted**: the binding reading's
`owner == tid` check is what the structure replaces, and
`cancelledCallerDonation?_independent_of_victim` pins that rather than leaving a
reader to infer it from an underscore.  The arm gate stays, because it is the
*arm selector* every exclusivity lemma in the cancellation family reads.

(2) **`donationHolderIsReplyTarget` is GONE** — WS-RR RR7.22's fact about a
cancelled caller's recorded reply target, which nothing reads any more.  Its
head-keyed successor is `donatedContextIsOwnerFrameHead`: the donation the victim
owns is the one its own frame heads, and the reclaim's trigger finds it.  It runs
binding → head, the opposite direction from the reply path's
`answeredHeadContextIsServerDonation`, because here the *consumers* quantify over
bindings while the trigger reads frames.  `…_of_donationOwnerValid` is the builder
and it measures what the fact costs: everything but two clauses comes out of
`donationOwnerValid`, and what is left — the frame-head link and the holder's
promotability — is what no invariant in this tree entails.

(3) **A holder the head reading names may resolve to nothing.**  The
binding-driven resolvers read a thread out of a stored binding, so the store held
it by construction; `SchedContext.boundThread` is tied to no stored TCB by any
invariant.  What rules the case out is the **pop declining**
(`returnDonatedSchedContext_ok_server_not_reserved`), with
`abortHolderPendingIpc_eq_self_of_lookup_none` the frame that lets a consumer act
on it.  New code must not read a resolved `(scId, holder)` as evidence that
`holder` is a live thread.

(4) **`returnDonatedSchedContext_ok_under_invariants` is now an instance.**  The
general form is `_ok_of_boundAndRecipient`, which takes the context, its bound
thread and the recipient's `.unbound` as *arguments* — the head reading supplies
the first two off the trigger and has no binding to read the third from — with
the binding-keyed form derived from it.  A new success argument reaches for
whichever form it can discharge, never for a second proof.

(5) **Two claims are theorems now, and were not stateable before.**
`cancelReclaimHead?_eq_replyObject` — the head the pop clears **is** the victim's
own reply object, which is `replyStackHeadIsAnsweredReply`'s content seen from the
cancellation end — and `cancelSplicedFrameAbove?_of_donation` /
`cancelSplicedFrameBelow?_of_donation`, a reclaim excludes both removal members.
Both were sentences about "every reachable state" in footprint docstrings; the
binding reading could not have stated either, since it reached the context through
a binding that relates to no reply frame.  Cite the theorems.

(6) **Below the cut the reclaim declines on the STACK.**
`cancelledCallerDonation?_none_below_the_cut` and
`cancelledCallerDonation?_some_of_frame_head` (renamed from
`…_some_of_immediate_donee` for what it now says) are stated over
`replyFrameAbove?` and `replyFrameHeadContext?` and carry **no** binding
hypothesis — a frame with a frame above it heads nothing, so the pop's trigger and
the splice's are exclusive by construction.  That is strictly cheaper than what it
replaces, and it is the fact HP6 consumes.

One thing HP5 measured rather than predicted, and one it got wrong first.  The wake
and both below-head footprint members needed **no** re-resolution, because
`cancelAbortedHolderWake?`, `cancelAbortedHolderWakeCore?` (the wake's resolvers,
retired with the wake at `v0.35.158` for `cancelUnboundHolder?` /
`cancelUnboundHolderCore?`, which derive the same way), `cancelBelowHeadReads?`
and `cancelReclaimHead?` are all *derived from* the trigger — the derivation
discipline paying off where an enumeration would have needed five edits.

The fixture sweep is the one it got wrong, and the shape is this file's own: the plan
named three files, **a sweep over a named list is a recognised set standing in for a
derived one**, and the three came back clean while the *golden trace* then failed —
`SeLe4n/Testing/MainTraceHarness.lean` was not among them.  The derived set is every
tracked test or harness file mentioning `.donated`, thirteen of them, and it holds two
live defects.  `SCO-020b/c/d` built a `.donated` binding with **no Reply object at
all**, so the reclaim became the identity and all three lines flipped to `false`; they
carry the stack a live `Call` builds now, which keeps `main_trace_smoke.expected`
byte-identical.  And `tests/SmpIpcSuite.lean`'s OD5.2 pair was passing **vacuously** —
its store's `pushOuter` named no reply object though `pushOuterReply.caller` named it
back, and both assertions handed the resolver a TCB without the field, so "fires" and
"declines below the cut" declined for the same reason.  **A suite's assertions can pass
vacuously; an exact golden trace cannot** — which is why the trace found what the suites
hid, and the reason to run it early in a flip rather than last.

The gap the sweep did surface is HP5.5: **nothing in the tree fired the reply-arm
reclaim with the head reading available**, so the flip would have landed untested.  A
sweep for fixtures that would *break* is not a sweep for fixtures that would
*exercise*, and only the second measures a flip.  HP5.5 is that witness:
`tests/SmpCancellationSuite.lean` §3.20 fires the reclaim on the agreeing shape and on
the orphan head, computing **both** readings side by side (the retired one spelled in
the suite and nowhere else) so the assertions are known to discriminate.  A behavioural
revert never reaches them — it fails four theorems in `Lifecycle/Suspend.lean` first,
because HP5 *states* the head reading rather than merely computing it.

**What new code must respect since HP6.1 (`v0.35.41`).**  The removal family was
renamed for the operation it becomes, and for four cuts **the name ran ahead of the
body**: `spliceReplyFrameOut{,OrSelf}`, `spliceThreadReplyFrameOut` and
`cancelSplicedFrameAbove?` wrote `above.prev := none` — the sever — until HP6.3
(`v0.35.45`).  Three things that row decided and one it found.  (1) **The name and
the body were separated by two facts, and neither was the other**:
`cancelledMiddleCallerPolicy` is the *declared policy* and
`spliceReplyFrameOutOrSelf_store_cases` states the *body's* writes, so the splice
could not land without changing that lemma's statement — which it did, from one
store to a three-step existential.  **Not** `cancelledMiddleCaller_severs_at_cut`:
its policy conjunct was `rfl` on the constant and its cut shape a hypothesis, so it
was a statement about the *pop* given a severed cut rather than about the removal
that produces one — the shape this file calls a theorem whose conclusion is one of
its own hypotheses.  It is `cancelledMiddleCaller_splices_at_cut` now.  (2) **The
FROZEN family keeps its `frozenDetach…` names**, because it still severs; HP8
renamed it in the cut that made it splice (`v0.35.47`), so a `frozenDetach…` beside
a live `splice…` read as the schedule rather than as a drift.  (3) **The English word
"detach" in prose describing what the operation does was accurate at that version**
and was deliberately left alone — prose follows behaviour at HP6.3, where the name
followed the design here, and that sweep is part of the same cut.  **That sweep was
not run**: the post-landing audit's second pass (`v0.35.62`) found the operation
still called *the detach* — and, at nine sites, the sever still described as what it
does — across some 120 docstrings, comments, test labels and documentation
sentences in 35 files, and swept them.  (4) A rename is a
sweep, and this one found a **dead citation**: WS-RM RM1.1 retired
`detachCancelledCallerFrame` at `v0.35.6` and four *live* claims still named it —
this file's own WS-OD item 5 and `SELE4N_SPEC.md` §8.12.7 twice.  That is the
tautological-pin shape one artefact over: prose citing a declaration that does not
exist reads exactly like prose citing one that does.  HP6.8 paid the same cost in
reverse, deleting `severAtCut_pop_leaves_no_head` and having to sweep its five prose
citations.

**What new code must respect since HP6.2 (`v0.35.44`).**  The two reply
footprints resolve their donation members through **the pop's own trigger**:
`lockSet_endpointReplyOnCore` and `lockSet_endpointReplyRecvOnCore` read
`answeredFrameHeadContext? st target`, the expression
`applyReplyDonationOnCore` itself reads, so the footprint and the transition
cannot disagree about which context is popped or which thread is unbound.  Six
things follow.

(1) **The pair's second component is the thread the pop UNBINDS**, and the
parameter says so: `lockSet_endpointReply`'s and `lockSet_replyRecv`'s
`donatedOriginalOwnerTid` is renamed `donatedScHolderTid`.  A resolved footprint
that passes the *recipient* there declares a lock for a write the pop does not
perform and omits one it does — the recipient needs no member, because the
head-driven pop hands the context to the answered caller and that is
`replyTargetTid`.

(2) **Coverage is definitional, and stated on both arms.**
`lockSet_endpointReplyOnCore_covers_donationPop` and its `.replyRecv` twin take
**no hypothesis**; HP4.4's `lockSet_endpointReplyOnCore_covers_headDrivenPop`,
which needed `donationOwnerValid` and `answeredHeadContextIsServerDonation` and
reached the holder's TCB by *proving it was the recorded server*, is deleted.  A
behavioural revert does not reach a witness — it fails the coverage theorem
first, which is where this relation belongs.

(3) **Three write-membership lemmas had to be added**, and their absence is the
finding: the second donation member had **none** on either footprint, and
`lockSet_replyRecv`'s SchedContext member had none either, so nothing could state
that the objects the hottest IPC arm's pop writes carried declared write locks.
The stand-in had routed around the gap through `callerTid`'s lemma.  Found by
asking the table to be symmetric, not by a review round.

(4) **`server` stays keyed on the RECORDED server**, because that is the thread
`propagatePipChainCrossCore` walks from and rewrites, and the splice can make it a
different thread from the holder — so both are declared.  Measured against the
composite's three write sites rather than reasoned from the resolver.

(5) **`lockSet_endpointReplyRecvOnCore_size_le_eighteen` is now unconditional**,
where it took `donationChainWellFormed` and `replyStackHeadIsAnsweredReply`: under
this trigger a frame that heads a context has no frame above it and none below
(`answeredReplyFrameAbove?_none_of_headContext`), so the exclusion is structural.
That is strictly stronger than what it replaces.

(6) **`lockSet_endpointReplyRecvOnCore_size_le_seventeen` is RETIRED**, and this is
what the repoint costs.  Its single merge was `replyDonationOwnerIsAnsweredCaller`
— the *owner* is the answered caller — and the head reading's second component is
the thread *running on* the context while the answered caller is
`.blockedOnReply`, so that coincidence occurs on **no** state this arm reaches:
the merge is false, not unproved.  The available substitute is *holder = recorded
server*, which is `answeredHeadContextIsServerDonation`'s content and exactly what
the splice falsifies, so a seventeen resting on it would stop holding in the cut
after next.  One unit of slack traded for two hypotheses and a figure that
survives HP6.  Both coherence facts had **no consumer at all** after this row,
which is the verification HP7.2 asked for and HP7 (`v0.35.46`) then ran — and
having run it, HP7 **deleted** both, so a sharper reachable bound cannot be built
on *holder = recorded server*: the splice falsifies it on reachable states.

**What new code must respect since HP6.3–HP6.9 (`v0.35.45`).**  The removal is
seL4's `reply_remove` with the middle case **spliced** rather than severed, and the
name has caught up with the body.  Eight things.

(1) **The splice is THREE stores, and the third is not optional.**
`spliceReplyFrameStores` writes `above.prev := some below`, `below.next := some
(.frame above)` and `rid.prev := none` — the last being seL4's `reply_unlink`
downward half.  A two-store splice leaves the cut frame with `prev = some below`
while nothing below names it back, which falsifies `prevLinkReciprocal` at the cut
frame, so the bare splice would owe a relaxed predicate and
`ReplyStackWriteCensus` would have to accept a half-step where the sever stated its
result outright.  With the third store `donationChainWellFormed` is preserved
**outright** (`spliceReplyFrameOut_preserves_donationChainWellFormed`,
`removeCallerReplyFrame_preserves_donationChainWellFormed`), and it is **free**: the
cut frame's lock is already a declared write member on both removal paths, so
`maxLockSetSize` was unmoved by it, at HP3.5's twenty-three (HP10.6 has since
taken it to twenty-four, for a member of its own).

(2) **The below side does not refuse — it degenerates.**  `spliceFrameBelow?` is an
`Option`: a `prev` that does not resolve, one naming the frame above, and a frame
below whose own `next` does not link back are all *not followed*, and the removal
then writes `above.prev := none`, which is the sever.  So this operation's refusal
set is **exactly** the pre-WS-HP one and every refusal theorem carries verbatim,
`spliceReplyFrameOutOrSelf`'s fold soundness included —
`spliceReplyFrameOut_eq_sever_of_no_frame_below` is the definitional equality that
makes every repair a case split whose `none` branch is the pre-HP proof.  A
consequence: a **stale upward link is still reachable**, so the reciprocity checks
(`donationChainFrom`, `replyFrameOnLiveStack`) stay and stay load-bearing.

(3) **`spliceReplyFrameOutOrSelf_reply_next` is GONE**, because the splice moves a
`next` from one `.frame` link to another and its old conclusion (`rq.next =
rp.next`) is false.  Its successor
`spliceReplyFrameOutOrSelf_preserves_reply_caller_and_headLink` is a disjunction,
which is still exactly what its one consumer needs: no reply's `next` acquires a
`.head` link, so `removeCallerReplyFrame_preserves_donationChainWellFormed` may read
`hNotHead` on the pre-state.

(4) **The composed store step is a write site, registered as a half-step.**
`spliceReplyFrameStores` is in `chainWritePrimitives` and registered `.halfStep
spliceReplyFrameOut`, exactly as the pop's two component stores are half-steps of
`storeDonationHeadPop`.  It cannot state a chain result of its own: given only
`above` and the two records, nothing says the frame above is the one whose `prev`
names `rid`, and the three reciprocal links are coherent only under the resolution
the operation performs.  `spliceReplyFrameOutOrSelf_store_cases` is spelled as a
three-step **existential** rather than a named relation, because a `Prop`-valued
relation whose body mentions `storeObject` is reported by the census's store
frontier and registering a relation as a write site is not an option — it writes
nothing.

(5) **The removal's write set is FOUR keys** — the consumed Reply, the answered
caller's TCB, and the two frames either side of the cut — so
`removeCallerReplyFrame_objects_frame` takes a fourth exclusion and
`spliceReplyFrameOut_objects_ne` takes two (the frame below, and the cut frame
unconditionally).  The information-flow half needs `hSetInv` threaded, because the
frame below is written at the *intermediate* state and its index membership is read
there.

(6) **The two facts the sever could not state.**
`removeCallerReplyFrame_splices_reciprocally` — after a middle removal the frame
above names the frame below and the frame below names the frame above — and
`donationAccountingPreserved_atCallDepthThree`, the pop that follows delivering the
reservation to the caller the surviving stack names.  Both are stated with **no**
key-distinctness hypothesis, derived instead from the store's contents (a key
holding a `.reply` is one at which the consume's own TCB lookup fails), because
`ReplyId.toObjId` and `ThreadId.toObjId` are two wrappers over one `ObjId` and a
collision is representable.  `removeCallerReplyFrame_getSchedContext?_eq` is the
same shape and is what lets a post-removal head be resolved against the pre-state
context record.

(7) **Cite the live policy's consumers, not the retired ones.**
`cancelledMiddleCallerPolicy = .spliceOutTheCut`;
`replyStackOuterCaller?_follows_policy` concludes `.ok (some outer)` at a frame with
one below it, where it used to conclude `.ok none` at a cleared `prev`; and
`cancelledMiddleCaller_splices_at_cut` gives the target `.donated scId outer`, where
`cancelledMiddleCaller_severs_at_cut` gave `.bound scId`.  `severAtCut_pop_leaves_no_head`
is **deleted**.  `CancelledMiddleCallerPolicy.severAtCut` is **kept** as a
constructor: it names the behaviour this kernel diverged from and that seL4-MCS
still has.

(8) **The orphan head is reachable now.**  A frame heading a context whose recorded
reply server is gone and `.unbound` is what the splice produces, so
`answeredHeadContextIsServerDonation_false_of_orphan_head` changed from a
*prohibition* into a *fact about reachable states* — and that, with both coherence
facts having no consumer since HP6.2, is the warrant HP7 spent: HP7 (`v0.35.46`)
**deleted the predicate and this theorem with it**, a refutation having no subject
once the thing it refutes is gone.  What carries the evidence instead is an
*executed* witness — `tests/SmpCrossCoreReplySuite.lean` computes the retired
binding-driven reading beside the live one at an orphan head.

**What new code must respect since HP7 (`v0.35.46`).**  The three *stated*
coherence facts the binding-driven pop needed are **deleted**, together with the
resolver and the scaffolding that consumed them — nine declarations, not three.
Six things.

(1) **Do not restate a retired fact as a hypothesis.**
`replyDonationOwnerIsAnsweredCaller`, `replyStackHeadIsAnsweredReply` and
`answeredHeadContextIsServerDonation` are gone, and Tier 3 refuses each of them
tree-wide.  The last is not merely unused but **false on reachable states** since
HP6.8: the splice re-heads a frame whose recorded reply server is gone and
`.unbound`, which is the orphan head.  A proof that wants one of these is a proof
asking for a premise the kernel refutes.

(2) **What replaced them is the HP2.4 family, and it is where to reach.**
`answeredFrameHeadContext?_head_is_answered_reply`, `…_donationHeadOf` and
`…_boundThread` are the *derivations*: under the head-driven trigger the resolver
reads the context off the answered frame's own `.head` link and validates that
context's `scReply` against the same frame, so each retired hypothesis is a
consequence of the trigger firing — no hypothesis at all.  They are anchored in
Tier 3 because a derivation nothing consults reads exactly like one nobody
checked.

(3) **The fourth stated fact is LIVE, and its docstring used to say otherwise.**
`replyFrameHeadHolderDonation` (HP4.2's rename of `answeredHeadHolderDonation`) is
the one binding fact the trigger does **not** witness — that the holder's binding
*is* a donation of the context its frame heads — and it has twelve-plus consumers,
the dispatch packs' two reply-stage fields among them.  Its own docstring claimed
HP7 retires it; that claim is corrected rather than acted on.  Of the row's three
facts, two are *eliminated* and one is *migrated*.

(4) **`endpointReplyServerDonation?` does not exist.**  The reply path's
binding-driven trigger was deleted, not kept beside the live one: two readings of
one question free to drift is this project's worst shape, and these two *disagree*
on reachable states.  `recordedReplyServer?` beside it is **not** retired — the
priority-inheritance chain walk reads it, because that walk keys on waiters rather
than on donations, and on a delegated reply the recorded server is not the holder.

(5) **The retired reading lives in the witness that refutes it, and nowhere
else.**  `tests/SmpCrossCoreReplySuite.lean`'s `private def
bindingDrivenReplyServerDonation?` computes it beside the live resolver on the
agreeing shape and on the orphan head, so the assertions are known to
discriminate rather than merely to pass — the pattern
`tests/SmpCancellationSuite.lean` §3.20 set at HP5.5 and `FrozenOpsSuite`'s
`FO-042` set for the frozen surface.  That keeps the *evidence* HP2 produced and
deletes the *code*.

(6) **The dispatch packs shed nothing here, and that is recorded rather than
claimed closed.**  `syscallDispatchQuiescence`'s eleven fields and
`checkedSyscallDispatchQuiescence`'s two never carried one of the three; HP4
re-keyed the reply-stage conjuncts onto the head-driven reading in the cut that
flipped the trigger, which is where a pack field belongs — one stated at a state
its own step no longer runs on is a claim about a different state.  So HP7.4 is
**vacuous**, and the phase's acceptance criterion was corrected to something
checkable instead of being reported as met.

**What new code must respect since HP8 (`v0.35.47`).**  The frozen execution
surface's removal **splices**, and the sever's names are gone.  Five things.

(1) **`frozenDetachReplyFrameAbove` and `…OrSelf` do not exist.**  The family is
`frozenSpliceFrameBelow?`, `frozenSpliceReplyFrameStores`,
`frozenSpliceReplyFrameOut` and `frozenSpliceReplyFrameOutOrSelf`, each clause for
clause with its live counterpart, and Tier 3 refuses the retired names tree-wide.
HP6.1 kept the sever's names deliberately — a `frozenDetach…` beside a live
`splice…` read as the *schedule*, where a `frozenDetach…` whose body splices would
read as a drift — and this is the cut that discharges that, because the name and
the body move together.

(2) **The three stores are the same three, and the third is masked here.**
`above.prev := some below`, `below.next := some (.frame above)`,
`rid.prev := none`.  The third is seL4's `reply_unlink` downward half and it is
*not observable through the frozen reply composite*: the `Reply.consumed` that
follows clears the cut frame's links anyway on a frame heading nothing, so the
suite still passes with that store deleted.  It is load-bearing regardless — a cut
frame keeping a `prev` nothing names back is what the store exists to prevent, and
it becomes observable the moment `consumed` changes — so `FO-043`'s last half
drives `frozenSpliceReplyFrameOut` **directly**, beside the live primitive, which
is the only place its deletion fails.  A new assertion about the cut frame's own
links taken from the composite's post-state is testing `consumed`, not the splice.

(3) **The below side declines rather than refusing**, for the reason it does live:
the `…OrSelf` fold turns a *refusal* into the identity, and that is sound only
because a refusal means nothing links down to the cut frame.  A below-side refusal
folded to the identity would leave a reciprocating frame above naming a frame whose
caller has been cleared.  So the refusal set is unchanged from the sever's, and
`frozenSpliceReplyFrameStores_eq_sever_of_no_frame_below` is the equality that
makes every pre-HP8 scenario answer as it did.

(4) **Depth ≤ 2 cannot measure this flip, and the suite was green before it.**
A two-frame stack's lower frame is its bottom, so both policies write the same
value there; `FO-031` and `FO-041`/`FO-042` all sit on such stacks and passed
byte-identically when the splice landed.  `FO-043` is the three-frame witness with
the answered caller holding the **middle** frame, mutation-verified in both
directions.  A new frozen removal scenario that asserts a connectivity property
must be at depth ≥ 3 or it is asserting about the fixture.

(5) **The census carries three frozen splice entries where the sever had two.**
The store step is registered on its own — as the live `spliceReplyFrameStores` is,
because it performs the writes with none of the removal's resolution or validation
— and each is a `.mirrors` entry naming the live counterpart of the *same shape*,
so the store step's chain terminates in a stating entry two hops out, through the
live `.halfStep`.  The census prints its own counts; they are not restated here,
for the reason the WS-RM section's item (6) gives — this paragraph carried them
until the post-landing audit (`v0.35.61`) found it doing so.

**What new code must respect since HP9 (`v0.35.48`).**  Five things, and three of
them are about what the phase did *not* do.

(1) **The depth-4 witness measures the splice's COMPOSITION, not its stores.**
`tests/SmpIpcSuite.lean` §3.23 cuts the third frame of a four-frame stack, so
**two** frames sit below the cut — the shallowest shape on which the splice's
transitivity is a proposition at all, since at depth 3 "the stack reconnects" and
"the frame beneath the reconnection survives" are one statement.  Three successive
pops then carry the reservation home, where §3.22 needs two.  What it deliberately
does **not** catch is a change to the three stores: `spliceReplyFrameStores_cases`
states them exactly, so both candidate mutations — the full sever, and a
reconnection that clobbers the frame below's own downward link — fail to
*elaborate* rather than failing a test.  A new reply-stack scenario that asserts a
store shape is duplicating a theorem; one that asserts a *walk* or a *pop chain* is
measuring something no theorem states.  And a pop chain **follows** the resolver's
answer rather than supplying it: `returnDonatedSchedContextResolved` reads
`replyStackOuterCaller?` of its own state, so each row asserts where the kernel says
the reservation is still owed and the next row pops at that same thread.  A chain
whose recipients are chosen by the fixture measures the fixture.

(2) **The upstream facts live beside the code they justify.**
`donationRecipientAcceptable`'s docstring carries all three — `reply_pop` donates
only under `if (tcb->tcbSchedContext == NULL)`, the trigger is
`call_stack_get_isHead(reply->replyNext)`, and `reply_remove`'s non-head branch
writes **zero** into the frame above — each naming the revisions read.  A claim
about an external artefact belongs at the code it justifies, and it names a **tag**
rather than a repository, because `v0.35.14` asserted the opposite, quoted a line
that exists in no release, and swept that error across nine prose sites and three
docstrings that had been right.

(3) **The anchors are where their cuts put them, not in a closing sweep.**  HP9.2
asked for positives and negatives over the splice, the trigger and the recipient
guard; every one of them had already landed with HP6.5, HP7 or HP8, mutation-tested
in both directions at the time.  So HP9 added only the depth-4 witness's own,
and **retired one it had first written**: a standalone check that the scenario is
*called* duplicated the WS-OD contiguous-run anchor, which already names every
runner of that group **in order** — and which is what caught the insertion, exactly
as its own comment says it caught OD3.1's and OD4.1's.  A new scenario in that
group therefore extends that anchor rather than adding a sibling; adding parallel
anchors to satisfy a row would have been the duplication this file spends its
length retiring.

(4) **The donation-accounting register row is still OPEN, and HP9's acceptance box
saying otherwise is struck through rather than ticked.**  That box was written
before `v0.35.42` found the depth-**2** loss, where the removal takes the client's
frame off the *bottom* of its stack and both policies write `none` into the frame
above — so the splice provably cannot reach it.  What WS-HP earned is the depth-≥ 3
half.  Closing the row would corrupt the artefact RR8.15's hand-off check reads, so
at HP9 v1.0.0 could still not claim that completing a call chain returns a client's
reservation *unconditionally*: that was HP10's, and **HP10.9 (`v0.35.53`) earned
it** — `donationAccountingPreserved_atCallDepthTwo`, closed by the reservation's
recorded origin rather than by any change to the removal.  The row itself retires at
HP10.10, which is why it is still open at HEAD.

(5) **An acceptance box is a present-tense claim, so a later phase that deletes its
artefacts must sweep it.**  HP9's closure read the plan's acceptance list against the
tree and found box 3 — *the two triggers are proved equivalent … and the theorem that
the splice breaks that equivalence exists* — citing two declarations that survive only
as tombstones: HP6.8 deleted `severAtCut_pop_leaves_no_head` because its first
conjunct was the policy constant at the old value, and HP7 deleted HP2.1's equivalence
with the binding-driven resolver it was stated over.  Both deletions were right, and
both were cuts whose own citation sweeps missed this box, because a criterion reads as
*history* while being written as a live claim.  It is corrected by recording the
lifecycle rather than by weakening the criterion: an **ordering pin** exists to make a
sequence machine-checked *while the ordering is still ahead*, and once the ordering is
taken its subject is gone — so the box says it is not re-verifiable by grep, names the
cut that earned it, and names what replaced each artefact.  A box whose artefacts a
later phase consumed, left in the present tense, reads exactly like a box nobody
checked.

**What new code must respect since HP10.6 (`v0.35.50`).**  Both reply footprints
declare the TCB a bottom-of-stack pop will redirect the reservation to, and
`maxLockSetSize` is **24**.  Seven things.

(1) **The resolver is `donationOriginRecipient?`, and it is the expression the arm
will read.**  It answers `some o` only where all three of the pop's own conditions
hold: `replyStackOuterCaller?` says bottom of stack (which *is*
`returnDonatedSchedContextResolved`'s `newOwner? = none`, so the member is declared
on exactly the states the pop writes it), the context records an origin, and that
thread passes HP4.6's recipient guard — and, since HP10.7, `donationOriginRebindable`.
It is a *distinct* key exactly on the out-of-order removal this phase exists for,
which is the state HP10.7's pop writes a different TCB on.

**HP10.6 claimed this member is live at depth 1, and HP10.8 measured that it is
not.**  The footprint resolves on the syscall's **pre-state**, where the answered
caller is `.blockedOnReply` — it is waiting on this very reply — so HP10.7's
rebindability guard refuses it and the member is `none` there.  The *transition*
resolves after the reply leg, which wakes that caller, so it may answer `some
answeredCaller`; the pop then writes `replyTargetTid`, which the footprint declares
unconditionally, so nothing is undeclared.  Two consequences a reader must not
lose.  The `insertOrMerge` collapse asserted in `tests/DeadlockFreedomSuite.lean`
is a statement about the **argument value**, not about a reachable resolution.  And
the footprint and the transition read the resolver at **different states**, which
every other member of this family avoids by construction — the asymmetry is
registered rather than assumed away (`docs/REGISTERED_DEBT.md`, WS-HP).  `donationOriginRecipient?_eq_some_iff` is
the one characterisation the three consumers read — a second case analysis over the
same four-way match is the duplication this file spends its length retiring.

(2) **The guard is applied to the CANDIDATE, not to the argument.**  That is the
whole difference between a recovery and a regression: a stale origin makes the
resolver answer `none` and the pop falls back to the reachability recipient, where
applying the guard after the choice would *refuse* the pop.  A resolver that
answered `some` unconditionally passes every positive anchor and breaks this; a
Tier 3 positive pins the `if … then some origin else none` shape.  **And since
`v0.35.61` a candidate is first of all a thread that resolves.**  Both guards pass
a thread with no TCB (their `_of_none` arms exist so the *operation's* argument
keeps its own error code), so as first landed a recorded origin naming no thread
was answered as a candidate and the pop's own `lookupTcb` then refused the reply
with `.objectNotFound` — a refusal on exactly the shape this item says falls back.
Unreachable, because objects are never erased and `clearDonationOriginReferences`
clears the field when the thread it names is retyped, and closed anyway: a
contract the code does not decide is one a later cut can break silently.  The
resolver resolves the origin through `lookupTcb` before it consults either guard,
`replyDonationRecipient_resolves` is the no-refusal fact the pop now has (whenever
the answered caller resolves, so does the recipient), the frozen mirror does the
same through `frozenLookupTcb`, and §3.25 and FO-044's third half are the
witnesses — each with the two-guard CONTROL that makes the decline attributable to
the resolution check alone.

(3) **The member is a WRITE, and coverage is a relation rather than a presence
check.**  `lockSet_endpointReply_originRecipient_write_mem` and its `.replyRecv`
twin state the membership at full arity, and
`lockSet_endpointReply{,Recv}OnCore_covers_originRecipient` state it of the
*resolved* footprint under the trigger's own answer.  The Tier 3 anchor over each
definition asks only that the resolver occur there, which is the presence check
those theorems replace.

(4) **The ceiling moved and the reachable figures did not — by theorem.**  The
origin member is live only at the bottom of a stack, and there the two below-head
members are both absent (`replyStackBelowHead?_of_originRecipient`, over
`replyStackBelowHead?_of_outer_none`), so a reachable footprint trades **two**
members for one: `lockSet_endpointReplyRecvOnCore_size_le_twenty` and
`…_size_le_eighteen` are unchanged, now by a case split on the redirect, and
`tests/LockSetSuite.lean` exhibits the redirecting shape at **seventeen** —
one *narrower* than the popping shape it is measured against at the same operands.
What moved is the union over all argument values, which is what
`boundedWait_under_2pl` and the WCRT surface consume.

(5) **The cost is not restated here.**  `maxLockSetSize` moved and the RPi5
per-lock cost and envelope moved with it; all three live in the canonical sentence
this file carries above, which `scripts/check_lock_ceiling_figures.py` derives from
the Lean sources and holds every prose copy to.  A second copy of the figures in
this paragraph would be a hand-kept number beside a derivation, which is the shape
that drifts on contact — and the gate refuses a near-miss of the canonical phrase
rather than skipping it, which is how this paragraph's first draft was caught.

(6) **The redirect's SCOPE is the reply path, and the declaration is what fixes
it.**  All six pop call sites thread `returnDonatedSchedContextResolved`, and only
the two reply footprints declare an origin member — so a redirect placed in that
shared resolver would make `lockSet_endpointReceive`, `lockSet_replyRecv`'s
pre-return group, `lockSet_cancelIpcBlocking`, `lockSet_cancelDonation` and
`lockSet_tcbSuspendOnCore` **false** of their own transitions.  HP10.7 therefore
redirects in `applyReplyDonation`, `applyReplyDonationOnCore` and
`replyRecvPopDonation` only; widening it is a cut that declares first.  That is
also the right scope on the merits — the registered defect is the reply path's, and
the cancellation reclaim's recipient comes off the victim's own frame head
(`cancelledCallerDonation?`), which is a different question.

(7) **Seven sharp bounds are DELETED, and one of them is a Tier 3 negative now.**
HP6.2 established that the owner merge — the returned donation's holder *is* the
thread the reply answers — is **false** on every state the arm reaches, retired the
resolved `…_size_le_seventeen` it licensed, and left five `_of_owner_eq_target`
bounds and two `_of_no_donation` corners with no consumer in the tree.  A sharp
figure resting on a refuted hypothesis is worse than no figure, so they are gone
with a tombstone naming what replaced them, and `_size_le_twentytwo_of_owner_eq_target`
must not come back.  The four live sharp bounds carry `_of_no_origin` in their names
because they are stated at the origin's absence; the three
`_of_no_belowHead` bounds beside them are the branches on which the redirect fires.

**What new code must respect since HP10.7 (`v0.35.51`).**  The reply path's
bottom-of-stack pop hands the reservation to the recorded **origin**.  Six things.

(1) **`replyDonationRecipient` is the one answer, and all three reply-path pops
read it.**  `applyReplyDonation`, `applyReplyDonationOnCore` and
`replyRecvPopDonation` take it; a second spelling of "which thread receives the
reservation" is the duplication this project spends its length retiring, and these
two readings *disagree* on exactly the states the phase exists for.  It is the
identity wherever HP10.6's resolver is silent
(`replyDonationRecipient_eq_of_no_origin`) and on every `some`-arm pop
(`_eq_of_outer_some`), so every pre-HP10.7 result is a case split whose `none`
branch is the old proof verbatim.

(2) **The scope is the reply path, and the declaration fixes it.**  All six
operational pops thread `returnDonatedSchedContextResolved` and only the two reply
footprints declare an origin member, so a redirect placed in that shared resolver
would make `lockSet_endpointReceive`, `lockSet_replyRecv`'s pre-return group,
`lockSet_cancelIpcBlocking`, `lockSet_cancelDonation` and
`lockSet_tcbSuspendOnCore` **false** of their own transitions.  Widening it is a
cut that declares first.

(3) **The guard is a CONJUNCTION, and the second half is soundness rather than
depth.**  `donationRecipientAcceptable` asks that the recipient hold no binding of
its own; `donationOriginRebindable` asks that no *other* thread's binding name it
as owner.  `donationOwnerValid` requires that owner to be `.unbound`, so a thread
can pass the first while a live binding is counting on it — and `.bound scId`
there falsifies that binding's clause.  Reachable with ordinary syscalls: a client
answered out of order is woken `.ready` and `.unbound`, and may bind a second
reservation and Call with it while the first is still parked on a server whose
stack records it as the origin.  **Since `v0.35.157` the second half is the
bind's own admissibility** — the origin's reply frame is on no live stack
(`replyFrameOnLiveStack`) — and `donationOriginRebindable_no_owner` derives "named
by no live binding" from it under `donatedContextIsOwnerFrameHead`; until then it
read the origin's `ipcState`, a proxy that refused the re-called client and
transferred its reservation (PR #897's review, `v0.35.141`).  An origin the guard
declines **falls back** to the reachability recipient rather than refusing the
pop, which is the difference between a recovery and a regression and the reason
HP10.6 applied the guard to the candidate.

(4) **The bundle splits the recipient from the binding's recorded owner.**  One
thread used to play three roles — the operation's argument, the binding's owner,
and the relaxation point of `ipcInvariantFullExceptDonationOwner` — and exactly
**one** conjunct argument cared: `donationOwnerUnique`, `donationBudgetTransfer`,
`passiveServerIdle`, the scheduler frame and the read agreement all take the
recipient purely as the operation's argument.  `donationOwnerValid` is the
exception, and `returnDonatedSchedContext_establishes_{donationOwnerValid,
ipcInvariantFull}_of_except_redirected` are where `hNoOwner` lands.  A new
argument reaches for the conflated form when the recipient *is* the binding's
owner and for the redirected one otherwise; the conflated form is the instance,
not a weaker statement.

(5) **The replenishment migration's DESTINATION follows the redirect.**
`ownerHome` was `determineTargetCore st1 target` — the answered caller's home —
and a redirect that moves the reservation without moving the queue leaves
`replenishQueueAffinityConsistentOnCore` false from the instant it commits, which
is the standing constraint every SchedContext hand-off in this tree is held to.
`replyDonationRecipientHome` mirrors HP4.3's source resolver clause for clause and
the three readers that must agree all take it: the live dispatch, the affinity
proof, and the SM8.B per-core write set that mirrors the dispatch's control flow.
`hOwnerHome` is quantified over the trigger's answer now — HP4.3 recorded that the
two home hypotheses swapped conditionality, and the redirect makes **both**
conditional.  A Tier 3 negative refuses the answered caller's home in that
position.

(6) **The witness is decisive, not merely green.**  `tests/SmpIpcSuite.lean` §3.25
resolves the redirect to a *different thread* on a *different core*, and each
guard's negative is paired with a **control** asserting the other guard admits
that state — so a decline is attributable to the guard it is about.  Reverting the
redirect does not reach the witness: it fails to elaborate, because
`replyDonationRecipient_eq_origin` and its siblings pin the definition
structurally.  A new scenario in that group **extends** the contiguous-run anchor
rather than adding a sibling.

**What new code must respect since HP10.8 (`v0.35.52`).**  The frozen mirror
redirects too, and running it beside the live arm found two defects.  Five things.

(1) **`frozenReplyDonationRecipient` is the mirror, and it had to land within one
cut of HP10.7.**  `frozenBranchOperationChecked .endpointReplyToBlockedCaller =
true` is a machine-checked claim that the two programs are run beside each other,
so a window in which the live arm redirects and the mirror does not makes that
claim an **over-claim** rather than a failing test — every existing scenario keeps
passing, because none of them recorded an origin that differs from the answered
caller.  That is HP4.7's situation verbatim, and this is why the plan's HP10.8 row
says *same cut*: HP10.7 landed alone at `v0.35.51`, and closing the window was the
first thing `v0.35.52` did.

(2) **The frozen return clears the origin on the bottom arm — it did not before,
and FO-044 is what found it.**  HP10.4 landed the field's clears on the live side
only; `FrozenOps` carries the **live** `SchedContext` record, so the field was
there and unswept.  A frozen state left with a stale origin is the thread-id-reuse
hazard the field's own docstring names, one surface over, and nothing could see it
until a frozen scenario recorded an origin at all.  **A field added to a shared
record is a sweep of both surfaces**, not of the one whose transition motivated
it.

(3) **The differential is what catches a mirror that agrees on the headline and
diverges underneath.**  FO-044's eleven earlier assertions all passed — both
surfaces bound the reservation to the origin, both left the answered caller
unbound — and `frozenRunAgrees` still failed, on the `donationOrigin` field no
per-object assertion mentioned.  A scenario that asserts only what it set out to
measure would have reported the flip as clean.

(4) **The answered caller's own frame HEADS the context at the state the resolver
reads, so the redirect DECLINES it and the recipient comes from the fallback.**
(Until `v0.35.157` the decline read its `.blockedOnReply` instead; the frame is
what the guard reads now, and the verdict there is the same.)  Same thread,
different route — and it is what makes FO-044's second half discriminating, since
a selector that fired unconditionally passes every outcome assertion and fails the
resolver one.  It also retires HP10.6's claim that this
member is live at depth 1: see the correction in that block, and the registered
asymmetry between the state the **footprint** resolves at and the state the
**transition** resolves at.

(5) **Both guards are mirrored, and mirroring one would be worse than mirroring
neither.**  `frozenDonationOriginRebindable` is `donationOriginRebindable`'s
counterpart because the frozen surface models the same bindings; a mirror carrying
the recipient guard alone would redirect on states the kernel refuses, which is
the direction that matters on a differential surface.  The resolution check is
mirrored too since `v0.35.61` (`frozenLookupTcb`), with FO-044's third half the
witness on both surfaces.

**What new code must respect since HP10.9 (`v0.35.53`).**  The depth-two payoff is
stated and measured, so the donation accounting holds at **every** reply-stack
depth.  Six things.

(1) **`donationAccountingPreserved_atCallDepthTwo` derives the reachability answer
and the rebindability, and hypothesises the recipient guard, and the split is not
stylistic.**  `replyStackOuterCaller? st' scId = .ok none` — the very answer that
names the wrong thread — is a **conclusion**, read off the removal through
`removeCallerReplyFrame_clears_prev_of_bottom_frame`, so no hypothesis hands the
payoff over.  `donationOriginRebindable st' origin` is a **conclusion too since
`v0.35.157`**: the removal took the owner's frame off the stack and cleared its
`replyObject` (`removeCallerReplyFrame_replyObject_none`), and a thread holding no
reply object is on no live stack (`donationOriginRebindable_of_no_reply`) — where
the retired `.blockedOnReply` proxy was false at the pre-state, true after the
wake, and false again the moment the owner re-Called.  `donationRecipientAcceptable`
stays a **hypothesis**, because nothing about the removal says the owner holds no
reservation of its own.  The origin's *existence* at that state is the other
hypothesis since `v0.35.61`, for the same reason: the removal's success says
nothing about the thread the field names (`consumeCallerReply` is total on an
absent caller), and the resolver now names only a thread it can resolve.  A cut
that "simplifies" the statement by hypothesising the resolver's answer, the
reachability answer or the rebindability has gutted it; Tier 3 negatives refuse
all three.

(2) **The sever-direction sibling is where the depth-two shape lives.**
`removeCallerReplyFrame_clears_prev_of_bottom_frame` is
`removeCallerReplyFrame_splices_reciprocally`'s counterpart: nothing sits below a
bottom frame, so `spliceFrameBelow?` answers `none`, the splice degenerates to the
sever, and the frame above is left `prev = none` — *the same value either policy
writes*, which is the whole reason HP6 could not reach this and HP10 had to.  Its
`above ≠ rid` is derived from bottom-ness (a frame that were its own frame above
would carry `prev = some rid`), not assumed; a Tier 3 negative refuses the
hypothesis.

(3) **The depth-three payoff is byte-identical, and that is the measurement.**
§3.22 and §3.23 are untouched and the golden trace is byte-identical, so this
phase is confined to the reachability gap rather than changing the chain — the
same criterion HP6.9 met in the other direction.  It is *structural* rather than
lucky: at depth ≥ 3 the pop sits at a `some` arm, where
`replyDonationRecipient_eq_of_outer_some` makes the redirect the identity by
theorem.

(4) **§3.20's accounting halves are PAYOFFs now, and they measure the live `.reply`
SPINE.**  They measured `returnDonatedSchedContextResolved` directly, which was an
accurate proxy for the pop while nothing redirected and is a proxy that *omits* the
redirect since HP10.7 — *a proxy is not the fact*.  `replyRemovalOutcome` drives
`endpointReplyCrossCoreDispatch`, so leg, pop, reversion and migration are all in
the measurement.  The retired `PAYOFF/COST` and `COST` labels are refused
tree-wide.

(5) **The decisive comparison is a differential WITHIN the suite, because no
mutation is available.**  Every mutation of the production code here — the origin
write, the resolver, the three pops, the dispatch's recipient — fails to
**elaborate** rather than failing the suite, which is the situation §3.23 recorded
for the splice's store shape.  So `replyRemovalOutcome` takes the chain as a
**parameter** and is applied twice: to a chain whose first push recorded an origin,
and to `pushStore`'s, which predates HP10.4 and records none.  One function, two
chains differing in exactly one field, opposite outcomes.  A new witness on this
surface should reach for that shape rather than for a mutation that will not
compile.

(6) **HP10.4's production write is measured, and it was not before.**  Every
fixture that carried an origin set the field by hand, so nothing asserted that
`donateSchedContext` records one — *a witness whose field is supplied by its
fixture asserts nothing about the production write that is supposed to supply it*.
`pushOwnerStore` is `pushStore` with the first push undone and `replyRemovalChain`
runs the live push **twice**, so §3.20 measures both directions of HP10.4: a
**first** push records the origin, an **onward** push leaves it alone, which is
what distinguishes an origin from a duplicate of `.donated scId owner`.  The same
construction asserts that the first push reproduces `pushStore`'s own shape, so
the hand-built fixture is known to be a state the kernel reaches.

One mechanical note, and it is this project's own silent-skip rule catching a gate
defect rather than a code one.  A Tier 3 anchor added in this cut lost the closing
quote of its `bash -lc '…'` argument, so it swallowed the following lines, ran a
search against the wrong file and **never decided** — `bash -n` passes, the gate
prints PASS, and only a mutation of its subject reveals the silence.  The mutation
harness reported it (as a negative that would not fire), and
`scripts/check_anchor_consistency.py` refuses it by name for exactly the stated
reason that *"the gate could not read it" and "the gate checked it" must never
produce the same PASS line*.  **Mutation-test a new negative anchor by breaking the
relation it forbids** — and read its verdict as a statement about the anchor, not
only about the tree.

**And the splice is not the whole remedy — depth 2 needs HP10** (registered
`v0.35.42`).  The register scoped this defect to reply-stack depth ≥ 3 and that
was its own error: at depth **2** the delegate answers the client out of order,
the removal takes the client's frame — the stack's *bottom* — off the stack, and
the later in-order pop finds the remaining frame at the bottom and binds the
reservation to the **intermediate** caller.  Both policies write `none` into the
frame above a bottom frame, so the splice **provably cannot** reach it: the
sentence that explains why §3.20 cannot measure the depth-≥ 3 defect is the
reason the depth-2 defect survives HP6 — and HP6.9's own acceptance criterion,
that §3.20's depth-two halves pass byte-identically, is the measurement that it
does.  §3.20 exercises the depth-2 *structural*
outcome and asserts nothing about where the reservation ends up, so this half was
in the tree's reach and in neither its witnesses nor its register.

The cause is not seL4-MCS and not the removal policy: the recipient is derived
from **stack reachability**, so removing a frame changes who the kernel believes
owns the context — and upstream's `reply_pop` donates to the answered frame's own
`replyTCB`, so it has the depth-2 loss too.  HP10's remedy is one `SchedContext`
field recording the reservation's **origin** and one arm reading it, with the
answered caller as the fallback, so it is a strengthening with no state on which
it is worse than today.  Three things new code must respect once it lands: the
origin is **history the kernel validates, not an invariant** (no
`donationChainWellFormed` clause can state it, because "or a thread whose frame
was removed" is unstateable from the store — the pop's
`donationRecipientAcceptable` guard is what makes reading it safe); **thread-id
reuse is the hazard**, closed by `lifecyclePreRetypeCleanup` clearing a stale
origin before anything reads the field; and **the footprint grows**, because
redirecting the recipient changes which TCB the pop writes —
`maxLockSetSize` 23 → 24.  It lands in WS-HP rather than WS-CB, whose plan has no
sub-task started and would defer a correctness fix indefinitely; WS-CB inherits
the field.

Three things a reader should take from the plan rather than infer.  (1) **The
payoff is larger than the accounting**: under the head-driven trigger the three
*stated* pre-state coherence hypotheses the reply path used to carry
(`replyStackHeadIsAnsweredReply`, `replyDonationOwnerIsAnsweredCaller`,
`answeredHeadContextIsServerDonation`) became derivable and are **deleted** at HP7
(`v0.35.46`) — no invariant in this tree entailed them, HP4 had already retired the
third from the chain composite for the strictly weaker `replyFrameHeadIsBound`, and
HP6.2 left none of the three with a consumer.
(2) **The cost is stated**: `maxLockSetSize` 22 → 23 and the RPi5 per-lock cost
15 → 14 µs, because the splice writes the frame below and no footprint named it
(HP3.5).  The splice's *third* store, added at HP6.3, costs nothing further — the
cut frame's lock was already declared on both paths.  (3) **HP5 was not optional**, and its reason was
derived rather than assumed: after the splice a frame becomes the head whose
recorded reply target is gone, so a *cancellation* there would leave a `.donated`
binding naming a `.ready` owner.  It landed at `v0.35.39`; the paragraphs above say
what it changed.

Registered in
[`docs/REGISTERED_DEBT.md`](../../REGISTERED_DEBT.md) table C, closed there at
`v0.35.54`, **re-opened at `v0.35.141` on the depth-2 half** — see the paragraph
above for what PR #897's review measured — and **closed again at `v0.35.157`**,
when the redirect's guard became the bind's own admissibility rather than a proxy
for it.  So v1.0.0 may claim both halves: a middle removal leaves the reservation
owed outward (HP6's chain-preserving removal), and a completed call chain returns
a client's reservation at every reply-stack depth (the recorded origin, under a
guard that is the fact).  What it must still not claim is *parity* with seL4-MCS
on reply-stack removal at depth ≥ 3: upstream severs and this kernel splices, so
the honest claim there is an improvement on upstream rather than a match for it.

**The post-landing audit (`v0.35.61`) — what reading the code against its prose
found.**  The whole of WS-HP, RR8.1–RR8.4 and the `v0.35.59`/`v0.35.60` cuts were
re-read with every docstring treated as a claim to check rather than a description
to trust.  The code held: each resolver, guard, pop, splice store and frozen
mirror does what its section above says; the deleted `detach*` theorems all have
splice twins; objects are never erased, so a recorded origin always resolves; and
the recipient guard is inert on reachable states because `schedContextBind`
refuses a thread whose frame is on a live stack.  What did not hold was prose
**about the future, or about the sever** — ten docstrings and comments across six
Lean files, and the plan's HP4 narrative.  `replyFrameHeadIsBound`'s docstring and
the chain composite's both said *"HP7 is where it becomes a clause of the chain
invariant"*, and HP7 did no such thing — no plan row ever scheduled it; the rest
still read *"once HP4 lands"*, *"once HP6 makes the removal a splice"*, *"the
sever today, the splice after HP6.3"*, *"the one HP10 will have to keep true"*,
or described the removal as clearing the frame above's `prev`, each about a phase
that had landed.  The retired-code section's rule — *sweep the forward-looking
prose when the phase it names closes* — is the one that catches these, and
WS-HP's own closure had not run it over WS-HP's own docstrings.  Three findings
beyond prose.  (1) **A contract the code does not decide is one a later cut can
break silently**: `donationOriginRecipient?` promised that a stale origin *falls
back rather than refusing*, and decided it only for an origin failing a guard — a
recorded origin naming no thread passed both guards and reached the pop's own
lookup as `.objectNotFound`.  Unreachable, and closed on both surfaces (item (2)
under HP10.6 above).  (2) **One thread, two spellings**: `replyRecvPopDonation`
passed `holderV.val` / `targetV.val` to the return and `holder` / `target` to the
migration, and four proofs carried `toValid?_some_val_eq` rewrites to reconcile
what one `let` now states once.  (3) **A hand-kept figure had crept back in**:
HP8's paragraph restated the reply-stack census's totals a few paragraphs after
the WS-RM section says why that shape drifts — accurate that day, deleted anyway.
And the two stated coherence facts HP7 left standing — `replyFrameHeadIsBound`
and `replyFrameHeadHolderDonation`, true on every reachable state by arguments
their docstrings carry and entailed by no invariant — had no register row; they
have one (`docs/REGISTERED_DEBT.md`, table C).

**The second pass (`v0.35.62`) — a sweep the closure claimed and had not run.**
HP6.1 recorded that the word *detach* was accurate at that version and that HP6.3's
cut would sweep it; the operation had been a splice for seventeen cuts and the
sweep had reached one docstring.  Measured rather than estimated: some 120 sites in
35 files still called the splice *the detach*, and nine of them described the
**sever** as its behaviour — "`spliceReplyFrameOut` sets its `prev := none`",
"clears the `prev` of the frame above", "the `severAtCut` policy is unchanged and
is now carried out by the detach", "the frame above becomes the bottom of the stack
it heads" — in `LockSetTransitions.lean`, `Endpoint.lean`, `Cancellation.lean`,
`CancellationReplyShape.lean`, `SchedContext/Operations.lean`, `Reply.lean`,
`Defs.lean`, the spec's §8.12.7 and GitBook 12.  Each now says what the splice
writes, and where the sever is still the truth — the *degenerate* arm, taken at a
bottom frame or when the frame below does not reciprocate — says that instead.
Three stale **figures** rode along, none of them in a theorem: two docstrings still
called the splicing `.replyRecv` branch *sixteen, two below* the popping one, on
theorems whose conclusions read seventeen (`lockSet_replyRecv_size_le_seventeen_of_no_sender_of_no_head_of_no_origin`,
`lockSet_endpointReplyRecvOnCore_size_le_eighteen`); `maxLockSetSize`'s own
docstring narrated the ceiling to twenty-three and stopped, one raise short of the
constant beneath it, and cited `lockSet_endpointReplyRecvOnCore_size_le_nineteen`,
renamed at HP3.2; and `tests/DeadlockFreedomSuite.lean` labelled a `.replyRecv`
shape *declares 22* while asserting `maxLockSetSize - 1`, which had been 23 since
HP10.6, with its negative pinned at the literal 21 rather than at the ceiling's
minus two — both derive from the constant now, and the Tier 3 anchor on the label
moved with it.  Two dead citations: `Endpoint.lean` named `replyDonationOwnerHome`
(retired at HP4.3) as live discipline, and `EndpointReplyDispatchInvariant.lean`'s
HP6.2 block said `answeredFrameHeadContext?_implies_serverDonation` was *not*
retired, forty lines below the HP7 comment recording that it was.  And
`SchedContext.donationOrigin`'s docstring pointed at §3.20's `PAYOFF/COST` rows,
which HP10.9 renamed.  One inert attribute went with the prose:
`cancelledCallerDonation?_independent_of_victim` was `@[simp]`, and a rewrite rule
whose right-hand side has a free variable can never fire.  What the pass
**re-verified**: every one of the 122 declarations this PR deleted has a splice or
head-driven twin or a documented retirement, every one of the 31 theorems whose
hypotheses changed is recorded in the section above, no added line carries a
`sorry`, `axiom`, `native_decide` or `partial`, and every declaration-shaped name
the CHANGELOG cites either resolves or is named as retired.

Plan: [`docs/planning/DONATION_POP_TRIGGER_PLAN.md`](DONATION_POP_TRIGGER_PLAN.md).

### WS-LC Lock datatype completion — COMPLETE (v0.34.51 → v0.34.55; closure audit v0.34.56)

The two SM2.C **datatype** residuals RR6 re-registered rather than absorbed —
`RwLockOp` had no withdrawal and `RwLockExecution` no notion of time.  Scoped
ahead of WS-RR RR7 because the fine-lock migration tracks widen `withLockSet`
footprints onto more syscall arms, and the withdrawal is what makes those
footprints unwindable.

| Phase | Status | Version | Scope (one line — detail in the canonical sources) |
|-------|--------|---------|----------------------------------------------------|
| LC1 | LANDED | v0.34.51 | The abstract withdrawal: `RwLockOp.cancel`, INV-R preservation, the liveness restatement, the CAS-retry bridge |
| LC2 | LANDED | v0.34.52 | The ticket-FIFO refinement of the withdrawal: the withdrawal word, skip-aware promotion, the capstones over live entries |
| LC3 | LANDED | v0.34.53 | The deployed withdrawal: `QueuedRwLock::cancel`, loom, miri, Tier-5, and the foreign-function surface |
| LC4 | LANDED | v0.34.54 | The two-phase-locking consumers: `cancelAll`, the revalidated refusal unwind, the `withLockSet` unwind |
| LC5 | LANDED | v0.34.55 | SM2.C-T: the timed execution and the cycle-denominated bounds; LC5.10 retired both debt rows |

**Plan**: [`docs/planning/SMP_LOCK_DATATYPE_COMPLETION_PLAN.md`](SMP_LOCK_DATATYPE_COMPLETION_PLAN.md)
(51 sub-tasks across LC1..LC5).
