# WS-CB — Hierarchical Constant Bandwidth Servers (HCBS)

> **Workstream**: WS-CB (constant-bandwidth server hierarchy)
> **Status**: **PLANNED** — registered at v0.34.49; no sub-task started.  Opens
> after WS-RR closes, or in parallel with RR6–RR8 under the file partition in
> §2.3.  Not a v1.0.0 blocker: SM10 may cut v1.0.0 with this workstream open,
> provided the release notes state that scheduling contexts are flat, the root
> scheduler is fixed-priority, and the CBS refill defect in §1.1 is open.
> **Relationship to WS-SM**: extends the SM5.A selector, the SM5.D/SM5.H
> per-core tick and CBS surface, the SM5.F priority-inheritance surface and the
> SM8/SM9 information-flow surface; orthogonal to SM10's image work.  It
> touches no Rust HAL seam and adds no Lean upcall (§3.2).
> **Audited cut**: `v0.34.48`
> **Sub-task count**: 73 across 9 phases (CB0..CB8), each phase numbered in
> the order it is to be implemented
> **Root policy**: **EDF-first** (maintainer's decision at planning time, §3.1)
> — the root scheduler orders by CBS deadline, with priority as the tie-break
> and as the order of the legacy deadline-less class.  This is a change to the
> flat model too, and CB1 lands it before any hierarchy exists.
> **Findings recorded**: two authority gaps in `schedContextConfigure` (§3.3)
> and a refill-accounting defect in the live CBS engine (§1.1, §4.2), all
> closed by CB0.3 and CB1 before any server exists.
> **Prefix**: `CB`.  The identifier-naming gate derives its family grammar
> from the workstream registry, so the prefix had to be one whose lowercase
> form followed by a digit matches no identifier in the tree: `cb<digit>`
> matches nothing, where `hc<digit>` (the obvious abbreviation) matches two
> hypotheses in the Robin Hood preservation proofs.
> **Document layout**: §1–§3 say what and why; **§4 is the implementation
> specification** every sub-task row points into; §7 is the schedule; §14
> records what the refinement pass and the review rounds changed.

## 1. Phase goal

A **Constant Bandwidth Server** (CBS) is a reservation `(Q, P)`: a budget `Q`
available in every window of length `P`, with the window's end as the
server's deadline, so that the server can never consume more than `Q/P` of the
processor whatever its clients do.  Under **EDF** with the servers'
utilisations summing to at most one, every server also *receives* its `Q` in
every window — that is the CBS guarantee, and it is why the classical CBS root
is EDF rather than fixed priority.  seLe4n already implements the server half
per thread: a `SchedContext` is a CBS bound to at most one thread, charged one
tick at a time by the per-core timer tick, replenished through the per-core
replenish queue, and admitted against a 100 % utilisation ceiling.  Its root
scheduler, however, is fixed-priority with the CBS deadline as a tie-break
inside a band, so the guarantee half is a per-band response-time argument
rather than the EDF theorem — and, as §1.1 records, its refill accounting
returns at most one tick per exhaustion, so no bound thread receives its `Q`
after its first window today.

**Hierarchical** CBS (HCBS) lets a reservation contain other reservations.  A
*server* SchedContext holds no thread; it holds members — leaf SchedContexts
bound to threads, or further servers — and its budget is charged whenever any
thread in its subtree runs.  With an EDF-first root, the roots of the trees are
ordered by their CBS deadlines on each core; inside a server the members are
ordered by the same rule on their own deadlines; and bandwidth composes: a
server's members are admitted against the server's `Q/P`, and the roots on
each core against that core's capacity — which is exactly EDF's schedulability
condition for the roots.  The result is the temporal isolation Linux's
`SCHED_DEADLINE`-based HCBS gives control groups, expressed in seL4-MCS terms:
a component gets a fraction of a core, its threads share that fraction, and no
thread outside the component can be delayed by anything the component does
beyond the fraction it was admitted for.  What the group's members receive
*inside* that fraction is bandwidth and isolation (§4.11 T11, T12); a
per-member window guarantee needs more than a utilisation sum and is a
registered follow-up (D19, Q10).

This workstream delivers, in order:

1. the EDF-first root on the flat model — kernel-owned deadlines and windows,
   the refill accounting the guarantee needs, the CBS wake-up rule, deadline
   inheritance in place of priority inheritance for deadline-bearing threads —
   as three switch cuts, each landing with the proofs that cover it and its
   own fixture refresh (CB1);
2. the model — server fields on `SchedContext`, bounded hierarchy queries,
   and the store-level hierarchy invariant bundle (CB2);
3. hierarchical selection and eligibility, provably identical to the CB1
   selector on every state with no servers (CB3);
4. hierarchical budget accounting on the per-core tick, with the CBS
   isolation theorems lifted from a single SchedContext to a subtree (CB4);
5. the hierarchy transitions — configure a server, bind and unbind a member —
   plus the hierarchy-aware forms of bind, configure, unbind, affinity,
   donation and retype, each with its preservation surface, and the per-core
   admission every reservation move re-checks (CB5);
6. three syscalls wiring those transitions live, on both sides of the ABI,
   with the label chokepoints and the `ipcInvariantFull` dispatch payoff
   extended over them (CB6);
7. the information-flow and liveness re-establishment: members of a server
   share a label, so a server's budget is not a cross-label channel, and the
   CBS guarantee — a runnable root receives its budget within its window —
   is stated with explicit hypotheses and proved as far as the plan commits
   to (CB7);
8. closure — specification verification, evidence index, theorem inventory,
   registered follow-ups, the status flip (CB8).

### 1.1 What is actually there, verified against `v0.34.48`

* `SchedContext` (`SeLe4n/Kernel/SchedContext/Types.lean`) carries `scId`,
  `budget`, `period`, `priority`, `deadline`, `domain`, `budgetRemaining`,
  `periodStart` (written nowhere), `replenishments` (bounded by
  `maxReplenishments = 8`), `boundThread : Option ThreadId`, `isActive` and
  the SM3.A.6 `lock`.  Nothing on it can express a parent or a member.
* The binding is 1:1: `schedContextBind` refuses when `sc.boundThread` is
  set, refuses a thread whose `domain` differs from the SchedContext's
  (`.invalidArgument`, the AE3-A/U-11 check), and `schedContextNotDualBound`
  (`SeLe4n/Kernel/CrossSubsystem.lean`) forbids two threads naming one
  SchedContext.  `TCB.schedContextBinding` is
  `.unbound | .bound scId | .donated scId owner`.
* Selection is `chooseBestInBucketEffective` behind
  `chooseThreadEffectiveOnCore` (`SeLe4n/Kernel/Scheduler/Operations/Selection.lean`):
  bucket-first over the core's `RunQueue` (priority buckets of `ThreadId`),
  `isBetterCandidate` on `resolveEffectivePrioDeadline` — **higher priority
  first**, then earlier CBS deadline, then the incumbent — filtered by
  `hasSufficientBudget`, which reads the bound SchedContext's
  `budgetRemaining` alone.  A deadline of `0` means "none".
* Deadlines are set in two places: `schedContextConfigure` stores the
  **caller-supplied** `deadline` argument verbatim (`validateSchedContextParams`
  ignores it), and `cbsUpdateDeadline` sets `deadline := now + period` when a
  replenishment lands with positive budget (`refillSchedContext`).  The
  legacy `TCB.deadline` is read for unbound threads and is set only by three
  test suites.  The per-core invariant `edfCurrentHasEarliestDeadlineOnCore`
  states the tie-break: among queued threads of the current's domain,
  effective priority **and** base priority, the current's deadline is earliest.
* **Refill accounting.**  A replenishment is scheduled at exactly three sites:
  the two tick exhaustion arms (`timerTickBudget`, `timerTickBudgetOnCore`)
  and `handleYieldWithBudget`.  The exhaustion arms run when
  `budgetRemaining ≤ 1` and schedule `consumedAmount := budgetRemaining` — at
  most **one tick** — eligible one period later; the docstring beside them
  says "the full remaining budget (not 1 tick), because the entire period's
  consumed budget is recorded", which the branch condition makes false.  The
  only full-budget refill is the entry `schedContextConfigure` installs for
  one period after configuration.  Consequently a bound thread that consumes
  its budget by ticks receives about one tick per period after its first
  window, and budget consumed without exhaustion (a thread that blocks with
  budget left) is never replenished at all.  `cbs_bandwidth_bounded` is an
  upper bound, so no theorem states the lower bound this violates, and the
  WCRT theorems take per-band budgets as hypotheses.  CB1.6 replaces the
  scheme (§4.2); this is reported to the maintainer as a functional defect.
* `schedContextUnbind` purges the SchedContext's entry from the replenish
  queue (`purgeReplenishmentOnCore`) but leaves `sc.replenishments` and
  `budgetRemaining` as they were, so the two representations of a pending
  refill can disagree after an unbind; nothing states that they agree.
* Priority inheritance (`SeLe4n/Kernel/Scheduler/PriorityInheritance/`) is a
  priority boost: `updatePipBoost` writes `pipBoost := computeMaxWaiterPriority`
  over `waitersOf` (the threads `.blockedOnReply` on this one) and re-buckets;
  `revertPriorityInheritance` **recomputes** through `updatePipBoost` from the
  waiters that remain rather than clearing the boost; `pipBoostWithWake`
  pokes a remote core only when the holder's *effective priority* changed
  (its materiality guard reads `(resolveEffectivePrioDeadline ·).1`);
  `pip_bounded_inversion` bounds the inversion in priority-band terms.
  Passive servers inherit a client's whole SchedContext through donation
  instead, and with it the client's deadline.
* The per-core tick `timerTickOnCore` (`SeLe4n/Kernel/Scheduler/Operations/Core.lean`)
  drains the core's replenish queue (`processReplenishmentsDueOnCore`, waking
  a bound thread whose budget went from zero to positive), then charges the
  running thread's SchedContext one tick (`timerTickBudgetOnCore`): on
  exhaustion it schedules the replenishment above, re-enqueues the thread,
  times out the threads the SchedContext bounds (`timeoutBlockedThreads`, via
  `scThreadIndex`) and preempts.  An exhausted thread stays queued and is
  skipped by eligibility; its deadline moves only when the refill lands.
* Threads leave the runnable set through `removeRunnableOnCore`
  (`SeLe4n/Kernel/IPC/CrossCore/EndpointCall.lean`) — the per-core primitive
  the cross-core send, reply, signal, fault and cancellation paths call
  directly — its `bootCoreId`-pinned wrapper `removeRunnable` and the
  all-core fold `removeRunnableFromAllCores`
  (`SeLe4n/Kernel/IPC/Operations/Endpoint.lean`), `suspendThreadOnCore`
  (`SeLe4n/Kernel/Lifecycle/Suspend.lean`), the cancellation and fault
  suspends, and retype cleanup; they enter it through `enqueueRunnableOnCore`
  (`wakeThread`, the replenish and timeout wakes, resume, the notification and
  IPC unblocks).  `removeRunnable` is still pinned to `bootCoreId`.
* Replenishments are per core and pinned to the bound thread's home core:
  `replenishQueueAffinityConsistentOnCore`
  (`SeLe4n/Kernel/SchedContext/ReplenishAffinity.lean`) and
  `replenishQueueEntriesBoundOnCore` (`BindingAffinity.lean`) both read
  `sc.boundThread`; `schedContextReplenishHome` resolves the home the same
  way.  `perCoreCbsInvariant` (`Operations/PerCoreCbs.lean`) bundles validity,
  pipeline order and affinity.
* `SchedContext.isActive` is written by eleven sites in the kernel with two
  meanings — the yield helper sets it from `budgetRemaining > 0`, the suspend
  and cancellation paths clear it when a thread stops — and read by one
  invariant (`replenishQueueValidOnCore`'s entry check) and the `BEq`
  instance.  A field two writers disagree about is the class §14 names; CB0.2
  settles what it means, CB1.6 pins it to the derived fact or retires it
  (D22).
* Admission is one flat sum: `checkAdmission` folds `utilizationPerMille`
  (ceiling-rounded) over **every** SchedContext in the object store against
  `1000`, so a four-core machine admits 100 % in total, not per core — which
  also means no single core can be over-subscribed today, by any path.
* Priority propagation is AK2-B option B: bind and configure copy
  `sc.priority` into `tcb.priority`, `boundThreadPriorityConsistent` holds
  them equal, and `effectiveParamsMatchRunQueueOnCore` reads the bucket off
  the SchedContext.
* The selection WCRT theorems (`wcrt_chooseThreadOnCore_eq` and siblings in
  `Operations/PerCoreWcrt.lean`) bound **lock wait** by footprint size; the
  scan cost of selection is not part of them.
* Lock sets for the three SchedContext syscalls exist as
  `lockSet_schedContextConfigure` / `_Bind` / `_Unbind`
  (`SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean`), over the
  caller's TCB (read), the CNode root (read), the SchedContext (write) and
  the bound TCB (write).  `lockSet_tcbSuspend` is the widest footprint in the
  tree: caller TCB, CNode root, target TCB, then optionally the blocked
  endpoint, the blocked notification, the binding SchedContext, the donation
  owner and the consumed reply — **eight** entries at its widest, which is
  `maxLockSetSize` exactly.
* `schedContextYieldTo` is the one hook already labelled "for hierarchical
  scheduling": kernel-internal, capability-free, a budget transfer between
  two SchedContexts that writes `budgetRemaining` on both — zeroing the
  source without scheduling a refill, raising the target without touching its
  window or its pending refill.  Its only callers are four probes in the main
  trace harness.  It is **not** what this workstream builds on, and it cannot
  coexist with the engine rules of §4.2 (a target with a pending refill would
  hold budget and an entry at once): CB1.6 retires it (Q7).
* The timer seam is a fixed 1000 Hz periodic tick whose only payload is the
  core id (`per_core_timer_tick_isr`, `lean_per_core_timer_tick`).  There is
  no one-shot deadline programming anywhere in the tree.
* `schedContextConfigure` is `.capabilityOnly` under the SchedContext write
  right and applies the requested `priority` and `domain` to the bound TCB
  with **no** caller-MCP check and no domain authority — where
  `setPriorityOp` gates the same write through `validatePriorityAuthority`.
  Recorded as a pre-existing finding in §3.3; CB0.3 closes it.  The same
  syscall's caller-supplied `deadline` is a tie-break today and would be the
  **primary** scheduling key under EDF-first; CB1.6 retires it.

### 1.2 The consequence, stated precisely

Every reservation is a leaf.  A component with three threads cannot be given
"20 % of core 1" and left to divide it: each thread needs its own admitted
`(Q, P)`, the three sums are what the component costs whether or not the
threads are all busy, and a thread that blocks leaves its share idle rather
than lending it to a sibling.  There is no object whose exhaustion suspends a
group, no admission relation between a group and its members, and no way to
state — let alone prove — that a component's total consumption is bounded by
one reservation.  `cbs_bandwidth_bounded` bounds one SchedContext; nothing
bounds a set of them jointly.  Because the root is fixed-priority, the CBS
*guarantee* — that an admitted server receives its budget every window — is
not a theorem the model can state; and because the refill returns one tick
per exhaustion, it is not true of the live model either.

### 1.3 What this workstream does *not* change

* The tick rate, the HAL, the FFI seam set, `SYSCALL_ABI_VERSION`, or any
  existing syscall's encoding.  New ids are appended (§3.2).
* The 1:1 thread ↔ leaf binding.  A server is a SchedContext with members and
  no thread; a leaf is a SchedContext with at most one thread and no members.
* The run queue's representation: priority buckets of `ThreadId` stay as the
  membership and FIFO structure; selection stops reading them as an order.
* The order of the legacy class.  Unbound, deadline-less threads — the idle
  threads among them — stay fixed-priority among themselves, below every
  deadline-bearing thread.
* Timeout semantics: an IPC-blocked thread times out when its **leaf**
  SchedContext exhausts, exactly as today (§4.5).

### 1.4 What CB1 changes, and its blast radius

The CBS engine's window and refill rules become the classical ones (§4.2),
the root order becomes EDF-first (§3.1), and priority inheritance gains a
deadline form (§4.7).  Each of the three is a live change to the flat model
and each lands as **one switch cut** that carries the proofs covering it —
the preservation suite, the frozen twins, the observer lift — because the
theorems unfold the very functions the switch replaces, so neither half
compiles alone (the rule in `CLAUDE.md`'s planning section).  The inert
definitions each switch needs are landed first (CB1.1–CB1.5), so the switch
rows are as small as the rule allows.  On every state whose runnable threads
all lack deadlines the selector is unchanged, and the order switch proves it
(`chooseThreadEffectiveOnCore_eq_flat_of_no_deadlines`).  On a state with a
deadline-bearing runnable thread the order changes by design, every
replenishment schedule changes by design, and a boosted holder's position
changes by design, so the fixtures built from bound threads — fourteen suites
and the main trace harness at the audited cut — are refreshed **three times**,
once per switch (CB1.6, CB1.7, CB1.8), each fixture with a rationale naming the
thread whose refill or position moved; after CB1 every generalising cut is
byte-identical again.  The other intended fixture moves are CB0.3's (the
configure authority gate) and CB5.2's (per-core admission and the reservation
moves it re-checks).

## 2. Scope and sequencing

### 2.1 In scope

* The EDF-first root on the flat model: kernel-owned implicit deadlines and
  windows, window-end refills of the full budget, the CBS wake-up rule,
  reconfiguration that never mints budget, deadline inheritance for bound
  blockers, the selector, its invariants and its three fixture refreshes
  (CB1).
* Server SchedContexts with bounded nesting; member leaves and member servers.
* Hierarchical ordering (§4.3), hierarchical charging, activation and
  replenishment (§4.5), hierarchical and per-core admission with every
  reservation move re-admitted (§4.6), core-homed servers (§4.8).
* Three syscalls: `schedContextConfigureServer`, `schedContextBindServer`,
  `schedContextUnbindServer`; hierarchy-aware forms of the existing
  operations that read or write a SchedContext's role (§4.8).
* The preservation surface for every touched invariant bundle, the
  `ipcInvariantFull` dispatch payoff over the new arms, per-core
  non-interference under the label-uniformity rule with its three
  chokepoints, and the CBS guarantee for roots with its hypotheses stated.
* Tier-2 suites with golden fixtures, Tier-3 anchors, ABI mirrors and
  conformance tests, specification and evidence-index rows — landed in the
  cut that makes each behaviour reachable, never deferred to closure.

### 2.2 Out of scope (registered follow-ups, §12)

Constrained deadlines (`D < P`); a per-core deadline-ordered index for
selection; server migration between cores; members homed on several cores
(Linux HCBS's per-CPU server replicas); bandwidth inheritance (a member's
inherited deadline lifting its *server*, and the dispatch effect of
inheritance across different parents); a per-member window guarantee (a
supply-bound admission test, or server-aligned member windows — D19);
admission with blocking terms so that T14 holds while inheritance is active;
boot-time server trees; a bucketed member queue; sub-tick enforcement through
a one-shot timer.

### 2.3 Ordering constraints and parallelism

* **Phase order is execution order.**  CB1 changes the engine, the root
  policy and inheritance on the flat model and is the only phase whose
  behavioural change is intended to reach existing fixtures; each of its
  three switch cuts lands whole, before any server field exists, so the
  hierarchy is built on the engine it will actually run under.  CB2 has no
  behavioural effect; CB3 and CB4 change live paths but only on states that
  CB5/CB6 cannot yet produce, and each carries its no-servers equivalence
  theorem in the same row; CB5 lands every transition with its proofs before
  CB6 makes any of them reachable, and lands the per-core admission together
  with every reservation move that could defeat it (CB5.2).
* **Overlap with WS-RR.**  CB1 edits the selector, the tick, the CBS engine
  and the priority-inheritance modules, so it must not overlap an RR7 cut that
  touches `SeLe4n/Kernel/Scheduler/**` or `SeLe4n/Kernel/SchedContext/**`;
  CB2–CB4 own those trees; CB5 onward edits `API.lean`, the donation
  primitives and the flow-classification tables and must not overlap a WS-RR
  cut that does.  RR6 (lock primitives) never collides.
* **Within a phase the rows are sequential** unless a row says otherwise.
  A row consumes only lower-numbered rows; the plan gate enforces this.
* **SM10 independence.**  Nothing here needs the image; nothing in SM10 needs
  this.  If SM10.1 lands first, CB6's fixtures are re-cut against the live
  seams and nothing else moves.

## 3. Architectural choices

| # | Decision | Alternative rejected | Why |
|---|----------|----------------------|-----|
| D1 | A server **is** a `SchedContext` with hierarchy fields (`parentServer`, `serverMembers`, `serverCore`, `activeDescendants`); a leaf is one without members | A new `KernelObject` kind | Reuses the capability target, retype tag `6`, lock kind `.schedContext` (level 7), admission arithmetic, replenish queue and every accessor; a new kind touches every exhaustive match in the tree |
| D2 | The root run queue stays a queue of **threads**, its priority buckets kept as the membership and FIFO structure; selection is a scan of the core's runnable list in the EDF-first order, and the hierarchy is an *ordering and accounting* structure read through the thread's SchedContext chain | A queue of scheduling entities, or buckets re-keyed by deadline | `RunQueue` is `ThreadId`-specialised with a thousand lines of proof and deadlines move on every refill; `currentOnCore` stays a thread; a deadline-ordered index is a registered optimisation proven equal to the scan, not a prerequisite |
| D3 | **EDF-first at every level** (§3.1, §4.3): earlier kernel-assigned deadline first, a deadline-less entity after every deadline-bearing one, then higher priority; a tie in the EDF class is broken by ascending `scId` (every EDF-class entity is a SchedContext, so the break is total), a tie in the legacy class keeps the incumbent (FIFO) | Fixed priority with EDF as the tie-break (the pre-CB1 root); FP-only local scheduling; FIFO for leaf pairs and `scId` for the rest (the first cut — not transitive when a leaf and a server tie) | The maintainer's decision; it is the order under which the CBS guarantee is a theorem rather than a per-band argument, one order at every level means one set of strict-order lemmas, and a tie-break that mixes two mechanisms admits a cycle (leaf `1` over server `50` over leaf `100` over leaf `1`) that no `_trans` lemma can close |
| D4 | A running thread's tick charges its leaf **and every ancestor**; exhaustion at any level makes the subtree ineligible until that level's refill lands; a server is *activated* by the CBS rule when its count of eligible-active members — members with budget and work below them, one predicate at every level — goes from zero to one, so a descendant's refill re-activates it (§4.5); timeouts are decided by the leaf only | Charge the leaf and transfer budget upward lazily | Eager charging is what makes the subtree bound a theorem; lazy transfer needs a second accounting state |
| D5 | Servers are **core-homed**; every member's thread has that home core; member affinity changes, and donations of a member leaf to a thread homed elsewhere, are refused (§4.8) | Per-core server replicas | Keeps every hierarchical write inside one core's scheduler slots and the existing tick lock set; replicas are the registered extension |
| D6 | Admission is hierarchical: members ≤ server; roots **per core** ≤ 1000 ‰, replacing the flat global sum (§4.6) | Keep the global sum and add the member rule | Per-core `Σ U ≤ 1` is EDF's schedulability condition for implicit deadlines, so per-core root admission is both the natural base case of the hierarchy and the hypothesis of the CBS guarantee |
| D7 | Priority is a **tie-break** for deadline-bearing entities and the order of the legacy class; a server's priority may change at any time, a member thread's priority through `.tcbSetPriority` under the caller's MCP, and neither moves anything but ties | Server priority frozen while populated; `.tcbSetPriority` refused on members | Both refusals existed only to keep a root-priority bucket consistent, and under EDF-first the bucket no longer orders anything |
| D8 | Every thread that runs on a member leaf, and every member, carries the server's security label; enforced at the three chokepoints that can put a thread or a context under a server — `schedContextBindServer`, `schedContextBind` onto a member leaf, and the donation of a member leaf — all in the flow-checked tier (§4.13) | Permit mixed labels and bound the channel; check object labels only (the first cut) | A shared budget lets one member starve another outright; that is not a channel to bound but a flow to forbid — and the observers and modulators of the budget are the *threads*, so a rule over SchedContext labels alone is bypassed by binding a differently labelled thread to an admitted leaf |
| D9 | `maxServerDepth = 3` counts the **contexts on a scheduling path**, leaf included (root server → server → leaf); `maxServerMembers = 16`; every walk is fuel-bounded by the depth | Unbounded recursion on `parentServer`; a bound on the ancestor chain alone (the first cut, which admitted a fourth context on the path) | Totality with a decidable bound; the path lock footprint (`≤ 3` SchedContext locks + the tick's three) stays within `maxLockSetSize` |
| D10 | Enforcement stays tick-quantised; no new upcall, no HAL change, `SYSCALL_ABI_VERSION` unchanged (ids appended, one argument's accepted values narrowed) | A one-shot timer programmed to the next budget event | A new FFI seam drags in the readiness-gate derivation and a new Rust surface for a precision gain the model does not need yet |
| D11 | The boot state has no servers; a hierarchy is built at run time by the root task | Boot-time server trees in `PlatformConfig` | Keeps the boot theorems of WS-RR RR5 untouched; boot-time trees are a follow-up once a deployment asks for them |
| D12 | Transitions land in production modules from day one (unreachable until CB6 wires the arms); theorem-heavy modules are staged and promoted when a production consumer imports them (§4.14) | Stage everything until CB6 | A definition nobody calls changes no behaviour; staging it only defers the partition work |
| D13 | Deadlines are **kernel-owned and implicit** (`D = P`): `schedContextConfigure`'s `deadline` argument must be `0`, and the kernel assigns `deadline := periodStart + period` at configure, at every refill and at activation (§4.2) | Keep the caller-supplied absolute deadline; or constrained deadlines `D < P` | A caller-chosen deadline under EDF is unbounded priority escalation; constrained deadlines need a density-based admission test and are a follow-up |
| D14 | The CBS wake-up rule at activation is the **classical** one: `if deadline ≤ now ∨ budgetRemaining·period ≥ (deadline − now)·budget then budgetRemaining := budget, periodStart := now, deadline := now + period` (§4.2 rule (e)) | Reset the deadline and leave the budget alone (the first cut's rule) | The first cut kept the budget because refills were per consumed chunk and a refill at activation would have minted budget the queue was still owed; with D16's per-window refills there is nothing owed, and the classical rule is what the guarantee's proof uses |
| D15 | Priority inheritance becomes **deadline inheritance** for bound blockers (`inheritedDeadline := min` over blocked waiters' effective deadlines, applied to the blocker's own leaf key) while the priority boost stays for the legacy class; inheritance never lifts a member's *server*, and its dispatch effect is stated for blockers under the waiter's parent (§4.7) | Keep the priority boost alone; inherit into unbound blockers too (the first cut) | Under EDF-first a priority boost changes nothing but ties, so `pip_bounded_inversion` would hold vacuously for every bound thread; an unbound blocker has no admitted budget, so running it at an inherited deadline is EDF-class demand outside every admission sum (D20); lifting the server is bandwidth inheritance, a follow-up |
| D16 | Refills are **per window**: exhaustion schedules one refill of the full budget at the window's end, and a window always starts with the full budget (§4.2 rules (a)–(d)) | Per-consumed-chunk refills one period after consumption (the seL4-MCS sporadic-server shape the current code approximates) | Per-chunk refills need consumption-interval tracking and refill coalescing under the 8-entry bound — the part of seL4-MCS that was hardest to verify — and the current approximation returns one tick; per-window refills are one entry per SchedContext, the classical hard-CBS rule, and the shape the EDF guarantee's proof assumes |
| D17 | **Reconfiguration never mints budget**: rule (f) keeps `periodStart`, clamps `budgetRemaining` to the new budget, re-keys a pending refill, and then applies the activation rule (e), so only the CBS density condition can open a fresh window (§4.2) | Rule (a) on a live entity (the first cut); refusing reconfiguration of a non-quiescent context | Under rule (a) the holder of the write capability re-submits the same admitted `(Q, P)` and receives a fresh full budget on every call, so admission bounds nothing; refusing live reconfiguration makes a long-running component unconfigurable; the density rule is the classical safe re-activation and its bandwidth argument is T17 |
| D18 | **A reservation is charged to a core, and every move re-admits on the destination before it commits**: a root leaf is charged to its thread's home core; an affinity change of its thread runs the root check on the destination; a cross-core donation admits on the donee's core for the donation's duration, charged on both cores until the return; members never move (§4.6, §4.8) | Let `rootCountsOnCore` follow the thread and state the guarantee under a no-migration hypothesis | Per-core admission (D6) is meaningless if a reservation can be carried onto a full core by an affinity change or a Call; charging on both cores during a donation makes the return unconditional, which the reply path needs |
| D19 | The **window guarantee (T14) is stated for roots**; members are given isolation (T11, T12) and their server's bandwidth.  Member admission stays the utilisation sum, so a member receives its budget per window only relative to the server's supply | Server-aligned member windows (`P_member = P_server`, one window per tree) now; a supply-bound admission test (`dbf ≤ sbf` over the periodic-resource model) now | A utilisation sum admits a `(1, 2)` member under a `(5, 10)` server that receives its five ticks at the end of its window, so the member misses its deadline while every sum holds — the guarantee is false for members under this admission; both stronger designs are real work with their own theorems and are registered follow-ups the maintainer chooses between (Q10) |
| D20 | **Deadline inheritance reaches bound blockers only**: an unbound blocker keeps the priority boost and stays in the legacy class, so the inversion it causes is the deployment's to avoid (give the server a SchedContext, or make it passive so it runs on the donated one) | Inherit into unbound blockers (the first cut) | An unbound thread has no admitted budget and no window; running it at an inherited deadline is unbounded EDF-class demand that no admission sum sees, and it makes admitted roots miss (§4.7); the seL4-MCS answer is donation, which the tree already has |
| D22 | **A derived fact is not stored.**  The stored `deadline` field goes: under implicit deadlines `deadline = periodStart + period` always, so `SchedContext.deadline` becomes a definition over the two fields it was mirroring, `deadlineWindowConsistent` is definitional rather than an invariant, and the twelve writer sites the engine rewrites anyway have one field fewer to keep consistent (CB1.6).  `isActive`, written by eleven sites with two meanings and read by one invariant, is settled in CB0.2 and pinned or retired in CB1.6 | Keep the field and carry the invariant (the previous cut) | Two representations of one fact diverge — the refill list and the replenish queue already did, and `schedContextYieldTo` wrote the pair inconsistently; a definition cannot |
| D23 | **Bandwidth is released at the window's end, not at departure**: a root share that leaves a core — unbind, move, a donation's return, a shrink, a link under a server — keeps counting there until the deadline it was released with, recorded as a `residual` on the context; a context with a live residual is re-homed only on that core, never retyped, and departs again only when the new share coalesces with the live one (same core and deadline), for at most one period (§4.6) | Release the share when it leaves; freeze the whole root set as a hypothesis of T14 | Instantaneous admission is defeated by churn (§4.6's example starves a root that was admitted all along), and a guarantee hypothesised on nothing else changing is a guarantee about nothing; `SCHED_DEADLINE` releases at the zero-lag time for the same reason, and the deadline is its conservative simplification |
| D21 | `maxLockSetSize` moves from `8` to `10` when the activation paths gain the ancestors' SchedContext locks (CB4.7), with the constant-dependent WCRT terms re-derived | Leave the bound and take the ancestor locks outside the set; lower `maxServerDepth` to `2` | `lockSet_tcbSuspend` is already eight entries at its widest and a member leaf adds up to two ancestors; a lock taken outside the set is invisible to the deadlock-freedom and serializability theorems, and depth two forbids the root server → server → leaf shape D9 exists for |

### 3.1 The root policy, in one paragraph

Two classes.  An entity with a kernel-assigned deadline — every bound thread
through its SchedContext, every server — is in the *EDF class*; an unbound
thread is in the *legacy class* and has no deadline.  Every EDF-class entity
outranks every legacy-class thread.  Within the EDF class: earlier deadline
first; equal deadlines by higher priority; equal priorities by ascending
`scId`, which is total because every EDF-class entity is a SchedContext and two
distinct entities have distinct ids.  Within the legacy class: the pre-CB1
order, higher priority then FIFO — which keeps the idle thread last.  A
deadline is always the end of the entity's current window (§4.2), the kernel
assigns it, and the guarantee (§4.11, T14) is that an admitted root with budget
at activation, kept continuously active, is dispatched for that budget before
the window ends.

### 3.2 What stays fixed

No new `@[export]`, so `LEAN_READY_GATED_SEAMS` and the readiness derivation
are untouched; no `extern`, so the kernel-entry export gate's requirement set
is untouched.  `SYSCALL_ABI_VERSION` stays `3`: ids `0..34` keep their
encodings and register layout (the configure `deadline` slot keeps its
position; only its accepted value narrows to `0`), the conformance suite pins
that, and `SyscallId::COUNT` moves to `38` on both sides with the existing
mirror tests holding them equal.  One existing id changes *class* without
changing encoding: `.schedContextBind` becomes policy-gated (D8), so its
`enforcementBoundary` row moves from `.capabilityOnly` to `.policyGated`
(§4.9, §4.13).

### 3.3 Pre-existing findings this workstream closes first

`schedContextConfigure` writes `priority`, `domain` and a caller-supplied
absolute `deadline` under the SchedContext write right alone.  A thread
holding such a capability escalates its own scheduling priority past its
`maxControlledPriority` — the very bound `setPriorityOp` enforces — and moves
itself into any of the sixteen domains.  Budgets and admission bound the
damage (a runnable thread cannot exceed its `Q/P`) but not the inversion: a
low-MCP thread with a 5 % reservation preempts every thread below 255 for
that 5 %.  The deadline argument is a tie-break today; under EDF-first it
would be the primary key, so a caller-chosen deadline of `1` would outrank
every other thread on the core for as long as its budget lasts.  CB0.3 gates
the priority through `validatePriorityAuthority` against the **caller's** MCP
and refuses a domain change on a bound SchedContext (`.illegalAuthority`);
CB5.6 extends the domain refusal to any context with a parent or members, the
two shapes CB0.3 cannot see yet (`serverDomainConsistent` would be false the
instant either changed domain); CB1.6 retires the deadline argument.  The
priority and domain half was reported to the maintainer as a vulnerability
finding at planning time.

The refill defect of §1.1 is the third finding: the live tick returns at most
one tick per exhaustion, so a bound thread's throughput collapses after its
first window and budget consumed without exhaustion is never returned.  It is
not an authority gap but a liveness defect in the scheduler's core function,
and CB1.6 closes it as part of the CBS engine rework the EDF-first root needs
anyway.

## 4. Implementation specification

Everything a sub-task row in §7 points into.  Lean fragments are the intended
shape, not compiled text; names are binding, signatures may gain implicit
arguments the proofs need.  All arithmetic is on `Nat` ticks.

### 4.1 Types and fields

```lean
-- SeLe4n/Kernel/Scheduler/Operations/Selection.lean (CB1.1)
/-- A scheduling key, root-first in a path (§4.3). `deadline = 0` means none;
    an unbound thread's key carries the sentinel `scId`, and the order never
    reads the `scId` of a deadline-less key. -/
structure SchedKey where
  deadline : Deadline
  priority : Priority
  scId     : SchedContextId

-- SeLe4n/Kernel/SchedContext/Hierarchy.lean (CB2.2, CB2.3)
def maxServerDepth   : Nat := 3    -- contexts on a path: root server → server → leaf
def maxServerMembers : Nat := 16

/-- Members in FIFO order, duplicate-free by construction, bounded. -/
structure MemberList where
  toNoDup : SeLe4n.NoDupList SchedContextId
  hBound  : toNoDup.val.length ≤ maxServerMembers

-- SeLe4n/Kernel/SchedContext/Types.lean (CB1.6 makes `periodStart` live; CB2.1 adds the rest)
structure SchedContext where
  scId, budget, period, priority, domain, budgetRemaining, replenishments,
  boundThread, isActive, lock : ... -- as today
  -- the stored `deadline` field is removed (CB1.6, D22): see the definition below
  /-- Start of the current window (§4.2). -/
  periodStart       : Nat := 0
  /-- The server this context is a member of; `none` at the root level. -/
  parentServer      : Option SchedContextId := none
  /-- Members, FIFO order; a leaf has none. -/
  serverMembers     : MemberList := MemberList.empty
  /-- `some c` iff this context is a server, homed on core `c`. -/
  serverCore        : Option CoreId := none
  /-- Number of members whose own count is positive (§4.5); for a leaf, `1`
      iff its bound thread is active. -/
  activeDescendants : Nat := 0
  /-- A root share that left a core — by unbind, a move, a donation's return,
      a shrink or a link under a server — and keeps counting there until the
      deadline it was released with (§4.6, D23): `some (core, perMille,
      deadline)` while live, cleared once `deadline ≤ now`.  At most one per
      context: a second departure coalesces when it names the same core and
      deadline (the shares add) and is refused otherwise, for at most one
      period (§4.6). -/
  residual          : Option (CoreId × Nat × Deadline) := none

/-- The window's end — derived, never stored (D22): every reader's
    `sc.deadline` resolves here, and `deadline = periodStart + period` is a
    `rfl`, not an invariant.  `0` for an unconfigured context (`period = 0`),
    which the order reads as "none". -/
def SchedContext.deadline (sc : SchedContext) : Deadline := ⟨sc.periodStart + sc.period.val⟩

def isServer (sc : SchedContext) : Bool := sc.serverCore.isSome
def isLeaf   (sc : SchedContext) : Bool := sc.serverCore.isNone

-- SeLe4n/Model/Object/Types.lean (CB1.5)
structure TCB where
  ...
  /-- Deadline inherited from the earliest-deadline thread blocked on this one
      (§4.7); `none` when nothing is blocked.  The `pipBoost` class.  Read by
      the order only when the thread is bound (D20). -/
  inheritedDeadline : Option Deadline := none
  -- `deadline` removed (CB1.4): unbound threads are deadline-less.

-- SeLe4n/Model/State.lean (CB1.3): the per-core scheduler state
structure SchedulerState where
  ...
  /-- `true` from the moment a transition surfaces a `.reschedule` SGI for this
      core — or, on the executing core, decides a preemption the gated
      context-restore seam cannot yet take — until `handleRescheduleSgiOnCore`
      runs there (§4.4).  The model's record of a scheduling point owed. -/
  reschedulePendingOnCore : Vector Bool numCores := default
```

Every added field is threaded through the manual `BEq` instances, the `ext`
lemmas, `bootSafeSchedContextCheck` / `bootSafeTcbCheck`, the idle-slot
reference sweep (`schedContextReferencesReservedIdleSlot`: a `parentServer`
or member naming a reserved idle object is refused), the observer projection
(§4.13) and the freeze mirror.  The constructor-arity destructurings in
`Platform/Boot.lean` make the build name every site that was missed.

Bounded queries (all total, fuel `maxServerDepth`):

```lean
def parentChain? (st : SystemState) (scId : SchedContextId) : Option (List SchedContextId)
  -- ancestors, nearest first; `none` on a dangling parent or a chain longer than the bound
def pathLength?  (st) (scId) : Option Nat            -- `chain.length + 1`: the contexts on the path
def rootOf?      (st) (scId) : Option SchedContextId
def isAncestorOf (st) (anc child : SchedContextId) : Bool
def schedPath?   (st) (scId) : Option (List SchedKey) -- root first, leaf last
/-- Where a context's refills live: a server on `serverCore`; a member on its
    root's `serverCore`; a parentless leaf on the core of the thread that
    currently runs on it (the donee's while donated, else the bound thread's,
    via `schedContextReplenishHome`); `none` for a parentless unbound leaf.
    CB1.2 defines the flat case; CB4.2 generalises it. -/
def replenishHomeOf? (st) (scId) : Option CoreId
/-- The cores a root's utilisation is charged to (§4.6): a root **server**'s
    `serverCore`; a root leaf's bound thread's home core and, while donated,
    the donee's home core; `[]` for members and for a parentless unbound leaf.
    A live `residual` (below) is charged on its own core besides. -/
def chargedCoresOf (st) (scId) : List CoreId
```

`hierarchyDepthBounded` (§4.10) is `pathLength? st sc = some n ∧ n ≤
maxServerDepth`, so a leaf under a server under a root server is the deepest
admitted shape and a scheduling path holds at most `maxServerDepth` contexts —
the bound the lock footprint (§4.12) is stated against.

### 4.2 Windows, deadlines and refills — the CBS engine rules

A SchedContext lives in a *window* `[periodStart, periodStart + period)` whose
end is its deadline.  Seven rules, all kernel-side; nothing else writes
`deadline`, `periodStart` or `replenishments`.  "Purge" means
`purgeReplenishmentOnCore` on the context's `replenishHomeOf?` (today's
configure purge); "re-key" means purge then `replenishOnCore` with the new
time.

| Rule | When | Effect |
|------|------|--------|
| (a) configure | `schedContextConfigure` on a context that is **not live** (no bound thread, no members), or `schedContextConfigureServer`, succeeds at time `t` | `budgetRemaining := budget`, `periodStart := t`, `deadline := t + period`, `replenishments := []`, purge |
| (b) exhaustion | the charge of §4.5 takes `budgetRemaining` to `0` at time `t` | `refillAt := max (periodStart + period) (t + 1)`; `replenishments := [{amount := budget, eligibleAt := refillAt}]`; `replenishOnCore home scId refillAt`; the deadline is **untouched** — the entity is ineligible until (d) |
| (c) surrender | `handleYieldWithBudget` at time `t` with `budgetRemaining > 0` | `budgetRemaining := 0`, then (b) |
| (d) landing | the drain pops `(scId, refillAt)` at `now ≥ refillAt` | if `sc.replenishments` names this `refillAt` **and** `refillAt ≥ periodStart + period`: `budgetRemaining := budget`, `periodStart := refillAt`, `deadline := refillAt + period`, `replenishments := []`; otherwise the queue entry is **stale** and is dropped with no other change.  Under `pendingRefillMirroredOnCore` the stale arm is unreachable (`cbsLandRefill_stale_unreachable_of_mirrored`); it stays total |
| (e) activation | a leaf whose bound thread becomes active from inactive; a leaf bound by `schedContextBind` to a thread that is **already** runnable or running (no enqueue happens there, so bind applies the rule itself); or a server whose `activeDescendants` goes `0 → 1` — at time `t` | (e1) `if deadline ≤ t ∨ budgetRemaining · period ≥ (deadline − t) · budget then budgetRemaining := budget, periodStart := t, deadline := t + period, replenishments := [], purge` — the classical CBS rule; (e2) `else if budgetRemaining = 0 ∧ replenishments = [] then` rule (b) at `t` — an exhausted entity re-armed after rule (g) cleared its refill; (e3) otherwise unchanged |
| (f) reconfigure | `schedContextConfigure` on a **live** context (bound, or a server with members) at time `t`, after re-admission (§4.6) | `budget := Q'`, `period := P'`, `budgetRemaining := min budgetRemaining Q'`, `deadline := periodStart + P'`; a pending refill becomes `{amount := Q', eligibleAt := max (periodStart + P') (t + 1)}` and is re-keyed; then, if the entity is active, rule (e) at `t` — never rule (a) (D17) |
| (g) detach | the context loses its replenish home: `schedContextUnbind` of a parentless leaf, `schedContextUnbindServer` of a leaf with no bound thread, retype cleanup | `replenishments := []`, purge — a context with no home has no refill in flight; its window fields are kept, so a later activation lands in rule (e) with the window it left |

Consequences the proofs use.  Per-object conjuncts of `SchedContext.wellFormed`
from CB1.6 on: `replenishments.length ≤ 1` (`atMostOnePendingRefill`);
`replenishments ≠ [] → budgetRemaining = 0` (`pendingRefillOnlyWhenExhausted`).
`deadline = periodStart + period` needs no conjunct: the deadline is derived
(D22), so the rules write `periodStart` and the deadline follows by `rfl`.  Per core, in
`perCoreCbsInvariant`: `pendingRefillMirroredOnCore st c` — for every context
whose `replenishHomeOf?` is `c`, `replenishments = [r]` iff core `c`'s queue
holds exactly one entry for it, `(scId, r.eligibleAt)`, and every entry of the
queue names such a context; store-level, in `schedContextStoreConsistent`:
`unhomedNoPendingRefill` — a context with no replenish home has
`replenishments = []`.  Consumption inside one window is at most the budget
in force when the window started (`window_consumption_le_budget`, T4): a
window starts with the full budget, nothing adds budget before the window
ends, and rule (f)'s clamp never adds.  The dead time after exhaustion is at
most one period (`refill_dead_time_le_period`, T5).  In (b) the `t + 1` arm is
reachable only when an entity exhausts after its deadline, which the
guarantee (§4.11, T14) rules out on an admitted core; the rule is total
regardless.  Under (e1) with `budgetRemaining = 0` the inequality reads
`0 ≥ (deadline − t) · budget`, true exactly when `deadline ≤ t`, so an
exhausted entity is refreshed at activation only once its window has ended —
which is also when its pending refill would have landed; (e2) exists for the
exhausted entity whose refill rule (g) removed, and lands at the same instant;
when (e2) is reached at bind for a thread that is already running, the
reschedule that ends the bind preempts it (§4.4, §4.8).

Why (f) is not (a): under rule (a) the holder of the write capability could
re-submit the same admitted `(Q, P)` every tick and start every tick with a
full budget, so no theorem about windows would bound anything.  Rule (f)'s
clamp never increases the remaining budget, and its only path to a fresh
window is (e1), whose condition `c · P ≥ (d − t) · Q` says the consumption so
far in this window, `Q − c` over `t − periodStart`, has run at a rate of at
most `Q/P` — the classical CBS argument that re-activation under the density
rule keeps the demand within the bandwidth (`cbsReconfigure_never_mints`,
T17: `budgetRemaining` does not increase except through (e1), and the
consumption of a context over any interval is at most `U · length + Q`
whatever sequence of reconfigurations and activations it undergoes).

Why this differs from the code today: the current arms schedule
`budgetRemaining` (≤ 1) one period after exhaustion and never refill without
exhaustion (§1.1).  Why it differs from Abeni–Buttazzo's soft CBS: the budget
is not refilled at exhaustion with the deadline postponed (which lets the
server keep running at a lower EDF priority), it is refilled at the window's
end — hard CBS, the variant without overrun, which is what a kernel enforcing
reservations wants.  Why the first cut's D14 is reversed: with per-window
refills nothing is owed when an entity is activated, so the classical
budget-refilling rule is sound and simpler.

`schedContextYieldTo` — a writer of `budgetRemaining` on two contexts at
once, outside every rule — is retired in the same cut (CB1.6, Q7); its four
harness probes go with it, and the engine refresh covers the trace lines they
wrote.  `cbsUpdateDeadline` is retired in favour of the rules above:
`cbsWindowStart sc t` implements the fresh window of (a)/(d)/(e1),
`cbsScheduleRefill sc t` implements (b), `cbsActivate sc t` implements (e),
`cbsLandRefill sc refillAt` implements (d), `cbsReconfigure sc Q' P' t`
implements (f), `cbsDetach sc` implements (g)'s field half.  Each is a pure
function on one `SchedContext`; the purge and `replenishOnCore` halves are
the state-level operations that already exist, applied on `replenishHomeOf?`.
The Z2 preservation theorems are restated over these six.

### 4.3 The order

```lean
/-- EDF-first comparison of two keys at the same path position (CB1.1 for
    thread keys; CB3.3 lifts it to paths).  `true` iff the challenger beats
    the incumbent. -/
def isBetterKey (inc chal : SchedKey) : Bool :=
  match chal.deadline.toNat, inc.deadline.toNat with
  | 0, 0      => legacyTie                              -- both legacy class
  | _, 0      => true                                   -- EDF class beats legacy
  | 0, _      => false
  | cd, id    =>
    if cd < id then true else if id < cd then false
    else if chal.priority > inc.priority then true
    else if chal.priority < inc.priority then false
    else chal.scId < inc.scId                           -- EDF-class tie: total on distinct entities
where
  legacyTie :=
    if chal.priority > inc.priority then true
    else if chal.priority < inc.priority then false
    else false                                          -- FIFO: keep the incumbent

/-- Lexicographic lift (CB3.3): positions compared root-first; the first
    position at which the keys differ decides; equal keys advance. -/
def isBetterPath : List SchedKey → List SchedKey → Bool
```

`isBetterCandidate` (live from CB1.7) is `isBetterKey` on the singleton thread
key.  One tie-break mechanism per class (D3): in the EDF class every entity is
a SchedContext, so `scId` is total on distinct entities and the relation is a
strict total order on the keys of distinct entities; in the legacy class every
entity is an unbound thread with the sentinel `scId`, ties keep the incumbent,
and the fold's FIFO order — the run queue's `toList` — decides, exactly as
today.  The first cut's mixed rule (FIFO for two leaves, `scId` otherwise)
was not transitive: leaf `1` beat server `50`, server `50` beat leaf `100`,
and leaf `100` kept its place against leaf `1`.  Strictness lemmas:
`isBetterKey_irrefl`, `isBetterKey_asymm`, `isBetterKey_trans`, and the same
three for `isBetterPath`; `isBetterPath_singleton_eq_isBetterKey`.  Equal
keys at a position mean the *same* entity (an ancestor two paths share), and a
shared ancestor is a server, so both paths continue past it
(`schedPath_equal_keys_advance`): the lift never runs one path out while the
other continues, and it is total on the paths of two distinct leaves.

A thread's key path (`resolveEffectiveSchedPath st tcb`, CB3.2): an unbound
thread yields the deadline-less singleton
`⟨0, effectiveRunQueuePriority tcb, sentinel⟩`; a bound thread yields
`schedPath? st scId` with the **leaf** key's deadline replaced by
`effectiveDeadline st tcb` (§4.7: `min(sc.deadline, inheritedDeadline)`) and
its priority lifted by `pipBoost`.  Ancestor keys are the servers' own
`(deadline, priority, scId)`.

### 4.4 Eligibility, selection and the key-worsening reschedule

```lean
def pathBudgetEligible (st : SystemState) (tcb : TCB) : Bool :=
  match tcb.schedContextBinding with
  | .unbound => true
  | .bound scId | .donated scId _ =>
    match parentChain? st scId with
    | some chain => (scId :: chain).all (fun s => (st.getSchedContext? s).any (·.budgetRemaining.isPositive))
    | none => false                                  -- dangling or over-deep: fail closed
```

Selection (`chooseBestRunnableHierarchical`, CB1.3 in singleton form beside
the live selector, live from CB1.7, CB3.4 in path form beside it, live from
CB3.6) is a left fold over
`(runQueueOnCore c).toList` — the FIFO `flat` order — keeping the best
eligible in-domain candidate under `isBetterPath`, skipping entries that do
not resolve to a TCB (the round-15 contract).  The bucket-first fast path
(`chooseBestInBucketEffective`) is retired at CB1.7; `maxPriorityBucket` and
`schedulerPriorityMatchOnCore` remain as membership facts.  Cost:
`O(n · maxServerDepth)` per decision with `n` the core's runnable count; the
lock-wait WCRT terms are unchanged (§4.12).  `candidateOutranksCurrentOnCore`
and `handleRescheduleSgiOnCore` decide with the same comparator on the same
keys; `edfCurrentEarliestOnCore` (§4.10) states the consequence.

**The key-worsening reschedule.**  Under fixed priority the only transition
that could leave a running thread outranked by a queued one was a priority
change, and SM8.B's `priorityRescheduleOnCore` (the "priority decreased"
seam behind `setPriorityOp`) handles it: on the executing core it runs
`handleRescheduleSgiOnCore` inline; for a thread running on a **remote** core
it returns the state **unchanged** and surfaces that core's `.reschedule` SGI,
and the remote core acts when the SGI lands.  Under EDF-first a running
thread's key also worsens when its window is reset later (reconfiguration,
rule (f)), when it gains an ancestor (`bindServer` of its leaf or of an
ancestor), or when an inherited deadline is recomputed away; and a queued
thread's key improves when it loses an ancestor (`unbindServer`), inherits an
earlier deadline, or is **bound** to a SchedContext while queued (it leaves
the legacy class for the EDF class and now outranks every legacy thread,
possibly the current one).  CB1.3 generalises the seam to
`keyRescheduleOnCore st c executingCore`, which re-evaluates
`candidateOutranksCurrentOnCore` on core `c` and applies the same decision,
and every transition that can move a key **calls it on every core whose
current thread's key it changed or whose queue holds a thread whose key it
improved** before it returns.  Which transitions those are is **derived, not
listed**: a thread's key path is a function of its leaf's window
(`periodStart`, `period`) and `priority`, its own `pipBoost` and
`inheritedDeadline`, its binding, its leaf's ancestor chain with their windows
and priorities, and its eligibility along the path — so the key-moving
transitions are exactly the writers of those inputs.  Window writers: rules
(a), (d), (e1) and (f) — `schedContextConfigure`, the drain, activation,
reconfiguration.  Priority writers: `setPriorityOp`, `schedContextConfigure`.
Inheritance writers: `updatePipBoost` / `revertPriorityInheritance` through
`pipBoostWithWake`, whose materiality guard compares the whole key —
effective priority **and** effective deadline — since a remote holder can
acquire an earlier inherited deadline at an unchanged priority.  **Binding
writers**: `schedContextBind` (a queued thread joins the EDF class; a running
thread whose leaf rule (e2) leaves at zero budget is no longer
`pathBudgetEligible`, and an ineligible current counts as outranked by every
eligible candidate and by idle, so the seam preempts it at once rather than at
the next tick), `schedContextUnbind` (a running or queued thread falls to the
legacy class and is outranked by any queued EDF thread), and the **three
donation composites and the return donation** — a call wakes the passive
receiver while it is still unbound, so the wake decision compared it as a
legacy thread, and `applyCallDonationOnCore` then hands it the donor's
deadline-bearing context: on a remote core the donated key can outrank the
current with no SGI posted, so donation and return end with the seam on the
receiver's core.  Ancestor writers: `schedContextBindServer`,
`schedContextUnbindServer`.  Eligibility writers: the charge, the refill
landing and the surrender, which are inside the tick's and the drain's own
scheduling points already.  `edfCurrentEarliestOnCore` in the bundle is the
check that this derivation is complete: a writer that forgets the call fails
its own preservation proof, which is how the enumeration in an earlier cut of
this section — missing bind, unbind and donation — would have been caught.

What the seam can and cannot establish.  A remote decision is not applied by
the transition: until the SGI lands, the remote core's model state still shows
the outranked thread current, so no theorem can say the current is maximal on
that core at that instant.  The model therefore records the request:
`reschedulePendingOnCore c` (§4.1) is set by **every** site that surfaces a
`.reschedule` SGI for `c` — the seam's remote arm, `pipBoostWithWake`, the
cross-core wake paths — and cleared by `handleRescheduleSgiOnCore` on entry,
and the per-core conjunct is stated **modulo the flag**:
`edfCurrentEarliestOnCore st c` requires maximality only when no scheduling
request is pending on `c` (§4.10).  The seam comes as the same wrapper pair
SM8.B has: `keyRescheduleOnCore` is the model-level seam, and
`keyRescheduleOnCoreLive` gates its **local** arm behind
`contextRestoreSeamLive` exactly as `priorityRescheduleOnCoreLive` does — with
one addition: while the gate is closed, the unapplied local preemption sets
the executing core's own flag, so the state says a scheduling point is owed
there rather than claiming a maximality the hardware has not enacted.  The
theorem that licenses each caller is `keyRescheduleOnCore_establishes_or_posts`
(T19): on the executing core with the seam live, `edfCurrentEarliestOnCore`
holds on the returned state; otherwise the affected core's flag is set and its
SGI surfaced, and `handleRescheduleSgiOnCore_establishes_edfCurrentEarliest`
closes the loop when that core takes its scheduling point.  The SGI list a
seam surfaces is tied to the flags it sets
(`sgi_surfaced_of_reschedulePending_set`: a core whose flag goes `false → true`
in a step is in the step's SGI list), so a site that sets the flag without
posting, or posts without setting it, fails a proof.

### 4.5 Charging, activation and the counter

```
chargeSchedPath st c path now : SystemState × Bool          -- CB4.1
  exhausted := false
  for sc in path (leaf first):                               -- path from parentChain?
    sc := consumeBudget sc 1
    if sc.budgetRemaining = 0:
      sc := cbsScheduleRefill sc now                         -- rule (b), writes core c's queue
      exhausted := true
    store sc
  return (st', exhausted)

timerTickBudgetOnCore, bound arm                              -- CB4.3
  (st', exhausted) := chargeSchedPath st c (leaf :: ancestors) now
  if leaf exhausted: timeoutBlockedThreads st' leafId c      -- leaf only (D4)
  if exhausted: re-enqueue tid; preempt                      -- as today
```

The **eligible-active** predicate and its counter.  `threadActive st tid :=
runnableOnSomeCore st tid ∨ runningOnSomeCore st tid`.  A node is
**eligible-active** when it can run something *now*: it has budget, and there
is work below it —

```
hasWork st sc        := if sc.isLeaf then ∃ tid, sc.boundThread = some tid ∧ threadActive st tid
                        else sc.activeDescendants > 0
eligibleActive st sc := sc.budgetRemaining.val > 0 ∧ hasWork st sc
```

— and `activeDescendants` counts, at a leaf, its thread (`1` iff the thread is
active), and, at a server, the **members that are eligible-active**.  One
predicate at every level, because a server is throttled by its own budget
exactly as a leaf is: an exhausted node's subtree stays queued but cannot run,
so it must count as inactive until its refill lands, and the landing must be
the `0 → 1` that fires rule (e) on an ancestor whose deadline passed meanwhile,
instead of letting that ancestor resume on a stale window.  A predicate that
read only the leaf's budget — the shape of an earlier cut of this section —
closed that hole for a leaf and left it open one level up, where a nested
server's exhaustion would have kept its parent's count positive and its
landing would have re-activated nothing.  The count climbs by one walk, fired
whenever a node's `eligibleActive` **flips**:

```
propagateCrossing st node dir now :                          -- dir ∈ {up, down}: `eligibleActive node` just flipped
  match node.parentServer with                               -- `node` itself is not touched
  | none => stop
  | some p =>
      old := p.activeDescendants; new := if dir = up then old + 1 else old − 1
      store p with activeDescendants := new
      if dir = up ∧ old = 0: p := cbsActivate p now           -- rule (e) on the server
      if eligibleActive p flipped:                           -- up: old = 0 ∧ p.budgetRemaining > 0 after rule (e)
        propagateCrossing st p dir now                       -- down: new = 0 ∧ p.budgetRemaining > 0
      else stop                                              -- the parent's count moved, its eligibility did not

linkActivity st child now   := if eligibleActive st child then propagateCrossing st child up now
unlinkActivity st child now := if eligibleActive st child then propagateCrossing st child down now
                                                             -- both leave the child's own fields alone
```

so a server's count changes only when one of its members flips, and the walk
stops at the first ancestor whose eligibility did not (a nested server with
one eligible leaf that gains a second goes `1 → 2` and its parent is
untouched; a server whose count goes `0 → 1` while its own budget is `0` and
its refill pending is not eligible yet, so the walk stops there and resumes
from that server when its landing (d) makes it eligible).  Rule (e) on a
server that a flip reaches is the walk's business; rule (e) on a **leaf** is
not — the transition that makes a thread active applies it
(`enqueueRunnableOnCore`, and `schedContextBind` of an active thread, from
CB1.6), and a budget-driven flip was set by the rule that moved the budget, so
the walk never re-arms a node it starts from: rule (e1) applied to a leaf after
its landing (d) holds trivially and would move a late drain's window from
`[refillAt, refillAt + P)` to `[now, now + P)`.  Linking and unlinking use the
two entry points rather than the walk on the child itself: an eligible child
contributes `1` to its new parent without its own fields changing, and an
eligible child withdraws that `1` before the edge goes — an earlier cut called
the walk on the child with a delta, which would have taken an active leaf from
`1` to `2` and never reached the parent.

Two shapes, on derived triggers, both reading the one predicate.
`syncLeafActivity st scId now` recomputes the leaf's count from `threadActive`
— the stored count is the pre-value, the recomputed one the post-value — and
climbs with `propagateCrossing` when the leaf's `eligibleActive` flipped
between them; it is idempotent, since a second call finds nothing to
recompute, and a site that omits it fails `activeDescendantsConsistent`.  A
budget crossing cannot be recovered from the post-state, so every rule that
moves a node's `budgetRemaining` runs under the bracket `withBudgetFlip st
scId now rule`, which evaluates `eligibleActive` before and after the rule and
climbs on a flip — a bracket rather than a sync, because only a bracket sees
both sides; around a rule that does not cross zero it is the rule
(`withBudgetFlip_eq_of_no_flip`).  Their call sites are **derived** from the
three things eligibility depends on, not enumerated:

* every transition that changes `threadActive tid` for a bound `tid`:
  `enqueueRunnableOnCore` (inactive → runnable); `removeRunnableOnCore`, the
  per-core primitive the cross-core send, reply, signal, fault and cancellation
  paths call directly, which both dequeues a queued thread **and clears the
  executing caller from `currentOnCore`** — the hook keys on the before/after
  `threadActive` predicate, never on queue membership, because a blocking
  caller is current, not queued; `suspendThreadOnCore`, the cancellation and
  fault suspends, `cleanupTcbReferences`, and the dispatch paths that clear a
  `current` slot without re-enqueueing — each synced **after** the leaf's own
  rule (e) where one fires, so the flip sees the re-armed budget;
* every transition that changes **which leaf a thread's activity is
  attributed to**: `schedContextBind`, `schedContextUnbind`, the three donation
  composites and the return donation — a call wakes the passive receiver
  unbound, removes the donor, then rebinds the leaf to the already-runnable
  receiver, so the leaf is synced **after the rebind** and the donor's
  departure and the receiver's arrival are one activity transfer under the
  ancestors' locks, with its own preservation proof — and
  `lifecyclePreRetypeCleanup`;
* every transition that moves a node's `budgetRemaining` across zero — **at
  every node**, not only the leaf: the refill landing (d), rules (a), (e1) and
  (f) (`0 → 1`) and the surrender (c) each run under `withBudgetFlip` on the
  node they move, so a landing that restores a nested server's eligibility is
  the flip that re-activates an ancestor whose window has passed; and
  `chargeSchedPath` (exhaustion of the leaf or of any ancestor, inside the
  tick's own scheduling point), which charges the path and then runs the flip
  test leaf first, each flipped node adjusting its parent's count by one —
  `propagateCrossing` unrolled along the path, since every node on it is
  visited anyway, so a parent whose count and budget both reach zero in one
  charge flips exactly once.

Dispatch (`switchToThreadOnCore`, `scheduleEffectiveOnCore`) moves a thread
from runnable to current, so the counter is untouched; preemption re-enqueues,
untouched; bindServer/unbindServer of a member call `linkActivity` /
`unlinkActivity`, so a whole subtree's activity enters or leaves the ancestors'
counts through the same walk without the child's fields moving (§4.8).  The invariant
`activeDescendantsConsistent` (§4.10) is what makes the enumeration complete:
every transition's cross-subsystem bridge must preserve it, so a runnability
change the helpers miss fails a proof rather than a review.  `removeRunnable`'s
`bootCoreId` pin is repointed to the thread's home core in the same row
(CB4.4) — the counter must see the queue the thread is really in.  Every
caller of the sync writes the leaf and up to `maxServerDepth − 1`
ancestors, so every caller's lock footprint gains those SchedContext locks in
that same row (§4.12, CB4.4).  Fallback if the counter proves too invasive: compute idleness
by a bounded subtree scan (at most `16 + 16·16 + 16·16·16` leaf checks at
depth 3, each `O(numCores)`); the plan prefers the counter and records the
fallback in §9.

### 4.6 Admission

`U(sc) := (sc.budget.val · 1000 + sc.period.val − 1) / sc.period.val`
(`Bandwidth.utilization`, ceiling per-mille).

```lean
/-- A root's utilisation is charged to every core in `chargedCoresOf` (§4.1):
    a server's `serverCore`; a bound leaf's thread home and, while donated,
    the donee's home too.  Runtime activity plays no part: an idle bound leaf
    is a reservation on its core. -/
def rootCountsOnCore (st) (sc) (c) : Bool :=
  sc.parentServer.isNone ∧ c ∈ chargedCoresOf st sc.scId
/-- Roots counting on `c` **plus every live residual on `c`** (D23). -/
def rootUtilisationOnCore (st) (c) (exclude : Option SchedContextId) : Nat
def checkRootAdmissionOnCore (st) (c) (candidate : SchedContext) (exclude) : Bool :=
  rootUtilisationOnCore st c exclude + U candidate ≤ 1000
def memberUtilisation (st) (server : SchedContext) (exclude) : Nat
def checkMemberAdmission (st) (server) (candidate) (exclude) : Bool :=
  memberUtilisation st server exclude + U candidate ≤ U server
```

Checked by every transition that creates, changes or **moves** a reservation
(D18): configure (root leaf with a bound thread → root check on **every**
core in `chargedCoresOf`, which is both cores while the leaf is donated;
member leaf → member check against the parent; server → root check on
`serverCore` if parentless, member check if a member — **and**, for a
populated server, its existing member sum against the candidate,
`memberUtilisation st server none ≤ U candidate`, so a server is never shrunk
under its members); bind of a thread to a
root leaf (root check on the thread's core — a new `.resourceExhausted`
refusal); bindServer (member check); unbindServer (root check on the child's
core whenever the detached child will count there — a server with a
`serverCore`, or a leaf with a bound thread — whether or not anything in it
is running); configureServer (root check); `.tcbSetAffinity` of a thread
bound to a root leaf (root check on the destination core, the leaf's own
share excluded, before the migration commits); a **cross-core donation** of
a root leaf (root check on the donee's home core, the leaf then charged on
both cores until the return donation releases the donee's share).  An
unbound parentless leaf counts for nothing.  `hierarchicalAdmissionHolds`
(§4.10) states both sums for every server and every core;
`rootAdmission_sound_per_core` (T13) says an admitted core's roots sum to at
most `1000`, and its preservation by every one of the moves above is proved
in the row that lands them (CB5.2).  The RPi5 canonical deployment's
`admissibleUtilisation = 750` stays a liveness-side margin above the kernel's
ceiling.

**Bandwidth is released at the window's end, not at departure** (D23).
Admission that only ever looks at the current reservation set is defeated by
churn: a `(5, 10)` root that ran ticks `0`–`4` and is then detached has
consumed half the core's window, and admitting `(2, 4)`, `(1, 2)`, `(1, 2)`
roots at ticks `5`, `7`, `8` keeps every instantaneous sum at or below
`1000 ‰` while their nine ticks of earlier-deadline demand starve a
continuously eligible `(5, 10)` root that was there all along.  The classical
answer — `SCHED_DEADLINE`'s zero-lag rule, simplified to the deadline — is
that a share keeps counting on the core it leaves until the deadline it was
released with.  So every transition that removes or reduces a root's share on
a core records a **residual** on the context (`residual := some (c, share,
deadline)`, §4.1): `schedContextUnbind` of a root leaf (its whole `U`), an
affinity move (on the source core), a donation's return (on the donee's core,
which the return no longer releases), a reconfiguration to a smaller
reservation (the difference), and `schedContextBindServer` of a root leaf (its
`U`, now counted under the server as well).  `rootUtilisationOnCore` sums live
residuals; a residual expires when `now ≥ deadline` and is cleared by the next
rule that touches the context or by the read that finds it expired.  While a
residual is live the context may be re-homed only on the residual's own core
(its share then counts twice there until expiry — conservative, never
optimistic), may not be retyped, and may not depart again unless the new
residual **coalesces** with the live one — same core and same deadline, the
shares adding (two shrinks inside one window) — so a move after a shrink, a
shrink after a move, a link under a server, or a cross-core donation
(refused by `donationAdmissible?`) waits for the live residual to expire;
`.illegalState` otherwise, for at most one period.  One slot per context is
therefore exact, not an approximation: a second live residual can never be
required, so none is ever dropped (the bounded ledger is Q15's alternative).  T15's contained-window demand then includes the departed windows,
T14 needs no hypothesis about the other roots, and T20 says the residual
covers exactly the demand a departed window could still place.

What the member rule buys (D19): a member's consumption is bounded by its own
`(Q, P)` per window (T12) and the server's by its own (T11), so the members
share the server's bandwidth and no member can take more than its share.
What it does **not** buy is a per-member window: a server `(5, 10)` may
receive its five ticks in `[5, 10)`, so a `(1, 2)` member — admitted, since
`500 ≤ 500` — misses every deadline before tick 5.  The guarantee T14 is
therefore stated for roots, and the two designs that would extend it to
members (server-aligned member windows, or a supply-bound admission test over
the periodic-resource model) are registered follow-ups the maintainer chooses
between (Q10).

### 4.7 Deadline inheritance

```lean
def computeMinWaiterDeadline (st : SystemState) (tid : ThreadId) : Option Deadline :=
  (waitersOf st tid).foldl (fun acc w =>
    match (st.getTcb? w).map (effectiveDeadline st) with
    | some (some d) => some (acc.elim d (min d))
    | _ => acc) none

/-- The deadline the order reads for a thread's own key: bound blockers only
    (D20).  An unbound thread has no own deadline and inherits none. -/
def effectiveDeadline (st : SystemState) (tcb : TCB) : Option Deadline :=
  match tcb.schedContextBinding.scId?.bind (st.getSchedContext? ·) with
  | none    => none
  | some sc => some (tcb.inheritedDeadline.elim sc.deadline (min sc.deadline))
```

`updatePipBoost` (and `updatePipBoostOnCore`, `propagatePipChainCrossCore`)
writes `pipBoost := computeMaxWaiterPriority` **and**
`inheritedDeadline := computeMinWaiterDeadline`; `revertPriorityInheritance`
keeps its shape — it **recomputes** both through `updatePipBoost` from the
waiters that remain, so a holder with waiters at deadlines `20` and `50` that
answers the first carries `50` until it answers the second, and clears both
only when no waiter is left; the bucket migration on a changed `pipBoost`
stays as it is (the bucket is a membership fact).  The inherited deadline
lowers the thread's **own** key only; a member's server keeps its key (D15).
An unbound blocker gets the priority boost and nothing else (D20): it has no
admitted budget, so an inherited deadline would make it EDF-class demand that
no admission sum counts, and `pip_bounded_inversion` in deadline terms would
then be a theorem about a schedule the guarantee cannot hold on.
`pipBoostWithWake`'s materiality guard compares the whole key
`(effective priority, effective deadline)` before and after (§4.4), so a
deadline-only change on a remote holder sends the `.reschedule` SGI.

Two theorems, two scopes.  `pip_bounded_inversion` (T7) is restated over
keys: under `blockingAcyclic`, a bound thread blocking a waiter of effective
deadline `d` has effective deadline `≤ d`.  Its dispatch consequence — the
blocker is selected no later than the waiter would have been — holds when the
blocker and the waiter have the **same parent** (both roots, or siblings
under one server), because their paths then agree above the leaf and the leaf
keys decide, and when the waiter's key beats the third thread's **strictly**
on deadline or, at equal deadlines, on priority
(`inherited_deadline_dispatch_effective_of_same_parent`, T18).  The `scId`
tie-break is the entity's own and is not inherited, so at an exact tie on
deadline and priority the blocker can still sort behind a sibling the waiter
would have beaten; T18 excludes that case rather than inherit a tie-break,
because a key whose `scId` is borrowed is no longer unique to its entity and
T1's totality would need a graph argument to recover.
For a blocker under a different parent the inherited leaf key is never
compared until its server's own key wins, so the client's deadline can pass
while the blocker's server waits behind another root — that is bandwidth
inheritance's territory, registered in §12 rather than claimed here.  T14
correspondingly takes the hypothesis that no thread on the core holds an
inherited deadline during the window (§4.11): an active inheritance makes a
blocker's window due earlier than its admission assumed, the classical
blocking term, and admission with blocking terms is a registered follow-up.

### 4.8 Transitions and refusals

Every refusal is an explicit `KernelError` arm evaluated before any write;
the `Kernel` monad (`SystemState → Except KernelError (α × SystemState)`)
discards a partial state on error.  Argument ids are validated through
`validateObjIdArg` / `validateThreadIdArg` (idle-slot and sentinel refusal)
before these tables apply.  Where an effect says **reschedule**, the
transition ends with `keyRescheduleOnCore` on every core whose current
thread's path it touched (§4.4).

**Every rule is written against the object's state dimensions, not its
nominal state.**  The review rounds' second recurring class was a rule
correct for a bound leaf whose thread is queued and silent about the other
states the model can produce.  So each row below is checked, and pinned in
the negative suite, across: for a SchedContext — `{root, member}` ×
`{unbound, bound to a queued thread, bound to a running thread, bound to a
blocked thread, mid-donation (boundThread is the donee), the leaf whose owner
is out on a donation}` × `{budget positive, exhausted with a refill pending,
exhausted with no refill}` × `{server with members, empty server, leaf}`; for
a thread — `{unbound, bound, donated, donation owner}` × `{inactive, queued,
running}` × `{home core = the leaf's, another core}`.  A cell the row does not
name is a cell the row refuses (`.illegalState`) until a later cut says
otherwise; the tables' "as today" entries are the cells the existing
transition already decides.

**`schedContextConfigureServer vScId core`** (new, CB5.1)

| Check, in order | Error |
|-----------------|-------|
| target is a SchedContext | `.objectNotFound` |
| `core < declaredCoreCount` (`MachineState.declaredCoreCount`) | `.invalidArgument` |
| `boundThread = none` | `.illegalState` |
| `parentServer = none` | `.illegalState` |
| `serverCore = none` (not already a server) — `serverMembers = []` then follows from `serverRoleExclusive` | `.illegalState` |
| root admission on `core` (excluding itself) | `.resourceExhausted` |
| effect | `serverCore := some core`; rule (a) — budget, window and both refill representations reset, so nothing a previous binding left behind is carried into the server's accounting (by `unhomedNoPendingRefill` an unbound parentless leaf already has none) |

**`schedContextBindServer vServer vChild`** (new, CB5.3; the child CPtr
resolved in the caller's CSpace with `.write` first — `.invalidCapability` /
`.invalidCapPtr` from `syscallLookupCap`)

| Check, in order | Error |
|-----------------|-------|
| both resolve to SchedContexts | `.objectNotFound` |
| `isServer server` | `.illegalState` |
| `child.parentServer = none` | `.illegalState` |
| `child ≠ server` and `¬ isAncestorOf st child server` | `.cyclicDependency` |
| depth: a leaf child needs `pathLength? server + 1 ≤ maxServerDepth`; a server child must be **empty** and needs `pathLength? server + 2 ≤ maxServerDepth` (room for the leaves it will hold) | `.illegalState` |
| `server.serverMembers.length < maxServerMembers` | `.resourceExhausted` |
| `child.domain = server.domain` | `.invalidArgument` |
| a child leaf's bound thread, if any, holds a `.bound` binding to it — a leaf in the middle of a donation (its `boundThread` is the donee while the donee's `.donated` binding names the owner it returns to) is refused, since the return would rebind a member to a thread this table never checked | `.illegalState` |
| child leaf with a bound thread: `determineTargetCore tid = serverCore`; child server: `child.serverCore = server.serverCore` | `.threadOnDifferentCore` |
| member admission against `server` | `.resourceExhausted` |
| (checked tier only) `objectLabelOf child ≡ objectLabelOf server`, and for a child leaf with a bound thread `threadLabelOf tid ≡ objectLabelOf server` (`≡` is `securityFlowsTo` both ways) | `.flowDenied` |
| effect | `child.parentServer := some server`; `server.serverMembers += child`; `linkActivity` on the child (its own count unchanged; rule (e) on every ancestor that crosses `0 → 1`); if the child was a root leaf with a bound thread its root share on that core becomes a residual until its deadline (D23 — the link is refused while a live residual that would not coalesce exists); reschedule |

**`schedContextUnbindServer vChild`** (new, CB5.4)

| Check, in order | Error |
|-----------------|-------|
| target is a SchedContext with `parentServer = some s` | `.illegalState` |
| `child.serverMembers = []` (a populated child server is not detached) | `.illegalState` |
| root admission on the child's core whenever the detached child will count there (`rootCountsOnCore` after the unlink: a server with a `serverCore`, or a leaf with a bound thread), active or not | `.resourceExhausted` |
| effect | `unlinkActivity` on the child before the edge goes; unlink both sides; a detached leaf with no bound thread takes rule (g); reschedule |

**Hierarchy-aware existing operations**

| Operation | New rule | Error |
|-----------|----------|-------|
| `schedContextConfigure` | `deadline` argument must be `0` (CB1.6); caller-MCP gate on `priority` (CB0.3); a `domain` change refused on a bound context (CB0.3, `.illegalAuthority`) and on any context with a parent or members (CB5.6, `.illegalState`); admission per §4.6 on every core in `chargedCoresOf` (both while donated), including a populated server's existing member sum against its new reservation; a shrink records the difference as a residual and is refused while a live residual that would not coalesce exists (D23); rule (a) on a context that is not live, rule (f) on one that is; a priority change on any context is a tie-break change and re-buckets nothing beyond the AK2-B mirror; reschedule | `.invalidArgument`, `.illegalAuthority`, `.illegalState`, `.resourceExhausted` |
| `schedContextBind` | target must be a leaf; a leaf carrying a live residual may be bound only to a thread homed on the residual's core (D23); the thread's domain equals the leaf's (today's rule); a member leaf's thread must be homed on the ancestor's `serverCore`; root leaf → root admission on the thread's core; (checked tier, member leaf only) `threadLabelOf tid ≡ objectLabelOf (rootOf leaf)`; a thread that is already runnable or running takes rule (e) at bind, since nothing enqueues it; the thread's activity enters the ancestors' counts through `syncLeafActivity` (the leaf's rule (e) first, so the flip sees its budget); a queued thread has joined the EDF class, so bind ends with `keyRescheduleOnCore` on its queue core; a running thread ends with it on its running core, where a current left ineligible by rule (e2) is preempted at once; a thread that is the recorded owner of an in-flight donation is refused (its return donation would rebind it and leave the new leaf's `boundThread` dangling) | `.illegalState`, `.invalidArgument`, `.threadOnDifferentCore`, `.resourceExhausted`, `.flowDenied` |
| `schedContextUnbind` | as today, plus `syncLeafActivity` on the leaf (the thread's activity leaves the ancestors' counts); a parentless leaf takes rule (g) and records its residual (D23); a running or queued thread has fallen to the legacy class, so unbind ends with `keyRescheduleOnCore` on its core | — |
| `.tcbSetAffinity` (`setThreadCpuAffinityWithMigration`) | the rule reads the thread's own binding — `.bound` **or `.donated`**, since a donee's core is a charged core too — **and** whether the thread is the recorded owner of an in-flight donation — a `.donated leaf tid` binding on the donee, found through the leaf's `scThreadIndex` entry — and treats an owner as bound to that leaf, since the return will rebind it: a member leaf → refused; a root leaf carrying a live residual that would not coalesce → refused until it expires (D23); otherwise root admission on the destination core (the leaf's own share excluded) before the migration, the source core keeping the share as a residual until the deadline, then the existing replenish migration | `.illegalState`, `.resourceExhausted` |
| `.tcbSetPriority` (`setPriorityOp`) | permitted on members (tie-break only, caller-MCP gated as today) | as today |
| `donateSchedContext` (the three donation composites) | a member leaf whose `serverCore` differs from the donee's home core is refused; a **root** leaf donated across cores is admitted on the donee's core first (charged on both cores; the return donation never fails and leaves the donee core's share as a residual until the deadline, so a cross-core donation of a leaf that already carries a live residual is refused, D23); donation and return each end with `syncLeafActivity` on the leaf and `keyRescheduleOnCore` on the receiving thread's core (§4.4, §4.5); (checked tier, member leaf only) `threadLabelOf donee ≡ objectLabelOf (rootOf leaf)`; the donated leaf keeps its position and window | `.illegalState`, `.resourceExhausted`, `.flowDenied` |
| `lifecyclePreRetypeCleanup` of a SchedContext | a populated server is refused, and so is a context carrying a live residual (D23 — destroying it would drop the share early; the refusal lasts at most one period); **any** member — a leaf or an empty server — is unlinked as `unbindServer` would before destruction, so no `serverMembers` entry outlives its object; rule (g); `syncLeafActivity` before the unlink | `.illegalState` |
| `handleYieldWithBudget` | rule (c) | — |

Error codes reuse the existing inductive: `.cyclicDependency` and
`.threadOnDifferentCore` already exist; no new `KernelError` variant is added.
The donation refusals land inside the three donation composites
(`applyCallDonationOnCore`, `applyReplyDonationOnCore`,
`replyRecvReturnDonation`'s forward half), which are live: they gain one
guard, `donationAdmissible? st client donee : Option KernelError`, evaluated
before the rendezvous commits, so a refused Call or Receive returns the error
to the thread that issued it and changes nothing.  The `.call` chain's staged
invariant surface and the production reply surface both gain the guard's
frame lemma (the guard writes nothing) and its refusal arm; CB5.2 carries the
admission half, CB6.5 the label half.

### 4.9 Syscall ABI and the total-table sweep

| Id | Lean arm | Rust variant | `min_inline_args` | Registers | Return shape |
|----|----------|--------------|-------------------|-----------|--------------|
| 35 | `.schedContextConfigureServer` | `SchedContextConfigureServer` | 1 | `MR0` = core (`u64`, `< numCores` at decode, `< declaredCoreCount` in the transition) | `.unit` |
| 36 | `.schedContextBindServer` | `SchedContextBindServer` | 1 | `MR0` = CPtr of the child SchedContext, resolved in the caller's CSpace with `.write` | `.unit` |
| 37 | `.schedContextUnbindServer` | `SchedContextUnbindServer` | 0 | none | `.unit` |

`SyscallId.count := 38` (Lean) and `SyscallId::COUNT = 38` (both Rust
tables).  `SYSCALL_ABI_VERSION` stays `3`.  `schedContextConfigure` (17) keeps
its five-register layout; its `MR3` (`deadline`) accepts only `0` after CB1.6.

Lean (`SeLe4n/Kernel/Architecture/SyscallArgDecode.lean`):
`SchedContextConfigureServerArgs { core : Nat }` with
`decodeSchedContextConfigureServerArgsChecked` refusing `core ≥ numCores`;
`SchedContextBindServerArgs { childCPtr : Nat }`;
`SchedContextUnbindServerArgs` (unit); `encode*`, `decode*_roundtrip`,
`decode*_error_iff` in the existing pattern.

Rust, **kernel side, in the id cut** (CB6.1): `rust/sele4n-types/src/syscall.rs`
gains the three variants, `COUNT = 38`, `from_u64`, `required_right → Write`,
and the discriminant tests; `rust/sele4n-hal/src/svc_dispatch.rs`'s hand
mirror gains the same plus `min_inline_args` (1, 1, 0) and its two mirror
tests keep the copies equal.  They land with the Lean ids, not after the arms,
because `dispatch_svc`'s prefilter refuses any id `SyscallId::from_u64` does
not know (`InvalidSyscallId`) **before** Lean is called: an id the Lean table
has and the Rust table lacks is unreachable on hardware, and the two tables
must never disagree in a shipped cut.  Rust, **argument side, with the
decoders** (CB6.2): `rust/sele4n-abi/src/args/sched_context.rs` gains
`SchedContextConfigureServerArgs { core: u64 }` (`encode → [u64; 1]`,
`decode` requiring one register), `SchedContextBindServerArgs { child: CPtr }`,
`SchedContextUnbindServerArgs` (zero registers), and documents
`SchedContextConfigureArgs.deadline` as `0`-only.  Rust, **userspace
convenience, after the activation** (CB6.7) — the ABI is invocable through
`invoke_syscall` with the ids and encoders above from the moment CB6.6 lands,
so the wrappers add no reachability: `rust/sele4n-sys/src/sched_context.rs` gains
`sched_context_configure_server(sc_cap: CPtr, core: u64)`,
`sched_context_bind_server(server_cap: CPtr, child: CPtr)`,
`sched_context_unbind_server(child_cap: CPtr)`, each an `invoke_syscall` with
`MessageInfo::new_const(n, 0, 0)` for its register count;
`rust/sele4n-abi/tests/conformance.rs` gains a `verify_regs` case per wrapper,
and the wrapper-length sweep covers them automatically.

**Where each arm lives.**  Both dispatchers begin
`match dispatchCapabilityOnly decoded cap tid with | some k => k | none => …`
and execute whatever the shared helper returns **before** their own arms are
consulted.  A policy-gated arm placed in that helper would therefore run its
*bare* form under `dispatchWithCapChecked` and the checked form would be
unreachable.  So: `.schedContextConfigureServer` and
`.schedContextUnbindServer` are capability-only and go into
`dispatchCapabilityOnly`; `.schedContextBindServer` is policy-gated (D8) and
goes into the **fall-through** arms of both dispatchers — the bare
`schedContextBindServerOnCore` in `dispatchWithCap`, and
`schedContextBindServerChecked` in `dispatchWithCapChecked` — exactly as
`.cspaceMint` / `cspaceMintChecked` do today.  The arm bodies and every
theorem about them land inert (CB6.3, CB6.4); the wiring is one activation
cut (CB6.6).  The bind arms' dispatch payoff lives with the staged
`dispatchWithCap_preserves_ipcInvariantFull` /
`dispatchWithCapChecked_preserves_ipcInvariantFull` pair, not with the
production `dispatchCapabilityOnly_preserves_ipcInvariantFull`; both are
composed from the per-arm theorems at CB6.6.
`.schedContextBind` (id 18) takes the same route at CB6.6: because the
helper is shared, its bare arm cannot stay in `dispatchCapabilityOnly` once a
checked form exists, so the arm **moves** to the fall-through position of both
dispatchers with `schedContextBindChecked` as its checked form, and the
equivalence theorem that holds the two forms equal when the policy permits
(`checkedDispatch_schedContextBind_eq_unchecked_when_allowed`) is stated in
the same cut.

**The total-table sweep** (CB6.1, with the ids) — every function over `SyscallId` the
elaborator refuses to compile until the three arms exist, with the value each
takes:

| Table | Where | `configureServer` | `bindServer` | `unbindServer` |
|-------|-------|-------------------|--------------|----------------|
| `SyscallId.toNat` / `ofNat?` / `ToString` | `Model/Object/Types.lean` | 35 | 36 | 37 |
| `syscallRequiredRight` | `Kernel/API.lean` | `.write` | `.write` | `.write` |
| `syscallChecksTargetFirst` | `Kernel/API.lean` | as `.schedContextBind` | as `.schedContextBind` | as `.schedContextUnbind` |
| `syscallDelegates` | `Kernel/API.lean` | the `…OnCore` transition | the `…OnCore` transition | the `…OnCore` transition |
| `syscallReturnShape` | `Architecture/SyscallReturn.lean` | `.unit` | `.unit` | `.unit` |
| `enforcementBoundary` + `syscallIdToEnforcementName` | `InformationFlow/Enforcement/Wrappers.lean` | `.capabilityOnly "schedContextConfigureServer"` | `.policyGated "schedContextBindServerChecked"` | `.capabilityOnly "schedContextUnbindServer"` |
| `syscallIdToEnforcementNamePerCore` | `InformationFlow/CovertChannelPerCore.lean` | the per-core form | the per-core form | the per-core form |
| `contentFlowClass` | `InformationFlow/TaintPropagation.lean` | control-only | control-only | control-only |
| `syscallRecordsDeclassification` | `InformationFlow/TaintPropagation.lean` | `false` | `false` | `false` |
| `refusalSeamClass` | `InformationFlow/RefusalRecord.lean` | not recorded | not recorded | not recorded |
| `frozenOpCoverage` (+ `_count`) | `FrozenOps/Operations.lean` | `true` (frozen twin) | `true` | `true` |
| `frozenOpUncheckedReason` | `FrozenOps/Agreement.lean` | the interlock's arm | the interlock's arm | the interlock's arm |
| `lockSetForSyscall` (+ `_undeclared_none`) | `Concurrency/Locks/LockSetForSyscall.lean` | `none` | `none` | `none` |
| `capFaultReceivePhase?` | `Platform/FFI.lean` | `none` | `none` | `none` |

**A table tells the truth about the tree as it is.**  The ids exist from
CB6.1 and the arms from CB6.6, and every table above is total over
`SyscallId`, so between the two cuts each table must say what is true of an
id the dispatcher refuses: `frozenOpCoverage := false` (the interlock
`frozenOpCoverage_obliges_differential_check` compares a claimed twin against
the live arm, and the live arm is the wildcard refusal), `syscallDelegates`
stating the refusal, the enforcement and per-core names naming the refusal
path, `lockSetForSyscall := none`.  CB6.6 flips them together with the arms.
Where a gate cannot accept a truthful placeholder — the Tier-1 routing gate
walks from a per-core name into the arm's body, and a refusal has no body to
walk — CB6.1 and CB6.6 merge into one cut rather than ship a table row that
describes an arm that does not exist (Q13); which it is, the gates decide at
CB6.1.

One **existing** row changes at CB6.6: `enforcementBoundary .schedContextBind`
becomes `.policyGated "schedContextBindChecked"` (D8), with
`enforcementBoundary_is_complete` and the per-core name table re-proved.
`lockSetForSyscall` answers `none` for the new ids because SM3.C.9's
migration has not reached any SchedContext arm; the model-level footprints of
§4.12 exist regardless, and the migration plan adopts them when it arrives.
The Tier-1 per-core routing gate (`check_live_arm_per_core_routing.py`) walks
from `syscallIdToEnforcementNamePerCore` two hops, so each arm's body must
reach a `…OnCore` transition rather than a `bootCoreId`-pinned primitive.

### 4.10 Invariants

Per-object, in `SchedContext.wellFormed` (`Types.lean`) and therefore carried
by `schedContextStoreConsistent` and by `bootSafeSchedContextCheck`:

| Conjunct | Statement | From |
|----------|-----------|------|
| (definitional, D22) | `deadline = ⟨periodStart + period.val⟩` by `rfl` — the stored field is gone, so no conjunct carries it | CB1.6 |
| `atMostOnePendingRefill` | `replenishments.length ≤ 1` | CB1.6 (defined CB1.2) |
| `pendingRefillOnlyWhenExhausted` | `replenishments ≠ [] → budgetRemaining.val = 0` | CB1.6 (defined CB1.2) |
| `serverRoleExclusive` | `isServer sc → boundThread = none` ∧ `isLeaf sc → serverMembers = []` | CB2.4 |
| `serverMembersBounded` | `serverMembers.length ≤ maxServerMembers` | CB2.4 |

Store-level, in `schedContextStoreConsistent` from CB1.6:
`unhomedNoPendingRefill` — `replenishHomeOf? st sc = none → sc.replenishments = []`.

Per core, in `perCoreCbsInvariant` from CB1.6: `pendingRefillMirroredOnCore
st c` — for every context homed on `c`, `replenishments = [r]` iff core `c`'s
replenish queue holds exactly one entry for it and that entry is
`(scId, r.eligibleAt)`, and every entry of the queue names a context homed on
`c` with that pending refill.  Rule (d)'s stale arm is unreachable under it.

Store-level, `schedHierarchyInvariant st` (`Invariant/HierarchyDefs.lean`,
CB2.5), the thirteenth conjunct of `crossSubsystemInvariant` from CB5.13:

| Conjunct | Statement |
|----------|-----------|
| `hierarchyBidirectional` | `∀ child s, child.parentServer = some s ↔ child ∈ s.serverMembers` (over `getSchedContext?`) |
| `hierarchyDepthBounded` | `∀ sc, ∃ n, pathLength? st sc = some n ∧ n ≤ maxServerDepth` — a total path, which is also acyclicity, of at most `maxServerDepth` contexts |
| `serverCoreConsistent` | a member server's `serverCore` equals its parent's; a member leaf with `boundThread = some tid` has `determineTargetCore st tid = parent.serverCore` |
| `serverDomainConsistent` | `∀ member s, member.domain = s.domain` |
| `hierarchicalAdmissionHolds` | `∀ c, rootUtilisationOnCore st c none ≤ 1000` ∧ `∀ s, isServer s → memberUtilisation st s none ≤ U s`, with `rootUtilisationOnCore` summing over `rootCountsOnCore` **and the live residuals on `c`** (§4.6, D23) |
| `residualWellFormed` | a live `residual = some (c, u, d)` names a declared core, `u ≤ 1000`, and `d` is the deadline the share was released with; an expired one (`d ≤ now`) counts for nothing |
| `activeDescendantsConsistent` | leaf: `activeDescendants = if ∃ tid, boundThread = some tid ∧ threadActive st tid then 1 else 0`; server: `activeDescendants = (serverMembers.filter (eligibleActive st ·)).length` — the members with budget **and** work below them, the one predicate of §4.5 |

Per-core (`Scheduler/Invariant/PerCore.lean`):

| Predicate | Statement |
|-----------|-----------|
| `edfCurrentEarliestOnCore st c` (defined CB1.3, in the bundle from CB1.7, replaces `edfCurrentHasEarliestDeadlineOnCore`) | if `reschedulePendingOnCore c = false` and `currentOnCore c = some cur` then for every `tid ∈ runQueueOnCore c` with `pathBudgetEligible` and the current's domain: `¬ isBetterPath (path cur) (path tid)` — the current is maximal in the selector's own order; a core with a scheduling request in flight is exempt until `handleRescheduleSgiOnCore` clears the flag there (§4.4) |

The pre-CB1 conjunct compared deadlines within a priority band; the new one is
the selector's order itself, so its preservation proofs are the selector's
optimality theorems applied at every dispatch and reschedule point, and
`keyRescheduleOnCore_establishes_or_posts` (T19) at every transition that
moves a key — establishing maximality where the decision is applied, and
setting the flag that exempts the core where it is only posted.  The flag is
what makes the conjunct a *state* invariant rather than a scheduling-point
postcondition: a remote `.reschedule` in flight is model state, not a gap the
invariant has to look away from.

Labeling (`InformationFlow/Invariant/Helpers.lean`; defined CB2.8, its
chokepoints proved CB6.5): `serverMembersUniformlyLabeled ctx st` — for every server `s` and member `m`:
`objectLabelOf m ≡ objectLabelOf s`, and for every TCB whose
`schedContextBinding` names `m` (`.bound m` or `.donated m _`):
`threadLabelOf tid ≡ objectLabelOf s`.  Vacuous on a server-free state, so the
tick's observer lift can take it as a hypothesis from CB4.3; established and
preserved by the three chokepoints of §4.13 and framed by everything else.

Retired or restated: `edfCurrentHasEarliestDeadlineOnCore` (replaced);
`boundThreadPriorityConsistent`, `schedulerPriorityMatchOnCore`,
`effectiveParamsMatchRunQueueOnCore` (kept, as membership facts about the
AK2-B mirror); `replenishment_within_period`, `replenishment_dead_time_exact`
(restated as `refill_dead_time_le_period`); `cbs_bandwidth_bounded` (kept, now
implied by `window_consumption_le_budget` with a tighter constant).

### 4.11 Key theorem statements

Each theorem's hypotheses were walked against every transition of §4.8 that
can fire inside its scope — configure, bind, unbind, bindServer,
unbindServer, affinity, donation and its return, inheritance and its
reversion, suspend, the remote reschedule — and a hypothesis is added where a
transition would otherwise falsify the conclusion; the walk is what turned
T14's original two hypotheses into nine, and it is repeated whenever §4.8
gains a row.

| # | Theorem | Statement (hypotheses named) | Row |
|---|---------|------------------------------|-----|
| T1 | `isBetterKey_irrefl`, `_asymm`, `_trans` | the order of §4.3 is a strict order on keys, total on the keys of distinct EDF-class entities; `isBetterPath_*` the same on key paths | CB1.1, CB3.3 |
| T2 | `chooseThreadEffectiveOnCore_eq_flat_of_no_deadlines` | if every `tid ∈ runQueueOnCore c` has `effectiveDeadline st tcb = none`, the scan selector equals the bucket-first selector on `(st, c)` — stated between the two definitions at CB1.3, about the live selector at CB1.7 | CB1.3, CB1.7 |
| T3 | `wellFormed_preserved_by_cbs_rules` | each of `cbsWindowStart`, `cbsScheduleRefill`, `cbsLandRefill`, `cbsActivate`, `cbsReconfigure`, `cbsDetach`, `consumeBudget` preserves the two CB1 refill conjuncts of §4.10 given `period > 0`, `0 < budget ≤ period` (the window equation is definitional) | CB1.2 |
| T4 | `window_consumption_le_budget` | for any `sc` with `wellFormed`, the ticks charged to `sc` while `periodStart` is unchanged sum to at most the value `budget` had when the window started | CB1.2 |
| T5 | `refill_dead_time_le_period` | a refill scheduled by rule (b) at `t` has `refillAt − t ≤ period`, and `refillAt > t` | CB1.2 |
| T6 | `cbsActivate_noop_of_fresh` | if `deadline > t`, `budgetRemaining · period < (deadline − t) · budget` and (`budgetRemaining > 0` or a refill is pending) then `cbsActivate sc t = sc` | CB1.2 |
| T7 | `pip_bounded_inversion` (restated) | under `blockingAcyclic`, a **bound** thread with a waiter of effective deadline `d` has effective deadline `≤ d` | CB1.8 |
| T8 | `edfCurrentEarliestOnCore` preservation | preserved by `scheduleEffectiveOnCore`, `handleRescheduleSgiOnCore`, `switchToThreadOnCore`, `timerTickOnCore`, `scheduleDomainOnCore`, `enqueueRunnableOnCore` (with the reschedule decision that follows a wake), and by every `keyRescheduleOnCore` caller through T19 | CB1.7, CB1.8 |
| T9 | `chooseThreadEffectiveOnCore_eq_flat_of_no_servers` | if every SchedContext in `st` has `parentServer = none`, the CB3 selector equals the CB1 selector | CB3.6 |
| T10 | `timerTickBudgetOnCore_eq_flat_of_root` | if the running thread's SchedContext has `parentServer = none`, the CB4 tick arm equals the CB1 tick arm | CB4.3 |
| T11 | `server_subtree_consumption_bounded` | for a server `s` with `wellFormed`, the ticks charged to threads in `s`'s subtree while `s.periodStart` is unchanged sum to at most `s.budget` (every such tick charges `s`, T4) | CB4.6 |
| T12 | `member_isolation` | a member's own consumption per window is bounded by its own `budget` whatever its siblings consume | CB4.6 |
| T13 | `rootAdmission_sound_per_core` | `hierarchicalAdmissionHolds st → ∀ c, Σ U over roots counting on c, live residuals included, ≤ 1000` (and the member sum for every server) — stated in CB2.5 over CB2.3's definitions; preserved by configure (checked on every charged core), bind, bindServer, unbindServer, configureServer, the affinity migration and the cross-core donation and its return — departures preserving it through the residual they leave (D23) | CB2.5, CB5.2 |
| T14 | `root_receives_budget_within_window` | **Hypotheses**: (H1) `hierarchicalAdmissionHolds` at the start of the run — and so at every state of it, since T13 makes it an invariant of every transition, departures included (D23), which is why no hypothesis freezes the *other* roots: they may come and go, and what leaves keeps counting until its deadline; (H2) `schedContextStoreConsistent st`; (H3) `schedHierarchyInvariant st`; (H4) `domainSchedule = []` (single-domain mode; the domain-rotating form is a follow-up); (H5) `continuouslyEligible e c s d` — at every state of the run on `[s, d)`, **from the window's release `s`**, some thread in `e`'s subtree is runnable or running on `c` and every context strictly below `e` on that thread's path has positive budget (an entity that blocks, or whose only leaf is exhausted, at any point of the window forfeits the guarantee for that window: the root's own budget is what the theorem accounts for, its descendants' eligibility is a hypothesis, and a suffix is not enough — a leaf that refills one tick before `d` cannot hand the root `Q` ticks); (H6) the run is a trace of the per-core step relation on `c` (`perCoreRunLoopStep`: tick, dispatch, wake, block, reschedule — one tick per tick step); (H7) `noInheritedDeadlineOnCore c` over `[s, d)` (an active inheritance is a blocking term the admission sum does not carry, §4.7); (H8) `entityStable e s d` — no `schedContextConfigure`, `schedContextBindServer`, `schedContextUnbindServer`, affinity change or cross-core donation involving `e` during `[s, d)`: rule (f) may abandon the window through (e1) — a `(10, 10)` root reconfigured after one tick to `(1, 100)` clamps to `1`, satisfies `1·100 ≥ 99·1` and opens a fresh window — a link or unlink changes what supplies `e`, and a move changes which core the guarantee is about; the guarantee is about the window as released, on the core it was released on; (H9) only if CB7.2 cannot close the composition: `edfBusyIntervalLemma` (below).  **Conclusion**: a **root** entity `e` on `c` whose window `[s, d)` opened at `s` with the full budget `Q` — by rule (a), (d) or (e1) — is charged `Q` ticks in `[s, d)` | CB7.2 |
| T15 | `cbs_demand_bound` | on a core satisfying `hierarchicalAdmissionHolds`, for every `t₁ ≤ t₂`, the budgets of the root windows **released at or after `t₁` with deadline at or before `t₂`** — an abandoned window (rule (e1) or (f)) counted by what it consumed, the windows of roots that have since left the core included, since their residual keeps their share admitted (D23) — sum to at most `t₂ − t₁`.  Not every window that *ends* in the interval: a `(5, 10)` window ending at `10` puts `5` into `[9, 11)` and is excluded by the release condition | CB7.2 |
| T16 | `edf_selects_earliest_eligible` | whenever `chooseThreadEffectiveOnCore` returns `some tid`, no eligible in-domain candidate has an `isBetterPath`-better key path | CB3.4, CB7.2 |
| T17 | `cbsReconfigure_never_mints` | `(cbsReconfigure sc Q' P' t).budgetRemaining ≤ sc.budgetRemaining` unless rule (e1) fired, and the consumption of any context over any interval is at most `U · length + budget` whatever reconfigurations and activations it undergoes | CB1.2 |
| T18 | `inherited_deadline_dispatch_effective_of_same_parent` | if `b` blocks `w`, both bound, with the same `parentServer`, then whenever `w`'s key beats a third thread `x`'s **strictly** on deadline or, at equal deadlines, on priority, `b` is selected over `x`; an exact tie on both, where only the non-inherited `scId` decides, is excluded (§4.7) | CB3.4 |
| T20 | `residual_covers_departed_demand` | a root share that leaves core `c` at time `t` with deadline `d` can still place at most the demand of its current window in `[t, d)`, and `rootUtilisationOnCore` counts its `U` on `c` until `d`; so admissions after `t` see the same bound they would have seen had the share stayed, and T15's sum is unchanged by departures | CB5.2 |
| T19 | `keyRescheduleOnCore_establishes_or_posts` | for any `st`, core `c` and executing core `e`: if `c = e` and the context-restore seam is live, `edfCurrentEarliestOnCore (keyRescheduleOnCore st c e).1 c`; otherwise the returned state has `reschedulePendingOnCore c = true` and, for `c ≠ e`, the `.reschedule` SGI for `c` is surfaced — and `handleRescheduleSgiOnCore_establishes_edfCurrentEarliest` says the handler on `c` clears the flag and establishes the conjunct | CB1.3 |

T14 is the classical EDF+CBS theorem, for roots.  The proof plan: T15 from
the admission sum, T4 and T17 (each window demands at most its budget, an
abandoned window at most what it consumed, and the density rule keeps every
entity's demand within `U · length + Q`); T16 from the selector's optimality;
the composition by the processor-demand argument over the per-core step
relation: in a busy interval `[t₀, d)` — one in which the selector never runs
a legacy-class thread or idles while an EDF-class entity is active, which H5
and the order give — EDF charges only entities with deadline `≤ d` before
`d`, so a miss at `d` would need more contained demand in `[t₀, d)` than
`d − t₀`, contradicting T15.  The busy-interval step is the one that may not
close within the row; if it does not, it is externalized **as exactly that
statement** — `edfBusyIntervalLemma`: in every busy interval of the step
relation the ticks charged to entities with deadline `≤ d` are bounded by the
contained demand with deadline `≤ d` — never as a hypothesis that restates
the conclusion, and registered with its closure target.  The per-core step
relation is defined for this theorem over `perCoreTimerTickStep` and the
dispatch transitions, not over WS-SL's `bootCoreId`-pinned `ValidTrace`;
WS-SL's limitation is cited, not crossed.  What T14 does **not** say: anything
about a member (D19), anything while an inheritance is active (H7), anything
under domain rotation (H4), anything about a window during part of which the
entity was ineligible (H5 runs from the release), anything about a window the
entity was reconfigured, re-linked or moved inside (H8).

### 4.12 Lock footprints and WCRT

The tick keeps `timerTickOnCoreLockSet c` (object store write, run queue `c`
write, replenish queue `c` write): `chargeSchedPath` writes only the path's
SchedContexts (object store) and core `c`'s replenish queue
(`chargeSchedPath_writes_within_timerTickOnCoreLockSet`).  The model-level
per-object footprint adds at most `maxServerDepth` SchedContext locks
(`chargeSchedPathLockSet`), so the tick's complete footprint is at most
`3 + 3 = 6` (`pathLockFootprint_le_maxLockSetSize`).

**Every activation caller** writes the leaf and its ancestors (§4.5), so
every footprint that reaches `syncLeafActivity` gains the
ancestors' SchedContext locks — `ancestorLockSetOf st tid`, at most
`maxServerDepth − 1 = 2` write locks at level 7, the leaf's lock being already
present wherever the SchedContext is written today: the wake footprints
(`wakeThread`, resume, the replenish and timeout wakes, the notification and
IPC unblocks), the IPC block footprints (`removeRunnable`'s callers),
`lockSet_tcbSuspend`, the cancellation and fault suspends, retype cleanup,
and the current-clearing dispatch paths.  `lockSet_tcbSuspend` is eight
entries at its widest — `maxLockSetSize` exactly — so the addition takes it
to ten: CB4.4 moves `maxLockSetSize` to `10` (D21), re-proves every
`_size_le_maxLockSetSize`, and re-derives the constant-dependent terms of
`WCRT_smp` and `PerCoreWcrt` with the new bound.  The ordering lemmas
(`_pairwise_le`) are unchanged in kind: the ancestors are SchedContext locks
and sort among the existing level-7 entries by `LockId`.  New transition
footprints, in the `lockSet_schedContextBind` pattern (`lockSetOfList`,
ascending by `LockId`):

| Transition | Footprint |
|------------|-----------|
| `schedContextConfigureServer` | caller TCB (read), CNode root (read), the SchedContext (write), the home core's replenish queue (write — rule (a)'s purge) |
| `schedContextBindServer` | caller TCB (read), CNode root (read), server (write), the server's ancestors (write, ≤ 1 at depth 3), child (write), the child's bound TCB (write) when present, the home core's replenish queue (write — rule (e1) on a `0 → 1` crossing) |
| `schedContextUnbindServer` | caller TCB (read), CNode root (read), child (write), parent (write), the parent's ancestors (write, ≤ 1), the child's bound TCB (write) when present, the former home core's replenish queue (write — rule (g)'s purge) |

Each carries `_write_only`-style shape lemmas, `_pairwise_le` and
`_size_le_maxLockSetSize` (at most 8).

**The replenish queue is a slot, and every rule that touches it declares
it.**  Rules (a), (e1), (f) and (g) purge or re-key a refill on the context's
home core, and the replenish queue is scheduler state that
`replenishOnCoreLockSet` already models as `SchedLockId.replenishQueue`, apart
from the object locks.  So every footprint of a transition that reaches one
of those rules composes the home core's queue lock in the row that lands the
rule: `schedContextConfigure` (whose rule (a) purge was unaccounted before
this workstream — CB1.6 extends `lockSet_schedContextConfigure`),
`schedContextUnbind` (rule (g), CB1.6), the activation callers — the wake
footprints behind `enqueueRunnableOnCore` and `lockSet_schedContextBind` in
CB1.6, the cut in which rule (e1) starts purging there, with the ancestors'
locks following in CB4.4 — and the three hierarchy transitions above
(CB5.14).  The tick already
holds it.  The bound of ten (D21) is re-verified against the widest footprint
after the slot is added and moves again only if the measurement demands.  The donation guard
`donationAdmissible?` reads the object store under locks the donation
composites already hold and writes nothing, so their footprints are
unchanged.  `WCRT_smp`'s lock-wait terms move only through the constant; the
selection scan's `O(n · maxServerDepth)` is a compute cost outside the
lock-WCRT model and is recorded in the docstring of
`chooseBestRunnableHierarchical` with the deadline-ordered index as the
registered remedy.

### 4.13 Information flow

Projection (`InformationFlow/Projection.lean`, `ObservableStatePerCore.lean`):
`parentServer`, `serverMembers`, `serverCore`, `activeDescendants` are erased
as structural scheduling plumbing (the `boundThread` class); `periodStart`
follows whatever class `deadline` is in today; `inheritedDeadline` follows
`pipBoost`.  `schedContextWriteSet` stays the singleton `[homeCore]`, since a
member's ancestors share its core.

**Three chokepoints, one invariant.**  `serverMembersUniformlyLabeled ctx st`
(§4.10) relates every member *and every thread whose binding names a member*
to the server's label, because the entities that modulate and observe a shared
budget are the threads: a rule over SchedContext labels alone is bypassed by
admitting an unbound leaf and then binding a differently labelled thread to it
through the capability-only `schedContextBind`.  The three transitions that
can put a context or a thread under a server each carry the check in the
flow-checked tier and refuse with `.flowDenied`, where `≡` is `securityFlowsTo`
in both directions under the installed labeling context:

| Chokepoint | Check | Row |
|------------|-------|-----|
| `schedContextBindServerChecked` | `objectLabelOf child ≡ objectLabelOf server`; for a child leaf with a bound thread, `threadLabelOf tid ≡ objectLabelOf server` (a child server's members are already `≡` its label by the invariant, and `≡` is transitive) | defined CB6.3, proved CB6.5, live CB6.6 |
| `schedContextBindChecked` (new checked form of id 18; the bare arm moves to the fall-through position, §4.9) | when the leaf has a parent: `threadLabelOf tid ≡ objectLabelOf (rootOf leaf)` | defined CB6.3, proved CB6.5, live CB6.6 |
| `donationAdmissible?`'s label half, inside the three donation composites when the client's leaf has a parent | `threadLabelOf donee ≡ objectLabelOf (rootOf leaf)` | landed CB6.4, proved CB6.5 |

Under it, `chargeSchedPath_confined_to_label`: the tick's ancestor writes are
same-label, and SM8.B's per-core non-interference lift over the tick keeps its
shape.  The three new arms are control-only in `contentFlowClass`; they record
no declassification and raise no fault.  The inter-server ordering channel at
the root — one server's deadline position observable through another's
dispatch latency — is the class SM8.D already bounds for priority bands,
re-derived for deadline order in CB1.7 (the cut that changes the order) and
recorded in the registers at CB7.1.

### 4.14 Staging and module layout

| Module | Role | Partition |
|--------|------|-----------|
| `SeLe4n/Kernel/SchedContext/Hierarchy.lean` (new) | constants, `MemberList`, the bounded queries | production from CB2.2 (imported by `Operations.lean`) |
| `SeLe4n/Kernel/SchedContext/HierarchyOperations.lean` (new) | the three transitions | production from CB5.1 (unreachable until CB6.6) |
| `SeLe4n/Kernel/SchedContext/Invariant/HierarchyDefs.lean` (new) | `schedHierarchyInvariant`, isolation theorems | production from CB2.5 (needed by `CrossSubsystem.lean` at CB5.13) |
| `SeLe4n/Kernel/SchedContext/Invariant/HierarchyPreservation.lean` (new) | the CB5.12 surface | staged (`Platform/Staged.lean` + allowlist line `SeLe4n.Kernel.SchedContext.Invariant.HierarchyPreservation  # marker: CB5.12 surface until the dispatch payoff imports it`), promoted at CB6.9 |
| `SeLe4n/Kernel/Scheduler/Liveness/EdfGuarantee.lean` (new) | T14–T16 | staged like `PerCoreWcrt.lean` |
| `SeLe4n/Kernel/SchedContext/HierarchyInventory.lean` (new) | theorem inventory | staged; claimed by the workstream manifest of CB8.2 |
| `tests/HierarchicalServerSuite.lean` (new) | Tier-2 suite, `lake exe hierarchical_server_suite` | `lakefile.toml` + `test_tier2_negative.sh` |

`SchedKey` and `isBetterKey` live in `Scheduler/Operations/Selection.lean`
from CB1.1, since the flat order needs them before any hierarchy module
exists.  Promotion (CB6.9) removes the allowlist lines and replaces
`STATUS: staged` markers with landing notes in the same cut; the partition
gate must pass in both directions.

### 4.15 Tests, scenarios and fixtures

Concrete scenarios (ticks; `(Q, P)` = budget, period; `dl` = deadline):

| Id | Scenario | Expected | Row |
|----|----------|----------|-----|
| S0 | two bound threads A `(prio 5, dl 100)`, B `(prio 3, dl 50)`, same domain, both eligible | pre-CB1: A; post-CB1: B — the witness inverted in CB1.7 | CB0.4 |
| S1 | legacy pair `prio 7` vs `prio 2`, unbound | `7` before and after; a bound `dl 1000` thread beats an unbound `prio 255` thread after CB1.7 | CB1.7 |
| S2 | `(Q, P) = (3, 10)` configured at `t = 0`; runs 3 ticks | exhausted at `t = 3`; one refill `(scId, 10)`; at `t = 10`: `budgetRemaining = 3`, window `[10, 20)`, `dl = 20`.  Pre-fix witness (inverted): a refill of `1` at `t = 13` | CB1.6 |
| S3 | same context, blocks at `t = 2` with `budgetRemaining = 1` | wake at `t = 12`: `dl 10 ≤ 12` → window `[12, 22)`, budget `3`; wake at `t = 5`: `1·10 < 5·3` → untouched; wake at `t = 8`: `1·10 ≥ 2·3` → window `[8, 18)`, budget `3` | CB1.6 |
| S4 | client C `(dl 20)` calls active bound server S `(own dl 100)`; thread X `(dl 50)` runnable | S's effective deadline `20`, S outranks X; after the reply S's `inheritedDeadline = none`; with a second waiter at `dl 50` still blocked after the first reply, S carries `50` | CB1.8 |
| S4b | S runnable on core 1 at unchanged effective priority acquires an inherited deadline from a client on core 0 | the `.reschedule` SGI to core 1 is surfaced — the materiality guard reads the whole key | CB1.8 |
| S5 | root server R `(dl 30)` with members m1 `(dl 200, prio 1)`, m2 `(dl 100, prio 9)`; root leaf L `(dl 40)` | order m2, then (R exhausted) L; two servers with equal deadline and priority order by `scId`; a leaf and a server with equal deadline and priority order by `scId` too | CB3.7 |
| S6 | server `(4, 20)` with members m1, m2 each `(3, 20)`; m1 runs 2 ticks, m2 runs 2 | server exhausted at `t = 4` with both members holding budget `1` → both ineligible; refill at `t = 20` → both eligible with the server's new window; nested: R `(6, 20)` ⊃ C `(3, 20)` ⊃ leaf — C exhausts at `t = 3` while R keeps `3`, C's leaf ineligible, R's other member runs; C with one active leaf gaining a second stays at R's count `1` | CB4.7 |
| S7 | through `syscallDispatchFromAbi`: retype three SchedContexts; configure the server `(4, 20)`; `configureServer core 1`; configure two leaves `(2, 20)` and `(3, 20)`; `bindServer` the first (ok) and the second (`.resourceExhausted`, `2 + 3 > 4` in per-mille terms); bind threads; ticks; `unbindServer`; error arms: cycle (`.cyclicDependency`), undeclared core (`.invalidArgument`), cross-domain (`.invalidArgument`), off-core thread (`.threadOnDifferentCore`), a fourth context on a path (`.illegalState`), a domain change on a member (`.illegalState`), retype of an empty member server (unlinked, `hierarchyBidirectional` holds after) | golden fixture `hierarchical_server_syscalls.expected` | CB6.6 |
| S8 | two labels; `bindServer` across labels → `.flowDenied`; same label → ok; a tick on the hierarchy leaves the other label's observation unchanged; two servers `(2, 5)` on one core (`U = 0.8`) each receive `2` per window over `[0, 10)` | in the information-flow and CBS suites | CB7.3 |
| S9 | `(3, 10)` at `t = 0` runs 2 ticks; `schedContextConfigure` with the same `(3, 10)` at `t = 2`, then again at `t = 8` with no run in between | at `t = 2`: `1·10 < 8·3` → budget stays `1`, window `[0, 10)`; at `t = 8`: `1·10 ≥ 2·3` → window `[8, 18)`, budget `3` (rate so far `2/8 ≤ 3/10`); the pre-D17 witness (rule (a)) would have minted `3` at `t = 2` | CB1.6 |
| S10 | core 1 admitted to `1000 ‰`; a root leaf `(1, 10)` bound to a thread on core 0: `.tcbSetAffinity` to core 1 → `.resourceExhausted`, state unchanged; a Call from that thread to a passive server on core 1 → `.resourceExhausted`; the same with core 1 at `900 ‰` → both succeed and core 1 reads `1000 ‰` while donated, `900 ‰` after the reply | CB5.2 |
| S11 | a member leaf under a server of label `L₁`; `schedContextBind` of a thread of label `L₂` → `.flowDenied`; a Call from an `L₁` member thread to a passive `L₂` server → `.flowDenied`; the same with `L₁` threads → ok | CB7.3 |
| S12 | `(3, 10)` configured at `t = 0` and left unbound; a **queued** unbound thread is bound to it at `t = 15` while a legacy thread runs | engine half: rule (e) fires at bind (`dl 10 ≤ 15` → window `[15, 25)`, budget `3`) with no enqueue; order half: the bind ends with the reschedule decision and the newly EDF-class thread preempts the legacy current | CB1.6, CB1.7 |
| S13 | a root server `(5, 10)` with members summing to `500 ‰`; `schedContextConfigure` to `(2, 10)` → `.resourceExhausted`; to `(5, 10)` again → ok, no fresh window (rule (f)) | the member-sum check at reconfiguration | CB5.6 |
| S15 | core 1 holds a continuously eligible `(5, 10)` root `e` and a second `(5, 10)` root that runs ticks `0`–`4` and is unbound at `t = 5`; at `t = 5`, `7`, `8` the caller admits `(2, 4)`, `(1, 2)`, `(1, 2)` roots | the unbound root's `500 ‰` stays counted on core 1 until `t = 10` (D23), so the first admission at `t = 5` is refused with `.resourceExhausted`; `e` receives its five ticks by `t = 10`; at `t = 10` the residual is expired and the same admission succeeds | CB5.2 |
| S16 | a passive server on core 1 is woken by a call from a client on core 0 whose leaf has `dl 20`, while core 1 runs a legacy thread and the wake compared the receiver as legacy | the donation ends with `keyRescheduleOnCore` on core 1: the flag is set and the `.reschedule` SGI surfaced; after the handler the receiver is current | CB1.7 |
| S14 | a thread current on core 1 has its window reset later by a configure issued from core 0 while a queued thread on core 1 holds an earlier deadline | core 1's `reschedulePendingOnCore` is set and its `.reschedule` SGI surfaced; `edfCurrentEarliestOnCore` holds on core 1 modulo the flag; after `handleRescheduleSgiOnCore` on core 1 the queued thread is current and the flag is clear | CB1.7 |

Fixture discipline: every new `.expected` ships with its `.expected.sha256`
and a row in `tests/fixtures/README.md`, following its *Regeneration
workflow*; scenario ids take a new bracket prefix `[HCB-nnn]` in
`tests/fixtures/scenario_registry.yaml` (subsystem `Scheduler`), which
`scripts/scenario_catalog.py validate-registry` checks.  Each of CB1's three
refreshes lists, per refreshed fixture, the deadline-bearing thread whose
refill, position or inherited deadline moved.

## 5. Dependencies

* **WS-SM SM5.A/SM5.D/SM5.F/SM5.H** (landed): the per-core selector, tick,
  priority-inheritance and CBS surface this workstream changes and then
  generalises.
* **WS-SM SM8.A–D** (landed): the per-core observer and the write-set
  discipline CB1.6, CB1.7, CB2.8, CB4.3 and CB6.4 extend; SM8.B's
  `priorityRescheduleOnCore` is the seam §4.4 generalises.
* **WS-RR RR5** (landed): the declared-core discipline CB5.1 reuses for a
  server's core, and the boot theorems CB2.6 keeps intact.
* **WS-RR RR6–RR8**: no dependency either way; §2.3 states the file partition.
* **SM10**: none.  CB6's fixtures are re-cut if the image lands first.

## 6. Phase map

| Phase | Scope (one line) | Subs | Est |
|-------|------------------|------|-----|
| CB0 | Registration, baseline verification, the pre-existing configure-authority gap, order and refill witnesses | 5 | S–M |
| CB1 | The EDF-first root on the flat model: five inert preparation rows, then three switch cuts — engine, order, inheritance — each with its proofs and its fixture refresh, then the liveness restatement | 9 | XL |
| CB2 | Model: hierarchy fields with their compiler sweep, bounded queries, per-object and store-level invariants, boot and observer erasure — inert | 9 | M–L |
| CB3 | Hierarchical selection and eligibility: inert path-form definitions, then one switch cut with its suite, provably identical on states without servers | 7 | L |
| CB4 | Hierarchical charging, activation and refills: two switch cuts — the tick with its server refills, the activation paths — each with its family, footprints and observer lift; the subtree isolation theorems | 7 | L–XL |
| CB5 | Per-core admission with every reservation move re-admitted; the hierarchy transitions and the hierarchy-aware forms of the existing operations, each with its preservation surface | 16 | XL |
| CB6 | The three syscalls: ids on both sides with their total-table sweep, arm bodies with every theorem an arm needs landed inert, then one activation cut with the specification and every pin of what it makes reachable | 9 | L–XL |
| CB7 | The CBS guarantee for roots; the covert-channel and lock-domain registers | 3 | L–XL |
| CB8 | Closure: specification verification, inventory, hardware spot-check script, follow-ups, the status flip | 8 | M |

## 7. Sub-tasks

Estimates: **T** trivial (<1h) · **S** small (<½ day) · **M** medium (1–2 days)
· **L** large (3–5 days) · **XL** extra-large (>1 week, expect to split further).
Each sub-task is sized to be one coherent PR or less, per the PR checklist.
Where a row says **in the same row as**, the switch and the theorem that
licenses it cannot compile apart and land as one cut.  Every row names the
§4 item it implements.  A row marked **inert** adds definitions and theorems
that no live path calls yet.

**Every row builds alone and leaves nothing uncovered.**  Five review rounds
found the same defect in different rows — a live change landing before, or
apart from, the proofs, tables or documents that cover it — so the rule is
stated once here and every row is held to it: (1) the tree builds after the
row with no later row applied, so a structure or inductive extension carries
the sweep the compiler forces; (2) every live definition the row changes has
every theorem that unfolds it re-proved in the row; (3) every behaviour the
row makes reachable is described by the specification and pinned by a test in
the row; (4) every table over a total type states what is **true after the
row** — never what a later row will make true — so a table entry for an
unwired id describes the refusal, not the arm; (5) every write the row adds
has its lock-footprint entry in the row.  The inert-then-switch shape of CB1,
CB3, CB4 and CB6 is what these five force whenever a change is large, not a
style.

### CB0 — Registration and baseline

Nothing here changes scheduling behaviour except CB0.3, which removes an
authority gap the flat model already has.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| CB0.1 | Register the workstream: the **WS-CB** registry row, the debt-register row pointing at this plan, the `CLAUDE.md`/`AGENTS.md` status subsection, this plan, the v0.34.49 CHANGELOG entry | `docs/REGISTERED_DEBT.md`, `CLAUDE.md`, `AGENTS.md`, `CHANGELOG.md` | S |
| CB0.2 | Pre-implementation refinement pass at the opening cut: re-verify every §1.1 claim against the tree, fold corrections into §1, §3 and §4 (the WS-RA precedent), re-run the prefix collision measurement; settle `isActive`'s meaning against its eleven writers and one reader (D22) and record the decision the engine switch pins | this plan | S |
| CB0.3 | Close the priority and domain half of §3.3: `schedContextConfigure` takes the caller, gates `priority` through `validatePriorityAuthority` against the caller's MCP, and refuses a `domain` change on a bound SchedContext with `.illegalAuthority` (§4.8); theorems `schedContextConfigure_priority_within_caller_mcp`, `schedContextConfigure_domain_fixed_of_bound`; negative-suite pins; trace-fixture refresh with rationale | `SeLe4n/Kernel/SchedContext/Operations.lean`, `SeLe4n/Kernel/API.lean`, `tests/NegativeStateSuite.lean`, `tests/fixtures/main_trace_smoke.expected` | M |
| CB0.4 | Order and refill witnesses landed **first** (§4.15 S0 and the pre-fix half of S2): Tier-2 pins of the pre-CB1 fixed-priority-first order and of the one-tick refill — the scenarios CB1 inverts in its switch cuts (the WS-RA RA.E.1 precedent: a witness that fails on the pre-migration tree, then pins the post-flip behaviour) | `tests/SmpCbsSuite.lean` | S |
| CB0.5 | Stale-comment sweep on files this workstream edits: the Rust `SyscallId` header's variant count and Lean line references, the `dispatchCapabilityOnly` docstring's arm count, the evidence index's staged-module count, and the exhaustion-arm docstring that describes the refill the code does not perform | `rust/sele4n-types/src/syscall.rs`, `SeLe4n/Kernel/API.lean`, `docs/CLAIM_EVIDENCE_INDEX.md`, `SeLe4n/Kernel/Scheduler/Operations/Core.lean` | S |

**Acceptance**: CB0.3's two theorems elaborate; `lake exe smp_cbs_suite` runs
the CB0.4 witnesses green against the pre-CB1 tree; Tier 0 and the docs-sync
lane pass.

### CB1 — The EDF-first root, on the flat model

The one phase whose behavioural change is intended to reach existing
fixtures.  Five inert rows land every definition and lemma the switches need
(CB1.1–CB1.5); three switch cuts then each flip one live surface **together
with** the proofs that cover it — the engine (CB1.6), the order (CB1.7),
inheritance (CB1.8) — so no intermediate release runs a policy its invariant
suite does not describe; the liveness restatement closes the phase (CB1.9).
The engine goes first because it retires the caller-supplied deadline (D13),
which must not be a primary key for even one release.  No server field exists
yet, so every theorem here is a flat-model theorem the hierarchy phases
generalise.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| CB1.1 | **Inert.** The order (§4.3): `SchedKey`, `isBetterKey` with `isBetterKey_irrefl`, `_asymm`, `_trans` (T1) and `isBetterKey_legacy_class_eq_fp` (two deadline-less keys compare as `isBetterCandidate` does today).  The live `isBetterCandidate` is untouched | `SeLe4n/Kernel/Scheduler/Operations/Selection.lean` | M |
| CB1.2 | **Inert.** The CBS engine rules as pure functions (§4.2): `cbsWindowStart`, `cbsScheduleRefill`, `cbsLandRefill`, `cbsActivate`, `cbsReconfigure`, `cbsDetach` beside the live `cbsUpdateDeadline`; the flat `replenishHomeOf?`; the predicates `atMostOnePendingRefill`, `pendingRefillOnlyWhenExhausted`, `pendingRefillMirroredOnCore`, `unhomedNoPendingRefill` as standalone definitions (the window equation needs none — D22); T3 for every rule, T4, T5, T6, T17, `cbsLandRefill_drops_stale`, `cbsLandRefill_stale_unreachable_of_mirrored` | `SeLe4n/Kernel/SchedContext/Budget.lean`, `SeLe4n/Kernel/SchedContext/Invariant/Defs.lean` | L |
| CB1.3 | **Inert.** The selector, the seam and the conjunct (§4.4, §4.10): `chooseBestRunnableHierarchical` in singleton form beside the live bucket-first path, with `_always_ok` and `_optimal`; T2 stated between the two selector definitions; `SchedulerState.reschedulePendingOnCore` (default `false`, written by nothing yet); `keyRescheduleOnCore` / `keyRescheduleOnCoreLive` generalising the SM8.B pair, with T19 and `handleRescheduleSgiOnCore_establishes_edfCurrentEarliest`; `edfCurrentEarliestOnCore` defined modulo the flag, with `edfCurrentEarliestOnCore_of_no_deadlines` (it follows from the current bundle on deadline-less states) | `SeLe4n/Kernel/Scheduler/Operations/Selection.lean`, `SeLe4n/Kernel/Scheduler/Operations/PerCoreChooseThread.lean`, `SeLe4n/Kernel/SchedContext/PriorityManagementPerCore.lean`, `SeLe4n/Kernel/Scheduler/Invariant/PerCore.lean`, `SeLe4n/Model/State.lean` | L |
| CB1.4 | Retire `TCB.deadline` (§4.1): `resolveEffectivePrioDeadline` yields no deadline for `.unbound`; the field removed with its `BEq`, `ext`, boot and projection sweeps; `resolveEffectivePrioDeadline_eq_of_zero_deadline` (unchanged wherever the field was `0`, which is every production state); the three suites that set it re-cut; the per-core suite re-elaborated (consumes CB1.3) | `SeLe4n/Model/Object/Types.lean`, `SeLe4n/Kernel/Scheduler/Operations/Selection.lean`, `SeLe4n/Kernel/Scheduler/Invariant/PerCoreInvariantSuite.lean`, `tests/SmpCancellationSuite.lean`, `tests/NegativeStateSuite.lean`, `tests/PriorityInheritanceSuite.lean` | M |
| CB1.5 | **Inert.** `TCB.inheritedDeadline` (§4.1, §4.7) with its `BEq`, `ext`, boot and projection sweeps (classified with `pipBoost`); `computeMinWaiterDeadline`, `effectiveDeadline` (bound blockers only, D20); `effectiveDeadline_eq_own_of_none`.  Nothing writes the field yet (consumes CB1.4) | `SeLe4n/Model/Object/Types.lean`, `SeLe4n/Kernel/Scheduler/PriorityInheritance/Compute.lean`, `SeLe4n/Kernel/InformationFlow/Projection.lean`, `SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean` | M |
| CB1.6 | **Switch cut 1 — the engine** (§4.2 rules (a)–(g); D13, D14, D16, D17): `schedContextConfigure` refuses a nonzero `deadline` (`.invalidArgument`) and applies rule (a) or (f) through `cbsReconfigure`; both tick exhaustion arms and `handleYieldWithBudget` through `cbsScheduleRefill`; the drain through `cbsLandRefill`; `enqueueRunnableOnCore` applies `cbsActivate` when a bound thread becomes active, and `schedContextBind` applies it when the thread it binds is already runnable or running (no enqueue happens there); `schedContextUnbind` applies rule (g); `cbsUpdateDeadline` and `schedContextYieldTo` retired (Q7), the latter's four harness probes with it; the stored `deadline` field is replaced by the derived `SchedContext.deadline` (D22) with its `BEq`, `ext`, boot and freeze sweeps, so `deadline = periodStart + period` holds by definition; `isActive` is pinned to the derived fact CB0.2 settled or retired; the two per-object refill conjuncts join `SchedContext.wellFormed`, `bootSafeSchedContextCheck`, `SchedContext.empty`/`mkChecked`; `lockSet_schedContextConfigure`, `lockSet_schedContextUnbind`, `lockSet_schedContextBind` and every wake footprint behind `enqueueRunnableOnCore` gain the home core's replenish-queue slot that rules (a), (g) and (e1) write from this cut (§4.12); `pendingRefillMirroredOnCore` joins `perCoreCbsInvariant` and `unhomedNoPendingRefill` joins `schedContextStoreConsistent`; **in the same row as**: the tick's CBS preservation family (`timerTickOnCore_preserves_perCoreCbsInvariant` and siblings) over the new arms, `replenishment_within_period` / `_dead_time_exact` restated as T5, the per-core suite's tick and wake cases against the unchanged fixed-priority bundle, the frozen twins `frozenTimerTickBudget` / `frozenSchedContextConfigure` with the agreement interlock, SM8.B's per-core lift over the tick, the pre-fix half of CB0.4's refill witness inverted, S2, S3, S9 and the engine half of S12, the **engine fixture refresh** (every `.expected` whose scenario configures, exhausts or refills a SchedContext) with rationale, the scenario registry, spec §8.12.2–§8.12.3 rewritten for windows and refills, evidence-index rows, Tier-3 anchors (consumes CB1.2, CB1.5) | `SeLe4n/Kernel/SchedContext/Budget.lean`, `SeLe4n/Kernel/SchedContext/Operations.lean`, `SeLe4n/Kernel/SchedContext/Types.lean`, `SeLe4n/Kernel/SchedContext/Invariant/Defs.lean`, `SeLe4n/Kernel/Scheduler/Operations/Core.lean`, `SeLe4n/Kernel/Scheduler/Operations/Selection.lean`, `SeLe4n/Kernel/Scheduler/Operations/PerCoreCbs.lean`, `SeLe4n/Kernel/Scheduler/Operations/PerCoreTickCbsPreservation.lean`, `SeLe4n/Kernel/Scheduler/Liveness/Replenishment.lean`, `SeLe4n/Kernel/Scheduler/Invariant/PerCoreInvariantSuite.lean`, `SeLe4n/Kernel/FrozenOps/Operations.lean`, `SeLe4n/Kernel/FrozenOps/Agreement.lean`, `SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean`, `SeLe4n/Platform/Boot.lean`, `tests/SmpCbsSuite.lean`, `tests/fixtures/`, `docs/spec/SELE4N_SPEC.md`, `docs/CLAIM_EVIDENCE_INDEX.md`, `scripts/test_tier3_invariant_surface.sh` | XL |
| CB1.7 | **Switch cut 2 — the order** (§4.3, §4.4; D3): `isBetterCandidate := isBetterKey` on singleton keys; `chooseThreadEffectiveOnCore` switches to the scan and the bucket-first path is retired; `candidateOutranksCurrentOnCore` and `handleRescheduleSgiOnCore` decide in the new order; `setPriorityOp`'s trigger becomes `keyRescheduleOnCore`; every binding writer ends with it — `schedContextConfigure` on a live context, `schedContextBind` of a queued or running thread, `schedContextUnbind` of a running or queued thread (it falls to the legacy class), and the three donation composites and the return donation on the receiving thread's core (a receiver woken unbound is handed a deadline-bearing context) — the set derived from the key's inputs in §4.4; every site that surfaces a `.reschedule` SGI — the seam's remote arm, `pipBoostWithWake`, the cross-core wake paths — sets `reschedulePendingOnCore` and `handleRescheduleSgiOnCore` clears it, with `sgi_surfaced_of_reschedulePending_set`; `edfCurrentEarliestOnCore` replaces `edfCurrentHasEarliestDeadlineOnCore` in the per-core bundle; **in the same row as**: T2 about the live selector, T8 (the `schedulerInvariantStrong_smp` family for `scheduleEffectiveOnCore`, `handleRescheduleSgiOnCore`, `switchToThreadOnCore`, the tick's preempt path, the domain switch, the wake and every `keyRescheduleOnCore` caller; the idle keystone unchanged, since the idle thread is deadline-less and last), SM8.B's per-core lift over dispatch (the observable order changes only through same-label deadlines) and SM8.D's root ordering-channel bound re-derived for deadline order, CB0.4's order witness inverted, S0, S1, S14, S16 and the order half of S12, the **order fixture refresh** (every `.expected` whose scenario has a deadline-bearing runnable thread) with rationale, spec §8.12.1 rewritten for EDF-first, the `CLAUDE.md`/`AGENTS.md` standing constraint, evidence-index rows, Tier-3 anchors (consumes CB1.3, CB1.6) | `SeLe4n/Kernel/Scheduler/Operations/Selection.lean`, `SeLe4n/Kernel/Scheduler/Operations/PerCoreChooseThread.lean`, `SeLe4n/Kernel/SchedContext/PriorityManagement.lean`, `SeLe4n/Kernel/SchedContext/PriorityManagementPerCore.lean`, `SeLe4n/Kernel/SchedContext/Operations.lean`, `SeLe4n/Kernel/Scheduler/Invariant/PerCore.lean`, `SeLe4n/Kernel/Scheduler/Invariant/PerCoreInvariantSuite.lean`, `SeLe4n/Kernel/Scheduler/Operations/PerCoreWake.lean`, `SeLe4n/Kernel/Scheduler/Operations/PerCoreTimerTick.lean`, `SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean`, `SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean`, `tests/SmpCbsSuite.lean`, `tests/fixtures/`, `docs/spec/SELE4N_SPEC.md`, `docs/CLAIM_EVIDENCE_INDEX.md`, `CLAUDE.md`, `AGENTS.md`, `scripts/test_tier3_invariant_surface.sh` | XL |
| CB1.8 | **Switch cut 3 — deadline inheritance** (§4.7; D15, D20): `updatePipBoost` / `updatePipBoostOnCore` / `propagatePipChainCrossCore` write `inheritedDeadline := computeMinWaiterDeadline` beside `pipBoost`; `revertPriorityInheritance` keeps recomputing both; `pipBoostWithWake`'s materiality guard compares the whole key and the boosted holder's core takes `keyRescheduleOnCore`; **in the same row as**: T7 over bound blockers, T8 for the inheritance writers, the donation-preservation family re-proved over the new field, S4 and S4b (the remote deadline-only SGI witness), the **inheritance fixture refresh** (the PIP and cross-core PIP goldens) with rationale, spec §8.13 rewritten for deadline inheritance and its scope, evidence-index rows, Tier-3 anchors (consumes CB1.5, CB1.7) | `SeLe4n/Kernel/Scheduler/PriorityInheritance/Propagate.lean`, `SeLe4n/Kernel/Scheduler/PriorityInheritance/PerCore.lean`, `SeLe4n/Kernel/Scheduler/PriorityInheritance/BoundedInversion.lean`, `SeLe4n/Kernel/Scheduler/PriorityInheritance/Preservation.lean`, `SeLe4n/Kernel/IPC/Invariant/DonationPreservation.lean`, `tests/PriorityInheritanceSuite.lean`, `tests/fixtures/`, `docs/spec/SELE4N_SPEC.md`, `docs/CLAIM_EVIDENCE_INDEX.md`, `scripts/test_tier3_invariant_surface.sh` | L |
| CB1.9 | Liveness surface restated for EDF: the band-based `WCRTHypotheses` and `bandExhaustionBound` kept for the legacy class; the EDF class's response bound stated as `edfResponseBound := domainRotationBound + period` with its hypotheses, proved as far as CB7 commits to; the lock-wait terms of `PerCoreWcrt` unchanged (consumes CB1.7) | `SeLe4n/Kernel/Scheduler/Liveness/WCRT.lean`, `SeLe4n/Kernel/Scheduler/Operations/PerCoreWcrt.lean` | L |

**Acceptance**: T2 elaborates with no hypothesis beyond the absence of
deadlines; every conjunct §4.10 adds to `SchedContext.wellFormed` is preserved
by every CBS rule and every transition; T4, T5 and T17 are stated over any
well-formed context; `edfCurrentEarliestOnCore` is preserved by every per-core
transition and every key-moving transition; T7 is stated over deadlines and is
not vacuous on bound threads; every refreshed fixture carries its rationale in
the fixture README; S0–S4b and S9 pass as written; no release between CB1.5
and CB1.9 runs a live policy its invariant suite does not describe.

### CB2 — The model, inert

Every definition here is unreachable from a live path until CB6; the only
behavioural change is that a boot SchedContext must be a parentless leaf,
which every existing fixture already is.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| CB2.1 | Add `parentServer`, `serverMembers`, `serverCore`, `activeDescendants` and `residual` to `SchedContext` with defaults (§4.1); `MemberList`; `isServer`, `isLeaf`; extend the manual `BEq` instance; **in the same row as** the sweep of every constructor-arity destructuring the build now rejects — `schedContextReferencesReservedIdleSlot`, `bootSafeSchedContextCheck`, the freeze mirror and siblings — classifying the new fields (a member or parent id naming a reserved idle object is refused; a boot SchedContext is a parentless leaf with no active descendants), since a structure extension and the sweep the compiler demands cannot build apart | `SeLe4n/Kernel/SchedContext/Types.lean`, `SeLe4n/Kernel/SchedContext/Hierarchy.lean` (new), `SeLe4n/Platform/Boot.lean`, `SeLe4n/Model/FrozenState.lean`, whatever else the build names | M |
| CB2.2 | Constants `maxServerDepth := 3`, `maxServerMembers := 16` (§4.1, D9) with `pathLockFootprint_le_maxLockSetSize` for the tick (§4.12) and a docstring recording the cost of one path charge | `SeLe4n/Kernel/SchedContext/Hierarchy.lean` | S |
| CB2.3 | Fuel-bounded hierarchy queries `parentChain?`, `pathLength?`, `rootOf?`, `isAncestorOf`, `schedPath?`, `chargedCoresOf` and the hierarchy-aware `replenishHomeOf?` (§4.1) with congruence over `getSchedContext?` and the `_of_root` simplifications (a parentless leaf's chain is empty, its path the singleton, its path length `1`); `schedPath_equal_keys_advance`; and the **pure admission arithmetic** over them (§4.6) — `rootCountsOnCore`, `rootUtilisationOnCore` (live residuals included), `checkRootAdmissionOnCore`, `memberUtilisation`, `checkMemberAdmission`, `residualLive`, `residualWellFormed` — inert definitions the store-level bundle and the hierarchy transitions consume, routed through by no live path until the admission cut two phases later | `SeLe4n/Kernel/SchedContext/Hierarchy.lean` | M |
| CB2.4 | Per-object well-formedness: `serverRoleExclusive` and `serverMembersBounded` join `SchedContext.wellFormed` (§4.10); `schedContextWellFormed` follows; the Z2 preservation theorems re-proved (every CBS rule frames the hierarchy fields); `bootSafeSchedContextCheck` decides the two new conjuncts in the same row (a boot SchedContext is a parentless, memberless, inactive leaf), so the boot theorem over `schedContextStoreConsistent` re-elaborates here rather than breaking until a later row | `SeLe4n/Kernel/SchedContext/Types.lean`, `SeLe4n/Kernel/SchedContext/Invariant/Defs.lean`, `SeLe4n/Platform/Boot.lean` | M |
| CB2.5 | The store-level bundle `schedHierarchyInvariant` (§4.10, six conjuncts, plus `residualWellFormed`), decidable where the arithmetic allows, with projections and `default_schedHierarchyInvariant`; T13 `rootAdmission_sound_per_core` in its pure form — the bundle implies every core's root sum, residuals included, is at most `1000` (consumes CB2.3) | `SeLe4n/Kernel/SchedContext/Invariant/HierarchyDefs.lean` (new) | M |
| CB2.6 | Boot: `bootFromPlatformCheckedWithIdleThreadsFor_schedHierarchyInvariant` on the production boot path — the bundle holds of the boot state, whose SchedContexts CB2.4's check already constrains (consumes CB2.5) | `SeLe4n/Platform/Boot.lean` | M |
| CB2.7 | Equality pins: the `BEq` instance reads every field (a witness that two contexts differing only in `parentServer` compare unequal, the SM3.A audit-pass lesson) and a `SchedContext.ext` lemma over the full field list | `SeLe4n/Kernel/SchedContext/Types.lean` | S |
| CB2.8 | Observer projection (§4.13): erase the four fields in `projectKernelObject` and the per-core observer; re-prove the projection lemmas the erasure touches; `schedContextWriteSet` stays the singleton; `serverMembersUniformlyLabeled ctx st` (§4.10) defined here over members and bindings, vacuous on a server-free state (`serverMembersUniformlyLabeled_of_no_servers`), so the tick switch in CB4 can take it as a hypothesis of the observer lift | `SeLe4n/Kernel/InformationFlow/Projection.lean`, `SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean`, `SeLe4n/Kernel/InformationFlow/Invariant/Helpers.lean` | M |
| CB2.9 | Freeze mirror: `FrozenKernelObject.schedContext` carries the record verbatim, so the freeze/thaw proofs and the lock projection re-elaborate over the new fields; Tier-3 anchors for CB2; `docs/codebase_map.json` regenerated; spec §8.12.8 skeleton stating "model landed, inert" | `SeLe4n/Model/FrozenState.lean`, `SeLe4n/Model/FreezeProofs.lean`, `scripts/test_tier3_invariant_surface.sh`, `docs/spec/SELE4N_SPEC.md` | S |

**Acceptance**: `lake build` of every touched module; `crossSubsystemInvariant`
is **not** yet extended (that is CB5.13, after the refusals it depends on);
every fixture byte-identical to the post-CB1 baseline.

### CB3 — Hierarchical selection

Three inert definition rows, one inert row for the path-form selector and its
theorems, one inert row for the path-form reschedule decision and conjunct,
then one switch cut that wires them together with the suite that covers them
— the shape CB1 has, because the suite's theorems unfold the selector and
cannot be re-proved apart from the switch.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| CB3.1 | **Inert.** `pathBudgetEligible st tcb` (§4.4) with `pathBudgetEligible_eq_hasSufficientBudget_of_root` (consumes CB2.3) | `SeLe4n/Kernel/Scheduler/Operations/Selection.lean` | S |
| CB3.2 | **Inert.** `resolveEffectiveSchedPath st tcb : List SchedKey` (§4.3), root-first, the leaf key lowered by `effectiveDeadline` and lifted by `pipBoost`; `resolveEffectiveSchedPath_root_eq_resolveEffectivePrioDeadline` (the singleton is CB1's key) | `SeLe4n/Kernel/Scheduler/Operations/Selection.lean` | M |
| CB3.3 | **Inert.** `isBetterPath` (§4.3) over `isBetterKey` with `isBetterPath_irrefl`, `_asymm`, `_trans` (T1), `isBetterPath_singleton_eq_isBetterKey` and `isBetterPath_total_on_distinct_leaves` (through `schedPath_equal_keys_advance`) | `SeLe4n/Kernel/Scheduler/Operations/Selection.lean` | M |
| CB3.4 | **Inert.** `chooseBestRunnableHierarchical` in path form beside the live singleton form, with `_always_ok` and `_optimal` (T16 in its selection form), T18 `inherited_deadline_dispatch_effective_of_same_parent` (§4.7), and T9 stated between the two selector definitions (consumes CB3.1–CB3.3) | `SeLe4n/Kernel/Scheduler/Operations/Selection.lean`, `SeLe4n/Kernel/Scheduler/Operations/PerCoreChooseThread.lean` | L |
| CB3.5 | **Inert.** `candidateOutranksCurrentOnCore`, `keyRescheduleOnCore` and `edfCurrentEarliestOnCore` in path form beside the live singleton forms, each with the corollary that on a state whose contexts are all parentless it equals its CB1 form; T19 restated on paths; `schedulerPriorityMatchOnCore` and `effectiveParamsMatchRunQueueOnCore` unchanged in meaning, since the bucket orders nothing (consumes CB3.4) | `SeLe4n/Kernel/Scheduler/Operations/Selection.lean`, `SeLe4n/Kernel/SchedContext/PriorityManagementPerCore.lean`, `SeLe4n/Kernel/Scheduler/Invariant/PerCore.lean` | L |
| CB3.6 | **Switch cut — hierarchical selection**: `chooseThreadEffectiveOnCore`, `candidateOutranksCurrentOnCore`, `keyRescheduleOnCore`, `handleRescheduleSgiOnCore` and the per-core bundle's conjunct switch to the path forms; **in the same row as** T9 about the live selector and the selection-dependent suite — `chooseThreadOnCore_ok_of_runnableTCBs`, the idle keystone (untouched: idle threads are unbound), the `schedulerInvariantStrong_smp` preservation family for `scheduleEffectiveOnCore`, `handleRescheduleSgiOnCore` and every `keyRescheduleOnCore` caller — re-proved by the flat corollaries plus T9; every `.expected` byte-identical to the post-CB1 baseline (consumes CB3.4, CB3.5) | `SeLe4n/Kernel/Scheduler/Operations/Selection.lean`, `SeLe4n/Kernel/Scheduler/Operations/PerCoreChooseThread.lean`, `SeLe4n/Kernel/SchedContext/PriorityManagementPerCore.lean`, `SeLe4n/Kernel/Scheduler/Invariant/PerCore.lean`, `SeLe4n/Kernel/Scheduler/Invariant/PerCoreInvariantSuite.lean`, `SeLe4n/Kernel/Scheduler/Operations/PerCoreWake.lean` | XL |
| CB3.7 | Fixtures byte-identical to the post-CB1 baseline (every `.expected`); Tier-2 scenario S5 (§4.15) on hand-built hierarchies via `StateBuilder.withServerHierarchy`; Tier-3 anchors; spec §8.12.8's selection subsection written in this cut, since the path selector is what the kernel now runs; evidence-index rows for T9, T16 and T18 | `tests/SmpCbsSuite.lean`, `SeLe4n/Testing/StateBuilder.lean`, `scripts/test_tier3_invariant_surface.sh`, `docs/spec/SELE4N_SPEC.md`, `docs/CLAIM_EVIDENCE_INDEX.md` | M |

**Acceptance**: T9 elaborates without hypotheses beyond parentlessness; no
theorem about the path selector is first stated in CB3.6;
`test_tier2_trace.sh` reports every sha256 unchanged from the post-CB1
baseline; S5 passes as written.

### CB4 — Hierarchical charging, activation and refills

Two switch cuts — the tick (CB4.3) and the activation paths (CB4.4) — each
carrying the preservation family, the footprints and the observer lift over
the writes it introduces; the fold, the frames and the footprint definitions
land inert first.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| CB4.1 | **Inert.** `chargeSchedPath st c path now : SystemState × Bool` (§4.5) with frames — `getTcb?` unchanged, every run queue unchanged, only core `c`'s replenish queue and the path's contexts written — and its footprint (§4.12): `chargeSchedPath_writes_within_timerTickOnCoreLockSet`, the model-level `chargeSchedPathLockSet` with `_pairwise_le` and `_size_le_maxLockSetSize` (consumes CB2.2, CB2.3) | `SeLe4n/Kernel/Scheduler/Operations/Core.lean`, `SeLe4n/Kernel/Scheduler/Operations/PerCoreTimerTick.lean` | M |
| CB4.2 | The three home readers generalised through `replenishHomeOf?` — a live definition change whose every consumer re-elaborates in the row: `schedContextReplenishHome`, `replenishQueueAffinityConsistentOnCore`, `replenishQueueEntriesBoundOnCore` (an entry's context is homed on `c`), `pendingRefillMirroredOnCore` and `unhomedNoPendingRefill` restated, each with its `_of_leaf` equivalence, and the existing preservation surface re-proved through the equivalences (consumes CB2.3) | `SeLe4n/Kernel/SchedContext/Operations.lean`, `SeLe4n/Kernel/SchedContext/ReplenishAffinity.lean`, `SeLe4n/Kernel/SchedContext/BindingAffinity.lean`, `SeLe4n/Kernel/Scheduler/Operations/PerCoreCbs.lean` | M |
| CB4.3 | **Switch cut — the hierarchical tick**: `timerTickBudgetOnCore`'s bound arm charges through `chargeSchedPath`, leaf-only timeouts, preemption iff any level exhausted; **in the same row as** T10 `timerTickBudgetOnCore_eq_flat_of_root`, the tick preservation family — the ten `timerTickOnCore_preserves_*` structural theorems, `allThreadsTimeSlicePositive`, `schedulerInvariantStructuralRegNodup_perCore`, and the CBS side (`replenishQueueValidOnCore`, `replenishmentPipelineOrderOnCore`, `pendingRefillMirroredOnCore`, `perCoreCbsInvariant`) — mostly by T10's reduction plus CB4.1's frames, and the per-core non-interference lift over the tick with `serverMembersUniformlyLabeled` (CB2.8) as a new hypothesis of the SM8.B capstone: `chargeSchedPath_confined_to_label` and the tick lift re-proved over the new body; and the server-aware refill decision — `replenishWakeDecision` (`.wakeThread`, `.rescheduleCore`, `.none`) replacing `replenishWakeTarget`, `processOneReplenishmentOnCore` landing a server's refill by rule (d) and raising the local-wake bit on `.rescheduleCore`, with `cbsReplenish_server_reschedules_local` and `replenishWakeDecision_leaf_eq_target` — since a tick that can exhaust a server needs the drain that re-arms its descendants in the same cut, or a newly eligible earlier-deadline descendant would not preempt; every `.expected` byte-identical (consumes CB4.1, CB4.2) | `SeLe4n/Kernel/Scheduler/Operations/Core.lean`, `SeLe4n/Kernel/Scheduler/Operations/PerCoreTimerTick.lean`, `SeLe4n/Kernel/Scheduler/Operations/PerCoreTickCbsPreservation.lean`, `SeLe4n/Kernel/Scheduler/Operations/PerCoreTickCbsAffinity.lean`, `SeLe4n/Kernel/Scheduler/Invariant/PerCoreInvariantSuite.lean`, `SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean`, `SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean` | XL |
| CB4.4 | **Switch cut — activation along the path** (§4.5, §4.12; D21): `eligibleActive` at every node, `propagateCrossing` on eligibility flips and the `linkActivity` / `unlinkActivity` entry points; the idempotent `syncLeafActivity` and the `withBudgetFlip` bracket on their three derived trigger sets (§4.5) — every change of a bound thread's `threadActive` (`enqueueRunnableOnCore`; `removeRunnableOnCore`, keyed on the before/after predicate so the executing caller it clears from `currentOnCore` is deactivated like a dequeued one; `suspendThreadOnCore`; the cancellation and fault suspends; `cleanupTcbReferences`; the current-clearing dispatch paths) and every change of a leaf's binding (`schedContextBind`, `schedContextUnbind`, the three donation composites and the return donation, synced after the rebind, `lifecyclePreRetypeCleanup`) and every crossing of a node's `budgetRemaining` through zero at any level of the charged path (`chargeSchedPath` with its leaf-first flip pass; the landing (d), rules (a), (e1), (f) and the surrender (c) under `withBudgetFlip`); `removeRunnable` repointed from `bootCoreId` to the home core; `cbsActivate` on every server whose count goes `0 → 1` and on no leaf the walk starts from; `propagateCrossing_stops_at_first_non_flip`, `withBudgetFlip_eq_of_no_flip`; `activeDescendantsConsistent` and the `wellFormed` conjuncts preserved by every path that moves the count; **in the same row as** every activation caller's footprint gaining `ancestorLockSetOf st tid` — the wake, block, suspend, cancellation, fault, cleanup and current-clearing paths, `lockSet_tcbSuspend` and `suspendFootprintOf` among them — `maxLockSetSize := 10` with every `_size_le_maxLockSetSize` and the constant-dependent `WCRT_smp` / `PerCoreWcrt` terms re-derived, `_pairwise_le` re-proved where the ancestors sort in, the ancestors' locks composed into every activation footprint (the replenish-queue slot itself landed with rule (e1) in CB1.6, §4.12), and the wake and block preservation surface re-elaborated in the row, since `enqueueRunnableOnCore` and `removeRunnableOnCore` change; every `.expected` byte-identical (consumes CB2.5, CB4.1) | `SeLe4n/Kernel/Scheduler/Operations/Selection.lean`, `SeLe4n/Kernel/Scheduler/Operations/Core.lean`, `SeLe4n/Kernel/IPC/Operations/Endpoint.lean`, `SeLe4n/Kernel/IPC/CrossCore/EndpointCall.lean`, `SeLe4n/Kernel/IPC/Operations/Donation/Primitives.lean`, `SeLe4n/Kernel/Lifecycle/Operations/Cleanup.lean`, `SeLe4n/Kernel/Lifecycle/Suspend.lean`, `SeLe4n/Kernel/SchedContext/Hierarchy.lean`, `SeLe4n/Kernel/SchedContext/Operations.lean`, `SeLe4n/Kernel/Concurrency/Locks/Deadlock.lean`, `SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean`, `SeLe4n/Kernel/Concurrency/Locks/LockSetForSyscall.lean`, `SeLe4n/Kernel/Scheduler/Operations/PerCoreWcrt.lean`, `SeLe4n/Kernel/Scheduler/Liveness/WCRT.lean` | XL |
| CB4.5 | `schedHierarchyInvariant` preserved by the tick, the drain, `replenishOnCore` and the activation paths — budgets, deadlines, window starts and counts move, the tree fields are framed; theorem-only, since the conjunct joins the cross-subsystem bundle in CB5 (consumes CB4.3, CB4.4) | `SeLe4n/Kernel/Scheduler/Operations/PerCoreTickCbsPreservation.lean` | M |
| CB4.6 | Isolation theorems (§4.11): `chargeSchedPath_charges_every_ancestor`, T11 `server_subtree_consumption_bounded`, T12 `member_isolation` (consumes CB4.3) | `SeLe4n/Kernel/SchedContext/Invariant/HierarchyDefs.lean` | L |
| CB4.7 | Tier-2 scenario S6 (§4.15) plus an idle-server activation by rule (e); golden fixture `tests/fixtures/hierarchical_server_tick.expected` with its sha256 and README row; Tier-3 anchors; spec §8.12.8's charging, activation and refill subsections written in this cut; evidence-index rows for T10–T12 | `tests/SmpCbsSuite.lean`, `tests/fixtures/`, `scripts/test_tier3_invariant_surface.sh`, `docs/spec/SELE4N_SPEC.md`, `docs/CLAIM_EVIDENCE_INDEX.md` | M |

**Acceptance**: `timerTickOnCore_preserves_perCoreCbsInvariant`, the
structural family and the SM8.B tick lift elaborate over the new body in the
cut that lands it; T11 is stated over an arbitrary subtree, not a fixed depth;
every activation caller's footprint carries its size and ordering lemmas under
the new bound in the cut that adds the writes; every pre-existing fixture
byte-identical to the post-CB1 baseline; S6 passes as written.

### CB5 — Hierarchy transitions, proven before they are reachable

Every new transition here is a production definition with no caller until
CB6, with the exceptions the rows name: CB5.2 changes live admission — per
core instead of global — and so lands **with** every existing transition
that can carry a reservation onto another core, since per-core admission is
false the instant one of them runs unchecked; and CB5.5–CB5.11 change live
transitions on branches no reachable state takes yet, so each re-elaborates
the preservation surface it touches in its own row.  The affinity refusal in CB5.8 lands before
CB5.13 because the cross-subsystem bridge for affinity is false without it.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| CB5.1 | `schedContextConfigureServer vScId core` per its §4.8 table — a quiescent parentless leaf, rule (a) resetting budget, window and both refill representations, root admission on `core` (consumes CB2.3, CB2.5) | `SeLe4n/Kernel/SchedContext/HierarchyOperations.lean` (new) | M |
| CB5.2 | Per-core root admission **with every reservation move and every departure** (§4.6; D6, D18, D23) — CB2.3's definitions go live: the `residual` rules — recorded by unbind of a root leaf, an affinity move, a donation's return, a shrink and a link under a server, expiring at its deadline, coalescing on the same core and deadline, confining re-homing to its core and refusing retype and a second departure while live — with T20; `schedContextConfigure` and `schedContextBind` route through them (a root leaf is admitted on its thread's core at bind, `.resourceExhausted` becoming a bind refusal); `setThreadCpuAffinityWithMigration` admits a root leaf's thread on the destination core before migrating; the three donation composites gain `donationAdmissible?`'s admission half — a cross-core donation of a root leaf is admitted on the donee's core, charged on both until the return and as a residual on the donee's core after it, refused with `.resourceExhausted` otherwise — with the `.call` chain's staged surface and the production reply surface re-proved over the guard's frame and refusal arms; **in the same row as** T13's preservation by every move and every departure (its pure form landed in CB2.5); S10 and S15; negative-suite and trace-fixture updates with rationale (an intended move: a Call that would over-admit a core now fails) (consumes CB2.3) | `SeLe4n/Kernel/SchedContext/Operations.lean`, `SeLe4n/Kernel/SchedContext/Budget.lean`, `SeLe4n/Kernel/Scheduler/Operations/Core.lean`, `SeLe4n/Kernel/IPC/Operations/Donation/Primitives.lean`, `SeLe4n/Kernel/IPC/Operations/Endpoint.lean`, `SeLe4n/Kernel/IPC/CrossCore/EndpointCallInvariant.lean`, `SeLe4n/Kernel/IPC/CrossCore/EndpointReplyInvariant.lean`, `tests/NegativeStateSuite.lean`, `tests/SmpCbsSuite.lean`, `tests/fixtures/` | XL |
| CB5.3 | `schedContextBindServer vServer vChild` per its §4.8 table: the check list in order, the `pathLength?` depth rule, the refusal of a child leaf whose binding is mid-donation, the bidirectional link, `linkActivity` on the child, the reschedule (consumes CB5.2) | `SeLe4n/Kernel/SchedContext/HierarchyOperations.lean` | L |
| CB5.4 | `schedContextUnbindServer vChild` per its §4.8 table — the root check whenever the detached child will count on its core, active or not; `unlinkActivity` before the edge goes; rule (g) for a detached unbound leaf; the reschedule (consumes CB5.2) | `SeLe4n/Kernel/SchedContext/HierarchyOperations.lean` | M |
| CB5.5 | Hierarchy-aware `schedContextBind` (§4.8): refuses a server target; checks the thread's home core against the ancestor's `serverCore`; the bound thread's activity enters the ancestors' counts through `syncLeafActivity`; `scThreadIndex` unchanged; the existing bind surface re-elaborated in the row (consumes CB4.4) | `SeLe4n/Kernel/SchedContext/Operations.lean` | M |
| CB5.6 | Hierarchy-aware `schedContextConfigure` (§4.8; D17): member admission against the parent, root admission per core, and a populated server's existing member sum against its new reservation (`.resourceExhausted`, S13); rule (f) through `cbsReconfigure` on a populated server; a `domain` change refused on any context with a parent or members (`.illegalState`, the CB0.3 refusal's two missing shapes); priority changes re-bucket nothing beyond the AK2-B mirror; `schedContextConfigure_domain_fixed_of_linked`; the existing configure surface re-elaborated in the row (consumes CB5.2) | `SeLe4n/Kernel/SchedContext/Operations.lean` | M |
| CB5.7 | `schedContextUnbind` on a member leaf: today's effect plus `syncLeafActivity` (the ancestors' counts through the walk if the leaf was eligible-active); a member leaf keeps its refill (it is still homed) and records no residual (it never counted as a root); `schedContextUnbindOnCore` follows; the existing unbind surface re-elaborated in the row | `SeLe4n/Kernel/SchedContext/Operations.lean`, `SeLe4n/Kernel/SchedContext/OperationsPerCore.lean` | S |
| CB5.8 | `setThreadCpuAffinityWithMigration` refuses a member thread — the thread's own binding or its ownership of an in-flight donation, resolved through the leaf's `scThreadIndex` entry (§4.8) — with `.illegalState` before any write; `setThreadCpuAffinityWithMigration_rejects_member`, `setThreadCpuAffinityWithMigration_rejects_member_owner`; the affinity surface re-elaborated in the row | `SeLe4n/Kernel/Scheduler/Operations/Core.lean` | S |
| CB5.9 | `setPriorityOp` on a member thread changes its tie-break under the caller's MCP and nothing else: `setPriorityOp_member_preserves_schedHierarchyInvariant`; `setMCPriorityOp` unchanged | `SeLe4n/Kernel/SchedContext/PriorityManagement.lean` | S |
| CB5.10 | Donation of a member (§4.8): `donationAdmissible?` refuses a member leaf whose `serverCore` differs from the donee's home core (`.illegalState`); the three donation composites and the return donation call `syncLeafActivity` after the rebind — the donor's departure and the receiver's arrival one activity transfer under the ancestors' locks — and end with `keyRescheduleOnCore` on the receiving thread's core (the flat-model half of both landed in CB1.7 and CB4.4; this row is the member case and its `schedHierarchyInvariant` preservation); the replenish migration inside the composites is a definitional no-op for members (`member_donation_same_core`); `applyCallDonationOnCore_preserves_schedHierarchyInvariant` and its reply and replyRecv twins; the `.call` chain's staged surface re-elaborated over the guard's new arm (consumes CB5.2) | `SeLe4n/Kernel/IPC/Operations/Endpoint.lean`, `SeLe4n/Kernel/IPC/Operations/Donation/Primitives.lean` | M |
| CB5.11 | Lifecycle (§4.8): `lifecyclePreRetypeCleanup` refuses to retype a populated server and unlinks **any** member — a leaf or an empty server — before destruction, applying rule (g); `hierarchyBidirectional` and `activeDescendantsConsistent` preserved under retype; the cleanup surface re-elaborated in the row | `SeLe4n/Kernel/Lifecycle/Operations/Cleanup.lean`, `SeLe4n/Kernel/Lifecycle/Operations/RetypeWrappers.lean` | M |
| CB5.12 | Preservation surface for CB5.1–CB5.11: each transition preserves `schedHierarchyInvariant`, `perCoreCbsInvariant`, `runQueueOnCoreWellFormed`, `queueCurrentConsistentOnCore`, `edfCurrentEarliestOnCore` (through T19 where the transition reschedules), objects `invExt`, `schedContextStoreConsistent`, `schedContextNotDualBound`, `scThreadIndexConsistent` | `SeLe4n/Kernel/SchedContext/Invariant/HierarchyPreservation.lean` (new; staged until the CB6 promotion cut) | XL |
| CB5.13 | `crossSubsystemInvariant` gains `schedHierarchyInvariant` as its thirteenth conjunct **with** `schedHierarchyInvariant_fields`, the pairwise disjointness analysis redone over the full list, the projections, and every existing operation's bridge extended (consumes CB5.8, CB5.12) | `SeLe4n/Kernel/CrossSubsystem.lean` | L |
| CB5.14 | Lock sets for the three transitions per §4.12 — `lockSet_schedContextConfigureServer`, `lockSet_schedContextBindServer`, `lockSet_schedContextUnbindServer`, each composing the home core's replenish-queue slot the rule it reaches writes — with the shape lemmas, `_pairwise_le`, `_size_le_maxLockSetSize` (consumes CB2.2) | `SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean` | M |
| CB5.15 | Frozen twins `frozenSchedContextConfigureServer`, `frozenSchedContextBindServer`, `frozenSchedContextUnbindServer` with their agreement theorems against the live transitions (the coverage-table rows follow once the ids exist, in CB6) | `SeLe4n/Kernel/FrozenOps/Operations.lean`, `SeLe4n/Kernel/FrozenOps/Agreement.lean` | M |
| CB5.16 | Tier-2 negative pins for every refusal arm in the §4.8 tables through a thin-dispatcher sub-helper `runHierarchyRefusalChecks`; Tier-3 anchors for the CB5 surface | `tests/NegativeStateSuite.lean`, `scripts/test_tier3_invariant_surface.sh` | M |

**Acceptance**: every CB5 transition has its row in CB5.12's surface;
`crossSubsystemInvariant` has thirteen conjuncts **and** thirteen field-sets;
every §4.8 refusal has a pin; T13 is preserved by every reservation move; no
live path reaches the three new transitions yet (the dispatcher's
wildcard-unreachable theorems are unchanged until CB6).

### CB6 — The syscalls, live

The hierarchy becomes reachable at CB6.6, where the dispatchers gain their
arms.  Everything a reachable arm needs — its checked form, its
`ipcInvariantFull`, projection and taint theorems, the label invariant's
chokepoint proofs — lands **inert** in CB6.3–CB6.5 as theorems about arm
bodies no dispatcher calls yet, so the activation cut wires, composes and
documents, and proves nothing new about a transition.  The two
capability-only arms live in the shared helper, which both dispatchers run
first, so their activation is the same cut as the checked arms'.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| CB6.1 | The ids on **both** sides per §4.9: Lean variants `.schedContextConfigureServer` (35), `.schedContextBindServer` (36), `.schedContextUnbindServer` (37) with `toNat`, `ofNat?`, `count := 38`, `ToString`; the `DecodingSuite` boundary moves to 37/38; the Rust `sele4n-types` variants, `COUNT = 38`, `from_u64`, `required_right` and discriminant tests; the HAL hand mirror with `min_inline_args` (1, 1, 0) and its two mirror tests — the HAL's prefilter refuses unknown ids before Lean runs, so the tables may never disagree in a shipped cut; `test_aarch64_cross_build.sh` green; **in the same row as** the total-table sweep of §4.9 — every function over `SyscallId` given the value that is **true of an id the dispatcher still refuses** (§4.9's placeholder rule) — and the SM9 pin `capFaultReceivePhase?_none_iff_records` restated over the wider inductive, since the extended inductive fails elaboration until every exhaustive function has its arms and the cut cannot build without them (consumes CB5.15) | `SeLe4n/Model/Object/Types.lean`, `tests/DecodingSuite.lean`, `rust/sele4n-types/src/syscall.rs`, `rust/sele4n-hal/src/svc_dispatch.rs`, `SeLe4n/Kernel/API.lean`, `SeLe4n/Kernel/Architecture/SyscallReturn.lean`, `SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean`, `SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean`, `SeLe4n/Kernel/InformationFlow/TaintPropagation.lean`, `SeLe4n/Kernel/InformationFlow/RefusalRecord.lean`, `SeLe4n/Kernel/FrozenOps/Operations.lean`, `SeLe4n/Kernel/FrozenOps/Agreement.lean`, `SeLe4n/Kernel/Concurrency/Locks/LockSetForSyscall.lean`, `SeLe4n/Platform/FFI.lean` | L |
| CB6.2 | Arg structures and decoders per §4.9 with encoders, `_roundtrip` and `_error_iff` theorems; the `sele4n-abi` argument structs (`encode` / `decode` with their register counts, the `0`-only `deadline` documented) so the register layout is fixed on both sides before any arm exists; `test_aarch64_cross_build.sh` green, since `sele4n-hal` depends on `sele4n-abi` | `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean`, `rust/sele4n-abi/src/args/sched_context.rs` | M |
| CB6.3 | **Inert.** The arm bodies as named functions no dispatcher calls yet: `dispatchConfigureServerArm` (cap target = the SchedContext), `dispatchBindServerArm` (cap = the server; the child CPtr resolved through the caller's CSpace with `.write` by `syscallLookupCap`, the `tcbBindNotification` pattern), `dispatchUnbindServerArm` (cap = the child), each through an `…OnCore` form; the checked forms `schedContextBindServerChecked` and `schedContextBindChecked` (§4.13) with `checkedDispatch_bindServer_eq_unchecked_when_allowed`, `checkedDispatch_schedContextBind_eq_unchecked_when_allowed` and the two capability-only `checkedDispatch_*_eq_unchecked` equivalences; the idle chokepoint `bindServerArm_idle_refused` (the child resolves through `syscallResolveCap`, which refuses a reserved idle object; the core operand is not an object id) (consumes CB6.1, CB6.2) | `SeLe4n/Kernel/API.lean`, `SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean` | L |
| CB6.4 | **Inert.** The per-arm IPC and information-flow surface over those bodies: `…_preserves_ipcInvariantFull` for each arm (frames on every conjunct — no IPC state moves), `…_preserves_projection` for every observer and `…_confinedToCores` in the SM8 style, the per-arm taint family (control-only in `contentFlowClass`); and the donation guard's label half — `donationAdmissible?` refusing a member leaf's donation to a donee whose label is not the server's — inside the three donation composites, a live change whose frame lemma, refusal arm and composition into the `.call` payoff land in this row (consumes CB6.3) | `SeLe4n/Kernel/IPC/Invariant/DispatchArmPreservation.lean`, `SeLe4n/Kernel/IPC/Invariant/DispatchPayoff.lean`, `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean`, `SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean`, `SeLe4n/Kernel/InformationFlow/TaintPropagation.lean`, `SeLe4n/Kernel/IPC/Operations/Donation/Primitives.lean` | L |
| CB6.5 | **Inert.** The label invariant's chokepoints (§4.13): `schedContextBindServerChecked_establishes_uniformLabels`, `schedContextBindChecked_preserves_uniformLabels`, `donationAdmissible_preserves_uniformLabels`, framing by every other transition, and `no_cross_label_server_membership` — the intra-server budget channel closed by construction (consumes CB6.4) | `SeLe4n/Kernel/InformationFlow/Invariant/Helpers.lean`, `SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean` | M |
| CB6.6 | **Activation cut**: the dispatchers gain the arms — `.schedContextConfigureServer` and `.schedContextUnbindServer` in `dispatchCapabilityOnly`, `.schedContextBindServer`'s bare arm in `dispatchWithCap`'s fall-through with `.schedContextBind`'s bare arm moved beside it, and the two checked arms in `dispatchWithCapChecked`'s fall-through (§4.9); the `enforcementBoundary` rows (`.schedContextBindServer` policy-gated, `.schedContextBind` **moved** to policy-gated) with `enforcementBoundary_is_complete` and the per-core name table re-proved; the wildcard-unreachable proofs restated; the dispatcher-level payoff composed from CB6.4's per-arm theorems — the production `dispatchCapabilityOnly_preserves_ipcInvariantFull` over the two capability-only arms, the staged `dispatchWithCap_preserves_ipcInvariantFull` / `dispatchWithCapChecked_preserves_ipcInvariantFull` over the bind arms; `capabilityDispatchQuiescence` needs no new field, stated as a theorem; the routing gate green; **in the same row as** the specification of the live ABI — spec §8.12.8's syscall, refusal, admission and label subsections, the spec's syscall table, `docs/CLAIM_EVIDENCE_INDEX.md` rows for the three arms and the moved row — and **every pin of what this cut makes reachable**: `SyscallReturnAbiSuite` cases for the three `.unit` frames, `SyscallDispatchSuite` discriminant pins for the new refusal arms and the moved `.schedContextBind` arm, `AbiRoundtripSuite` cases for the two decoders and the `0`-only deadline, scenario S7 through `syscallDispatchFromAbi` in the new Tier-2 suite with golden fixture `tests/fixtures/hierarchical_server_syscalls.expected`, the scenario-registry entries `[HCB-nnn]`, and the `NegativeStateSuite` pins for each error arm through the dispatcher — since this is the cut that makes them reachable, and a reachable arm without its pin is the sequencing defect this plan's §7 rule exists to refuse (consumes CB6.3, CB6.4, CB6.5) | `SeLe4n/Kernel/API.lean`, `SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean`, `SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean`, `SeLe4n/Kernel/IPC/Invariant/DispatchArmPreservation.lean`, `SeLe4n/Kernel/IPC/Invariant/DispatchPayoff.lean`, `docs/spec/SELE4N_SPEC.md`, `docs/CLAIM_EVIDENCE_INDEX.md`, `tests/SyscallReturnAbiSuite.lean`, `tests/SyscallDispatchSuite.lean`, `tests/AbiRoundtripSuite.lean`, `tests/HierarchicalServerSuite.lean`, `tests/NegativeStateSuite.lean`, `lakefile.toml`, `scripts/test_tier2_negative.sh`, `tests/fixtures/scenario_registry.yaml` | XL |
| CB6.7 | Userspace convenience per §4.9: the `sele4n-sys` wrappers with their docs and the conformance `verify_regs` cases — the ABI is already invocable through `invoke_syscall` with CB6.1's ids and CB6.2's encoders, so this row adds no reachability; `test_rust.sh` and `test_aarch64_cross_build.sh` green (consumes CB6.1, CB6.2) | `rust/sele4n-sys/src/sched_context.rs`, `rust/sele4n-abi/tests/conformance.rs` | S |
| CB6.8 | ABI version decision recorded on all three sides (§3.2): `SYSCALL_ABI_VERSION` stays `3`, with a conformance pin that every prior discriminant encodes as before | `rust/sele4n-abi/tests/conformance.rs`, `SeLe4n/Kernel/Architecture/SyscallReturn.lean` | S |
| CB6.9 | Staging promotion (§4.14): the staged theorem modules enter the `SeLe4n.lean` closure through their production consumers; allowlist entries removed and `STATUS: staged` markers replaced in the same cut; the partition gate passes in both directions (consumes CB6.6) | `SeLe4n.lean`, `SeLe4n/Platform/Staged.lean`, `scripts/staged_module_allowlist.txt` | S |

**Acceptance**: the Lean and Rust id tables agree under the existing mirror
tests from CB6.1 on; the routing gate reports zero exceptions; both dispatch
payoffs elaborate over 38 arms; every checked arm has its
equivalence-when-allowed theorem; no theorem about a transition is first
stated in CB6.6, and no arm is reachable in a release without its dispatch,
return-shape and end-to-end pins; the spec describes every arm the checked
dispatcher reaches; S7 is byte-verified in-suite.

### CB7 — The CBS guarantee, and the registers

The information-flow surface the hierarchy needs — the label invariant, its
chokepoints, the tick's non-interference lift, the per-arm projection and
taint theorems — landed ahead of the transitions it covers (CB2.8, CB4.3,
CB6.4, CB6.5).  What remains is the liveness result and the two registers.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| CB7.1 | Registers: the intra-server budget channel recorded as closed by construction (CB6.5's `no_cross_label_server_membership`) beside SM8.D's root ordering-channel bound, which CB1.7 re-derived for deadline order; `UncoveredLockDomain`'s completeness theorem re-proved — servers add no lock domain (the SchedContext kind and the per-core replenish queue cover them) — and `SchedLockId` unchanged, stated as a pin | `SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean`, `SeLe4n/Kernel/InformationFlow/FineLockFlow.lean` | S |
| CB7.2 | The CBS guarantee for roots (§4.11 T14–T16): `cbs_demand_bound` over contained windows, `edf_selects_earliest_eligible` and `root_receives_budget_within_window` with hypotheses H1–H8 named — eligibility from the window's release, the entity stable inside it — over a per-core step relation defined for it; the composition lands closed, or as the externalized `edfBusyIntervalLemma` (H9) with its exact statement and the closure registered in §12 (consumes CB1.9, CB3.4, CB4.6) | `SeLe4n/Kernel/Scheduler/Liveness/EdfGuarantee.lean` (new), `SeLe4n/Kernel/Scheduler/Operations/PerCoreWcrt.lean` | XL |
| CB7.3 | Tier-2 scenarios S8 and S11 (§4.15) in the information-flow and CBS suites; Tier-3 anchors for CB6 and CB7; spec §8.14 gains the CBS guarantee with its hypotheses and its scope (roots; D19), in this cut; evidence-index rows for T14–T16 | `tests/SmpInformationFlowSuite.lean`, `tests/SmpCbsSuite.lean`, `scripts/test_tier3_invariant_surface.sh`, `docs/spec/SELE4N_SPEC.md`, `docs/CLAIM_EVIDENCE_INDEX.md` | M |

**Acceptance**: the SM8.B per-core non-interference capstone elaborates over
the hierarchical tick with `serverMembersUniformlyLabeled` as its only new
hypothesis, and did so from CB4.3; T14 states every hypothesis it uses, and
if `edfBusyIntervalLemma` is among them the register carries its closure
target; S8 and S11 pass as written.

### CB8 — Closure

The workstream stays **IN FLIGHT** through CB8.7; CB8.8 flips every canonical
status site in one cut, so no release reports a closed workstream while a
closure row is still open.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| CB8.1 | Specification **verification**: every sentence of §8.12.8, §8.13 and §8.14 — written by the cuts that made each behaviour live (CB1.6–CB1.8, CB3.7, CB4.7, CB6.6, CB7.3) — is checked against the tree for a theorem or a fixture that pins it, and the evidence index for a row that cites it; no new normative prose is added here | `docs/spec/SELE4N_SPEC.md`, `docs/CLAIM_EVIDENCE_INDEX.md` | M |
| CB8.2 | Theorem inventory `hierarchicalServerTheorems` with its nodup witnesses, and the census extended so a workstream inventory can be **claimed**: a workstream-keyed manifest beside the SMP phase manifest, read by the generator, so an unclaimed inventory still fails Tier 0 | `SeLe4n/Kernel/SchedContext/HierarchyInventory.lean` (new), `SeLe4n/Kernel/Concurrency/PhaseTheoremManifest.lean`, `scripts/generate_smp_theorem_manifest.py` | M |
| CB8.3 | Hardware spot-check script in the `test_qemu_smp_cbs.sh` shape — skips until SM10.1's image carries the driver and lists its formal stand-ins in the header | `scripts/test_qemu_hierarchical_servers.sh`, `scripts/test_tier4_smp_bootcheck.sh` | S |
| CB8.4 | `CLAUDE.md`/`AGENTS.md`: standing-constraint bullets (the root is EDF-first with kernel-owned window deadlines and per-window refills; reconfiguration never mints; every reservation move re-admits; member affinity fixed; off-core member donation refused; deadline inheritance reaches bound blockers only; enforcement tick-quantised); the large-files snapshot refreshed.  The status row is **not** touched here | `CLAUDE.md`, `AGENTS.md` | S |
| CB8.5 | Debt register: the §12 follow-ups registered with owners and closure targets.  The WS-CB rows stay open here | `docs/REGISTERED_DEBT.md` | S |
| CB8.6 | README metrics sync and the GitBook roadmap row; `docs/codebase_map.json` regenerated; `docs/DEVELOPMENT.md` where a tier gained a suite | `README.md`, `docs/gitbook/05-specification-and-roadmap.md`, `docs/codebase_map.json`, `docs/DEVELOPMENT.md` | S |
| CB8.7 | Full validation sweep — `test_full.sh`, `test_rust.sh`, `test_aarch64_cross_build.sh`, `test_docs_sync.sh` — recorded in the CHANGELOG entry of this cut | `CHANGELOG.md` | S |
| CB8.8 | **The status flip**, every canonical site in one cut: this plan's phase map to LANDED with versions and its status line to CLOSED; the registry row's span closed and the debt-register rows closed with versions; the `CLAUDE.md`/`AGENTS.md` status subsection and its row; the CHANGELOG closure entry; the hand-off note to SM10 (what §8.12.8 adds to SM10.2's documentation sweep and what CB8.3's script adds to SM10.3's hardware validation list) | this plan, `docs/REGISTERED_DEBT.md`, `CLAUDE.md`, `AGENTS.md`, `CHANGELOG.md`, `docs/planning/SMP_RELEASE_CLOSURE_PLAN.md` | S |

**Acceptance**: every row of the phase map reports LANDED with a version; the
plan gate, the naming gate and the docs-sync lane pass on the closing cut;
no status site reads CLOSED before CB8.8.

## 8. Verification strategy

### 8.1 Per PR

* `lake build <Module>` for every touched module (the pre-commit hook), then
  `./scripts/test_smoke.sh`; `./scripts/test_full.sh` whenever a theorem or a
  Tier-3 anchor moves — which is every phase from CB1 on.
* `./scripts/test_aarch64_cross_build.sh` after any change under `rust/`
  (CB0.5, CB6.1, CB6.2, CB6.7, CB6.8) — `sele4n-hal` depends on `sele4n-abi`,
  so the argument-struct cut is a kernel-target change like the id cut.
* Stage before running Tier 0: the plan gate and the naming gate read the
  index.
* Before opening the PR for a row, walk the five questions of §7's preamble
  against the diff: builds alone; every theorem over a changed live
  definition re-proved; every newly reachable behaviour specified and pinned;
  every total table true of the tree as it is; every new write in a
  footprint.  A row that fails one is two rows, or one row merged with the
  next — never a row that ships and a row that catches up.

### 8.2 The equivalence discipline

CB1.6 changes the refill schedule and lands with T3–T5, T17 and the inverted
refill witness; CB1.7 changes the root order and lands with T2 and the
inverted order witness; CB1.8 changes a boosted holder's key and lands with
T7.  Each of the three carries its own fixture refresh, each fixture with its
rationale.  From then on CB3.6, CB4.3 and CB4.4 change live selection, charging and activation,
and each lands with the theorem that on a state whose contexts are all
parentless the new definition equals the CB1 one (T9, T10), with
`./scripts/test_tier2_trace.sh` reporting every `.expected` sha256 unchanged
from the post-CB1 baseline.  A fixture that moves in CB2–CB4 is a defect in the
cut, not a fixture to refresh; the intended moves are CB0.3's (the configure
authority gate), CB1.6's, CB1.7's and CB1.8's (the engine, the order,
inheritance), and CB5.2's (per-core admission and the reservation moves it
re-checks), plus the new fixtures CB4.7, CB6.6 and CB7.3 add.

### 8.3 What each phase proves

| Phase | Proof obligation discharged |
|-------|-----------------------------|
| CB1 | T1–T8, T17, T19: the EDF-first order is strict; the selector is total, optimal, and equal to the old one on deadline-less states; the engine rules preserve `wellFormed`; a window consumes at most its budget; dead time is at most a period; reconfiguration never mints; every key move restores the current's maximality; inversion is bounded in deadline terms for bound blockers |
| CB2 | `schedHierarchyInvariant` holds of the default and boot states; the engine rules frame the hierarchy fields |
| CB3 | T1 on paths, T9, T16 in selection form, T18 |
| CB4 | T10–T12; the tick preserves every structural and CBS invariant over path charging and activation; the SM8.B tick lift holds under uniform labels; every activation caller's footprint is bounded |
| CB5 | T13 and its preservation by every reservation move; every hierarchy transition preserves the per-core, CBS, hierarchy and cross-subsystem bundles; every refusal is explicit |
| CB6 | the dispatcher stays total over 38 ids; `ipcInvariantFull` survives every new arm and the donation guard; the Lean and Rust tables agree; every checked arm equals its bare arm when the policy permits; every theorem about an arm precedes its wiring |
| CB7 | T14–T16 for roots; the registers closed |

### 8.4 What each phase validates

Tier 2: `smp_cbs_suite` (S0–S3, S4b, S5, S6, S8–S12, S14), `PriorityInheritanceSuite`
(S4), the new `hierarchical_server_suite` (S7), `NegativeStateSuite` (CB0.3,
CB1.4, CB5.2, CB5.6 with S13, CB5.16, CB6.6), `SmpInformationFlowSuite` (S8, S11), the
decode and ABI suites (CB6.1, CB6.6), and every refreshed golden (CB1.6,
CB1.7, CB1.8, CB5.2).  Tier 3: anchors per phase.  Tier 4: CB8.3's script, a
skip until SM10.1 produces an image.

## 9. Risk inventory

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| CB1's three switch cuts are each large, and a refreshed fixture can hide a defect behind a "policy change" rationale | HIGH | MED | Five inert rows shrink each switch to its irreducible core; CB0.4's witnesses pin the old order and the old refill and are inverted deliberately; each refreshed fixture's rationale names the thread whose refill, position or inherited deadline moved; T2 shows nothing else moved |
| The engine switch (CB1.6) touches both ticks, the drain, yield, configure, unbind and the Z2 proof family at once | HIGH | MED | The six rules are pure functions on one `SchedContext` with their own T3 lemmas landed inert in CB1.2; the ticks call them; the CBS preservation family is re-proved by the rules' lemmas plus the existing frames |
| The inheritance switch (CB1.8) is larger than estimated across the per-core and cross-core PIP surface | HIGH | MED | The priority boost is kept, not removed, so the change is additive; the donation-preservation family is re-proved by frame where the new field is untouched; the field and its readers land inert in CB1.5 |
| The `activeDescendants` counter needs maintenance at every runnability transition (CB4.4) and one is missed | MED | HIGH | `activeDescendantsConsistent` is a cross-subsystem conjunct from CB5.13, so a missed site fails a bridge proof, not a review; the bounded subtree scan is the recorded fallback |
| The activation footprints (CB4.4) push the widest lock set past `maxLockSetSize` | CERTAIN | MED | Measured at planning time: `lockSet_tcbSuspend` is eight at its widest, the ancestors add two; the constant moves to ten (D21) with the WCRT terms re-derived, rather than a lock taken outside the set |
| The donation guard (CB5.2, CB6.4) adds a refusal arm to the live `.call` chain, whose invariant surface is staged and large | HIGH | MED | The guard writes nothing (one frame lemma) and refuses before the rendezvous commits, so every existing `.call` theorem transfers under the guard's `none` arm; the refusal arm is one new case per composite |
| The CBS guarantee's composition (CB7.2) does not close within its row | HIGH | MED | T15 and T16 land regardless; the composition lands as `edfBusyIntervalLemma` with its exact statement and a registered closure, stated conditionally — the `hBandProgress` precedent — never as a restatement of the conclusion |
| The tick switch (CB4.3) is larger than estimated, since it carries the tick family and the observer lift | HIGH | MED | T10 reduces most cases to the CB1 proof; the fold's frames and footprint (CB4.1) are proved once; the row cannot split without leaving a live tick uncovered, so it is sized XL and lands whole |
| Selection by scan costs `O(runnable · depth)` per decision where the bucket-first path cost `O(bucket)` | MED | LOW | The lock-wait WCRT theorems are unaffected; the deadline-ordered index is a registered follow-up proven equal to the scan |
| Per-core admission (CB5.2) changes existing refusals — more admits per core, and a new refusal on a Call or an affinity change that would over-admit a core | MED | LOW | Enumerate the affected fixtures at CB5.2, refresh with rationale; no flat theorem depends on the global sum; S10 pins both refusals |
| A deployment relies on a member's own period as a deadline guarantee that D19 does not give | MED | MED | The spec states the guarantee's scope (roots) and the member semantics (isolation and bandwidth) in the same cut that lands each; Q10 offers the two designs that would extend it |
| The path order admits a tie the proofs cannot break | LOW | HIGH | §4.3's rule is one mechanism per class — `scId` in the EDF class, the incumbent in the legacy class — and T1 is proved on keys in CB1.1 and on paths in CB3.3 before anything relies on the order |
| The receive-side refusal of an off-core or off-label member donation surfaces as an error to a blameless passive server | LOW | MED | Documented in §4.8 and the spec; the follow-up (per-core server replicas) removes the core refusal; S10 and S11 pin the behaviour |
| The workstream inventory cannot be claimed by the SMP-only manifest census | HIGH | LOW | CB8.2 extends the census rather than misfiling the inventory under SM5 |
| Overlap with WS-RR on the scheduler, the CBS engine, `API.lean`, the donation primitives or the flow tables | MED | MED | §2.3's partition; CB1 and CB5 onward wait for a WS-RR cut touching those files to land |

## 10. Acceptance gate

- [ ] Every CB row LANDED with a version in the phase map, flipped together in
      CB8.8.
- [ ] T2, T9 and T10 elaborate with no hypothesis beyond the absence of
      deadlines, respectively of servers.
- [ ] Every §4.10 conjunct of `SchedContext.wellFormed` preserved by every CBS
      rule and every transition; no caller-supplied deadline reaches a
      SchedContext; a window never receives budget before it ends (T4); no
      reconfiguration mints budget (T17); the two refill representations
      mirror each other on every core.
- [ ] `edfCurrentEarliestOnCore` preserved by every per-core transition and
      restored by every key-moving transition (T19).
- [ ] T11 and T12 stated over arbitrary subtrees within `maxServerDepth`,
      with the depth counting the leaf.
- [ ] `crossSubsystemInvariant` has thirteen conjuncts and thirteen field-sets.
- [ ] T13 preserved by every reservation move: configure, bind, bindServer,
      unbindServer, configureServer, the affinity migration, the cross-core
      donation and its return.
- [ ] Both dispatch payoffs elaborate over 38 ids; the routing gate reports
      zero exceptions; `SyscallId::COUNT` agrees on both sides; the
      policy-gated bind arms live in the fall-through positions of both
      dispatchers.
- [ ] The SM8.B per-core non-interference capstone holds over the hierarchical
      tick under `serverMembersUniformlyLabeled` stated over bindings, with
      its three chokepoints proved before the activation cut.
- [ ] T14 states every hypothesis it uses and is scoped to roots; T7 is stated
      over deadlines for bound blockers and is not vacuous; T18 states the
      dispatch effect's scope.
- [ ] Every activation caller's lock footprint carries its size and ordering
      lemmas under the moved bound.
- [ ] Every pre-existing `.expected` unchanged except CB0.3's, CB1.6's,
      CB1.7's, CB1.8's and CB5.2's, each refreshed with rationale; three new
      fixtures byte-verified; S0–S11 pass as written in §4.15.
- [ ] Zero `sorry`, zero axioms; Tier 0, docs-sync, Tier 3 and the cross build
      green on the closing cut.
- [ ] Follow-ups (§12) registered with owners.

## 11. Questions for the maintainer

Decided at planning time: **EDF-first root** (D3, D13–D15), per-window refills
(D16), reconfiguration under the density rule (D17), core-stable reservations
(D18), the guarantee's scope (D19), inheritance into bound blockers only
(D20), core-homed servers, label uniformity over bindings, the depth and
member bounds, off-core donation refused, leaf-only timeouts.  Each remaining
question has a default the plan is written against; changing one changes the
rows named.

| # | Question | Default | If changed |
|---|----------|---------|------------|
| Q1 | Implicit deadlines only (`D = P`), the configure `deadline` argument `0`-only? | Yes (D13) | Constrained deadlines `D < P` need a density-based admission test in CB5.2 and a different T14 in CB7.2 |
| Q2 | Per-window refills (hard CBS), rather than per-consumed-chunk refills? | Yes (D16) | Per-chunk refills need consumption tracking and refill coalescing under the 8-entry bound in CB1.2/CB1.6, and change T4/T5 and T14's demand argument |
| Q3 | Deadline inheritance stays within a member's server (no bandwidth inheritance)? | Yes (D15) | Lifting the server's deadline for a client in another server is bandwidth inheritance; CB4 and CB7.2 change shape |
| Q4 | Selection by scan now, the deadline-ordered index later? | Yes (D2) | An index in CB1 adds a per-core structure with its consistency invariant to every transition in CB1.7 and CB4.3 |
| Q5 | Open after WS-RR, or beside RR6–RR8 under §2.3's partition? | After | CB1 may start once RR7 is quiet in the scheduler and the CBS engine; CB5 onward waits for `API.lean` and the donation primitives |
| Q6 | Land CB0.3 as the next cut, ahead of the workstream — and the engine switch (CB1.2 then CB1.6, the refill defect) as the ones after? | Yes to both | The authority gap and the starvation defect stay open until the workstream opens |
| Q7 | Retire `schedContextYieldTo` in the engine switch (CB1.6), as the plan now schedules? | Retire | Keeping it means redesigning it as an engine rule — the source takes rule (c), the target an activation-shaped credit that respects its window and its pending refill — with its own T3 lemmas and a consumer, since nothing but four harness probes calls it today; as it stands it writes `budgetRemaining` on two contexts outside every rule and would falsify `pendingRefillOnlyWhenExhausted` and T4 |
| Q8 | Remove `TCB.deadline` in CB1.4 rather than keep it as a dead field? | Remove | Keeping it means a proof that selection never reads it, renewed at every selector change |
| Q9 | Single-domain mode as T14's hypothesis, the domain-rotating guarantee a follow-up? | Yes | A domain-rotating T14 needs the rotation folded into the demand bound; the RPi5 default is single-domain |
| Q10 | Members get isolation and bandwidth only (D19) — or server-aligned member windows (`P_member = P_server`, one window per tree, the member guarantee falling out of T14 and T12), or a supply-bound admission test (`dbf ≤ sbf` over the periodic-resource model) with its compositional theorem? | Isolation and bandwidth, both alternatives registered | Aligned windows change §4.2 (a member's window is its server's, refilled by the server's landing), §4.6 (`Σ Q_member ≤ Q_server`) and CB4/CB7; the supply-bound test adds a bounded arithmetic check to CB5.2 and a theorem larger than T14 to CB7.2 |
| Q11 | A cross-core donation of a root leaf is admitted on the donee's core and refused with `.resourceExhausted` when the core is full (D18) — or refused whenever it crosses cores? | Admit on the destination | Refusing every cross-core donation makes cross-core passive servers unusable, which the tree supports today with proofs; it removes the double count and the guard's admission half from CB5.2 |
| Q13 | Between the id cut (CB6.1) and the activation cut (CB6.6), the total tables carry values true of a refused id — or the two cuts merge? | Placeholders where every gate accepts them, decided by running the gates at CB6.1 | Merging makes one cut of the ids, the sweep, the bodies, their theorems, the wiring and the specification; nothing in the plan's proofs changes, only the size of the PR |
| Q14 | Derive `deadline` from `periodStart + period` and drop the stored field (D22) — or keep the field with `deadlineWindowConsistent` as an invariant? | Derive | Keeping the field keeps one conjunct in `wellFormed`, twelve writers to hold consistent and a class of defect the review rounds found twice in other pairs |
| Q15 | Residual bandwidth until the deadline (D23), with re-homing confined to the residual's core and retype refused while it lives — or `SCHED_DEADLINE`'s exact zero-lag time, or a per-core departure ledger? | The deadline, on the context | The zero-lag time `d − c·P/Q` releases earlier and needs the remaining budget at departure; a per-core ledger frees the context immediately but needs a bounded structure and a tick-side prune; both are refinements of the same rule and change only CB5.2 |
| Q12 | `maxLockSetSize` to `10` (D21) — or `maxServerDepth` to `2`? | `10` | Depth two forbids the root server → server → leaf shape; the constant stays, CB4.4 shrinks to the footprint additions |

## 12. Cross-references and registered follow-ups

* Debt register: [`../REGISTERED_DEBT.md`](../REGISTERED_DEBT.md) — the
  WS-CB rows in the registry and in table C.
* Neighbours: [`SMP_PER_CORE_SCHEDULER_PLAN.md`](SMP_PER_CORE_SCHEDULER_PLAN.md)
  (SM5, the surface changed and generalised), [`SMP_INFORMATION_FLOW_PLAN.md`](SMP_INFORMATION_FLOW_PLAN.md)
  (SM8, the observer and the reschedule seam), [`SMP_RELEASE_READINESS_PLAN.md`](SMP_RELEASE_READINESS_PLAN.md)
  (WS-RR, the partition in §2.3), [`SMP_RELEASE_CLOSURE_PLAN.md`](SMP_RELEASE_CLOSURE_PLAN.md)
  (SM10, CB8.8's hand-off).
* Specification: `docs/spec/SELE4N_SPEC.md` §8.12 (the flat model this
  extends, rewritten by CB1.6 and CB1.7 and completed by CB3.7, CB4.7 and
  CB6.6), §8.13 (priority inheritance, rewritten by CB1.8), §8.14 (the bound
  CB7.3 records for the EDF class).

Follow-ups this plan deliberately leaves for a later workstream, to be
registered by CB8.5 with owners and closure targets: constrained deadlines
(`D < P`, density admission); a per-core deadline-ordered index for selection,
proven equal to the scan; the closure of `edfBusyIntervalLemma` if CB7.2 lands
it externalized; the domain-rotating form of T14; a per-member window
guarantee by either design of Q10; admission with blocking terms so that T14
holds while a deadline inheritance is active (H7 dropped); bandwidth
inheritance — a member's inherited deadline lifting its server, and the
dispatch effect of inheritance across different parents (T18's complement);
server migration between cores (a whole subtree re-homed, refills included);
per-core server replicas so a component may span cores; boot-time server trees
in `PlatformConfig`; a bucketed `MemberList`; sub-tick enforcement through a
one-shot timer seam.

## 13. Theorem catalogue

| Theorem | Phase | Statement |
|---------|-------|-----------|
| `isBetterKey_irrefl`, `_asymm`, `_trans`; `isBetterKey_legacy_class_eq_fp` | CB1 | T1 on keys; deadline-less candidates compare as before |
| `chooseThreadEffectiveOnCore_eq_flat_of_no_deadlines` | CB1 | T2 |
| `wellFormed_preserved_by_cbs_rules` (family) | CB1 | T3 for `cbsWindowStart`, `cbsScheduleRefill`, `cbsLandRefill`, `cbsActivate`, `cbsReconfigure`, `cbsDetach` |
| `window_consumption_le_budget`, `refill_dead_time_le_period`, `cbsLandRefill_drops_stale`, `cbsLandRefill_stale_unreachable_of_mirrored` | CB1 | T4, T5, the stale-entry rule and its unreachability under the mirror |
| `cbsActivate_noop_of_fresh`, `cbsReconfigure_never_mints` | CB1 | T6, T17 |
| `keyRescheduleOnCore_establishes_edfCurrentEarliest` | CB1 | T19 |
| `edfCurrentEarliestOnCore` (preservation family) | CB1 | T8 |
| `pip_bounded_inversion` (restated) | CB1 | T7, for bound blockers |
| `pathLockFootprint_le_maxLockSetSize` | CB2 | the tick's path footprint fits the SM3 bound |
| `default_schedHierarchyInvariant`, `bootFromPlatformCheckedWithIdleThreadsFor_schedHierarchyInvariant` | CB2 | the bundle holds of the default and production boot states |
| `schedPath_equal_keys_advance` | CB2 | equal keys at a position are one shared server, so both paths continue |
| `pathBudgetEligible_eq_hasSufficientBudget_of_root` | CB3 | eligibility is CB1's on a parentless leaf |
| `isBetterPath_irrefl`, `_asymm`, `_trans`; `isBetterPath_singleton_eq_isBetterKey`; `isBetterPath_total_on_distinct_leaves` | CB3 | T1 on paths; the order is CB1's on singleton paths; total on distinct leaves |
| `chooseThreadEffectiveOnCore_eq_flat_of_no_servers` | CB3 | T9 |
| `chooseBestRunnableHierarchical_always_ok`, `_optimal`; `inherited_deadline_dispatch_effective_of_same_parent` | CB3 | totality; T16 in selection form; T18 |
| `timerTickBudgetOnCore_eq_flat_of_root` | CB4 | T10 |
| `chargeSchedPath_charges_every_ancestor`, `server_subtree_consumption_bounded`, `member_isolation` | CB4 | one consumed tick reaches every level; T11; T12 |
| `timerTickOnCore_preserves_perCoreCbsInvariant` (re-proved), `cbsReplenish_server_reschedules_local`, `propagateCrossing_stops_at_first_non_flip`, `syncLeafActivity_idempotent` | CB4 | the CBS bundle survives path charging; a server refill triggers the executing core's reschedule decision; the counter walk is the crossing walk |
| `rootAdmission_sound_per_core` (+ preservation by every reservation move and departure), `residual_covers_departed_demand` | CB5 | T13, T20 |
| `setThreadCpuAffinityWithMigration_rejects_member`, `member_donation_same_core`, `applyCallDonationOnCore_preserves_schedHierarchyInvariant` (+ reply twins), `schedContextConfigure_domain_fixed_of_linked` | CB5 | the affinity refusal; a member's donation never migrates refills; donation keeps the tree well-formed; a linked context's domain is fixed |
| `dispatchWithCap_bindServer_idle_refused`, `checkedDispatch_bindServer_eq_unchecked_when_allowed`, `checkedDispatch_schedContextBind_eq_unchecked_when_allowed`, `dispatchCapabilityOnly_preserves_ipcInvariantFull` (extended) | CB6 | the chokepoint covers the new operand; the flow gates are transparent when they permit; the production payoff over the capability-only arms |
| `schedContextBindServerChecked_establishes_uniformLabels`, `schedContextBindChecked_preserves_uniformLabels`, `donationAdmissible_preserves_uniformLabels`, `chargeSchedPath_confined_to_label`, `no_cross_label_server_membership` | CB7 | the label rule is established and kept by its three chokepoints; path charging writes one label; the intra-server channel is closed by construction |
| `cbs_demand_bound`, `edf_selects_earliest_eligible`, `root_receives_budget_within_window` | CB7 | T15, T16, T14 |

## 14. Refinement-pass record

What the pass over the second cut changed, so a reader of the schedule knows
which rows moved and why:

1. **A defect found, and a decision reversed.**  Reading the tick for the
   refill rules surfaced the one-tick refill (§1.1).  Fixing it (D16)
   made the first cut's wake-up rule — "reset the deadline, keep the budget,
   because chunk refills are owed" — unnecessary: nothing is owed under
   per-window refills, so D14 is now the classical CBS rule.  Q2 changed from
   "which wake rule" to "which refill scheme".
2. **One engine, six rules.**  `cbsUpdateDeadline`, the two tick arms, the
   yield arm and `refillSchedContext` each carried their own reading of when
   a deadline moves; §4.2 replaces them with pure functions the ticks call,
   so the theorems are about the rules and the ticks inherit them.
3. **Per-object, not store-level.**  `atMostOnePendingRefill` and
   `pendingRefillOnlyWhenExhausted` — and, until D22 derived the deadline
   instead of storing it, `deadlineWindowConsistent` — are
   properties of one context, so they joined `SchedContext.wellFormed` and
   ride `schedContextStoreConsistent` and the boot check for free, instead of
   becoming a fourth bundle.  `schedHierarchyInvariant` shrank from nine
   conjuncts to six.
4. **The counter got its chokepoints.**  The first cut asserted
   `activeDescendantsConsistent` without saying where the count moves; §4.5
   names the helpers, the sites that call them, and the fact that the
   cross-subsystem bridge is what makes the enumeration complete.  It also
   found that `removeRunnable` is still `bootCoreId`-pinned, which CB4.5 must
   fix to read the right queue.
5. **Refusals got codes.**  Every check in §4.8 names its `KernelError`; two
   existing variants (`.cyclicDependency`, `.threadOnDifferentCore`) cover the
   cases the first cut left as "refused", so no new variant is added.
6. **Every §4 item is owned.**  Each sub-task row names the §4 subsection it
   implements and, where a theorem is involved, its T-number; the acceptance
   lines name the scenarios that pin them.
7. **Counts.**  `TCB.deadline` removal, previously a question, is the default
   with the question retained (Q8).  The single-domain hypothesis of T14
   became an explicit question (Q9) rather than a footnote.
8. **What the pass did not change.**  The phase order, the core-homing
   decision, the label rule, the constants, the syscall surface and the ABI
   decision all survived re-derivation; the plan gate, the naming gate and the
   docs-sync lane hold the document's structure.
9. **Seven review rounds, fifty-eight findings, one plan.**  The automated
   review of the second through eighth cuts found defects in the *design*, not
   only in the schedule, and each is folded in where it binds rather than
   answered in a thread:

   | Finding | Change |
   |---------|--------|
   | The comparator switch went live before its selector tests and preservation suite | CB1 restructured: five inert rows, then three switch cuts each carrying its proofs (§1.4, §7) |
   | Configuring a running thread's context could worsen its EDF key with no reschedule | `keyRescheduleOnCore` generalises SM8.B's seam and every key-moving transition calls it; T19 (§4.4) |
   | The policy-gated bind, placed in the shared helper, would have bypassed its own checked arm | `.schedContextBindServer` and `.schedContextBind` live in the fall-through arms of both dispatchers (§4.9, CB6.3, CB6.6) |
   | T14 was false without continuous backlog | H5 `continuouslyActive`, and the hypotheses H1–H8 named (§4.11) |
   | Deadline inheritance across roots claimed a dispatch effect it cannot have | T7 over keys for bound blockers; T18 scopes the dispatch effect to a shared parent; the rest is registered (§4.7) |
   | Membership changes touched only the immediate server | the crossing walk (now `propagateCrossing`) climbs the ancestors — and only across zero-crossings, the second round's correction (§4.5) |
   | Converting a used leaf into a server could carry stale budget state | configureServer requires a quiescent parentless leaf and applies rule (a) to both refill representations (§4.8) |
   | A domain change on a server or an unbound member broke `serverDomainConsistent` | refused for any context with a parent or members (CB5.6, §3.3) |
   | CLOSED was written before the closure rows had run | CB8.8 flips every canonical status site in one cut; CB8.4/CB8.5 no longer touch status |
   | The live ABI shipped ahead of its specification | the spec lands in the activation cuts (CB1.6–CB1.8, CB3.7, CB4.7, CB6.6, CB7.3); CB8.1 verifies |
   | The depth bound admitted a fourth context on a path | `pathLength?` counts the leaf; `hierarchyDepthBounded` and the bindServer rule read it (D9, §4.1) |
   | The mixed tie-break (FIFO for leaves, `scId` otherwise) was not transitive | one mechanism per class: `scId` in the EDF class, the incumbent in the legacy class (D3, §4.3) |
   | Detaching a counted-but-idle child skipped the root admission check | unbindServer checks whenever the child will count on its core; `rootCountsOnCore` reads reservations, not activity (§4.6, §4.8) |
   | Label uniformity over SchedContext labels was bypassed by binding a thread | the invariant is over members **and bindings**, with three chokepoints in the checked tier (D8, §4.13) |
   | T15 was false on arbitrary intervals | restated over windows released and due inside the interval, abandoned windows by their consumption (§4.11) |
   | Rule (a) on a live entity let the write capability mint budget on every call | rule (f) clamps and re-activates under the density rule; T17 (D17, §4.2) |
   | Utilisation admission cannot give a nested member its window | T14 scoped to roots; the two member designs registered and put to the maintainer (D19, Q10) |
   | An unbound blocker inheriting a deadline was unaccounted EDF demand | inheritance reaches bound blockers only; H7 for the blocking term (D20, §4.7) |
   | Affinity changes and donations carried a root's utilisation onto other cores unchecked | every reservation move re-admits on the destination, donation charged on both cores until the return, all in CB5.2 with T13's preservation (D18, §4.6) |
   | An empty member server retyped left a dangling `serverMembers` edge | cleanup unlinks any member, leaf or server (§4.8) |
   | Reversion was written as clearing the inherited deadline | it recomputes, as `revertPriorityInheritance` already does through `updatePipBoost` (§4.7) |
   | A deadline-only inheritance change sent no remote SGI | `pipBoostWithWake`'s guard compares the whole key; S4b (§4.4, §4.7) |
   | Activation-path writes had no lock footprint | every activation caller gains the ancestors' locks; `maxLockSetSize` to ten, measured against `lockSet_tcbSuspend` (D21, §4.12, CB4.4) |
   | The exhausted-then-unbound leaf could stall with no refill in flight (found while fixing the two refill representations) | rule (g) clears both on detach, rule (e2) re-arms on activation, and `pendingRefillMirroredOnCore` / `unhomedNoPendingRefill` hold the representations equal (§4.2) |
   | Shrinking a populated server passed admission while its members no longer fit | configure checks the existing member sum against the new reservation (§4.6, CB5.6, S13) |
   | H5 admitted a root whose only leaf was exhausted | `continuouslyEligible`: a runnable descendant with positive budget on every context below the root (§4.11) |
   | T19 claimed maximality on a core whose reschedule SGI had not landed | `reschedulePendingOnCore` records the request; the conjunct is stated modulo the flag; T19 establishes or posts; the handler clears (§4.1, §4.4, §4.10, S14) |
   | T18 failed at an exact deadline-and-priority tie, where the non-inherited `scId` decides | T18 requires strict dominance on deadline or priority; the tie case is excluded, not papered over (§4.7) |
   | Binding a queued unbound thread moved it into the EDF class with no scheduling point | `schedContextBind` ends with `keyRescheduleOnCore` on the queue core (§4.4, §4.8, CB1.7) |
   | Binding an already-active thread skipped the activation rule, since nothing enqueued it | rule (e) fires at bind for a runnable or running thread; the leaf's activity is synced there too (§4.2, §4.5, CB1.6) |
   | The Rust id tables trailed the live Lean arms by two rows, so the ABI was unreachable on hardware in between | the `sele4n-types` variants and the HAL mirror land with the ids (CB6.1), the argument structs with the decoders (CB6.2); CB6.7 keeps only the userspace wrappers (§4.9) |
   | The cross-core IPC paths call `removeRunnableOnCore` directly, so a hook on the boot-pinned wrapper missed every block | the deactivation hook moved to `removeRunnableOnCore` — and, one round later, became the before/after `threadActive` sync (§4.5, CB4.4) |
   | Reconfiguring a donated root checked one of its two charged cores | configure admits on every core in `chargedCoresOf` (§4.6, §4.8) |
   | The activation cut made arms reachable before their payoff, the label chokepoints and the tick's non-interference lift | CB6 takes the inert-then-switch shape: bodies, per-arm theorems and chokepoint proofs in CB6.3–CB6.5, wiring in CB6.6; the tick's lift moved into the tick switch (CB4.3) with the invariant defined at CB2.8 — and the same sweep found CB3 and CB4 in the shape CB1 had been corrected for, so CB3.6, CB4.3 and CB4.4 are switch cuts with inert rows before them (§7) |
   | H5 on a suffix let a leaf that refilled one tick before the deadline satisfy it | `continuouslyEligible` runs from the window's release; T14 is stated per window with the full budget (§4.11) |
   | `schedContextYieldTo` wrote `budgetRemaining` on two contexts outside every rule, starving the source and double-crediting a target with a pending refill | retired in the engine switch with its four harness probes; Q7's default flips (§1.1, §4.2, CB1.6) |
   | A leaf mid-donation could be attached to the donee's core's server and rebound off-core at the reply | bindServer refuses a child whose bound thread holds a `.donated` binding (§4.8, CB5.3) |
   | A donation owner, unbound while it waits, could be moved off-core and rebound to a member leaf at the return | the affinity rule treats the recorded owner of an in-flight donation as bound to that leaf (§4.8, CB5.8) |
   | T14 admitted a window abandoned mid-way by a reconfiguration | H8 `entityStable`: no configure, link, unlink or move of the entity inside the window (§4.11) |
   | A structure or inductive extension and the compiler sweep it forces were separate rows, so neither cut built alone | the field sweep joins CB2.1 and the total-table sweep joins CB6.1, with the placeholder rule for tables over an unwired id (§4.9, §7) |
   | The three hierarchy footprints omitted the replenish-queue slot that rules (a), (e1) and (g) write | every footprint that reaches a purging rule composes `SchedLockId.replenishQueue`, configure's pre-existing gap included (§4.12, CB1.6, CB4.4, CB5.14) |
   | Binding a running thread whose leaf rule (e2) left at zero budget kept it current until the next tick | the bind's reschedule runs on the running core and an ineligible current is preempted at once (§4.2, §4.4, §4.8) |
   | The argument-struct cut edits a crate the HAL depends on but was not on the cross-build list | CB6.2 requires `test_aarch64_cross_build.sh`; §8.1's list names every Rust-touching row |
   | The tick switch could exhaust a server one row before the drain learned to re-arm its descendants | the server-aware refill decision lands in the tick switch (CB4.3) |
   | The deactivation hook keyed on queue membership, so the executing caller `removeRunnableOnCore` clears from `currentOnCore` was never deactivated | one idempotent `syncLeafActivity`, keyed on the before/after `threadActive` predicate (§4.5) |
   | Donation rebinds a leaf to an already-runnable receiver and no activation site saw the new binding | the sync's second trigger set is every binding change — bind, unbind, the donation composites and the return, retype — derived from what the count depends on (§4.5, CB4.4, CB5.10) |
   | Other roots could churn inside the guarantee window while every instantaneous sum held | bandwidth is released at the window's end: a departing share stays counted until its deadline as a `residual` (D23, §4.6, T20, S15) |
   | `chargedCoresOf`'s documented cases omitted a root server | the server case is its `serverCore` singleton (§4.1, §4.6) |
   | Donation gave a receiver woken as legacy a deadline-bearing key with no scheduling point | the key-moving set is derived from the key's inputs, and its binding writers include the donation composites and the return (§4.4, CB1.7) |
   | Unbinding a running thread dropped it to the legacy class with no scheduling point | the same derivation names unbind (§4.4, §4.8, CB1.7) |
   | A server whose only leaf exhausted kept a positive count, so the leaf's later refill re-activated nothing and the server resumed on a stale window | the counter tracks **eligible** activity — budget and work below, one predicate at **every** node, since a nested server is throttled by its budget exactly as a leaf is — and every budget crossing on the charged path is a sync trigger; the walk never re-arms the node it starts from, which the leaf-level sync had done twice (§4.5, §4.10, D4) |
   | One optional residual could be overwritten by a second departure inside one window | one slot is made exact: a second departure coalesces on the same core and deadline or is refused until the first expires (§4.1, §4.6, D23) |
   | The crossing walk was called on the linked child with a delta, taking an active leaf from `1` to `2` and never reaching the parent | `propagateCrossing` climbs from a node's crossing to its parent; `linkActivity` / `unlinkActivity` climb from the child's existing count without touching it (§4.5, §4.8) |
   | Rule (e1) purged the replenish queue from the wake and bind paths in CB1.6 while their footprints gained the slot in CB4.4 | the wake and bind footprints take the slot in CB1.6; CB4.4 adds the ancestors' locks only (§4.12) |
   | The activation cut made the arms reachable with their dispatch, return and end-to-end pins two and five rows later | the pins and S7 are in CB6.6; two rows retired (§7) |
   | The bundle's admission conjuncts and configureServer's check consumed definitions scheduled two phases later | the pure admission arithmetic lands with the queries in CB2.3; T13's pure form in CB2.5; CB5.2 only routes the transitions through them (§7) |
   | The CHANGELOG named switch-cut rows by ids the plan had since renumbered | the ids corrected; the entry now cites phases and named cuts, since the plan gate holds the four companion files but not the CHANGELOG (§14) |

   The sub-task count moved from 93 to 73: CB1, CB3, CB4 and CB6 each took
   the inert-then-switch shape, CB7's information-flow rows moved ahead of
   the activation they cover, the specification and pin rows folded into the
   cuts that make their subject reachable, and the compiler sweeps and the
   server refills joined the cuts that cannot build or hold without them.

10. **What the forty-five findings had in common, and what changed so the
    next forty-five are not found one at a time.**  Patching the instance a
    reviewer names converges only if the instances are independent; these were
    not.  Read together they are five classes, and the fifth cut fixes the
    class, not the instance:

    | Class | Instances | Root cause | Fix at the root |
    |-------|-----------|------------|-----------------|
    | **Sequencing**: a live change lands before, or apart from, what covers it | the comparator switch, the spec after activation, CLOSED before closure, the Rust mirrors after the arms, the payoff and chokepoints after activation, the compiler sweeps after the extensions, the server refills after the tick, the cross build missing on a Rust row | the schedule was decomposed by *theme* (types, queries, invariants, transitions, proofs, tests, spec) — how one would organise the work — rather than by what compiles and stays covered together | §7's preamble states the five per-row questions and §8.1 makes them the per-PR check; every row was re-walked against them, which is how CB3 and CB4 were found before a reviewer named them |
    | **The nominal state**: a rule correct for a bound leaf whose thread is queued, silent about the other states | detach of an idle-but-counted child, a root moving cores, a server shrunk under its members, bind of a queued or running thread, reconfigure of a donated root, a leaf mid-donation, a donation owner's affinity, a running thread left ineligible at bind | each transition was written against one picture of its objects | §4.8's preamble names the state dimensions and holds every row to every cell, refusing the cells a row does not decide |
    | **A theorem stated from the textbook**, not against the kernel's transitions | T14's activity, eligibility, release, abandonment and stability hypotheses; T15's interval; T18's tie; T19's remote SGI | the statements were the classical ones; the kernel has transitions the classical model does not | §4.11's intro states the walk — every §4.8 transition that can fire inside a theorem's scope, checked against its conclusion — and repeats it whenever §4.8 gains a row |
    | **One fact in two places** | the refill list and the replenish queue; `deadline` and `periodStart + period`; `isActive` and the budget; the Lean and Rust id tables; `schedContextYieldTo` writing budgets outside the rules | a stored copy of a derivable fact, or a second writer of a shared one | the queue is mirrored by an invariant; `deadline` is derived and `isActive` settled (D22); the tables move together with the ids (CB6.1); the helper is retired — each is `CLAUDE.md`'s "derive both answers from one, or make the second impossible" |
    | **An enumeration where a derivation was needed** | the deactivation hook on the wrong primitive; the key-moving list missing bind; the SGI-surfacing sites | hand-written lists of call sites | the invariants are the derivation: a missed deactivation site fails `activeDescendantsConsistent`, a missed reschedule fails `edfCurrentEarliestOnCore`, a missed flag fails `sgi_surfaced_of_reschedulePending_set` — the lists in this plan are estimates, the proofs are the check |

    The plan-level lesson is `CLAUDE.md`'s sweep rule turned inward: when a
    review names a defect, the fix is not applied to the row named but to
    every row that asks the same question, and the question is written into
    the plan where the next author will read it before writing the next row.

    The sixth round is the test of that lesson, and the fifth cut half-passed
    it: the class rules were stated, but two of them — *derive the call-site
    set* and *walk every transition against the theorem* — had been applied
    by hand to the rows a reviewer had named, and the sixth round found four
    more sites in the same two classes (a current-slot removal, donation's
    rebind, unbind's class change, donation's key change) and one theorem
    hypothesis that froze the wrong thing.  So this cut writes the
    **derivations themselves** into §4.4 and §4.5 — the key's inputs and the
    count's dependencies, with the transition set read off them — and closes
    the reservation-churn class structurally (D23) rather than with a
    hypothesis that would have made T14 a statement about a frozen machine.
    A rule that says "derive it" is not applied until the derivation is on
    the page.

    The seventh round found the derivations themselves incomplete in the
    predictable direction — a dependency the count has that the derivation
    had not listed (the budget), a walk applied to the wrong node, a slot
    sized for the common case — and two more rows that consumed later work.
    Each is folded in above, and the first was folded in twice: the reported
    instance was a leaf, the fix as first written read the leaf's budget,
    and the same hole stood one level up, where a nested server is throttled
    by its own budget.  The rule for that shape is the one this plan already
    applies to admission and to the key: **state the predicate once, at
    every level, and derive the count from it** — `eligibleActive` is budget
    and work below, whatever the node — rather than patching the level the
    finding named.  Folding the fix in also surfaced a *one fact in two
    places* instance of this plan's own making: the leaf-level sync
    re-applied rule (e) to the leaf that `enqueueRunnableOnCore` had just
    applied it to, harmless while both ran at the same instant and a window
    shift the moment a late drain became a trigger.  The one new kind of
    finding was a *restatement*: the CHANGELOG entry had named switch-cut
    rows by id and kept the ids of a superseded numbering.  The plan gate
    resolves every row citation in this plan and its four companion
    documents, but not in the CHANGELOG, so the entry now cites phases and
    named cuts and leaves row ids to the documents the gate holds.

## Appendix A — Verification commands

```bash
source ~/.elan/env
lake build SeLe4n.Kernel.SchedContext.Budget                # CB1.2, CB1.6
lake build SeLe4n.Kernel.Scheduler.Operations.Selection    # CB1, CB3
lake build SeLe4n.Kernel.Scheduler.PriorityInheritance     # CB1.5, CB1.8
lake build SeLe4n.Kernel.SchedContext.Hierarchy            # CB2
lake build SeLe4n.Kernel.Scheduler.Operations.Core         # CB4
lake build SeLe4n.Kernel.API                               # CB6
lake exe smp_cbs_suite                                     # S0–S3, S4b, S5, S6, S8–S11
lake exe hierarchical_server_suite                         # S7
./scripts/test_tier2_trace.sh                              # every fixture sha256
./scripts/test_full.sh                                     # Tier 0–3
./scripts/test_aarch64_cross_build.sh                      # after rust/ changes
python3 scripts/check_live_arm_per_core_routing.py         # CB6.3
python3 scripts/check_workstream_plan.py                   # this plan (stage first)
./scripts/test_docs_sync.sh                                # citations, mirrors, map
```

## Appendix B — Implementation dependency graph

```
CB0.3 (authority gate) ─────────────────────────────────────────────┐
CB0.4 (witnesses) ─► CB1.1 ─► CB1.2 ─► CB1.3 ─► CB1.4 ─► CB1.5 ─► CB1.6 ─► CB1.7 ─► CB1.8 ─► CB1.9
                     (inert) (inert) (inert)            (inert)  engine   order   inherit.  │
                                                                                            │
CB2.1 ─► CB2.2 ─► CB2.3 ─► CB2.4 ─► CB2.5 ─► CB2.6 ─► CB2.7 ─► CB2.8 ─► CB2.9
                               │
CB3.1 ─► CB3.2 ─► CB3.3 ─► CB3.4 ─► CB3.5 ─► CB3.6 (switch: path selection) ─► CB3.7
(inert) (inert) (inert)   (inert)  (inert)                                     │
CB4.1 ─► CB4.2 ─► CB4.3 (switch: the tick + server refills) ─► CB4.4 (switch: activation) ─► CB4.5 ─► CB4.6 ─► CB4.7
(inert)                                                                                                    │
CB5.1 ─► CB5.2 (admission + every move) ─► CB5.3 ─► CB5.4 ─► … ─► CB5.8 ─► … ─► CB5.12 ─► CB5.13 ─► CB5.14 ─► CB5.15 ─► CB5.16
                                                                                                                          │
CB6.1 (ids + sweep) ─► CB6.2 ─► CB6.3 ─► CB6.4 ─► CB6.5 ─► CB6.6 (activation: wiring + spec + pins + S7) ─► CB6.7 ─► CB6.8 ─► CB6.9
                                (inert)  (inert)  (inert)                                                              │
CB7.1 ─► CB7.2 (T14–T16) ─► CB7.3
                              │
CB8.1 ─► CB8.2 ─► CB8.3 ─► CB8.4 ─► CB8.5 ─► CB8.6 ─► CB8.7 ─► CB8.8 (the status flip)
```

Arrows are the `consumes` relations the rows state; a phase's first row
consumes the previous phase's last acceptance.
