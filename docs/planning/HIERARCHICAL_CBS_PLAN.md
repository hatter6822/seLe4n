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
> **Sub-task count**: 93 across 9 phases (CB0..CB8), each phase numbered in
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
> records what the refinement pass changed.

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
condition.  The result is the temporal isolation Linux's
`SCHED_DEADLINE`-based HCBS gives control groups, expressed in seL4-MCS terms:
a component gets a fraction of a core, its threads share that fraction, and no
thread outside the component can be delayed by anything the component does
beyond the fraction it was admitted for.

This workstream delivers, in order:

1. the EDF-first root on the flat model — kernel-owned deadlines and windows,
   the refill accounting the guarantee needs, the CBS wake-up rule, deadline
   inheritance in place of priority inheritance for deadline-bearing threads,
   the one intended fixture refresh (CB1);
2. the model — server fields on `SchedContext`, bounded hierarchy queries,
   and the store-level hierarchy invariant bundle (CB2);
3. hierarchical selection and eligibility, provably identical to the CB1
   selector on every state with no servers (CB3);
4. hierarchical budget accounting on the per-core tick, with the CBS
   isolation theorems lifted from a single SchedContext to a subtree (CB4);
5. the hierarchy transitions — configure a server, bind and unbind a member —
   plus the hierarchy-aware forms of bind, configure, unbind, affinity,
   donation and retype, each with its preservation surface (CB5);
6. three syscalls wiring those transitions live, on both sides of the ABI,
   with the `ipcInvariantFull` dispatch payoff extended over them (CB6);
7. the information-flow and liveness re-establishment: members of a server
   share a label, so a server's budget is not a cross-label channel, and the
   CBS guarantee — a runnable server receives its budget within its window —
   is stated with explicit hypotheses and proved as far as the plan commits
   to (CB7);
8. closure — specification, evidence index, theorem inventory, fixtures,
   registered follow-ups (CB8).

### 1.1 What is actually there, verified against `v0.34.48`

* `SchedContext` (`SeLe4n/Kernel/SchedContext/Types.lean`) carries `scId`,
  `budget`, `period`, `priority`, `deadline`, `domain`, `budgetRemaining`,
  `periodStart` (written nowhere), `replenishments` (bounded by
  `maxReplenishments = 8`), `boundThread : Option ThreadId`, `isActive` and
  the SM3.A.6 `lock`.  Nothing on it can express a parent or a member.
* The binding is 1:1: `schedContextBind` refuses when `sc.boundThread` is
  set, and `schedContextNotDualBound` (`SeLe4n/Kernel/CrossSubsystem.lean`)
  forbids two threads naming one SchedContext.  `TCB.schedContextBinding` is
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
  WCRT theorems take per-band budgets as hypotheses.  CB1.4 replaces the
  scheme (§4.2); this is reported to the maintainer as a functional defect.
* Priority inheritance (`SeLe4n/Kernel/Scheduler/PriorityInheritance/`) is a
  priority boost: `updatePipBoost` writes `pipBoost := computeMaxWaiterPriority`
  over `waitersOf` (the threads `.blockedOnReply` on this one) and re-buckets;
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
* Threads leave the runnable set through `removeRunnable`
  (`SeLe4n/Kernel/IPC/Operations/Endpoint.lean`, every IPC block path),
  `suspendThreadOnCore` (`SeLe4n/Kernel/Lifecycle/Suspend.lean`), the
  cancellation and fault suspends, and retype cleanup; they enter it through
  `enqueueRunnableOnCore` (`wakeThread`, the replenish and timeout wakes,
  resume, the notification and IPC unblocks).  `removeRunnable` is still
  pinned to `bootCoreId`.
* Replenishments are per core and pinned to the bound thread's home core:
  `replenishQueueAffinityConsistentOnCore`
  (`SeLe4n/Kernel/SchedContext/ReplenishAffinity.lean`) and
  `replenishQueueEntriesBoundOnCore` (`BindingAffinity.lean`) both read
  `sc.boundThread`; `schedContextReplenishHome` resolves the home the same
  way.  `perCoreCbsInvariant` (`Operations/PerCoreCbs.lean`) bundles validity,
  pipeline order and affinity.
* Admission is one flat sum: `checkAdmission` folds `utilizationPerMille`
  (ceiling-rounded) over **every** SchedContext in the object store against
  `1000`, so a four-core machine admits 100 % in total, not per core.
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
  the bound TCB (write).
* `schedContextYieldTo` is the one hook already labelled "for hierarchical
  scheduling": kernel-internal, capability-free, a budget transfer between
  two SchedContexts.  It is **not** what this workstream builds on and is left
  in place.
* The timer seam is a fixed 1000 Hz periodic tick whose only payload is the
  core id (`per_core_timer_tick_isr`, `lean_per_core_timer_tick`).  There is
  no one-shot deadline programming anywhere in the tree.
* `schedContextConfigure` is `.capabilityOnly` under the SchedContext write
  right and applies the requested `priority` and `domain` to the bound TCB
  with **no** caller-MCP check and no domain authority — where
  `setPriorityOp` gates the same write through `validatePriorityAuthority`.
  Recorded as a pre-existing finding in §3.3; CB0.3 closes it.  The same
  syscall's caller-supplied `deadline` is a tie-break today and would be the
  **primary** scheduling key under EDF-first; CB1.3 retires it.

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

The root order becomes EDF-first (§3.1) and the CBS engine's window and refill
rules become the classical ones (§4.2).  On every state whose runnable
threads all lack deadlines the selector is unchanged, and CB1.2 proves it
(`chooseThreadEffectiveOnCore_eq_flat_of_no_deadlines`).  On a state with a
deadline-bearing runnable thread the order changes by design, and every
replenishment schedule changes by design, so the fixtures built from bound
threads — fourteen suites and the main trace harness at the audited cut — are
refreshed **once**, in CB1.14, with the rationale recorded; after CB1 every
generalising cut is byte-identical again.  The other two intended fixture moves
are CB0.3's (the configure authority gate) and CB5.2's (per-core admission).

## 2. Scope and sequencing

### 2.1 In scope

* The EDF-first root on the flat model: kernel-owned implicit deadlines and
  windows, window-end refills of the full budget, the CBS wake-up rule,
  deadline inheritance for deadline-bearing threads, the selector, its
  invariants and its one fixture refresh (CB1).
* Server SchedContexts with bounded nesting; member leaves and member servers.
* Hierarchical ordering (§4.3), hierarchical charging, activation and
  replenishment (§4.5), hierarchical admission (§4.6), core-homed servers
  (§4.8).
* Three syscalls: `schedContextConfigureServer`, `schedContextBindServer`,
  `schedContextUnbindServer`; hierarchy-aware forms of the existing
  operations that read or write a SchedContext's role (§4.8).
* The preservation surface for every touched invariant bundle, the
  `ipcInvariantFull` dispatch payoff over the new arms, per-core
  non-interference under the label-uniformity rule, and the CBS guarantee
  with its hypotheses stated.
* Tier-2 suites with golden fixtures, Tier-3 anchors, ABI mirrors and
  conformance tests, specification and evidence-index rows.

### 2.2 Out of scope (registered follow-ups, §12)

Constrained deadlines (`D < P`); a per-core deadline-ordered index for
selection; server migration between cores; members homed on several cores
(Linux HCBS's per-CPU server replicas); bandwidth inheritance (a member's
inherited deadline lifting its *server*); boot-time server trees; a bucketed
member queue; sub-tick enforcement through a one-shot timer.

### 2.3 Ordering constraints and parallelism

* **Phase order is execution order.**  CB1 changes the root policy and the
  refill scheme on the flat model and is the only phase whose behavioural
  change is intended to reach existing fixtures; it lands whole, before any
  server field exists, so the hierarchy is built on the engine it will
  actually run under.  CB2 has no behavioural effect; CB3 and CB4 change live
  paths but only on states that CB5/CB6 cannot yet produce, and each carries
  its no-servers equivalence theorem in the same row; CB5 lands every
  transition with its proofs before CB6 makes any of them reachable.
* **Overlap with WS-RR.**  CB1 edits the selector, the tick, the CBS engine
  and the priority-inheritance modules, so it must not overlap an RR7 cut that
  touches `SeLe4n/Kernel/Scheduler/**` or `SeLe4n/Kernel/SchedContext/**`;
  CB2–CB4 own those trees; CB5 onward edits `API.lean` and the
  flow-classification tables and must not overlap a WS-RR cut that does.  RR6
  (lock primitives) never collides.
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
| D3 | **EDF-first at every level** (§3.1, §4.3): earlier kernel-assigned deadline first, a deadline-less entity after every deadline-bearing one, then higher priority, then FIFO among leaves and ascending `scId` among distinct servers | Fixed priority with EDF as the tie-break (the pre-CB1 root); FP-only local scheduling | The maintainer's decision; it is the order under which the CBS guarantee is a theorem rather than a per-band argument, and one order at every level means one set of strict-order lemmas |
| D4 | A running thread's tick charges its leaf **and every ancestor**; exhaustion at any level makes the subtree ineligible until that level's refill lands; a server is *activated* by the CBS rule when its first member becomes active; timeouts are decided by the leaf only (§4.5) | Charge the leaf and transfer budget upward lazily | Eager charging is what makes the subtree bound a theorem; lazy transfer needs a second accounting state |
| D5 | Servers are **core-homed**; every member's thread has that home core; member affinity changes, and donations of a member leaf to a thread homed elsewhere, are refused (§4.8) | Per-core server replicas | Keeps every hierarchical write inside one core's scheduler slots and the existing tick lock set; replicas are the registered extension |
| D6 | Admission is hierarchical: members ≤ server; roots **per core** ≤ 1000 ‰, replacing the flat global sum (§4.6) | Keep the global sum and add the member rule | Per-core `Σ U ≤ 1` is EDF's schedulability condition for implicit deadlines, so per-core root admission is both the natural base case of the hierarchy and the hypothesis of the CBS guarantee |
| D7 | Priority is a **tie-break** for deadline-bearing entities and the order of the legacy class; a server's priority may change at any time, a member thread's priority through `.tcbSetPriority` under the caller's MCP, and neither moves anything but ties | Server priority frozen while populated; `.tcbSetPriority` refused on members | Both refusals existed only to keep a root-priority bucket consistent, and under EDF-first the bucket no longer orders anything |
| D8 | Every member of a server carries the server's security label; enforced at `schedContextBindServer` in the flow-checked tier (§4.13) | Permit mixed labels and bound the channel | A shared budget lets one member starve another outright; that is not a channel to bound but a flow to forbid |
| D9 | `maxServerDepth = 3` (root server → server → leaf), `maxServerMembers = 16`; every walk is fuel-bounded by the depth | Unbounded recursion on `parentServer` | Totality with a decidable bound; the path lock footprint (`≤ 3` SchedContext locks + the tick's three) stays within `maxLockSetSize = 8` |
| D10 | Enforcement stays tick-quantised; no new upcall, no HAL change, `SYSCALL_ABI_VERSION` unchanged (ids appended, one argument's accepted values narrowed) | A one-shot timer programmed to the next budget event | A new FFI seam drags in the readiness-gate derivation and a new Rust surface for a precision gain the model does not need yet |
| D11 | The boot state has no servers; a hierarchy is built at run time by the root task | Boot-time server trees in `PlatformConfig` | Keeps the boot theorems of WS-RR RR5 untouched; boot-time trees are a follow-up once a deployment asks for them |
| D12 | Transitions land in production modules from day one (unreachable until CB6 wires the arms); theorem-heavy modules are staged and promoted when a production consumer imports them (§4.14) | Stage everything until CB6 | A definition nobody calls changes no behaviour; staging it only defers the partition work |
| D13 | Deadlines are **kernel-owned and implicit** (`D = P`): `schedContextConfigure`'s `deadline` argument must be `0`, and the kernel assigns `deadline := periodStart + period` at configure, at every refill and at activation (§4.2) | Keep the caller-supplied absolute deadline; or constrained deadlines `D < P` | A caller-chosen deadline under EDF is unbounded priority escalation; constrained deadlines need a density-based admission test and are a follow-up |
| D14 | The CBS wake-up rule at activation is the **classical** one: `if deadline ≤ now ∨ budgetRemaining·period ≥ (deadline − now)·budget then budgetRemaining := budget, periodStart := now, deadline := now + period` (§4.2 rule (e)) | Reset the deadline and leave the budget alone (the first cut's rule) | The first cut kept the budget because refills were per consumed chunk and a refill at activation would have minted budget the queue was still owed; with D16's per-window refills there is nothing owed, and the classical rule is what the guarantee's proof uses |
| D15 | Priority inheritance becomes **deadline inheritance** for the EDF class (`inheritedDeadline := min` over blocked waiters' effective deadlines, applied to the thread's own key) while the priority boost stays for the legacy class; inheritance never lifts a member's *server* (§4.7) | Keep the priority boost alone | Under EDF-first a priority boost changes nothing but ties, so `pip_bounded_inversion` would hold vacuously for every bound thread; lifting the server is bandwidth inheritance, a follow-up |
| D16 | Refills are **per window**: exhaustion schedules one refill of the full budget at the window's end, and a window always starts with the full budget (§4.2 rules (a)–(d)) | Per-consumed-chunk refills one period after consumption (the seL4-MCS sporadic-server shape the current code approximates) | Per-chunk refills need consumption-interval tracking and refill coalescing under the 8-entry bound — the part of seL4-MCS that was hardest to verify — and the current approximation returns one tick; per-window refills are one entry per SchedContext, the classical hard-CBS rule, and the shape the EDF guarantee's proof assumes |

### 3.1 The root policy, in one paragraph

Two classes.  An entity with a kernel-assigned deadline — every bound thread
through its SchedContext, every server — is in the *EDF class*; an unbound
thread is in the *legacy class* and has no deadline.  Every EDF-class entity
outranks every legacy-class thread.  Within the EDF class: earlier deadline
first; equal deadlines by higher priority; then FIFO among leaves and
ascending `scId` among distinct servers.  Within the legacy class: the pre-CB1
order, higher priority then FIFO — which keeps the idle thread last.  A
deadline is always the end of the entity's current window (§4.2), the kernel
assigns it, and the guarantee (§4.11, T14) is that an admitted entity with
budget at activation is dispatched for it before the window ends.

### 3.2 What stays fixed

No new `@[export]`, so `LEAN_READY_GATED_SEAMS` and the readiness derivation
are untouched; no `extern`, so the kernel-entry export gate's requirement set
is untouched.  `SYSCALL_ABI_VERSION` stays `3`: ids `0..34` keep their
encodings and register layout (the configure `deadline` slot keeps its
position; only its accepted value narrows to `0`), the conformance suite pins
that, and `SyscallId::COUNT` moves to `38` on both sides with the existing
mirror tests holding them equal.

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
CB1.3 retires the deadline argument.  The priority and domain half was
reported to the maintainer as a vulnerability finding at planning time.

The refill defect of §1.1 is the third finding: the live tick returns at most
one tick per exhaustion, so a bound thread's throughput collapses after its
first window and budget consumed without exhaustion is never returned.  It is
not an authority gap but a liveness defect in the scheduler's core function,
and CB1.4 closes it as part of the CBS engine rework the EDF-first root needs
anyway.

## 4. Implementation specification

Everything a sub-task row in §7 points into.  Lean fragments are the intended
shape, not compiled text; names are binding, signatures may gain implicit
arguments the proofs need.  All arithmetic is on `Nat` ticks.

### 4.1 Types and fields

```lean
-- SeLe4n/Kernel/SchedContext/Hierarchy.lean (CB2.3, CB2.4)
def maxServerDepth   : Nat := 3    -- root server → server → leaf
def maxServerMembers : Nat := 16

/-- Members in FIFO order, duplicate-free by construction, bounded. -/
structure MemberList where
  toNoDup : SeLe4n.NoDupList SchedContextId
  hBound  : toNoDup.val.length ≤ maxServerMembers

-- SeLe4n/Kernel/SchedContext/Types.lean (CB1.3 reuses `periodStart`; CB2.1 adds the rest)
structure SchedContext where
  scId, budget, period, priority, deadline, domain, budgetRemaining, replenishments,
  boundThread, isActive, lock : ... -- as today
  /-- Start of the current window; `deadline = periodStart + period` (§4.2). -/
  periodStart       : Nat := 0
  /-- The server this context is a member of; `none` at the root level. -/
  parentServer      : Option SchedContextId := none
  /-- Members, FIFO order; a leaf has none. -/
  serverMembers     : MemberList := MemberList.empty
  /-- `some c` iff this context is a server, homed on core `c`. -/
  serverCore        : Option CoreId := none
  /-- Members whose subtree holds an active thread (§4.5); a leaf's is `1` iff
      its bound thread is active. -/
  activeDescendants : Nat := 0

def isServer (sc : SchedContext) : Bool := sc.serverCore.isSome
def isLeaf   (sc : SchedContext) : Bool := sc.serverCore.isNone

/-- A scheduling key, root-first in a path (§4.3). `deadline = 0` means none. -/
structure SchedKey where
  deadline : Deadline
  priority : Priority
  scId     : SchedContextId
  isLeaf   : Bool

-- SeLe4n/Model/Object/Types.lean (CB1.7)
structure TCB where
  ...
  /-- Deadline inherited from the earliest-deadline thread blocked on this one
      (§4.7); `none` when nothing is blocked.  The `pipBoost` class. -/
  inheritedDeadline : Option Deadline := none
  -- `deadline` removed (CB1.5): unbound threads are deadline-less.
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
def rootOf?     (st) (scId) : Option SchedContextId
def depthOf?    (st) (scId) : Option Nat            -- 0 for a root
def isAncestorOf (st) (anc child : SchedContextId) : Bool
def schedPath?  (st) (scId) : Option (List SchedKey) -- root first, leaf last
```

### 4.2 Windows, deadlines and refills — the CBS engine rules

A SchedContext lives in a *window* `[periodStart, periodStart + period)` whose
end is its deadline.  Six rules, all kernel-side; nothing else writes
`deadline`, `periodStart` or `replenishments`:

| Rule | When | Effect |
|------|------|--------|
| (a) configure | `schedContextConfigure` / `schedContextConfigureServer` succeed at time `t` | `budgetRemaining := budget`, `periodStart := t`, `deadline := t + period`, `replenishments := []`, the core's queue entry for this context purged (today's purge) |
| (b) exhaustion | the charge of §4.5 takes `budgetRemaining` to `0` at time `t` | `refillAt := max (periodStart + period) (t + 1)`; `replenishments := [{amount := budget, eligibleAt := refillAt}]`; `replenishOnCore home scId refillAt`; the deadline is **untouched** — the entity is ineligible until (d) |
| (c) surrender | `handleYieldWithBudget` at time `t` with `budgetRemaining > 0` | `budgetRemaining := 0`, then (b) |
| (d) landing | the drain pops `(scId, refillAt)` at `now ≥ refillAt` | if `sc.replenishments` still names this `refillAt` **and** `refillAt ≥ periodStart + period` (the entry belongs to a window that has not been superseded): `budgetRemaining := budget`, `periodStart := refillAt`, `deadline := refillAt + period`, `replenishments := []`; otherwise the queue entry is **stale** (rule (a), (e) or (f) advanced the window past it and cleared the list) and is dropped with no other change |
| (e) activation | a leaf whose bound thread becomes active from inactive, or a server whose `activeDescendants` goes `0 → 1`, at time `t` | `if deadline ≤ t ∨ budgetRemaining · period ≥ (deadline − t) · budget then budgetRemaining := budget, periodStart := t, deadline := t + period, replenishments := []` — the classical CBS rule; a pending refill's queue entry, if any, is now stale and is dropped by (d) |
| (f) reconfigure of a live entity | (a) on a context that is bound or a server | as (a); admission re-checked first (§4.6) |

Consequences the proofs use, all per-object conjuncts of `SchedContext.wellFormed`
from CB1.3/CB1.4 on: `replenishments.length ≤ 1` (`atMostOnePendingRefill`);
`replenishments ≠ [] → budgetRemaining = 0` (`pendingRefillOnlyWhenExhausted`);
`deadline = periodStart + period`
(`deadlineWindowConsistent`); consumption inside one window is at most
`budget` (`window_consumption_le_budget`), because a window starts with the
full budget and nothing adds budget before the window ends; the dead time
after exhaustion is at most one period (`refill_dead_time_le_period`).  In (b)
the `t + 1` arm is reachable only when an entity exhausts after its deadline,
which the guarantee (§4.11, T14) rules out on an admitted core; the rule is
total regardless.  Under (e) with `budgetRemaining = 0` the inequality reads
`0 ≥ (deadline − t) · budget`, true exactly when `deadline ≤ t`, so an
exhausted entity is refreshed at activation only once its window has ended —
which is also when its pending refill would have landed.

Why this differs from the code today: the current arms schedule
`budgetRemaining` (≤ 1) one period after exhaustion and never refill without
exhaustion (§1.1).  Why it differs from Abeni–Buttazzo's soft CBS: the budget
is not refilled at exhaustion with the deadline postponed (which lets the
server keep running at a lower EDF priority), it is refilled at the window's
end — hard CBS, the variant without overrun, which is what a kernel enforcing
reservations wants.  Why the first cut's D14 is reversed: with per-window
refills nothing is owed when an entity is activated, so the classical
budget-refilling rule is sound and simpler.

`cbsUpdateDeadline` is retired in favour of the rules above:
`cbsWindowStart sc t` implements (a)/(d)/(e)'s window start,
`cbsScheduleRefill sc t` implements (b), `cbsActivate sc t` implements (e),
`cbsLandRefill sc refillAt` implements (d).  The Z2 preservation theorems are
restated over these four.

### 4.3 The order

```lean
/-- EDF-first comparison of two keys at the same path position (CB1.1 for
    thread keys; CB3.3 lifts it to paths).  `true` iff the challenger beats
    the incumbent. -/
def isBetterKey (inc chal : SchedKey) : Bool :=
  match chal.deadline.toNat, inc.deadline.toNat with
  | 0, 0      => byPriority
  | _, 0      => true
  | 0, _      => false
  | cd, id    => if cd < id then true else if id < cd then false else byPriority
where
  byPriority :=
    if chal.priority > inc.priority then true
    else if chal.priority < inc.priority then false
    else if chal.isLeaf && inc.isLeaf then false          -- FIFO: keep the incumbent
    else chal.scId < inc.scId                            -- distinct servers: lower id

/-- Lexicographic lift (CB3.3): positions compared root-first; the first
    position at which the keys differ decides; equal keys advance. -/
def isBetterPath : List SchedKey → List SchedKey → Bool
```

`isBetterCandidate` (CB1.1) is `isBetterKey` on the singleton thread key,
with `isLeaf := true` for both, so its tie is always FIFO.  Strictness lemmas:
`isBetterKey_irrefl`, `isBetterKey_asymm`, `isBetterKey_trans`, and the same
three for `isBetterPath`; `isBetterPath_singleton_eq_isBetterKey`.  Two
distinct leaves never have one path a proper prefix of the other
(`schedPath_not_prefix`: a server is never a leaf), so the lift is total on
the paths selection compares.

A thread's key path (`resolveEffectiveSchedPath st tcb`, CB3.2): `none`
entries for an unbound thread yield the deadline-less singleton
`⟨0, effectiveRunQueuePriority tcb, sentinel, true⟩`; a bound thread yields
`schedPath? st scId` with the **leaf** key's deadline replaced by
`min(sc.deadline, tcb.inheritedDeadline)` (§4.7) and its priority lifted by
`pipBoost`.  Ancestor keys are the servers' own `(deadline, priority, scId)`.

### 4.4 Eligibility and selection

```lean
def pathBudgetEligible (st : SystemState) (tcb : TCB) : Bool :=
  match tcb.schedContextBinding with
  | .unbound => true
  | .bound scId | .donated scId _ =>
    match parentChain? st scId with
    | some chain => (scId :: chain).all (fun s => (st.getSchedContext? s).any (·.budgetRemaining.isPositive))
    | none => false                                  -- dangling or over-deep: fail closed
```

Selection (`chooseBestRunnableHierarchical`, CB1.2 in singleton form, CB3.4
in path form) is a left fold over `(runQueueOnCore c).toList` — the FIFO
`flat` order — keeping the best eligible in-domain candidate under
`isBetterPath`, skipping entries that do not resolve to a TCB (the round-15
contract).  The bucket-first fast path (`chooseBestInBucketEffective`) is
retired; `maxPriorityBucket` and `schedulerPriorityMatchOnCore` remain as
membership facts.  Cost: `O(n · maxServerDepth)` per decision with `n` the
core's runnable count; the lock-wait WCRT terms are unchanged (§4.12).
`candidateOutranksCurrentOnCore` and `handleRescheduleSgiOnCore` decide with
the same comparator on the same keys; `edfCurrentEarliestOnCore` (§4.10)
states the consequence.

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

The **active** predicate and its counter.  `threadActive st tid :=
runnableOnSomeCore st tid ∨ runningOnSomeCore st tid`.  For a leaf,
`activeDescendants = 1` iff its bound thread is active; for a server, the
number of members with a positive count.  Two helpers hold it:

* `noteActivated st tid` — called where a thread becomes active from
  inactive: `enqueueRunnableOnCore` (its `runnableOnSomeCore` guard already
  detects the transition).  It increments the counter on the leaf and, walking
  `parentChain?`, on each ancestor; every ancestor whose count went `0 → 1`,
  and the leaf itself, get `cbsActivate` (rule (e)).
* `noteDeactivated st tid` — called where a thread becomes inactive:
  `removeRunnable` (every IPC block path), `suspendThreadOnCore`, the
  cancellation and fault suspends, `cleanupTcbReferences` on retype, and the
  dispatch paths that clear a `current` slot without re-enqueueing.  It
  decrements along the path.

Dispatch (`switchToThreadOnCore`, `scheduleEffectiveOnCore`) moves a thread
from runnable to current, so the counter is untouched; preemption re-enqueues,
untouched; bind/unbind of a leaf to a thread and bindServer/unbindServer of a
member transfer the member's whole count into or out of the parent.  The
invariant `activeDescendantsConsistent` (§4.10) is what makes the enumeration
complete: every transition's cross-subsystem bridge must preserve it, so a
runnability change the helpers miss fails a proof rather than a review.
`removeRunnable`'s `bootCoreId` pin is repointed to the thread's home core in
the same row (CB4.6) — the counter must see the queue the thread is really in.
Fallback if the counter proves too invasive: compute idleness by a bounded
subtree scan (at most `16 + 16·16 + 16·16·16` leaf checks at depth 3, each
`O(numCores)`); the plan prefers the counter and records the fallback in §9.

### 4.6 Admission

`U(sc) := (sc.budget.val · 1000 + sc.period.val − 1) / sc.period.val`
(`Bandwidth.utilization`, ceiling per-mille).

```lean
def rootActiveOnCore (st) (sc) (c) : Bool :=           -- roots that count against core c
  sc.parentServer.isNone ∧ (sc.serverCore = some c ∨
    (sc.boundThread.any fun tid => determineTargetCore st tid = c))
def rootUtilisationOnCore (st) (c) (exclude : Option SchedContextId) : Nat
def checkRootAdmissionOnCore (st) (c) (candidate : SchedContext) (exclude) : Bool :=
  rootUtilisationOnCore st c exclude + U candidate ≤ 1000
def memberUtilisation (st) (server : SchedContext) (exclude) : Nat
def checkMemberAdmission (st) (server) (candidate) (exclude) : Bool :=
  memberUtilisation st server exclude + U candidate ≤ U server
```

Checked by: configure (root leaf with a bound thread → root check on the
thread's core; member leaf → member check against the parent; server → root
check on `serverCore` if parentless, member check if a member), bind of a
thread to a root leaf (root check on the thread's core — a new
`.resourceExhausted` refusal), bindServer (member check), unbindServer (root
check on the child's core), configureServer (root check).  An unbound root
leaf counts for nothing.  `hierarchicalAdmissionHolds` (§4.10) states both
sums for every server and every core; `rootAdmission_sound_per_core` says an
admitted core's roots sum to at most `1000`.  The RPi5 canonical deployment's
`admissibleUtilisation = 750` stays a liveness-side margin above the kernel's
ceiling.

### 4.7 Deadline inheritance

```lean
def computeMinWaiterDeadline (st : SystemState) (tid : ThreadId) : Option Deadline :=
  (waitersOf st tid).foldl (fun acc w =>
    match (st.getTcb? w).map (effectiveDeadline st) with
    | some (some d) => some (acc.elim d (min d))
    | _ => acc) none

def effectiveDeadline (st : SystemState) (tcb : TCB) : Option Deadline :=
  let own := (tcb.schedContextBinding.scId?.bind (st.getSchedContext? ·)).map (·.deadline)
  match own, tcb.inheritedDeadline with
  | some d, some i => some (min d i)
  | some d, none   => some d
  | none,   i      => i          -- an unbound thread inherits but has no own deadline
```

`updatePipBoost` (and `updatePipBoostOnCore`, `propagatePipChainCrossCore`)
writes `pipBoost := computeMaxWaiterPriority` **and**
`inheritedDeadline := computeMinWaiterDeadline`; `revertPriorityInheritance`
clears both; the bucket migration on a changed `pipBoost` stays as it is (the
bucket is a membership fact).  The inherited deadline lowers the thread's
**own** key only; a member's server keeps its key (D15).  An unbound thread
with an inherited deadline joins the EDF class for as long as it holds it —
which is the intended effect: a legacy-class server blocking an EDF-class
client runs at the client's deadline.  `pip_bounded_inversion` is restated: a
thread blocking a waiter of effective deadline `d` has effective deadline
`≤ d`.

### 4.8 Transitions and refusals

Every refusal is an explicit `KernelError` arm evaluated before any write;
the `Kernel` monad (`SystemState → Except KernelError (α × SystemState)`)
discards a partial state on error.  Argument ids are validated through
`validateObjIdArg` / `validateThreadIdArg` (idle-slot and sentinel refusal)
before these tables apply.

**`schedContextConfigureServer vScId core`** (new, CB5.1)

| Check, in order | Error |
|-----------------|-------|
| target is a SchedContext | `.objectNotFound` |
| `core < declaredCoreCount` (`MachineState.declaredCoreCount`) | `.invalidArgument` |
| `boundThread = none` | `.illegalState` |
| `parentServer = none` | `.illegalState` |
| `serverMembers = []` or `serverCore = some core` already | `.illegalState` |
| root admission on `core` (excluding itself) | `.resourceExhausted` |
| effect | `serverCore := some core`; rule (a) window start |

**`schedContextBindServer vServer vChild`** (new, CB5.3; the child CPtr
resolved in the caller's CSpace with `.write` first — `.invalidCapability` /
`.invalidCapPtr` from `syscallLookupCap`)

| Check, in order | Error |
|-----------------|-------|
| both resolve to SchedContexts | `.objectNotFound` |
| `isServer server` | `.illegalState` |
| `child.parentServer = none` | `.illegalState` |
| `child ≠ server` and `¬ isAncestorOf st child server` | `.cyclicDependency` |
| `depthOf? server + 1 + subtreeDepth child ≤ maxServerDepth` — a child server must be **empty**, so `subtreeDepth child = 0` | `.illegalState` |
| `server.serverMembers.length < maxServerMembers` | `.resourceExhausted` |
| `child.domain = server.domain` | `.invalidArgument` |
| child leaf with a bound thread: `determineTargetCore tid = serverCore`; child server: `child.serverCore = server.serverCore` | `.threadOnDifferentCore` |
| member admission against `server` | `.resourceExhausted` |
| (checked tier only) `securityFlowsTo(childLabel, serverLabel) ∧ securityFlowsTo(serverLabel, childLabel)` | `.flowDenied` |
| effect | `child.parentServer := some server`; `server.serverMembers += child`; `server.activeDescendants += (child.activeDescendants > 0)`, propagated to the server's ancestors with rule (e) on any `0 → 1`; if the child was a root leaf with a bound thread its root-admission share on that core is released |

**`schedContextUnbindServer vChild`** (new, CB5.4)

| Check, in order | Error |
|-----------------|-------|
| target is a SchedContext with `parentServer = some s` | `.illegalState` |
| `child.serverMembers = []` (a populated child server is not detached) | `.illegalState` |
| root admission on the child's core, if the child is active there | `.resourceExhausted` |
| effect | unlink both sides; the parent's chain loses the child's count |

**Hierarchy-aware existing operations**

| Operation | New rule | Error |
|-----------|----------|-------|
| `schedContextConfigure` | `deadline` argument must be `0` (CB1.3); caller-MCP gate on `priority`, domain fixed once bound (CB0.3); admission per §4.6; rule (a) window start; priority change on any context is a tie-break change and re-buckets nothing beyond the AK2-B mirror | `.invalidArgument`, `.illegalAuthority`, `.resourceExhausted` |
| `schedContextBind` | target must be a leaf; a member leaf's thread must be homed on the ancestor's `serverCore`; root leaf → root admission on the thread's core; the thread's activity enters the ancestors' counts with rule (e) on any `0 → 1` | `.illegalState`, `.threadOnDifferentCore`, `.resourceExhausted` |
| `schedContextUnbind` | as today, plus the thread's activity leaves the ancestors' counts | — |
| `.tcbSetAffinity` (`setThreadCpuAffinityWithMigration`) | refused when the thread's leaf has a parent | `.illegalState` |
| `.tcbSetPriority` (`setPriorityOp`) | permitted on members (tie-break only, caller-MCP gated as today) | as today |
| `donateSchedContext` | refused when the client's leaf has a parent and the donee's home core differs from the ancestor's `serverCore`; the donated leaf keeps its position and window | `.illegalState` |
| `lifecyclePreRetypeCleanup` of a SchedContext | a populated server is refused; a member leaf is unlinked (as unbindServer) before destruction | `.illegalState` |
| `handleYieldWithBudget` | rule (c) | — |

Error codes reuse the existing inductive: `.cyclicDependency` and
`.threadOnDifferentCore` already exist; no new `KernelError` variant is added.

### 4.9 Syscall ABI and the total-table sweep

| Id | Lean arm | Rust variant | `min_inline_args` | Registers | Return shape |
|----|----------|--------------|-------------------|-----------|--------------|
| 35 | `.schedContextConfigureServer` | `SchedContextConfigureServer` | 1 | `MR0` = core (`u64`, `< numCores` at decode, `< declaredCoreCount` in the transition) | `.unit` |
| 36 | `.schedContextBindServer` | `SchedContextBindServer` | 1 | `MR0` = CPtr of the child SchedContext, resolved in the caller's CSpace with `.write` | `.unit` |
| 37 | `.schedContextUnbindServer` | `SchedContextUnbindServer` | 0 | none | `.unit` |

`SyscallId.count := 38` (Lean) and `SyscallId::COUNT = 38` (both Rust
tables).  `SYSCALL_ABI_VERSION` stays `3`.  `schedContextConfigure` (17) keeps
its five-register layout; its `MR3` (`deadline`) accepts only `0` after CB1.3.

Lean (`SeLe4n/Kernel/Architecture/SyscallArgDecode.lean`):
`SchedContextConfigureServerArgs { core : Nat }` with
`decodeSchedContextConfigureServerArgsChecked` refusing `core ≥ numCores`;
`SchedContextBindServerArgs { childCPtr : Nat }`;
`SchedContextUnbindServerArgs` (unit); `encode*`, `decode*_roundtrip`,
`decode*_error_iff` in the existing pattern.

Rust: `rust/sele4n-types/src/syscall.rs` gains the three variants,
`COUNT = 38`, `from_u64`, `required_right → Write`, and the discriminant
tests; `rust/sele4n-hal/src/svc_dispatch.rs`'s hand mirror gains the same
plus `min_inline_args` (1, 1, 0) and its two mirror tests keep the copies
equal; `rust/sele4n-abi/src/args/sched_context.rs` gains
`SchedContextConfigureServerArgs { core: u64 }` (`encode → [u64; 1]`,
`decode` requiring one register), `SchedContextBindServerArgs { child: CPtr }`,
`SchedContextUnbindServerArgs` (zero registers), and documents
`SchedContextConfigureArgs.deadline` as `0`-only;
`rust/sele4n-sys/src/sched_context.rs` gains
`sched_context_configure_server(sc_cap: CPtr, core: u64)`,
`sched_context_bind_server(server_cap: CPtr, child: CPtr)`,
`sched_context_unbind_server(child_cap: CPtr)`, each an `invoke_syscall` with
`MessageInfo::new_const(n, 0, 0)` for its register count;
`rust/sele4n-abi/tests/conformance.rs` gains a `verify_regs` case per wrapper,
and the wrapper-length sweep covers them automatically.

**The total-table sweep** (CB6.2) — every function over `SyscallId` the
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

`lockSetForSyscall` answers `none` because SM3.C.9's migration has not
reached any SchedContext arm; the model-level footprints of §4.12 exist
regardless, and the migration plan adopts them when it arrives.  The Tier-1
per-core routing gate (`check_live_arm_per_core_routing.py`) walks from
`syscallIdToEnforcementNamePerCore` two hops, so each arm's body must reach a
`…OnCore` transition rather than a `bootCoreId`-pinned primitive.

### 4.10 Invariants

Per-object, in `SchedContext.wellFormed` (`Types.lean`) and therefore carried
by `schedContextStoreConsistent` and by `bootSafeSchedContextCheck`:

| Conjunct | Statement | From |
|----------|-----------|------|
| `deadlineWindowConsistent` | `deadline.toNat = periodStart + period.val` | CB1.3 |
| `atMostOnePendingRefill` | `replenishments.length ≤ 1` | CB1.4 |
| `pendingRefillOnlyWhenExhausted` | `replenishments ≠ [] → budgetRemaining.val = 0` | CB1.4 |
| `serverRoleExclusive` | `isServer sc → boundThread = none` ∧ `isLeaf sc → serverMembers = []` | CB2.5 |
| `serverMembersBounded` | `serverMembers.length ≤ maxServerMembers` | CB2.5 |

Store-level, `schedHierarchyInvariant st` (`Invariant/HierarchyDefs.lean`,
CB2.6), the thirteenth conjunct of `crossSubsystemInvariant` from CB5.13:

| Conjunct | Statement |
|----------|-----------|
| `hierarchyBidirectional` | `∀ child s, child.parentServer = some s ↔ child ∈ s.serverMembers` (over `getSchedContext?`) |
| `hierarchyDepthBounded` | `∀ sc, ∃ chain, parentChain? st sc = some chain ∧ chain.length ≤ maxServerDepth` — which is also acyclicity |
| `serverCoreConsistent` | a member server's `serverCore` equals its parent's; a member leaf with `boundThread = some tid` has `determineTargetCore st tid = parent.serverCore` |
| `serverDomainConsistent` | `∀ member s, member.domain = s.domain` |
| `hierarchicalAdmissionHolds` | `∀ c, rootUtilisationOnCore st c none ≤ 1000` ∧ `∀ s, isServer s → memberUtilisation st s none ≤ U s` |
| `activeDescendantsConsistent` | leaf: `activeDescendants = if ∃ tid, boundThread = some tid ∧ threadActive st tid then 1 else 0`; server: `activeDescendants = (serverMembers.filter (activeDescendants · > 0)).length` |

Per-core (`Scheduler/Invariant/PerCore.lean`):

| Predicate | Statement |
|-----------|-----------|
| `edfCurrentEarliestOnCore st c` (CB1.9, replaces `edfCurrentHasEarliestDeadlineOnCore`) | if `currentOnCore c = some cur` then for every `tid ∈ runQueueOnCore c` with `pathBudgetEligible` and the current's domain: `¬ isBetterPath (path cur) (path tid)` — the current is maximal in the selector's own order |

The pre-CB1 conjunct compared deadlines within a priority band; the new one is
the selector's order itself, so its preservation proofs are the selector's
optimality theorems applied at every dispatch and reschedule point.

Retired or restated: `edfCurrentHasEarliestDeadlineOnCore` (replaced);
`boundThreadPriorityConsistent`, `schedulerPriorityMatchOnCore`,
`effectiveParamsMatchRunQueueOnCore` (kept, as membership facts about the
AK2-B mirror); `replenishment_within_period`, `replenishment_dead_time_exact`
(restated as `refill_dead_time_le_period`); `cbs_bandwidth_bounded` (kept, now
implied by `window_consumption_le_budget` with a tighter constant).

### 4.11 Key theorem statements

| # | Theorem | Statement (hypotheses named) | Row |
|---|---------|------------------------------|-----|
| T1 | `isBetterKey_irrefl`, `_asymm`, `_trans` | the order of §4.3 is a strict order on keys; `isBetterPath_*` the same on key paths | CB1.1, CB3.3 |
| T2 | `chooseThreadEffectiveOnCore_eq_flat_of_no_deadlines` | if every `tid ∈ runQueueOnCore c` has `effectiveDeadline st tcb = none`, the CB1 selector equals the pre-CB1 selector on `(st, c)` | CB1.2 |
| T3 | `wellFormed_preserved_by_cbs_rules` | each of `cbsWindowStart`, `cbsScheduleRefill`, `cbsLandRefill`, `cbsActivate`, `consumeBudget` preserves `SchedContext.wellFormed` (all conjuncts of §4.10) given `period > 0`, `0 < budget ≤ period` | CB1.3, CB1.4, CB1.6 |
| T4 | `window_consumption_le_budget` | for any `sc` with `wellFormed`, the ticks charged to `sc` while `periodStart` is unchanged sum to at most `budget` | CB1.4 |
| T5 | `refill_dead_time_le_period` | a refill scheduled by rule (b) at `t` has `refillAt − t ≤ period`, and `refillAt > t` | CB1.4 |
| T6 | `cbsActivate_noop_of_fresh` | if `deadline > t` and `budgetRemaining · period < (deadline − t) · budget` then `cbsActivate sc t = sc` | CB1.6 |
| T7 | `pip_bounded_inversion` (restated) | under `blockingAcyclic`, a thread with a waiter of effective deadline `d` has effective deadline `≤ d` | CB1.8 |
| T8 | `edfCurrentEarliestOnCore` preservation | preserved by `scheduleEffectiveOnCore`, `handleRescheduleSgiOnCore`, `switchToThreadOnCore`, `timerTickOnCore`, `scheduleDomainOnCore`, `enqueueRunnableOnCore` (with the reschedule decision that follows a wake) | CB1.9, CB1.10 |
| T9 | `chooseThreadEffectiveOnCore_eq_flat_of_no_servers` | if every SchedContext in `st` has `parentServer = none`, the CB3 selector equals the CB1 selector | CB3.4 |
| T10 | `timerTickBudgetOnCore_eq_flat_of_root` | if the running thread's SchedContext has `parentServer = none`, the CB4 tick arm equals the CB1 tick arm | CB4.3 |
| T11 | `server_subtree_consumption_bounded` | for a server `s` with `wellFormed`, the ticks charged to threads in `s`'s subtree while `s.periodStart` is unchanged sum to at most `s.budget` (every such tick charges `s`, T4) | CB4.9 |
| T12 | `member_isolation` | a member's own consumption per window is bounded by its own `budget` whatever its siblings consume | CB4.9 |
| T13 | `rootAdmission_sound_per_core` | `hierarchicalAdmissionHolds st → ∀ c, Σ U over roots active on c ≤ 1000` (and the member sum for every server) | CB5.2 |
| T14 | `server_receives_budget_within_window` | **Hypotheses**: `hierarchicalAdmissionHolds st`, `schedContextStoreConsistent st`, `schedHierarchyInvariant st`, `domainSchedule = []` (single-domain mode; the domain-rotating form is a follow-up), the per-core run loop steps (`perCoreTimerTickStep`, the dispatch and wake transitions) on core `c`, and — if CB7.7 cannot close the composition — `edfTraceFeasible`.  **Conclusion**: a root entity active on `c` at `t` with `budgetRemaining = b > 0` is charged `b` ticks before `deadline`, or becomes inactive first | CB7.7 |
| T15 | `cbs_demand_bound` | on a core satisfying `hierarchicalAdmissionHolds`, the total budget of windows ending in any interval `[t₁, t₂)` is at most `t₂ − t₁` | CB7.7 |
| T16 | `edf_selects_earliest_eligible` | whenever `chooseThreadEffectiveOnCore` returns `some tid`, no eligible in-domain candidate has an `isBetterPath`-better key path | CB3.5, CB7.7 |

T14 is the classical EDF+CBS theorem.  The proof plan: T15 from the admission
sum and T4 (each window demands at most its budget); T16 from the selector's
optimality; the composition by the processor-demand argument over the per-core
step relation (a deadline miss at `d` would need more demand in some
`[t₀, d)` than `d − t₀`, contradicting T15).  The per-core step relation is
defined for this theorem over `perCoreTimerTickStep` and the dispatch
transitions, not over WS-SL's `bootCoreId`-pinned `ValidTrace`; WS-SL's
limitation is cited, not crossed.

### 4.12 Lock footprints and WCRT

The tick keeps `timerTickOnCoreLockSet c` (object store write, run queue `c`
write, replenish queue `c` write): `chargeSchedPath` writes only the path's
SchedContexts (object store) and core `c`'s replenish queue
(`chargeSchedPath_writes_within_timerTickOnCoreLockSet`).  The model-level
per-object footprint adds at most `maxServerDepth` SchedContext locks
(`chargeSchedPathLockSet`), so the tick's complete footprint is at most
`3 + 3 = 6 ≤ maxLockSetSize` (`pathLockFootprint_le_maxLockSetSize`).  New
transition footprints, in the `lockSet_schedContextBind` pattern
(`lockSetOfList`, ascending by `LockId`):

| Transition | Footprint |
|------------|-----------|
| `schedContextConfigureServer` | caller TCB (read), CNode root (read), the SchedContext (write) |
| `schedContextBindServer` | caller TCB (read), CNode root (read), server (write), child (write), the child's bound TCB (write) when present |
| `schedContextUnbindServer` | caller TCB (read), CNode root (read), child (write), parent (write), the child's bound TCB (write) when present |

Each carries `_write_only`-style shape lemmas, `_pairwise_le` and
`_size_le_maxLockSetSize` (at most 5).  `WCRT_smp`'s lock-wait terms are
unchanged; the selection scan's `O(n · maxServerDepth)` is a compute cost
outside the lock-WCRT model and is recorded in the docstring of
`chooseBestRunnableHierarchical` with the deadline-ordered index as the
registered remedy.

### 4.13 Information flow

Projection (`InformationFlow/Projection.lean`, `ObservableStatePerCore.lean`):
`parentServer`, `serverMembers`, `serverCore`, `activeDescendants` are erased
as structural scheduling plumbing (the `boundThread` class); `periodStart`
follows whatever class `deadline` is in today; `inheritedDeadline` follows
`pipBoost`.  `schedContextWriteSet` stays the singleton `[homeCore]`, since a
member's ancestors share its core.

`schedContextBindServerChecked` requires
`securityFlowsTo (objectLabelOf child) (objectLabelOf server) ∧ securityFlowsTo (objectLabelOf server) (objectLabelOf child)`
under the installed labeling context and refuses with `.flowDenied`; it is the
only member-adding transition, so `serverMembersUniformlyLabeled ctx st`
(every member's label is equivalent to its server's) is established there and
preserved everywhere else.  Under it, `chargeSchedPath_confined_to_label`: the
tick's ancestor writes are same-label, and SM8.B's per-core non-interference
lift over the tick keeps its shape.  The three arms are control-only in
`contentFlowClass`; they record no declassification and raise no fault.  The
inter-server ordering channel at the root — one server's deadline position
observable through another's dispatch latency — is the class SM8.D already
bounds for priority bands, re-derived for deadline order in CB7.5 and recorded
in the lock-domain register.

### 4.14 Staging and module layout

| Module | Role | Partition |
|--------|------|-----------|
| `SeLe4n/Kernel/SchedContext/Hierarchy.lean` (new) | constants, `MemberList`, queries, `SchedKey` | production from CB2.3 (imported by `Operations.lean`) |
| `SeLe4n/Kernel/SchedContext/HierarchyOperations.lean` (new) | the three transitions | production from CB5.1 (unreachable until CB6.4) |
| `SeLe4n/Kernel/SchedContext/Invariant/HierarchyDefs.lean` (new) | `schedHierarchyInvariant`, isolation theorems | production from CB2.6 (needed by `CrossSubsystem.lean` at CB5.13) |
| `SeLe4n/Kernel/SchedContext/Invariant/HierarchyPreservation.lean` (new) | the CB5.12 surface | staged (`Platform/Staged.lean` + allowlist line `SeLe4n.Kernel.SchedContext.Invariant.HierarchyPreservation  # marker: CB5.12 surface until the dispatch payoff imports it`), promoted at CB6.11 |
| `SeLe4n/Kernel/Scheduler/Liveness/EdfGuarantee.lean` (new) | T14–T16 | staged like `PerCoreWcrt.lean` |
| `SeLe4n/Kernel/SchedContext/HierarchyInventory.lean` (new) | theorem inventory | staged; claimed by the workstream manifest of CB8.2 |
| `tests/HierarchicalServerSuite.lean` (new) | Tier-2 suite, `lake exe hierarchical_server_suite` | `lakefile.toml` + `test_tier2_negative.sh` |

Promotion (CB6.11) removes the allowlist lines and replaces `STATUS: staged`
markers with landing notes in the same cut; the partition gate must pass in
both directions.

### 4.15 Tests, scenarios and fixtures

Concrete scenarios (ticks; `(Q, P)` = budget, period; `dl` = deadline):

| Id | Scenario | Expected | Row |
|----|----------|----------|-----|
| S0 | two bound threads A `(prio 5, dl 100)`, B `(prio 3, dl 50)`, same domain, both eligible | pre-CB1: A; post-CB1: B — the witness inverted in CB1.2 | CB0.4 |
| S1 | legacy pair `prio 7` vs `prio 2`, unbound | `7` before and after; a bound `dl 1000` thread beats an unbound `prio 255` thread after CB1 | CB1.2 |
| S2 | `(Q, P) = (3, 10)` configured at `t = 0`; runs 3 ticks | exhausted at `t = 3`; one refill `(scId, 10)`; at `t = 10`: `budgetRemaining = 3`, window `[10, 20)`, `dl = 20`.  Pre-fix witness (inverted): a refill of `1` at `t = 13` | CB1.4 |
| S3 | same context, blocks at `t = 2` with `budgetRemaining = 1` | wake at `t = 12`: `dl 10 ≤ 12` → window `[12, 22)`, budget `3`; wake at `t = 5`: `1·10 < 5·3` → untouched; wake at `t = 8`: `1·10 ≥ 2·3` → window `[8, 18)`, budget `3` | CB1.6 |
| S4 | client C `(dl 20)` calls active server S `(own dl 100)`; thread X `(dl 50)` runnable | S's effective deadline `20`, S outranks X; after the reply S's `inheritedDeadline = none` | CB1.7 |
| S5 | root server R `(dl 30)` with members m1 `(dl 200, prio 1)`, m2 `(dl 100, prio 9)`; root leaf L `(dl 40)` | order m2, then (R exhausted) L; two servers with equal deadline and priority order by `scId` | CB3.9 |
| S6 | server `(4, 20)` with members m1, m2 each `(3, 20)`; m1 runs 2 ticks, m2 runs 2 | server exhausted at `t = 4` with both members holding budget `1` → both ineligible; refill at `t = 20` → both eligible with the server's new window; nested: R `(6, 20)` ⊃ C `(3, 20)` ⊃ leaf — C exhausts at `t = 3` while R keeps `3`, C's leaf ineligible, R's other member runs | CB4.10 |
| S7 | through `syscallDispatchFromAbi`: retype three SchedContexts; configure the server `(4, 20)`; `configureServer core 1`; configure two leaves `(2, 20)` and `(3, 20)`; `bindServer` the first (ok) and the second (`.resourceExhausted`, `2 + 3 > 4` in per-mille terms); bind threads; ticks; `unbindServer`; error arms: cycle (`.cyclicDependency`), undeclared core (`.invalidArgument`), cross-domain (`.invalidArgument`), off-core thread (`.threadOnDifferentCore`) | golden fixture `hierarchical_server_syscalls.expected` | CB6.12 |
| S8 | two labels; `bindServer` across labels → `.flowDenied`; same label → ok; a tick on the hierarchy leaves the other label's observation unchanged; two servers `(2, 5)` on one core (`U = 0.8`) each receive `2` per window over `[0, 10)` | in the information-flow and CBS suites | CB7.9 |

Fixture discipline: every new `.expected` ships with its `.expected.sha256`
and a row in `tests/fixtures/README.md`, following its *Regeneration
workflow*; scenario ids take a new bracket prefix `[HCB-nnn]` in
`tests/fixtures/scenario_registry.yaml` (subsystem `Scheduler`), which
`scripts/scenario_catalog.py validate-registry` checks.  CB1.14's refresh
lists, per refreshed fixture, the deadline-bearing thread whose position or
refill moved.

## 5. Dependencies

* **WS-SM SM5.A/SM5.D/SM5.F/SM5.H** (landed): the per-core selector, tick,
  priority-inheritance and CBS surface this workstream changes and then
  generalises.
* **WS-SM SM8.A–D** (landed): the per-core observer and the write-set
  discipline CB1.12, CB2.9 and CB7 extend.
* **WS-RR RR5** (landed): the declared-core discipline CB5.1 reuses for a
  server's core, and the boot theorems CB2.7 keeps intact.
* **WS-RR RR6–RR8**: no dependency either way; §2.3 states the file partition.
* **SM10**: none.  CB6's fixtures are re-cut if the image lands first.

## 6. Phase map

| Phase | Scope (one line) | Subs | Est |
|-------|------------------|------|-----|
| CB0 | Registration, baseline verification, the pre-existing configure-authority gap, order witnesses | 5 | S–M |
| CB1 | The EDF-first root on the flat model: windows and kernel-owned deadlines, the refill accounting, the wake-up rule, deadline inheritance, the selector and its suite, the one fixture refresh | 14 | XL |
| CB2 | Model: hierarchy fields, bounded queries, per-object and store-level invariants, boot and observer erasure — inert | 10 | M–L |
| CB3 | Hierarchical selection and eligibility, provably identical on states without servers | 9 | L |
| CB4 | Hierarchical charging, activation and refills on the per-core tick; the subtree isolation theorems | 10 | L–XL |
| CB5 | Hierarchy transitions and the hierarchy-aware forms of the existing operations, each with its preservation surface | 16 | XL |
| CB6 | The three syscalls on both sides of the ABI, flow classification, dispatch payoff, end-to-end fixtures | 12 | L |
| CB7 | Information-flow re-establishment and the CBS guarantee | 9 | L–XL |
| CB8 | Closure: specification, evidence, inventory, hardware spot-check script, hand-off | 8 | M |

## 7. Sub-tasks

Estimates: **T** trivial (<1h) · **S** small (<½ day) · **M** medium (1–2 days)
· **L** large (3–5 days) · **XL** extra-large (>1 week, expect to split further).
Each sub-task is sized to be one coherent PR or less, per the PR checklist.
Where a row says **in the same row as**, the switch and the theorem that
licenses it cannot compile apart and land as one cut.  Every row names the
§4 item it implements.

### CB0 — Registration and baseline

Nothing here changes scheduling behaviour except CB0.3, which removes an
authority gap the flat model already has.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| CB0.1 | Register the workstream: the **WS-CB** registry row, the debt-register row pointing at this plan, the `CLAUDE.md`/`AGENTS.md` status subsection, this plan, the v0.34.49 CHANGELOG entry | `docs/REGISTERED_DEBT.md`, `CLAUDE.md`, `AGENTS.md`, `CHANGELOG.md` | S |
| CB0.2 | Pre-implementation refinement pass at the opening cut: re-verify every §1.1 claim against the tree, fold corrections into §1, §3 and §4 (the WS-RA precedent), re-run the prefix collision measurement | this plan | S |
| CB0.3 | Close the priority and domain half of §3.3: `schedContextConfigure` takes the caller, gates `priority` through `validatePriorityAuthority` against the caller's MCP, and refuses a `domain` change on a bound SchedContext with `.illegalAuthority` (§4.8); theorems `schedContextConfigure_priority_within_caller_mcp`, `schedContextConfigure_domain_fixed_of_bound`; negative-suite pins; trace-fixture refresh with rationale | `SeLe4n/Kernel/SchedContext/Operations.lean`, `SeLe4n/Kernel/API.lean`, `tests/NegativeStateSuite.lean`, `tests/fixtures/main_trace_smoke.expected` | M |
| CB0.4 | Order and refill witnesses landed **first** (§4.15 S0 and the pre-fix half of S2): Tier-2 pins of the pre-CB1 fixed-priority-first order and of the one-tick refill — the scenarios CB1 inverts in its switch cuts (the WS-RA RA.E.1 precedent: a witness that fails on the pre-migration tree, then pins the post-flip behaviour) | `tests/SmpCbsSuite.lean` | S |
| CB0.5 | Stale-comment sweep on files this workstream edits: the Rust `SyscallId` header's variant count and Lean line references, the `dispatchCapabilityOnly` docstring's arm count, the evidence index's staged-module count, and the exhaustion-arm docstring that describes the refill the code does not perform | `rust/sele4n-types/src/syscall.rs`, `SeLe4n/Kernel/API.lean`, `docs/CLAIM_EVIDENCE_INDEX.md`, `SeLe4n/Kernel/Scheduler/Operations/Core.lean` | S |

**Acceptance**: CB0.3's two theorems elaborate; `lake exe smp_cbs_suite` runs
the CB0.4 witnesses green against the pre-CB1 tree; Tier 0 and the docs-sync
lane pass.

### CB1 — The EDF-first root, on the flat model

The one phase whose behavioural change is intended to reach existing
fixtures.  It lands in this order: the order and the selector with their
equivalence theorem (CB1.1–CB1.2), the CBS engine rules (CB1.3–CB1.6),
inheritance (CB1.7–CB1.8), the decisions and suite (CB1.9–CB1.13), the
refresh (CB1.14).  No server field exists yet, so every theorem here is a
flat-model theorem the hierarchy phases generalise.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| CB1.1 | The order (§4.3): `isBetterKey` and `isBetterCandidate` rewritten EDF-first; `isBetterKey_irrefl`, `_asymm`, `_trans` (T1); `isBetterCandidate_legacy_class_eq_fp` (two deadline-less candidates compare as before) | `SeLe4n/Kernel/Scheduler/Operations/Selection.lean` | M |
| CB1.2 | Selection by scan (§4.4): `chooseBestRunnableHierarchical` in singleton form inside `chooseThreadEffectiveOnCore`, the bucket-first fast path retired, totality and optimality re-proved, **in the same row as** T2 `chooseThreadEffectiveOnCore_eq_flat_of_no_deadlines` and the inversion of CB0.4's order witness (consumes CB1.1) | `SeLe4n/Kernel/Scheduler/Operations/Selection.lean`, `SeLe4n/Kernel/Scheduler/Operations/PerCoreChooseThread.lean`, `tests/SmpCbsSuite.lean` | XL |
| CB1.3 | Windows and kernel-owned deadlines (§4.2 rules (a), (f); D13): `periodStart` becomes the window start; `schedContextConfigure` refuses a nonzero `deadline` argument (`.invalidArgument`) and applies rule (a); `deadlineWindowConsistent` joins `SchedContext.wellFormed`; `bootSafeSchedContextCheck` and `SchedContext.empty`/`mkChecked` follow; T3 for `cbsWindowStart` | `SeLe4n/Kernel/SchedContext/Types.lean`, `SeLe4n/Kernel/SchedContext/Operations.lean`, `SeLe4n/Kernel/SchedContext/Budget.lean`, `SeLe4n/Kernel/SchedContext/Invariant/Defs.lean`, `SeLe4n/Platform/Boot.lean` | M |
| CB1.4 | Refill accounting (§4.2 rules (b)–(d); D16 — the §1.1 defect): `cbsScheduleRefill`, `cbsLandRefill`, the surrender rule in `handleYieldWithBudget`; both tick arms and `refillSchedContext` rewritten over them; `cbsUpdateDeadline` retired; `atMostOnePendingRefill` and `pendingRefillOnlyWhenExhausted` join `wellFormed`; T3 for the two rules, T4 `window_consumption_le_budget`, T5 `refill_dead_time_le_period`; `replenishment_within_period` / `_dead_time_exact` restated; the tick's CBS preservation family (`timerTickOnCore_preserves_perCoreCbsInvariant` and siblings) re-proved over the new arms; the pre-fix half of CB0.4's refill witness inverted (consumes CB1.3) | `SeLe4n/Kernel/SchedContext/Budget.lean`, `SeLe4n/Kernel/Scheduler/Operations/Core.lean`, `SeLe4n/Kernel/SchedContext/Invariant/Defs.lean`, `SeLe4n/Kernel/Scheduler/Liveness/Replenishment.lean`, `SeLe4n/Kernel/Scheduler/Operations/PerCoreTickCbsPreservation.lean`, `tests/SmpCbsSuite.lean` | XL |
| CB1.5 | Retire `TCB.deadline` from selection (§4.1): `resolveEffectivePrioDeadline` yields no deadline for `.unbound`; the field removed with its `BEq`, `ext`, boot and projection sweeps; the three suites that set it re-cut | `SeLe4n/Model/Object/Types.lean`, `SeLe4n/Kernel/Scheduler/Operations/Selection.lean`, `tests/SmpCancellationSuite.lean`, `tests/NegativeStateSuite.lean`, `tests/PriorityInheritanceSuite.lean` | M |
| CB1.6 | The CBS wake-up rule `cbsActivate` (§4.2 rule (e); D14) applied in `enqueueRunnableOnCore` when a bound thread becomes active from inactive; T3 for it, T6 `cbsActivate_noop_of_fresh`; the stale-refill interaction with rule (d) proved (`cbsLandRefill_drops_stale`) (consumes CB1.4) | `SeLe4n/Kernel/Scheduler/Operations/Selection.lean`, `SeLe4n/Kernel/SchedContext/Budget.lean`, `SeLe4n/Kernel/SchedContext/Invariant/Defs.lean` | M |
| CB1.7 | Deadline inheritance (§4.7; D15): `TCB.inheritedDeadline` with its `BEq`, `ext`, boot and projection sweeps; `computeMinWaiterDeadline`, `effectiveDeadline`; `updatePipBoost` writes both fields; `revertPriorityInheritance` clears both; the per-core forms `updatePipBoostOnCore` and `propagatePipChainCrossCore` follow (consumes CB1.2) | `SeLe4n/Kernel/Scheduler/PriorityInheritance/Compute.lean`, `SeLe4n/Kernel/Scheduler/PriorityInheritance/Propagate.lean`, `SeLe4n/Kernel/Scheduler/PriorityInheritance/PerCore.lean`, `SeLe4n/Model/Object/Types.lean` | L |
| CB1.8 | The PIP theorem surface in deadline terms: T7 `pip_bounded_inversion` restated, blocking-graph acyclicity untouched, the donation-preservation family re-proved over the new field (consumes CB1.7) | `SeLe4n/Kernel/Scheduler/PriorityInheritance/BoundedInversion.lean`, `SeLe4n/Kernel/Scheduler/PriorityInheritance/Preservation.lean`, `SeLe4n/Kernel/IPC/Invariant/DonationPreservation.lean` | L |
| CB1.9 | Reschedule decisions in the selector's order (§4.4): `candidateOutranksCurrentOnCore` and `handleRescheduleSgiOnCore`; `setPriorityOp`'s "priority decreased" trigger becomes "key worsened"; bind and configure keep the AK2-B priority mirror as the bucket rule; `edfCurrentEarliestOnCore` (§4.10) replaces `edfCurrentHasEarliestDeadlineOnCore` in the per-core bundle (consumes CB1.7) | `SeLe4n/Kernel/Scheduler/Operations/Selection.lean`, `SeLe4n/Kernel/SchedContext/PriorityManagement.lean`, `SeLe4n/Kernel/Scheduler/Invariant/PerCore.lean` | L |
| CB1.10 | The per-core suite re-proved over the new selector, engine and conjunct (T8): the `schedulerInvariantStrong_smp` family for `scheduleEffectiveOnCore`, `handleRescheduleSgiOnCore`, `switchToThreadOnCore`, the tick's preempt path and the domain switch; the idle keystone unchanged, since the idle thread is deadline-less and last (consumes CB1.9) | `SeLe4n/Kernel/Scheduler/Invariant/PerCoreInvariantSuite.lean`, `SeLe4n/Kernel/Scheduler/Operations/PerCoreWake.lean`, `SeLe4n/Kernel/Scheduler/Operations/PerCoreTimerTick.lean` | XL |
| CB1.11 | Frozen twins and agreement: `frozenTimerTickBudget` and `frozenSchedContextConfigure` over the new rules; the agreement interlock re-proved | `SeLe4n/Kernel/FrozenOps/Operations.lean`, `SeLe4n/Kernel/FrozenOps/Agreement.lean` | S |
| CB1.12 | Observer and non-interference (§4.13): `inheritedDeadline` and `periodStart` classified for the projection; SM8.B's per-core lift re-proved over the new selector and engine — the observable order changes only through same-label deadlines (consumes CB1.10) | `SeLe4n/Kernel/InformationFlow/Projection.lean`, `SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean`, `SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean` | L |
| CB1.13 | Liveness surface restated for EDF: the band-based `WCRTHypotheses` and `bandExhaustionBound` kept for the legacy class; the EDF class's response bound stated as `edfResponseBound := domainRotationBound + period` with its hypotheses, proved as far as CB7 commits to; the lock-wait terms of `PerCoreWcrt` unchanged | `SeLe4n/Kernel/Scheduler/Liveness/WCRT.lean`, `SeLe4n/Kernel/Scheduler/Operations/PerCoreWcrt.lean` | L |
| CB1.14 | The one policy refresh (§1.4, §4.15): every `.expected` whose scenario has a deadline-bearing runnable thread or a refill re-cut with rationale (the SM5.K four-core golden, the main trace, the WS-RA and fault fixtures where bound threads appear), the scenario registry updated; spec §8.12.1–§8.12.3 and §8.13 rewritten for the engine rules, EDF-first and deadline inheritance; evidence-index rows; Tier-3 anchors; the `CLAUDE.md`/`AGENTS.md` standing constraint | `tests/fixtures/`, `docs/spec/SELE4N_SPEC.md`, `docs/CLAIM_EVIDENCE_INDEX.md`, `scripts/test_tier3_invariant_surface.sh`, `CLAUDE.md`, `AGENTS.md` | L |

**Acceptance**: T2 elaborates with no hypothesis beyond the absence of
deadlines; every conjunct §4.10 adds to `SchedContext.wellFormed` is preserved
by every CBS rule and every transition; T4 and T5 are stated over any
well-formed context; `edfCurrentEarliestOnCore` is preserved by every per-core
transition; T7 is stated over deadlines and is not vacuous on bound threads;
every refreshed fixture carries its rationale in the fixture README; S2 and S3
pass as written.

### CB2 — The model, inert

Every definition here is unreachable from a live path until CB6; the only
behavioural change is that a boot SchedContext must be a parentless leaf,
which every existing fixture already is.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| CB2.1 | Add `parentServer`, `serverMembers`, `serverCore`, `activeDescendants` to `SchedContext` with defaults (§4.1); `MemberList`; `isServer`, `isLeaf`; extend the manual `BEq` instance | `SeLe4n/Kernel/SchedContext/Types.lean`, `SeLe4n/Kernel/SchedContext/Hierarchy.lean` (new) | M |
| CB2.2 | Sweep every constructor-arity destructuring the build now rejects — `schedContextReferencesReservedIdleSlot`, `bootSafeSchedContextCheck` and siblings — classifying the new fields: a member or parent id naming a reserved idle object is refused, and a boot SchedContext is a parentless leaf with no active descendants | `SeLe4n/Platform/Boot.lean`, whatever else the build names | S |
| CB2.3 | Constants `maxServerDepth := 3`, `maxServerMembers := 16` (§4.1) with `pathLockFootprint_le_maxLockSetSize` (§4.12) and a docstring recording the cost of one path charge | `SeLe4n/Kernel/SchedContext/Hierarchy.lean` | S |
| CB2.4 | Fuel-bounded hierarchy queries `parentChain?`, `rootOf?`, `depthOf?`, `isAncestorOf`, `schedPath?` (§4.1) with congruence over `getSchedContext?` and the `_of_root` simplifications (a parentless leaf's chain is empty, its path the singleton); `schedPath_not_prefix` | `SeLe4n/Kernel/SchedContext/Hierarchy.lean` | M |
| CB2.5 | Per-object well-formedness: `serverRoleExclusive` and `serverMembersBounded` join `SchedContext.wellFormed` (§4.10); `schedContextWellFormed` follows; the Z2 preservation theorems re-proved (every CBS rule frames the hierarchy fields) | `SeLe4n/Kernel/SchedContext/Types.lean`, `SeLe4n/Kernel/SchedContext/Invariant/Defs.lean` | M |
| CB2.6 | The store-level bundle `schedHierarchyInvariant` (§4.10, six conjuncts), decidable where the arithmetic allows, with projections and `default_schedHierarchyInvariant` | `SeLe4n/Kernel/SchedContext/Invariant/HierarchyDefs.lean` (new) | M |
| CB2.7 | Boot: `bootSafeSchedContextCheck` requires a parentless, memberless, inactive leaf; `bootFromPlatformCheckedWithIdleThreadsFor_schedHierarchyInvariant` on the production boot path (consumes CB2.6) | `SeLe4n/Platform/Boot.lean` | M |
| CB2.8 | Equality pins: the `BEq` instance reads every field (a witness that two contexts differing only in `parentServer` compare unequal, the SM3.A audit-pass lesson) and a `SchedContext.ext` lemma over the full field list | `SeLe4n/Kernel/SchedContext/Types.lean` | S |
| CB2.9 | Observer projection (§4.13): erase the four fields in `projectKernelObject` and the per-core observer; re-prove the projection lemmas the erasure touches; `schedContextWriteSet` stays the singleton | `SeLe4n/Kernel/InformationFlow/Projection.lean`, `SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean` | M |
| CB2.10 | Freeze mirror: `FrozenKernelObject.schedContext` carries the record verbatim, so the freeze/thaw proofs and the lock projection re-elaborate over the new fields; Tier-3 anchors for CB2; `docs/codebase_map.json` regenerated; spec §8.12.8 skeleton stating "model landed, inert" | `SeLe4n/Model/FrozenState.lean`, `SeLe4n/Model/FreezeProofs.lean`, `scripts/test_tier3_invariant_surface.sh`, `docs/spec/SELE4N_SPEC.md` | S |

**Acceptance**: `lake build` of every touched module; `crossSubsystemInvariant`
is **not** yet extended (that is CB5.13, after the refusal it depends on);
every fixture byte-identical to the post-CB1 baseline.

### CB3 — Hierarchical selection

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| CB3.1 | `pathBudgetEligible st tcb` (§4.4) with `pathBudgetEligible_eq_hasSufficientBudget_of_root` (consumes CB2.4) | `SeLe4n/Kernel/Scheduler/Operations/Selection.lean` | S |
| CB3.2 | `resolveEffectiveSchedPath st tcb : List SchedKey` (§4.3), root-first, the leaf key lowered by `inheritedDeadline` and lifted by `pipBoost`; `resolveEffectiveSchedPath_root_eq_resolveEffectivePrioDeadline` (the singleton is CB1's key) | `SeLe4n/Kernel/Scheduler/Operations/Selection.lean` | M |
| CB3.3 | `isBetterPath` (§4.3) over `isBetterKey` with `isBetterPath_irrefl`, `_asymm`, `_trans` (T1) and `isBetterPath_singleton_eq_isBetterKey` | `SeLe4n/Kernel/Scheduler/Operations/Selection.lean` | M |
| CB3.4 | `chooseBestRunnableHierarchical` in path form inside `chooseThreadEffectiveOnCore`, **in the same row as** T9 `chooseThreadEffectiveOnCore_eq_flat_of_no_servers` (consumes CB3.1–CB3.3) | `SeLe4n/Kernel/Scheduler/Operations/Selection.lean` | L |
| CB3.5 | Totality and optimality restated: `chooseBestRunnableHierarchical_always_ok` and `_optimal` (T16 in its selection form), the skip-corrupt-entry contract kept | `SeLe4n/Kernel/Scheduler/Operations/PerCoreChooseThread.lean` | L |
| CB3.6 | `candidateOutranksCurrentOnCore` in path form, so `handleRescheduleSgiOnCore` decides in the selector's own order | `SeLe4n/Kernel/Scheduler/Operations/Selection.lean` | M |
| CB3.7 | `edfCurrentEarliestOnCore` in path form (§4.10) with the flat corollary; `schedulerPriorityMatchOnCore` and `effectiveParamsMatchRunQueueOnCore` unchanged in meaning, since the bucket orders nothing | `SeLe4n/Kernel/Scheduler/Invariant/PerCore.lean` | L |
| CB3.8 | Re-prove the selection-dependent suite: `chooseThreadOnCore_ok_of_runnableTCBs`, the idle keystone (untouched — idle threads are unbound), and the `schedulerInvariantStrong_smp` preservation family for `scheduleEffectiveOnCore` and `handleRescheduleSgiOnCore` | `SeLe4n/Kernel/Scheduler/Invariant/PerCoreInvariantSuite.lean`, `SeLe4n/Kernel/Scheduler/Operations/PerCoreWake.lean` | L |
| CB3.9 | Fixtures byte-identical to the post-CB1 baseline (every `.expected`); Tier-2 scenario S5 (§4.15) on hand-built hierarchies via `StateBuilder.withServerHierarchy`; Tier-3 anchors | `tests/SmpCbsSuite.lean`, `SeLe4n/Testing/StateBuilder.lean` | M |

**Acceptance**: T9 elaborates without hypotheses beyond parentlessness;
`test_tier2_trace.sh` reports every sha256 unchanged from the post-CB1
baseline; S5 passes as written.

### CB4 — Hierarchical charging, activation and refills

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| CB4.1 | `chargeSchedPath st c path now : SystemState × Bool` (§4.5) with frames: `getTcb?` unchanged, every run queue unchanged, only core `c`'s replenish queue and the path's contexts written | `SeLe4n/Kernel/Scheduler/Operations/Core.lean` | M |
| CB4.2 | Generalise the three home readers to servers: `schedContextReplenishHome` (a server's home is `serverCore`), `replenishQueueAffinityConsistentOnCore` and `replenishQueueEntriesBoundOnCore` (an entry's context is bound **or** a server homed on `c`), each with its `_of_leaf` equivalence | `SeLe4n/Kernel/SchedContext/Operations.lean`, `SeLe4n/Kernel/SchedContext/ReplenishAffinity.lean`, `SeLe4n/Kernel/SchedContext/BindingAffinity.lean` | M |
| CB4.3 | `timerTickBudgetOnCore`'s bound arm charges through `chargeSchedPath`, leaf-only timeouts, preemption iff any level exhausted, **in the same row as** T10 `timerTickBudgetOnCore_eq_flat_of_root` (consumes CB4.1, CB4.2) | `SeLe4n/Kernel/Scheduler/Operations/Core.lean` | L |
| CB4.4 | Re-prove the tick preservation family over the new body — the ten `timerTickOnCore_preserves_*` structural theorems, `allThreadsTimeSlicePositive`, `schedulerInvariantStructuralRegNodup_perCore`, and the CBS side (`replenishQueueValidOnCore`, `replenishmentPipelineOrderOnCore`, `perCoreCbsInvariant`) — mostly by T10's reduction plus CB4.1's frames | `SeLe4n/Kernel/Scheduler/Operations/PerCoreTimerTick.lean`, `SeLe4n/Kernel/Scheduler/Operations/PerCoreTickCbsPreservation.lean`, `SeLe4n/Kernel/Scheduler/Operations/PerCoreTickCbsAffinity.lean`, `SeLe4n/Kernel/Scheduler/Invariant/PerCoreInvariantSuite.lean` | XL |
| CB4.5 | Server refills: `replenishWakeDecision` (`.wakeThread`, `.rescheduleCore`, `.none`) replacing `replenishWakeTarget`; `processOneReplenishmentOnCore` lands a server's refill by rule (d) and raises the local-wake bit on `.rescheduleCore`; `cbsReplenish_server_reschedules_local`, `replenishWakeDecision_leaf_eq_target` (consumes CB1.4) | `SeLe4n/Kernel/Scheduler/Operations/Core.lean`, `SeLe4n/Kernel/Scheduler/Operations/PerCoreTimerTick.lean` | M |
| CB4.6 | Activation along the path (§4.5): `noteActivated` in `enqueueRunnableOnCore`, `noteDeactivated` in `removeRunnable` (repointed from `bootCoreId` to the thread's home core), `suspendThreadOnCore`, the cancellation and fault suspends, `cleanupTcbReferences` and the current-clearing dispatch paths; `cbsActivate` on every server whose count goes `0 → 1`; `activeDescendantsConsistent` and the `wellFormed` conjuncts preserved by every path that moves the count (consumes CB1.6, CB2.6) | `SeLe4n/Kernel/Scheduler/Operations/Selection.lean`, `SeLe4n/Kernel/Scheduler/Operations/Core.lean`, `SeLe4n/Kernel/IPC/Operations/Endpoint.lean`, `SeLe4n/Kernel/Lifecycle/Suspend.lean` | L |
| CB4.7 | Lock footprint (§4.12): `chargeSchedPath_writes_within_timerTickOnCoreLockSet` and the model-level `chargeSchedPathLockSet` with `_pairwise_le` and `_size_le_maxLockSetSize` (consumes CB2.3) | `SeLe4n/Kernel/Scheduler/Operations/PerCoreTimerTick.lean` | M |
| CB4.8 | `schedHierarchyInvariant` preserved by the tick, the drain, `replenishOnCore` and the activation paths — budgets, deadlines, window starts and counts move, the tree fields are framed | `SeLe4n/Kernel/Scheduler/Operations/PerCoreTickCbsPreservation.lean` | M |
| CB4.9 | Isolation theorems (§4.11): `chargeSchedPath_charges_every_ancestor`, T11 `server_subtree_consumption_bounded`, T12 `member_isolation` | `SeLe4n/Kernel/SchedContext/Invariant/HierarchyDefs.lean` | L |
| CB4.10 | Tier-2 scenario S6 (§4.15) plus an idle-server activation by rule (e); golden fixture `tests/fixtures/hierarchical_server_tick.expected` with its sha256 and README row; Tier-3 anchors | `tests/SmpCbsSuite.lean`, `tests/fixtures/` | M |

**Acceptance**: `timerTickOnCore_preserves_perCoreCbsInvariant` and the
structural family elaborate over the new body; T11 is stated over an arbitrary
subtree, not a fixed depth; every pre-existing fixture byte-identical to the
post-CB1 baseline; S6 passes as written.

### CB5 — Hierarchy transitions, proven before they are reachable

Every transition here is a production definition with no caller until CB6.
The affinity refusal in CB5.8 lands before CB5.13 because the cross-subsystem
bridge for affinity is false without it.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| CB5.1 | `schedContextConfigureServer vScId core` per its §4.8 table, rule (a) window start, root admission on `core` (consumes CB2.4, CB2.6) | `SeLe4n/Kernel/SchedContext/HierarchyOperations.lean` (new) | M |
| CB5.2 | Per-core root admission (§4.6): `rootActiveOnCore`, `rootUtilisationOnCore`, `checkRootAdmissionOnCore`, `memberUtilisation`, `checkMemberAdmission`; `schedContextConfigure` and `schedContextBind` route through them — a root leaf is admitted on its thread's core at bind, `.resourceExhausted` becoming a bind refusal; T13 `rootAdmission_sound_per_core`; negative-suite and trace-fixture updates with rationale | `SeLe4n/Kernel/SchedContext/Operations.lean`, `SeLe4n/Kernel/SchedContext/Budget.lean` | L |
| CB5.3 | `schedContextBindServer vServer vChild` per its §4.8 table: the check list in order, the bidirectional link, the child's count folded into the ancestors' with rule (e) on any `0 → 1` (consumes CB5.2) | `SeLe4n/Kernel/SchedContext/HierarchyOperations.lean` | L |
| CB5.4 | `schedContextUnbindServer vChild` per its §4.8 table (consumes CB5.2) | `SeLe4n/Kernel/SchedContext/HierarchyOperations.lean` | M |
| CB5.5 | Hierarchy-aware `schedContextBind` (§4.8): refuses a server target; checks the thread's home core against the ancestor's `serverCore`; the bound thread's activity enters the ancestors' counts; `scThreadIndex` unchanged (consumes CB4.6) | `SeLe4n/Kernel/SchedContext/Operations.lean` | M |
| CB5.6 | Hierarchy-aware `schedContextConfigure` (§4.8): member admission against the parent, root admission per core; rule (a) on a populated server re-assigns its window; priority changes re-bucket nothing beyond the AK2-B mirror (consumes CB5.2) | `SeLe4n/Kernel/SchedContext/Operations.lean` | M |
| CB5.7 | `schedContextUnbind` on a member leaf: today's effect plus the ancestors' counts decremented if the thread was active; `schedContextUnbindOnCore` follows | `SeLe4n/Kernel/SchedContext/Operations.lean`, `SeLe4n/Kernel/SchedContext/OperationsPerCore.lean` | S |
| CB5.8 | `setThreadCpuAffinityWithMigration` refuses a member thread with `.illegalState` before any write; `setThreadCpuAffinityWithMigration_rejects_member` | `SeLe4n/Kernel/Scheduler/Operations/Core.lean` | S |
| CB5.9 | `setPriorityOp` on a member thread changes its tie-break under the caller's MCP and nothing else: `setPriorityOp_member_preserves_schedHierarchyInvariant`; `setMCPriorityOp` unchanged | `SeLe4n/Kernel/SchedContext/PriorityManagement.lean` | S |
| CB5.10 | Donation (§4.8): `donateSchedContext` refuses a member leaf whose `serverCore` differs from the donee's home core; the replenish migration inside the three donation composites is a definitional no-op for members (`member_donation_same_core`); `applyCallDonationOnCore_preserves_schedHierarchyInvariant` and its reply and replyRecv twins | `SeLe4n/Kernel/IPC/Operations/Endpoint.lean`, `SeLe4n/Kernel/IPC/Operations/Donation/Primitives.lean` | M |
| CB5.11 | Lifecycle (§4.8): `lifecyclePreRetypeCleanup` refuses to retype a populated server and unlinks a member leaf before destruction; `hierarchyBidirectional` and `activeDescendantsConsistent` preserved under retype | `SeLe4n/Kernel/Lifecycle/Operations/Cleanup.lean`, `SeLe4n/Kernel/Lifecycle/Operations/RetypeWrappers.lean` | M |
| CB5.12 | Preservation surface for CB5.1–CB5.11: each transition preserves `schedHierarchyInvariant`, `perCoreCbsInvariant`, `runQueueOnCoreWellFormed`, `queueCurrentConsistentOnCore`, `edfCurrentEarliestOnCore`, objects `invExt`, `schedContextStoreConsistent`, `schedContextNotDualBound`, `scThreadIndexConsistent` | `SeLe4n/Kernel/SchedContext/Invariant/HierarchyPreservation.lean` (new; staged until the CB6 promotion cut) | XL |
| CB5.13 | `crossSubsystemInvariant` gains `schedHierarchyInvariant` as its thirteenth conjunct **with** `schedHierarchyInvariant_fields`, the pairwise disjointness analysis redone over the full list, the projections, and every existing operation's bridge extended (consumes CB5.8, CB5.12) | `SeLe4n/Kernel/CrossSubsystem.lean` | L |
| CB5.14 | Lock sets for the three transitions per §4.12 — `lockSet_schedContextConfigureServer`, `lockSet_schedContextBindServer`, `lockSet_schedContextUnbindServer` — with the shape lemmas, `_pairwise_le`, `_size_le_maxLockSetSize` (consumes CB2.3) | `SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean` | M |
| CB5.15 | Frozen twins `frozenSchedContextConfigureServer`, `frozenSchedContextBindServer`, `frozenSchedContextUnbindServer` with their agreement theorems against the live transitions (the coverage-table rows follow once the ids exist, in CB6) | `SeLe4n/Kernel/FrozenOps/Operations.lean`, `SeLe4n/Kernel/FrozenOps/Agreement.lean` | M |
| CB5.16 | Tier-2 negative pins for every refusal arm in the §4.8 tables through a thin-dispatcher sub-helper `runHierarchyRefusalChecks`; Tier-3 anchors for the CB5 surface | `tests/NegativeStateSuite.lean`, `scripts/test_tier3_invariant_surface.sh` | M |

**Acceptance**: every CB5 transition has its row in CB5.12's surface;
`crossSubsystemInvariant` has thirteen conjuncts **and** thirteen field-sets;
every §4.8 refusal has a pin; no live path reaches any of them yet (the
dispatcher's wildcard-unreachable theorems are unchanged until CB6).

### CB6 — The syscalls, live

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| CB6.1 | `SyscallId` variants `.schedContextConfigureServer` (35), `.schedContextBindServer` (36), `.schedContextUnbindServer` (37) per §4.9: `toNat`, `ofNat?`, `count := 38`, `ToString`; the `DecodingSuite` boundary moves to 37/38 | `SeLe4n/Model/Object/Types.lean`, `tests/DecodingSuite.lean` | S |
| CB6.2 | The total-table sweep of §4.9, every table with the value the table there names (consumes CB5.15, CB6.1) | `SeLe4n/Kernel/API.lean`, `SeLe4n/Kernel/Architecture/SyscallReturn.lean`, `SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean`, `SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean`, `SeLe4n/Kernel/InformationFlow/TaintPropagation.lean`, `SeLe4n/Kernel/InformationFlow/RefusalRecord.lean`, `SeLe4n/Kernel/FrozenOps/Operations.lean`, `SeLe4n/Kernel/FrozenOps/Agreement.lean`, `SeLe4n/Kernel/Concurrency/Locks/LockSetForSyscall.lean`, `SeLe4n/Platform/FFI.lean` | M |
| CB6.3 | Arg structures and decoders per §4.9 with encoders, `_roundtrip` and `_error_iff` theorems | `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` | M |
| CB6.4 | `dispatchCapabilityOnly` arms per §4.8/§4.9: configureServer (cap target = the SchedContext), bindServer (cap = the server; the child CPtr resolved through the caller's CSpace with `.write` by `syscallLookupCap`, the `tcbBindNotification` pattern), unbindServer (cap = the child) — each through an `…OnCore` form so the Tier-1 per-core routing gate passes; the wildcard-unreachable proofs restated (consumes CB6.2, CB6.3) | `SeLe4n/Kernel/API.lean` | M |
| CB6.5 | Idle-reservation chokepoint: the child CPtr resolves through `syscallResolveCap`, which refuses a reserved idle object; the core operand is not an object id; `dispatchCapabilityOnly_bindServer_idle_refused` | `SeLe4n/Kernel/API.lean` | S |
| CB6.6 | Checked tier (§4.13): `schedContextBindServerChecked`, the `dispatchWithCapChecked` arms, `checkedDispatch_bindServer_eq_unchecked_when_allowed` and the two `checkedDispatch_*_eq_unchecked` equivalences for the capability-only arms; `enforcementBoundary_is_complete` re-proved (consumes CB6.4) | `SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean`, `SeLe4n/Kernel/API.lean` | M |
| CB6.7 | Dispatch payoff: per-arm `…_preserves_ipcInvariantFull` for the three arms (frames on every conjunct — no IPC state moves), extending `dispatchCapabilityOnly_preserves_ipcInvariantFull` (production) and the staged `dispatchWithCap_preserves_ipcInvariantFull` / `dispatchWithCapChecked_preserves_ipcInvariantFull`; `capabilityDispatchQuiescence` needs no new field, stated as a theorem (consumes CB6.6) | `SeLe4n/Kernel/IPC/Invariant/DispatchArmPreservation.lean`, `SeLe4n/Kernel/IPC/Invariant/DispatchPayoff.lean`, `SeLe4n/Kernel/API.lean` | L |
| CB6.8 | Rust mirrors per §4.9: `sele4n-types`, the HAL hand mirror with `min_inline_args` (1, 1, 0), `sele4n-abi` argument structs (and the `0`-only `deadline`), `sele4n-sys` wrappers, conformance cases; `test_aarch64_cross_build.sh` green (consumes CB6.1, CB6.3) | `rust/sele4n-types/src/syscall.rs`, `rust/sele4n-hal/src/svc_dispatch.rs`, `rust/sele4n-abi/src/args/sched_context.rs`, `rust/sele4n-sys/src/sched_context.rs`, `rust/sele4n-abi/tests/conformance.rs` | M |
| CB6.9 | ABI version decision recorded on all three sides (§3.2): `SYSCALL_ABI_VERSION` stays `3`, with a conformance pin that every prior discriminant encodes as before | `rust/sele4n-abi/tests/conformance.rs`, `SeLe4n/Kernel/Architecture/SyscallReturn.lean` | S |
| CB6.10 | Return-shape and dispatch pins: `SyscallReturnAbiSuite` cases for the three `.unit` frames; `SyscallDispatchSuite` discriminant pins for the new refusal arms; `AbiRoundtripSuite` cases for the two decoders and the `0`-only deadline | `tests/SyscallReturnAbiSuite.lean`, `tests/SyscallDispatchSuite.lean`, `tests/AbiRoundtripSuite.lean` | M |
| CB6.11 | Staging promotion (§4.14): the staged theorem modules enter the `SeLe4n.lean` closure through their production consumers; allowlist entries removed and `STATUS: staged` markers replaced in the same cut; the partition gate passes in both directions (consumes CB6.7) | `SeLe4n.lean`, `SeLe4n/Platform/Staged.lean`, `scripts/staged_module_allowlist.txt` | S |
| CB6.12 | End to end: scenario S7 (§4.15) through `syscallDispatchFromAbi` in the new Tier-2 suite with golden fixture `tests/fixtures/hierarchical_server_syscalls.expected`; scenario-registry entries `[HCB-nnn]`; `NegativeStateSuite` pins for each error arm through the dispatcher (consumes CB6.4, CB6.8) | `tests/HierarchicalServerSuite.lean`, `lakefile.toml`, `scripts/test_tier2_negative.sh`, `tests/fixtures/scenario_registry.yaml` | M |

**Acceptance**: the Lean and Rust id tables agree under the existing mirror
tests; the routing gate reports zero exceptions; both dispatch payoffs
elaborate over 38 arms; S7 is byte-verified in-suite.

### CB7 — Information flow and the CBS guarantee

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| CB7.1 | `serverMembersUniformlyLabeled ctx st` (§4.13); `schedContextBindServerChecked_establishes_uniformLabels` (the only member-adding transition) and preservation by every other transition (consumes CB6.6) | `SeLe4n/Kernel/InformationFlow/Invariant/Helpers.lean` | M |
| CB7.2 | Per-core NI for the hierarchical tick: `chargeSchedPath_confined_to_label` and the SM8.B tick lift re-proved over the new body (consumes CB4.3, CB7.1) | `SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean`, `SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean` | L |
| CB7.3 | Projection and confinement theorems for the three arms in the SM8 style: `…_preserves_projection` for every observer and `…_confinedToCores` | `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean`, `SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean` | M |
| CB7.4 | Refusal-ledger partition: the SM9 pin `capFaultReceivePhase?_none_iff_records` restated over the wider inductive — the new arms record nothing and fault nothing | `SeLe4n/Platform/FFI.lean`, `SeLe4n/Kernel/InformationFlow/RefusalRecord.lean` | S |
| CB7.5 | Covert-channel classification (§4.13): the intra-server budget channel closed by construction (`no_cross_label_server_membership`); the inter-server root channel re-derived for deadline order and recorded in the lock-domain register rather than in prose | `SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean`, `SeLe4n/Kernel/InformationFlow/FineLockFlow.lean` | M |
| CB7.6 | Taint: the three arms are control-only in `contentFlowClass` and the per-arm taint family gains the three arms | `SeLe4n/Kernel/InformationFlow/TaintPropagation.lean` | S |
| CB7.7 | The CBS guarantee (§4.11 T14–T16): `cbs_demand_bound`, `edf_selects_earliest_eligible` and `server_receives_budget_within_window` with every hypothesis named, over a per-core step relation defined for it; the composition lands closed, or as the externalized hypothesis `edfTraceFeasible` with the closure registered in §12 (consumes CB1.13, CB3.5, CB4.9) | `SeLe4n/Kernel/Scheduler/Liveness/EdfGuarantee.lean` (new), `SeLe4n/Kernel/Scheduler/Operations/PerCoreWcrt.lean` | XL |
| CB7.8 | Lock-domain register: `UncoveredLockDomain`'s completeness theorem re-proved — servers add no lock domain (the SchedContext kind and the per-core replenish queue cover them) — and `SchedLockId` unchanged, stated as a pin | `SeLe4n/Kernel/InformationFlow/FineLockFlow.lean` | S |
| CB7.9 | Tier-2 scenario S8 (§4.15) in the information-flow and CBS suites; Tier-3 anchors for CB7 | `tests/SmpInformationFlowSuite.lean`, `tests/SmpCbsSuite.lean`, `scripts/test_tier3_invariant_surface.sh` | M |

**Acceptance**: the SM8.B per-core non-interference capstone elaborates over
the hierarchical tick with `serverMembersUniformlyLabeled` as its only new
hypothesis; T14 states every hypothesis it uses, and if `edfTraceFeasible` is
among them the register carries its closure target; S8 passes as written.

### CB8 — Closure

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| CB8.1 | Specification: §8.12.8 "Hierarchical servers" complete (model, EDF-first order, the engine rules, charging, activation, admission, syscalls, refusals, isolation theorems); §8.14 gains the CBS guarantee with its hypotheses; evidence-index rows under §4 SMP | `docs/spec/SELE4N_SPEC.md`, `docs/CLAIM_EVIDENCE_INDEX.md` | M |
| CB8.2 | Theorem inventory `hierarchicalServerTheorems` with its nodup witnesses, and the census extended so a workstream inventory can be **claimed**: a workstream-keyed manifest beside the SMP phase manifest, read by the generator, so an unclaimed inventory still fails Tier 0 | `SeLe4n/Kernel/SchedContext/HierarchyInventory.lean` (new), `SeLe4n/Kernel/Concurrency/PhaseTheoremManifest.lean`, `scripts/generate_smp_theorem_manifest.py` | M |
| CB8.3 | Hardware spot-check script in the `test_qemu_smp_cbs.sh` shape — skips until SM10.1's image carries the driver and lists its formal stand-ins in the header | `scripts/test_qemu_hierarchical_servers.sh`, `scripts/test_tier4_smp_bootcheck.sh` | S |
| CB8.4 | `CLAUDE.md`/`AGENTS.md`: standing-constraint bullets (the root is EDF-first with kernel-owned window deadlines and per-window refills; member affinity fixed; off-core member donation refused; enforcement tick-quantised) and the status row to CLOSED; large-files snapshot refreshed | `CLAUDE.md`, `AGENTS.md` | S |
| CB8.5 | Debt register: the WS-CB rows closed with versions; the §12 follow-ups registered with owners and closure targets; the registry row's span closed | `docs/REGISTERED_DEBT.md` | S |
| CB8.6 | README metrics sync and the GitBook roadmap row; `docs/codebase_map.json` regenerated; `docs/DEVELOPMENT.md` where a tier gained a suite | `README.md`, `docs/gitbook/05-specification-and-roadmap.md`, `docs/codebase_map.json`, `docs/DEVELOPMENT.md` | S |
| CB8.7 | Full validation sweep — `test_full.sh`, `test_rust.sh`, `test_aarch64_cross_build.sh`, `test_docs_sync.sh` — and the CHANGELOG closure entry | `CHANGELOG.md` | S |
| CB8.8 | Hand-off note to SM10: what §8.12.8 adds to SM10.2's documentation sweep and what CB8.3's script adds to SM10.3's hardware validation list | `docs/planning/SMP_RELEASE_CLOSURE_PLAN.md` | T |

**Acceptance**: every row of the phase map reports LANDED with a version; the
plan gate, the naming gate and the docs-sync lane pass on the closing cut.

## 8. Verification strategy

### 8.1 Per PR

* `lake build <Module>` for every touched module (the pre-commit hook), then
  `./scripts/test_smoke.sh`; `./scripts/test_full.sh` whenever a theorem or a
  Tier-3 anchor moves — which is every phase from CB1 on.
* `./scripts/test_aarch64_cross_build.sh` after any change under `rust/`
  (CB0.5, CB6.8, CB6.9).
* Stage before running Tier 0: the plan gate and the naming gate read the
  index.

### 8.2 The equivalence discipline

CB1.2 changes the root order and lands with T2; CB1.4 changes the refill
schedule and lands with T4/T5 and the inverted refill witness; the one
intended fixture refresh is CB1.14, each fixture with its rationale.  From
then on CB3.4 and CB4.3 change live selection and charging, and each lands
with the theorem that on a state whose contexts are all parentless the new
definition equals the CB1 one (T9, T10), with `./scripts/test_tier2_trace.sh`
reporting every `.expected` sha256 unchanged from the post-CB1 baseline.  A
fixture that moves in CB2–CB4 is a defect in the cut, not a fixture to
refresh; the intended moves are CB0.3's (the configure authority gate),
CB1.14's (the policy and the engine), and CB5.2's (per-core admission), plus
the new fixtures CB4.10, CB6.12 and CB7.9 add.

### 8.3 What each phase proves

| Phase | Proof obligation discharged |
|-------|-----------------------------|
| CB1 | T1–T8: the EDF-first order is strict; the selector is total, optimal, and equal to the old one on deadline-less states; the engine rules preserve `wellFormed`; a window consumes at most its budget; dead time is at most a period; inversion is bounded in deadline terms |
| CB2 | `schedHierarchyInvariant` holds of the default and boot states; the engine rules frame the hierarchy fields |
| CB3 | T1 on paths, T9, T16 in selection form |
| CB4 | T10–T12; the tick preserves every structural and CBS invariant over path charging and activation |
| CB5 | T13; every hierarchy transition preserves the per-core, CBS, hierarchy and cross-subsystem bundles; every refusal is explicit |
| CB6 | the dispatcher stays total over 38 ids; `ipcInvariantFull` survives every new arm; the Lean and Rust tables agree |
| CB7 | per-core non-interference under uniform labels; T14–T16 |

### 8.4 What each phase validates

Tier 2: `smp_cbs_suite` (S0–S3, S5, S6, S8), the new
`hierarchical_server_suite` (S7), `NegativeStateSuite` (CB0.3, CB1.5, CB5.16,
CB6.12), `SmpInformationFlowSuite` (S8), the decode and ABI suites (CB6.1,
CB6.10), and every refreshed golden (CB1.14).  Tier 3: anchors per phase.
Tier 4: CB8.3's script, a skip until SM10.1 produces an image.

## 9. Risk inventory

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| CB1's fixture refresh reaches fourteen suites and the main trace, and a refreshed fixture can hide a defect behind a "policy change" rationale | HIGH | MED | CB0.4's witnesses pin the old order and the old refill and are inverted deliberately; each refreshed fixture's rationale names the thread whose position or refill moved; T2 shows nothing else moved |
| The refill rework (CB1.4) touches both ticks, the drain, yield and the Z2 proof family at once | HIGH | MED | The four rules are pure functions on one `SchedContext` with their own T3 lemmas; the ticks call them; the CBS preservation family is re-proved by the rules' lemmas plus the existing frames |
| Converting priority inheritance to deadline inheritance (CB1.7–CB1.8) is larger than estimated across the per-core and cross-core PIP surface | HIGH | MED | The priority boost is kept, not removed, so the change is additive; the donation-preservation family is re-proved by frame where the new field is untouched |
| The `activeDescendants` counter needs maintenance at every runnability transition (CB4.6) and one is missed | MED | HIGH | `activeDescendantsConsistent` is a cross-subsystem conjunct from CB5.13, so a missed site fails a bridge proof, not a review; the bounded subtree scan is the recorded fallback |
| The CBS guarantee's composition (CB7.7) does not close within its row | HIGH | MED | T15 and T16 land regardless; the composition lands as `edfTraceFeasible` with a registered closure, stated conditionally — the `hBandProgress` precedent |
| CB4.4's re-proof of the tick family is larger than estimated | HIGH | MED | T10 reduces most cases to the CB1 proof; the fold's frames (CB4.1) are proved once; split CB4.4 by theorem family if it exceeds one PR |
| Selection by scan costs `O(runnable · depth)` per decision where the bucket-first path cost `O(bucket)` | MED | LOW | The lock-wait WCRT theorems are unaffected; the deadline-ordered index is a registered follow-up proven equal to the scan |
| Per-core admission (CB5.2) changes an existing refusal on fixtures that over-admit only in aggregate | MED | LOW | Enumerate the affected fixtures at CB5.2, refresh with rationale; no flat theorem depends on the global sum |
| The path order admits a tie the proofs cannot break | LOW | HIGH | §4.3's `byPriority` breaks every tie: FIFO for leaf pairs, `scId` otherwise; T1 is proved in CB3.3 before anything relies on the order |
| The receive-side refusal of an off-core member donation surfaces as an error to a blameless passive server | LOW | MED | Documented in §4.8 and the spec; the follow-up (per-core server replicas) removes the refusal; a Tier-2 scenario pins the behaviour |
| The workstream inventory cannot be claimed by the SMP-only manifest census | HIGH | LOW | CB8.2 extends the census rather than misfiling the inventory under SM5 |
| Overlap with WS-RR on the scheduler, the CBS engine, `API.lean` or the flow tables | MED | MED | §2.3's partition; CB1 and CB5 onward wait for a WS-RR cut touching those files to land |

## 10. Acceptance gate

- [ ] Every CB row LANDED with a version in the phase map.
- [ ] T2, T9 and T10 elaborate with no hypothesis beyond the absence of
      deadlines, respectively of servers.
- [ ] Every §4.10 conjunct of `SchedContext.wellFormed` preserved by every CBS
      rule and every transition; no caller-supplied deadline reaches a
      SchedContext; a window never receives budget before it ends (T4).
- [ ] `edfCurrentEarliestOnCore` preserved by every per-core transition.
- [ ] T11 and T12 stated over arbitrary subtrees within `maxServerDepth`.
- [ ] `crossSubsystemInvariant` has thirteen conjuncts and thirteen field-sets.
- [ ] Both dispatch payoffs elaborate over 38 ids; the routing gate reports
      zero exceptions; `SyscallId::COUNT` agrees on both sides.
- [ ] The SM8.B per-core non-interference capstone holds over the hierarchical
      tick under `serverMembersUniformlyLabeled`.
- [ ] T14 states every hypothesis it uses; T7 is stated over deadlines and is
      not vacuous.
- [ ] Every pre-existing `.expected` unchanged except CB0.3's, CB1.14's and
      CB5.2's, each refreshed with rationale; three new fixtures byte-verified;
      S0–S8 pass as written in §4.15.
- [ ] Zero `sorry`, zero axioms; Tier 0, docs-sync, Tier 3 and the cross build
      green on the closing cut.
- [ ] Follow-ups (§12) registered with owners.

## 11. Questions for the maintainer

Decided at planning time: **EDF-first root** (D3, D13–D15), per-window refills
(D16), core-homed servers, label uniformity, the depth and member bounds,
off-core donation refused, leaf-only timeouts.  Each remaining question has a
default the plan is written against; changing one changes the rows named.

| # | Question | Default | If changed |
|---|----------|---------|------------|
| Q1 | Implicit deadlines only (`D = P`), the configure `deadline` argument `0`-only? | Yes (D13) | Constrained deadlines `D < P` need a density-based admission test in CB5.2 and a different T14 in CB7.7 |
| Q2 | Per-window refills (hard CBS), rather than per-consumed-chunk refills? | Yes (D16) | Per-chunk refills need consumption tracking and refill coalescing under the 8-entry bound in CB1.4, and change T4/T5 and T14's demand argument |
| Q3 | Deadline inheritance stays within a member's server (no bandwidth inheritance)? | Yes (D15) | Lifting the server's deadline for a client in another server is bandwidth inheritance; CB4 and CB7.7 change shape |
| Q4 | Selection by scan now, the deadline-ordered index later? | Yes (D2) | An index in CB1 adds a per-core structure with its consistency invariant to every transition in CB1.10 and CB4.4 |
| Q5 | Open after WS-RR, or beside RR6–RR8 under §2.3's partition? | After | CB1 may start once RR7 is quiet in the scheduler and the CBS engine; CB5 onward waits for `API.lean` |
| Q6 | Land CB0.3 as the next cut, ahead of the workstream — and CB1.4 (the refill defect) as the one after? | Yes to both | The authority gap and the starvation defect stay open until the workstream opens |
| Q7 | Retire `schedContextYieldTo`, or leave it? | Leave | Retiring it removes one proven-but-unwired helper and its cross-subsystem bridge |
| Q8 | Remove `TCB.deadline` in CB1.5 rather than keep it as a dead field? | Remove | Keeping it means a proof that selection never reads it, renewed at every selector change |
| Q9 | Single-domain mode as T14's hypothesis, the domain-rotating guarantee a follow-up? | Yes | A domain-rotating T14 needs the rotation folded into the demand bound; the RPi5 default is single-domain |

## 12. Cross-references and registered follow-ups

* Debt register: [`../REGISTERED_DEBT.md`](../REGISTERED_DEBT.md) — the
  WS-CB rows in the registry and in table C.
* Neighbours: [`SMP_PER_CORE_SCHEDULER_PLAN.md`](SMP_PER_CORE_SCHEDULER_PLAN.md)
  (SM5, the surface changed and generalised), [`SMP_INFORMATION_FLOW_PLAN.md`](SMP_INFORMATION_FLOW_PLAN.md)
  (SM8, the observer), [`SMP_RELEASE_READINESS_PLAN.md`](SMP_RELEASE_READINESS_PLAN.md)
  (WS-RR, the partition in §2.3), [`SMP_RELEASE_CLOSURE_PLAN.md`](SMP_RELEASE_CLOSURE_PLAN.md)
  (SM10, CB8.8's hand-off).
* Specification: `docs/spec/SELE4N_SPEC.md` §8.12 (the flat model this
  extends, rewritten in CB1.14 and completed in CB8.1), §8.13 (priority
  inheritance, rewritten by CB1.14), §8.14 (the bound CB7.7 replaces for the
  EDF class).

Follow-ups this plan deliberately leaves for a later workstream, to be
registered by CB8.5 with owners and closure targets: constrained deadlines
(`D < P`, density admission); a per-core deadline-ordered index for selection,
proven equal to the scan; the closure of `edfTraceFeasible` if CB7.7 lands it
externalized; the domain-rotating form of T14; server migration between cores
(a whole subtree re-homed, refills included); per-core server replicas so a
component may span cores; bandwidth inheritance for a member blocking a client
of another server; boot-time server trees in `PlatformConfig`; a bucketed
`MemberList`; sub-tick enforcement through a one-shot timer seam.

## 13. Theorem catalogue

| Theorem | Phase | Statement |
|---------|-------|-----------|
| `isBetterKey_irrefl`, `_asymm`, `_trans`; `isBetterCandidate_legacy_class_eq_fp` | CB1 | T1 on keys; deadline-less candidates compare as before |
| `chooseThreadEffectiveOnCore_eq_flat_of_no_deadlines` | CB1 | T2 |
| `wellFormed_preserved_by_cbs_rules` (family) | CB1 | T3 for `cbsWindowStart`, `cbsScheduleRefill`, `cbsLandRefill`, `cbsActivate` |
| `window_consumption_le_budget`, `refill_dead_time_le_period`, `cbsLandRefill_drops_stale` | CB1 | T4, T5, and the stale-entry rule |
| `cbsActivate_noop_of_fresh` | CB1 | T6 |
| `edfCurrentEarliestOnCore` (preservation family) | CB1 | T8 |
| `pip_bounded_inversion` (restated) | CB1 | T7 |
| `pathLockFootprint_le_maxLockSetSize` | CB2 | the path footprint fits the SM3 bound |
| `default_schedHierarchyInvariant`, `bootFromPlatformCheckedWithIdleThreadsFor_schedHierarchyInvariant` | CB2 | the bundle holds of the default and production boot states |
| `schedPath_not_prefix` | CB2 | two leaves' paths never nest |
| `pathBudgetEligible_eq_hasSufficientBudget_of_root` | CB3 | eligibility is CB1's on a parentless leaf |
| `isBetterPath_irrefl`, `_asymm`, `_trans`; `isBetterPath_singleton_eq_isBetterKey` | CB3 | T1 on paths; the order is CB1's on singleton paths |
| `chooseThreadEffectiveOnCore_eq_flat_of_no_servers` | CB3 | T9 |
| `chooseBestRunnableHierarchical_always_ok`, `_optimal` | CB3 | totality; T16 in selection form |
| `timerTickBudgetOnCore_eq_flat_of_root` | CB4 | T10 |
| `chargeSchedPath_charges_every_ancestor`, `server_subtree_consumption_bounded`, `member_isolation` | CB4 | one consumed tick reaches every level; T11; T12 |
| `timerTickOnCore_preserves_perCoreCbsInvariant` (re-proved), `cbsReplenish_server_reschedules_local` | CB4 | the CBS bundle survives path charging; a server refill triggers the executing core's reschedule decision |
| `rootAdmission_sound_per_core` | CB5 | T13 |
| `setThreadCpuAffinityWithMigration_rejects_member`, `member_donation_same_core`, `applyCallDonationOnCore_preserves_schedHierarchyInvariant` (+ reply twins) | CB5 | the affinity refusal; a member's donation never migrates refills; donation keeps the tree well-formed |
| `dispatchCapabilityOnly_bindServer_idle_refused`, `checkedDispatch_bindServer_eq_unchecked_when_allowed`, `dispatchCapabilityOnly_preserves_ipcInvariantFull` (extended) | CB6 | the chokepoint covers the new operand; the flow gate is transparent when it permits; the production payoff over 38 arms |
| `schedContextBindServerChecked_establishes_uniformLabels`, `chargeSchedPath_confined_to_label`, `no_cross_label_server_membership` | CB7 | the label rule is established by the only member-adding transition; path charging writes one label; the intra-server channel is closed by construction |
| `cbs_demand_bound`, `edf_selects_earliest_eligible`, `server_receives_budget_within_window` | CB7 | T15, T16, T14 |

## 14. Refinement-pass record

What the pass over the second cut changed, so a reader of the schedule knows
which rows moved and why:

1. **A defect found, and a decision reversed.**  Reading the tick for the
   refill rules surfaced the one-tick refill (§1.1).  Fixing it (CB1.4, D16)
   made the first cut's wake-up rule — "reset the deadline, keep the budget,
   because chunk refills are owed" — unnecessary: nothing is owed under
   per-window refills, so D14 is now the classical CBS rule.  Q2 changed from
   "which wake rule" to "which refill scheme".
2. **One engine, four rules.**  `cbsUpdateDeadline`, the two tick arms, the
   yield arm and `refillSchedContext` each carried their own reading of when
   a deadline moves; §4.2 replaces them with four pure functions the ticks
   call, so the theorems are about the rules and the ticks inherit them.
3. **Per-object, not store-level.**  `deadlineWindowConsistent`,
   `atMostOnePendingRefill` and `pendingRefillOnlyWhenExhausted` are
   properties of one context, so they joined `SchedContext.wellFormed` and
   ride `schedContextStoreConsistent` and the boot check for free, instead of
   becoming a fourth bundle.  `schedHierarchyInvariant` shrank from nine
   conjuncts to six.
4. **The counter got its chokepoints.**  The first cut asserted
   `activeDescendantsConsistent` without saying where the count moves; §4.5
   names the two helpers, the sites that call them, and the fact that the
   cross-subsystem bridge is what makes the enumeration complete.  It also
   found that `removeRunnable` is still `bootCoreId`-pinned, which CB4.6 must
   fix to read the right queue.
5. **Refusals got codes.**  Every check in §4.8 names its `KernelError`; two
   existing variants (`.cyclicDependency`, `.threadOnDifferentCore`) cover the
   cases the first cut left as "refused", so no new variant is added.
6. **Every §4 item is owned.**  Each sub-task row names the §4 subsection it
   implements and, where a theorem is involved, its T-number; the acceptance
   lines name the scenarios (S0–S8) that pin them.
7. **Counts.**  CB1 grew from 13 to 14 rows (the refill fix); the total is 93.
   `TCB.deadline` removal, previously a question, is the default with the
   question retained (Q8).  The single-domain hypothesis of T14 became an
   explicit question (Q9) rather than a footnote.
8. **What the pass did not change.**  The phase order, the core-homing
   decision, the label rule, the constants, the syscall surface and the ABI
   decision all survived re-derivation; the plan gate, the naming gate and the
   docs-sync lane hold the document's structure.

## Appendix A — Verification commands

```bash
source ~/.elan/env
lake build SeLe4n.Kernel.SchedContext.Budget                # CB1.3–CB1.6
lake build SeLe4n.Kernel.Scheduler.Operations.Selection    # CB1, CB3
lake build SeLe4n.Kernel.Scheduler.PriorityInheritance     # CB1.7–CB1.8
lake build SeLe4n.Kernel.SchedContext.Hierarchy            # CB2
lake build SeLe4n.Kernel.Scheduler.Operations.Core         # CB4
lake build SeLe4n.Kernel.API                               # CB6
lake exe smp_cbs_suite                                     # S0–S3, S5, S6, S8
lake exe hierarchical_server_suite                         # S7
./scripts/test_tier2_trace.sh                              # every fixture sha256
./scripts/test_full.sh                                     # Tier 0–3
./scripts/test_aarch64_cross_build.sh                      # after rust/ changes
python3 scripts/check_live_arm_per_core_routing.py         # CB6.4
python3 scripts/check_workstream_plan.py                   # this plan (stage first)
./scripts/test_docs_sync.sh                                # citations, mirrors, map
```

## Appendix B — Implementation dependency graph

```
CB0.3 (authority gate) ──────────────────────────────┐
CB0.4 (witnesses) ─► CB1.1 ─► CB1.2 ─┬─► CB1.7 ─► CB1.8 ─► CB1.9 ─► CB1.10 ─► CB1.12 ─► CB1.14
                                     │                                  │
                     CB1.3 ─► CB1.4 ─┴─► CB1.6                          └─► CB1.13
                                                                                 │
CB2.1 ─► CB2.2 ─► CB2.3 ─► CB2.4 ─► CB2.5 ─► CB2.6 ─► CB2.7 ─► CB2.8 ─► CB2.9 ─► CB2.10
                                        │
CB3.1 ─► CB3.2 ─► CB3.3 ─► CB3.4 ─► CB3.5 ─► CB3.6 ─► CB3.7 ─► CB3.8 ─► CB3.9
                                        │
CB4.1 ─► CB4.2 ─► CB4.3 ─► CB4.4 ─► CB4.5 ─► CB4.6 ─► CB4.7 ─► CB4.8 ─► CB4.9 ─► CB4.10
                                                                          │
CB5.1 ─► CB5.2 ─► CB5.3 ─► CB5.4 ─► … ─► CB5.8 ─► … ─► CB5.12 ─► CB5.13 ─► CB5.14 ─► CB5.15 ─► CB5.16
                                                                                       │
CB6.1 ─► CB6.2 ─► CB6.3 ─► CB6.4 ─► CB6.5 ─► CB6.6 ─► CB6.7 ─► CB6.8 ─► … ─► CB6.11 ─► CB6.12
                                                       │
CB7.1 ─► CB7.2 ─► CB7.3 ─► CB7.4 ─► CB7.5 ─► CB7.6 ─► CB7.7 (T14–T16) ─► CB7.8 ─► CB7.9
                                                                                    │
CB8.1 ─► CB8.2 ─► CB8.3 ─► CB8.4 ─► CB8.5 ─► CB8.6 ─► CB8.7 ─► CB8.8
```

Arrows are the `consumes` relations the rows state; a phase's first row
consumes the previous phase's last acceptance.
