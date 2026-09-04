# WS-CB — Hierarchical Constant Bandwidth Servers (HCBS)

> **Workstream**: WS-CB (constant-bandwidth server hierarchy)
> **Status**: **PLANNED** — registered at v0.34.49; no sub-task started.  Opens
> after WS-RR closes, or in parallel with RR6–RR8 under the file partition in
> §2.3.  Not a v1.0.0 blocker: SM10 may cut v1.0.0 with this workstream open,
> provided the release notes state that scheduling contexts are flat and the
> root scheduler is fixed-priority.
> **Relationship to WS-SM**: extends the SM5.A selector, the SM5.D/SM5.H
> per-core tick and CBS surface, the SM5.F priority-inheritance surface and the
> SM8/SM9 information-flow surface; orthogonal to SM10's image work.  It
> touches no Rust HAL seam and adds no Lean upcall (§3.10).
> **Audited cut**: `v0.34.48`
> **Sub-task count**: 92 across 9 phases (CB0..CB8), each phase numbered in
> the order it is to be implemented
> **Root policy**: **EDF-first** (maintainer's decision at planning time, §3.11)
> — the root scheduler orders by CBS deadline, with priority as the tie-break
> and as the order of the legacy deadline-less class.  This is a change to the
> flat model too, and CB1 lands it before any hierarchy exists.
> **Prefix**: `CB`.  The identifier-naming gate derives its family grammar
> from the workstream registry, so the prefix had to be one whose lowercase
> form followed by a digit matches no identifier in the tree: `cb<digit>`
> matches nothing, where `hc<digit>` (the obvious abbreviation) matches two
> hypotheses in the Robin Hood preservation proofs.

## 1. Phase goal

A **Constant Bandwidth Server** (CBS) is a reservation `(Q, P)`: a budget `Q`
replenished every period `P`, whose deadline is postponed by `P` each time the
budget is exhausted, so that the server can never consume more than `Q/P` of
the processor whatever its clients do.  Under **EDF** with the servers'
utilisations summing to at most one, every server also *receives* its `Q` in
every period — that is the CBS guarantee, and it is why the classical CBS root
is EDF rather than fixed priority.  seLe4n already implements the server half
per thread: a `SchedContext` is a CBS bound to at most one thread, charged one
tick at a time by the per-core timer tick, replenished through the per-core
replenish queue, and admitted against a 100 % utilisation ceiling.  Its root
scheduler, however, is fixed-priority with the CBS deadline as a tie-break
inside a band, so the guarantee half is a per-band response-time argument
rather than the EDF theorem.

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

1. the EDF-first root on the flat model — kernel-owned deadlines, the CBS
   wake-up rule, deadline inheritance in place of priority inheritance for
   deadline-bearing threads, the one intended fixture refresh (CB1);
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
   CBS guarantee — a runnable server receives its budget within its period —
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
* Priority inheritance (`SeLe4n/Kernel/Scheduler/PriorityInheritance/`) is a
  priority boost: `updatePipBoost` writes `pipBoost := computeMaxWaiterPriority`
  and re-buckets; `pip_bounded_inversion` bounds the inversion in
  priority-band terms.  Passive servers inherit a client's whole SchedContext
  through donation instead, and with it the client's deadline.
* The per-core tick `timerTickOnCore` (`SeLe4n/Kernel/Scheduler/Operations/Core.lean`)
  drains the core's replenish queue (`processReplenishmentsDueOnCore`, waking
  a bound thread whose budget went from zero to positive), then charges the
  running thread's SchedContext one tick (`timerTickBudgetOnCore`): on
  exhaustion it schedules a replenishment of the consumed amount one period
  out (`scheduleReplenishment`, `replenishOnCore`), re-enqueues the thread,
  times out the threads the SchedContext bounds (`timeoutBlockedThreads`, via
  `scThreadIndex`) and preempts.  An exhausted thread stays queued and is
  skipped by eligibility; its deadline moves only when the refill lands.
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
  Recorded as a pre-existing finding in §3.9; CB0.3 closes it.  The same
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
bounds a set of them jointly.  And because the root is fixed-priority, the
CBS *guarantee* — that an admitted server receives its budget every period —
is not a theorem the model can even state: a low-priority server with a
tight deadline waits behind every higher band regardless of admission.

### 1.3 What this workstream does *not* change

* The tick rate, the HAL, the FFI seam set, `SYSCALL_ABI_VERSION`, or any
  existing syscall's encoding.  New ids are appended (§3.10).
* The 1:1 thread ↔ leaf binding.  A server is a SchedContext with members and
  no thread; a leaf is a SchedContext with at most one thread and no members.
* The run queue's representation: priority buckets of `ThreadId` stay as the
  membership and FIFO structure; selection stops reading them as an order.
* The order of the legacy class.  Unbound, deadline-less threads — the idle
  threads among them — stay fixed-priority among themselves, below every
  deadline-bearing thread.

### 1.4 What CB1 changes, and its blast radius

The root order becomes EDF-first (§3.11).  On every state whose runnable
threads all lack deadlines the selector is unchanged, and CB1.2 proves it
(`chooseThreadEffectiveOnCore_eq_flat_of_no_deadlines`).  On a state with a
deadline-bearing runnable thread the order changes by design, so the fixtures
built from bound threads — fourteen suites and the main trace harness at the
audited cut — are refreshed **once**, in CB1.13, with the rationale recorded;
after CB1 every generalising cut is byte-identical again.  The other two
intended fixture moves are CB0.3's (the configure authority gate) and CB5.2's
(per-core admission).

## 2. Scope and sequencing

### 2.1 In scope

* The EDF-first root on the flat model: kernel-owned implicit deadlines, the
  CBS wake-up rule, deadline inheritance for deadline-bearing threads, the
  selector, its invariants and its one fixture refresh (CB1).
* Server SchedContexts with bounded nesting; member leaves and member servers.
* Hierarchical ordering (§3.3), hierarchical charging, activation and
  replenishment (§3.4), hierarchical admission (§3.5), core-homed servers
  (§3.6).
* Three syscalls: `schedContextConfigureServer`, `schedContextBindServer`,
  `schedContextUnbindServer`; hierarchy-aware forms of the existing
  operations that read or write a SchedContext's role (§3.8).
* The preservation surface for every touched invariant bundle, the
  `ipcInvariantFull` dispatch payoff over the new arms, per-core
  non-interference under the label-uniformity rule, and the CBS guarantee
  with its hypotheses stated.
* Tier-2 suites with golden fixtures, Tier-3 anchors, ABI mirrors and
  conformance tests, specification and evidence-index rows.

### 2.2 Out of scope (registered follow-ups, §11)

Constrained deadlines (`D < P`); a per-core deadline-ordered index for
selection; server migration between cores; members homed on several cores
(Linux HCBS's per-CPU server replicas); bandwidth inheritance (a member's
inherited deadline lifting its *server*); boot-time server trees; a bucketed
member queue; sub-tick enforcement through a one-shot timer.

### 2.3 Ordering constraints and parallelism

* **Phase order is execution order.**  CB1 changes the root policy on the
  flat model and is the only phase whose behavioural change is intended to
  reach existing fixtures; it lands whole, before any server field exists, so
  the hierarchy is built on the order it will actually run under.  CB2 has no
  behavioural effect; CB3 and CB4 change live paths but only on states that
  CB5/CB6 cannot yet produce, and each carries its no-servers equivalence
  theorem in the same row; CB5 lands every transition with its proofs before
  CB6 makes any of them reachable.
* **Overlap with WS-RR.**  CB1 edits the selector, the tick and the
  priority-inheritance modules, so it must not overlap an RR7 cut that
  touches `SeLe4n/Kernel/Scheduler/**`; CB2–CB4 own
  `SeLe4n/Kernel/SchedContext/**` and the scheduler's selection and tick
  modules; CB5 onward edits `API.lean` and the flow-classification tables and
  must not overlap a WS-RR cut that does.  RR6 (lock primitives) never
  collides.
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
| D3 | **EDF-first at every level** (§3.11): earlier kernel-assigned deadline first, a deadline-less entity after every deadline-bearing one, then higher priority, then FIFO among leaves and ascending `scId` among distinct servers | Fixed priority with EDF as the tie-break (the pre-CB1 root); FP-only local scheduling | The maintainer's decision; it is the order under which the CBS guarantee is a theorem rather than a per-band argument, and one order at every level means one set of strict-order lemmas |
| D4 | A running thread's tick charges its leaf **and every ancestor**; exhaustion at any level makes the subtree ineligible until that level's replenishment lands; a server is *activated* by the CBS rule when its first member becomes runnable; timeouts are decided by the leaf only (§3.4) | Charge the leaf and transfer budget upward lazily | Eager charging is what makes the subtree bound a theorem; lazy transfer needs a second accounting state |
| D5 | Servers are **core-homed**; every member's thread has that home core; member affinity changes, and donations of a member leaf to a thread homed elsewhere, are refused (§3.6) | Per-core server replicas | Keeps every hierarchical write inside one core's scheduler slots and the existing tick lock set; replicas are the registered extension |
| D6 | Admission is hierarchical: members ≤ server; roots **per core** ≤ 1000 ‰, replacing the flat global sum (§3.5) | Keep the global sum and add the member rule | Per-core `Σ U ≤ 1` is EDF's schedulability condition for implicit deadlines, so per-core root admission is both the natural base case of the hierarchy and the hypothesis of the CBS guarantee |
| D7 | Priority is a **tie-break** for deadline-bearing entities and the order of the legacy class; a server's priority may change at any time, a member thread's priority through `.tcbSetPriority` under the caller's MCP, and neither moves anything but ties | Server priority frozen while populated; `.tcbSetPriority` refused on members | Both refusals existed only to keep a root-priority bucket consistent, and under EDF-first the bucket no longer orders anything |
| D8 | Every member of a server carries the server's security label; enforced at `schedContextBindServer` in the flow-checked tier (§3.7) | Permit mixed labels and bound the channel | A shared budget lets one member starve another outright; that is not a channel to bound but a flow to forbid |
| D9 | `maxServerDepth = 3` (root server → server → leaf), `maxServerMembers = 16`; every walk is fuel-bounded by the depth | Unbounded recursion on `parentServer` | Totality with a decidable bound; the path lock footprint (`≤ 3` SchedContext locks + the tick's three) stays within `maxLockSetSize = 8` |
| D10 | Enforcement stays tick-quantised; no new upcall, no HAL change, `SYSCALL_ABI_VERSION` unchanged (ids appended, one argument's accepted values narrowed) | A one-shot timer programmed to the next budget event | A new FFI seam drags in the readiness-gate derivation and a new Rust surface for a precision gain the model does not need yet |
| D11 | The boot state has no servers; a hierarchy is built at run time by the root task | Boot-time server trees in `PlatformConfig` | Keeps the boot theorems of WS-RR RR5 untouched; boot-time trees are a follow-up once a deployment asks for them |
| D12 | Transitions land in production modules from day one (unreachable until CB6 wires the arms); theorem-heavy modules are staged and promoted when a production consumer imports them | Stage everything until CB6 | A definition nobody calls changes no behaviour; staging it only defers the partition work |
| D13 | Deadlines are **kernel-owned and implicit** (`D = P`): `schedContextConfigure`'s `deadline` argument must be `0`, and the kernel assigns `deadline := periodStart + period` at configure, at every refill and at activation | Keep the caller-supplied absolute deadline; or constrained deadlines `D < P` | A caller-chosen deadline under EDF is unbounded priority escalation; constrained deadlines need a density-based admission test and are a follow-up |
| D14 | The CBS wake-up rule at activation resets the deadline only — `if d ≤ now ∨ c·P ≥ (d − now)·Q then d := now + P` — and leaves the budget alone | Abeni–Buttazzo's rule, which also refills `c := Q` | This model's refills are deferred by consumption time (`scheduleReplenishment`), so a refill at activation would mint budget the replenish queue is still owed |
| D15 | Priority inheritance becomes **deadline inheritance** for the EDF class (`inheritedDeadline := min` over blocked waiters' effective deadlines, applied to the thread's own key) while the priority boost stays for the legacy class; inheritance never lifts a member's *server* | Keep the priority boost alone | Under EDF-first a priority boost changes nothing but ties, so `pip_bounded_inversion` would hold vacuously for every bound thread; lifting the server is bandwidth inheritance, a follow-up |

### 3.1 The model

```lean
-- SeLe4n/Kernel/SchedContext/Types.lean (CB2.1)
structure SchedContext where
  ... existing fields, `periodStart` now the window start (CB1.3) ...
  /-- The server this context is a member of; `none` at the root level. -/
  parentServer      : Option SchedContextId := none
  /-- Members, in FIFO order; a leaf has none.  Duplicate-free by construction. -/
  serverMembers     : MemberList := MemberList.empty
  /-- `some c` iff this context is a server, homed on core `c`. -/
  serverCore        : Option CoreId := none
  /-- Members whose subtree holds a runnable or current thread; a leaf's is
      `1` iff its thread is runnable or current.  Drives activation (§3.11). -/
  activeDescendants : Nat := 0
```

`isServer sc := sc.serverCore.isSome`.  A server never binds a thread
(`serverNotThreadBound`); a leaf never has members (`leafHasNoMembers`); a
context is one or the other.  `MemberList` is a `NoDupList SchedContextId`
bounded by `maxServerMembers`, in the style of `Notification.waitingThreads`.

Bounded queries, all total, all fuel-bounded by `maxServerDepth`:
`parentChain? st scId` (the ancestors, root last; `none` on a dangling
parent or a chain longer than the bound), `rootOf?`, `depthOf?`,
`isAncestorOf`, `schedPath? st scId : Option (List SchedKey)` where
`SchedKey := Deadline × Priority × SchedContextId` read root-first.

### 3.2 The hierarchy invariant bundle (`schedHierarchyInvariant`, CB2.6)

| Conjunct | Meaning |
|----------|---------|
| `hierarchyBidirectional` | `child.parentServer = some s` ↔ `child ∈ s.serverMembers` |
| `hierarchyDepthBounded` | every context's `parentChain?` is `some` with length `≤ maxServerDepth` — which is also acyclicity |
| `serverRoleExclusive` | `serverNotThreadBound ∧ leafHasNoMembers` for every context |
| `serverCoreConsistent` | a member server's `serverCore` equals its parent's; a member leaf's bound thread has `determineTargetCore = serverCore` |
| `serverDomainConsistent` | `member.domain = server.domain` (the AE3-A rule lifted one level) |
| `serverMembersBounded` | `serverMembers.length ≤ maxServerMembers` |
| `hierarchicalAdmissionHolds` | §3.5's two inequalities, for every server and every core |
| `activeDescendantsConsistent` | a leaf's count is `1` iff its thread is runnable or current on its core, a server's count is the number of its members with a positive count |
| `deadlineWindowConsistent` | every context has `deadline = periodStart + period` (CB1.3, lifted to the whole tree) |

The bundle joins `crossSubsystemInvariant` as its thirteenth conjunct **with**
a `_fields` entry, because the register already records what happens when a
conjunct is appended without one.

### 3.3 The scheduling order

A runnable thread `t` bound to leaf `sc` has the key path
`schedPath? st sc = some [k_root, …, k_leaf]`, each key `(deadline, priority,
scId)` with the leaf's deadline lowered by its `inheritedDeadline` (D15).
`isBetterPath` compares two paths lexicographically: at each position the
EDF-first `isBetterCandidate` of CB1 on `(deadline, priority)`; on a tie
between **distinct** servers the lower `scId` wins (deterministic, and
transient — every refill re-assigns a deadline, so two servers tie only when
refilled in the same tick); on a tie between two leaves the incumbent is
retained, which is FIFO.  For a thread whose leaf has no parent the path is the
singleton `k_leaf` and `isBetterPath` **is** `isBetterCandidate` — the
no-servers equivalence theorem CB3.4 carries.  An unbound thread has the
deadline-less singleton path and sorts after every deadline-bearing path.

Eligibility is `pathBudgetEligible`: every context on the path has
`budgetRemaining > 0`.  On a parentless leaf it is `hasSufficientBudget`.  The
bucket a thread sits in stays its AK2-B priority mirror; it orders nothing.

### 3.4 Charging, activation and replenishment

```
timerTickBudgetOnCore, bound arm (CB4.3):
  path   := leaf :: ancestors                      -- CB2.4, fuel-bounded
  for each sc in path, in leaf-to-root order:
    consumeBudget sc 1
    if exhausted:
      scheduleReplenishment sc now consumedAmount  -- into sc's own list
      replenishOnCore c sc.scId (now + period)     -- core c's queue; deadline
                                                    --   moves when the refill lands
  if leaf exhausted: timeoutBlockedThreads leaf     -- leaf only (D4)
  preempted := any level exhausted
  re-enqueue the running thread

enqueueRunnableOnCore, bound thread (CB1.5, CB4.6):
  cbsActivateDeadline leaf now                      -- §3.11 (d)
  for each server on the path whose activeDescendants goes 0 → 1:
    cbsActivateDeadline server now                  -- the server was idle
  increment activeDescendants along the path
```

Only consumed ticks charge ancestors: a yield that surrenders the leaf's
remaining budget surrenders nothing above it.  A server's replenishment is
drained by the same `processReplenishmentsDueOnCore` and re-assigns its
deadline exactly as a leaf's does; its wake decision (`replenishWakeDecision`,
CB4.5) is "reschedule this core" rather than "wake thread `t`", because the
members never left the queue.  Since the server is homed on the executing
core, that decision is the existing local-wake bit and no SGI is needed.

### 3.5 Admission

Utilisation stays `Bandwidth.utilization` (ceiling per-mille).  Two
inequalities, both decidable, both checked by every transition that changes a
term of either sum:

* for every server `s`:  Σ over `m ∈ s.serverMembers` of `U(m)` ≤ `U(s)`;
* for every core `c`:  Σ over root-level contexts *active on `c`* of `U` ≤ 1000,
  where a root server is active on its `serverCore` and a root leaf is active
  on its bound thread's home core (an unbound root leaf consumes nothing and
  is admitted when `schedContextBind` gives it a thread).

The second inequality is EDF's schedulability condition for implicit-deadline
servers and the hypothesis of CB7.7's guarantee.  The RPi5 canonical
deployment's `admissibleUtilisation = 750` remains a liveness-side margin on
top of the kernel's 1000 ‰ ceiling.

### 3.6 Core-homed servers

`schedContextConfigureServer` fixes `serverCore`, refusing a core the machine
does not declare (`MachineState.declaredCoreCount`, the RR5 rule).  Binding a
member checks the core (D5); `.tcbSetAffinity` on a member thread and
`donateSchedContext` of a member leaf to a thread homed elsewhere both refuse
with `.illegalState` **before** any state is committed — the `Kernel` monad
discards the rendezvous on the call path, and the receive-side arm returns the
error to the receiver.  A member SchedContext donated to a same-core passive
server keeps its position in the tree, so the passive server runs within the
client's reservation and at the client's deadline, which is the semantics
HCBS wants.

### 3.7 Information flow

`schedContextBindServer` is `.policyGated`: the checked arm requires
`securityFlowsTo(childLabel, serverLabel) ∧ securityFlowsTo(serverLabel, childLabel)`
under the installed labeling context, so every member of a server carries a
label equivalent to the server's (`serverMembersUniformlyLabeled`, CB7.1).
With that, a tick that writes a member's ancestors writes only same-label
objects and SM8.B's per-core non-interference lift goes through unchanged in
shape (CB7.2); the projection erases the four new fields as structural
scheduling plumbing, the class `boundThread` already belongs to (CB2.9).

### 3.8 The syscall surface

| Id | Syscall | Capability | Registers | Effect |
|----|---------|------------|-----------|--------|
| 35 | `schedContextConfigureServer` | SchedContext, `.write` | `MR0` = core | leaf with no thread and no parent → server on `core`; root admission on `core` |
| 36 | `schedContextBindServer` | **server** SchedContext, `.write` | `MR0` = CPtr of the child, resolved in the caller's CSpace with `.write` (the `tcbBindNotification` pattern) | link child under server: role, acyclicity, depth, core, domain, admission, label checks |
| 37 | `schedContextUnbindServer` | **child** SchedContext, `.write` | none | unlink; the child becomes a root and is admitted on its core; a child server with members is refused |

Hierarchy-aware existing operations: `schedContextBind` (refuses a server;
checks the ancestor's core; admits a root leaf on the thread's core),
`schedContextConfigure` (the `deadline` argument must be `0` since CB1.3;
member admission against the parent; root admission per core; priority is a
tie-break and may change at any time), `schedContextUnbind` (unchanged
effect, restated invariants), `.tcbSetAffinity` (refused on members),
`donateSchedContext` (§3.6), `lifecycleRetype` (a populated server is refused;
a member leaf is unlinked before destruction).

Every refusal is an explicit `KernelError` arm; none is a fault.  All three
new ids are `.unit`-shaped returns and non-blocking, so
`capFaultReceivePhase?` answers `none` for each.

### 3.9 Pre-existing finding this workstream closes first

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
reported to the maintainer as a vulnerability finding at planning time; the
plan records the remediation.

### 3.10 What stays fixed

No new `@[export]`, so `LEAN_READY_GATED_SEAMS` and the readiness derivation
are untouched; no `extern`, so the kernel-entry export gate's requirement set
is untouched.  `SYSCALL_ABI_VERSION` stays `3`: ids `0..34` keep their
encodings and register layout (the configure `deadline` slot keeps its
position; only its accepted value narrows to `0`), the conformance suite pins
that, and `SyscallId::COUNT` moves to `38` on both sides with the existing
mirror tests holding them equal.

### 3.11 The EDF-first root, precisely

**Two classes.**  An entity with a kernel-assigned deadline — every bound
thread through its SchedContext, every server — is in the *EDF class*; an
unbound thread is in the *legacy class* and has no deadline.  Every EDF-class
entity outranks every legacy-class thread.  Within the EDF class: earlier
deadline first; equal deadlines by higher priority; then FIFO among leaves
and ascending `scId` among distinct servers.  Within the legacy class: the
pre-CB1 order, higher priority then FIFO — which keeps the idle thread last.

**Deadline rules** (all kernel-side; `periodStart` records the window start):

* (a) configure: `deadline := now + period`, `periodStart := now`;
* (b) a refill landing at `t_r`: `deadline := t_r + period`,
  `periodStart := t_r` — `cbsUpdateDeadline` as it runs in `refillSchedContext`
  today, now also writing `periodStart`;
* (c) exhaustion: the deadline is untouched; the entity is ineligible until
  its refill lands, so its stale deadline orders nothing;
* (d) activation — a bound thread becoming runnable from not-runnable, or a
  server whose `activeDescendants` goes from `0` to `1`:
  `if deadline ≤ now ∨ budgetRemaining · period ≥ (deadline − now) · budget`
  `then deadline := now + period, periodStart := now`, budget unchanged (D14).

Rule (d) is what keeps an entity that idled with an old deadline from
returning at the head of the queue and spending a whole budget there; rules
(a)–(c) are what make `deadlineWindowConsistent` an invariant rather than a
convention.  The invariant `edfCurrentEarliestOnCore` states the order's
consequence for dispatch: if the current thread has a deadline, no eligible
queued thread of its domain has an earlier one; if it has none, no eligible
queued thread of its domain has one at all.

**Inheritance** (D15).  A thread that blocks others carries
`inheritedDeadline := min` over its blocked waiters' effective deadlines,
maintained where `updatePipBoost` maintains the priority boost today and
cleared where `revertPriorityInheritance` clears it; its effective deadline is
`min(own, inherited)`, applied to its own key.  A passive server inherits
through donation as today.  The priority boost keeps its meaning for the
legacy class and as the tie-break.

**The guarantee** (CB7.7).  On a core whose admitted roots satisfy §3.5, every
root entity with positive budget at activation is dispatched for its remaining
budget before its deadline.  This is the classical EDF+CBS theorem; the plan
commits to its algebraic core (`cbs_demand_bound`: in any window of length `L`
the admitted roots demand at most `L`), to EDF optimality over the per-core
step relation (`edf_selects_earliest_eligible`), and to the composed statement
with every hypothesis named.  If the composition does not close within its
row, it lands as an externalized hypothesis `edfTraceFeasible` in the style of
`hBandProgress`, with the closure registered in §11 — the model then states
the guarantee conditionally, never vacuously.

## 4. Dependencies

* **WS-SM SM5.A/SM5.D/SM5.F/SM5.H** (landed): the per-core selector, tick,
  priority-inheritance and CBS surface this workstream changes and then
  generalises.
* **WS-SM SM8.A–D** (landed): the per-core observer and the write-set
  discipline CB1.11, CB2.9 and CB7 extend.
* **WS-RR RR5** (landed): the declared-core discipline CB5.1 reuses for a
  server's core, and the boot theorems CB2.7 keeps intact.
* **WS-RR RR6–RR8**: no dependency either way; §2.3 states the file partition.
* **SM10**: none.  CB6's fixtures are re-cut if the image lands first.

## 5. Phase map

| Phase | Scope (one line) | Subs | Est |
|-------|------------------|------|-----|
| CB0 | Registration, baseline verification, the pre-existing configure-authority gap, order witnesses | 5 | S–M |
| CB1 | The EDF-first root on the flat model: kernel-owned deadlines, the wake-up rule, deadline inheritance, the selector and its suite, the one fixture refresh | 13 | XL |
| CB2 | Model: hierarchy fields, bounded queries, per-object and store-level invariants, boot and observer erasure — inert | 10 | M–L |
| CB3 | Hierarchical selection and eligibility, provably identical on states without servers | 9 | L |
| CB4 | Hierarchical charging, activation and replenishment on the per-core tick; the subtree isolation theorems | 10 | L–XL |
| CB5 | Hierarchy transitions and the hierarchy-aware forms of the existing operations, each with its preservation surface | 16 | XL |
| CB6 | The three syscalls on both sides of the ABI, flow classification, dispatch payoff, end-to-end fixtures | 12 | L |
| CB7 | Information-flow re-establishment and the CBS guarantee | 9 | L–XL |
| CB8 | Closure: specification, evidence, inventory, hardware spot-check script, hand-off | 8 | M |

## 6. Sub-tasks

Estimates: **T** trivial (<1h) · **S** small (<½ day) · **M** medium (1–2 days)
· **L** large (3–5 days) · **XL** extra-large (>1 week, expect to split further).
Each sub-task is sized to be one coherent PR or less, per the PR checklist.
Where a row says **in the same row as**, the switch and the theorem that
licenses it cannot compile apart and land as one cut.

### CB0 — Registration and baseline

Nothing here changes scheduling behaviour except CB0.3, which removes an
authority gap the flat model already has.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| CB0.1 | Register the workstream: the **WS-CB** registry row, the debt-register row pointing at this plan, the `CLAUDE.md`/`AGENTS.md` status subsection, this plan, the v0.34.49 CHANGELOG entry | `docs/REGISTERED_DEBT.md`, `CLAUDE.md`, `AGENTS.md`, `CHANGELOG.md` | S |
| CB0.2 | Pre-implementation refinement pass at the opening cut: re-verify every §1.1 claim against the tree, fold corrections into §1 and §3 (the WS-RA precedent), re-run the prefix collision measurement | this plan | S |
| CB0.3 | Close the priority and domain half of §3.9: `schedContextConfigure` takes the caller, gates `priority` through `validatePriorityAuthority` against the caller's MCP, and refuses a `domain` change on a bound SchedContext with `.illegalAuthority`; theorems `schedContextConfigure_priority_within_caller_mcp`, `schedContextConfigure_domain_fixed_of_bound`; negative-suite pins; trace-fixture refresh with rationale | `SeLe4n/Kernel/SchedContext/Operations.lean`, `SeLe4n/Kernel/API.lean`, `tests/NegativeStateSuite.lean`, `tests/fixtures/main_trace_smoke.expected` | M |
| CB0.4 | Order witnesses landed **first**: Tier-2 pins of the pre-CB1 fixed-priority-first order among SchedContext threads, the exhaustion re-enqueue, and the replenish wake — the scenarios CB1 inverts to the EDF order in its switch cut (the WS-RA RA.E.1 precedent: a witness that fails on the pre-migration tree, then pins the post-flip order) | `tests/SmpCbsSuite.lean` | S |
| CB0.5 | Stale-comment sweep on files this workstream edits: the Rust `SyscallId` header's variant count and Lean line references, the `dispatchCapabilityOnly` docstring's arm count, the evidence index's staged-module count | `rust/sele4n-types/src/syscall.rs`, `SeLe4n/Kernel/API.lean`, `docs/CLAIM_EVIDENCE_INDEX.md` | S |

**Acceptance**: CB0.3's two theorems elaborate; `lake exe smp_cbs_suite` runs
the CB0.4 witnesses green against the pre-CB1 tree; Tier 0 and the docs-sync
lane pass.

### CB1 — The EDF-first root, on the flat model

The one phase whose behavioural change is intended to reach existing
fixtures.  It lands as a small number of cuts in this order: the order and
selector with their equivalence theorem, the deadline rules, inheritance, the
suite, the refresh.  No server field exists yet, so every theorem here is a
flat-model theorem the hierarchy phases generalise.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| CB1.1 | The order: `isBetterCandidate` rewritten EDF-first (§3.11) — a deadline-bearing challenger beats a deadline-less incumbent, an earlier deadline wins, then higher priority, then the incumbent; `isBetterCandidate_irrefl`, `_asymm`, `_transitive` re-proved; `isBetterCandidate_legacy_class_eq_fp` (two deadline-less candidates compare as before) | `SeLe4n/Kernel/Scheduler/Operations/Selection.lean` | M |
| CB1.2 | Selection by scan: `chooseBestRunnableEffective` over the core's runnable list under the new order, the bucket-first fast path retired (the priority buckets stay as membership and FIFO), totality and optimality re-proved, **in the same row as** `chooseThreadEffectiveOnCore_eq_flat_of_no_deadlines` (a state whose runnable threads all lack deadlines selects as before) and the inversion of CB0.4's witnesses to the EDF order (consumes CB1.1) | `SeLe4n/Kernel/Scheduler/Operations/Selection.lean`, `SeLe4n/Kernel/Scheduler/Operations/PerCoreChooseThread.lean`, `tests/SmpCbsSuite.lean` | XL |
| CB1.3 | Kernel-owned deadlines (D13): `schedContextConfigure` refuses a nonzero `deadline` argument (`.invalidArgument`; the ABI slot stays, its only accepted value is `0`) and assigns `deadline := timer + period`, `periodStart := timer`; `refillSchedContext` records `periodStart := now` beside the deadline it already sets; `deadlineWindowConsistent` (`deadline = periodStart + period`) defined, proved of the boot state, preserved by the Z2 budget engine; `bootSafeSchedContextCheck` requires it | `SeLe4n/Kernel/SchedContext/Operations.lean`, `SeLe4n/Kernel/SchedContext/Budget.lean`, `SeLe4n/Kernel/Scheduler/Operations/Core.lean`, `SeLe4n/Kernel/SchedContext/Invariant/Defs.lean`, `SeLe4n/Platform/Boot.lean` | M |
| CB1.4 | Retire `TCB.deadline` from selection: `resolveEffectivePrioDeadline` yields no deadline for `.unbound`; the field removed with its `BEq`, `ext`, boot and projection sweeps, or, where a consumer remains, proved unread by selection; the three suites that set it re-cut | `SeLe4n/Model/Object/Types.lean`, `SeLe4n/Kernel/Scheduler/Operations/Selection.lean`, `tests/SmpCancellationSuite.lean`, `tests/NegativeStateSuite.lean`, `tests/PriorityInheritanceSuite.lean` | M |
| CB1.5 | The CBS wake-up rule `cbsActivateDeadline sc now` (§3.11 (d), D14) applied in `enqueueRunnableOnCore` when a bound thread becomes runnable from not-runnable; preserves `deadlineWindowConsistent` and `schedContextWellFormed`; `cbsActivateDeadline_noop_of_fresh` (a thread whose window still has room is untouched); the deviation from the classical rule documented at the definition (consumes CB1.3) | `SeLe4n/Kernel/Scheduler/Operations/Selection.lean`, `SeLe4n/Kernel/SchedContext/Budget.lean`, `SeLe4n/Kernel/SchedContext/Invariant/Defs.lean` | M |
| CB1.6 | Deadline inheritance (D15): `TCB.inheritedDeadline : Option Deadline` with its `BEq`, `ext`, boot and projection sweeps; `computeMinWaiterDeadline`; `updatePipBoost` writes both `pipBoost` and `inheritedDeadline`; the effective key reads `min(own, inherited)`; `revertPriorityInheritance` clears both; the per-core forms `updatePipBoostOnCore` and `propagatePipChainCrossCore` follow (consumes CB1.2) | `SeLe4n/Kernel/Scheduler/PriorityInheritance/Compute.lean`, `SeLe4n/Kernel/Scheduler/PriorityInheritance/Propagate.lean`, `SeLe4n/Kernel/Scheduler/PriorityInheritance/PerCore.lean`, `SeLe4n/Model/Object/Types.lean` | L |
| CB1.7 | The PIP theorem surface in deadline terms: `pip_bounded_inversion` restated (a blocked client's effective deadline bounds the blocker's), blocking-graph acyclicity untouched, the donation-preservation family re-proved over the new field (consumes CB1.6) | `SeLe4n/Kernel/Scheduler/PriorityInheritance/BoundedInversion.lean`, `SeLe4n/Kernel/Scheduler/PriorityInheritance/Preservation.lean`, `SeLe4n/Kernel/IPC/Invariant/DonationPreservation.lean` | L |
| CB1.8 | Reschedule decisions in the selector's order: `candidateOutranksCurrentOnCore` and `handleRescheduleSgiOnCore`; `setPriorityOp`'s "priority decreased" trigger becomes "key worsened"; bind and configure keep the AK2-B priority mirror as the bucket rule; `edfCurrentEarliestOnCore` replaces `edfCurrentHasEarliestDeadlineOnCore` in the per-core bundle (consumes CB1.6) | `SeLe4n/Kernel/Scheduler/Operations/Selection.lean`, `SeLe4n/Kernel/SchedContext/PriorityManagement.lean`, `SeLe4n/Kernel/Scheduler/Invariant/PerCore.lean` | L |
| CB1.9 | The per-core suite re-proved over the new selector and the new conjunct: the `schedulerInvariantStrong_smp` family for `scheduleEffectiveOnCore`, `handleRescheduleSgiOnCore`, `switchToThreadOnCore`, the tick's preempt path and the domain switch; the idle keystone unchanged, since the idle thread is deadline-less and last (consumes CB1.8) | `SeLe4n/Kernel/Scheduler/Invariant/PerCoreInvariantSuite.lean`, `SeLe4n/Kernel/Scheduler/Operations/PerCoreWake.lean`, `SeLe4n/Kernel/Scheduler/Operations/PerCoreTimerTick.lean` | XL |
| CB1.10 | Frozen twins and agreement: `frozenTimerTickBudget` and `frozenSchedContextConfigure` over the deadline rules; the agreement interlock re-proved | `SeLe4n/Kernel/FrozenOps/Operations.lean`, `SeLe4n/Kernel/FrozenOps/Agreement.lean` | S |
| CB1.11 | Observer and non-interference: `inheritedDeadline` and `periodStart` classified for the projection (structural scheduling plumbing, the `pipBoost` class); SM8.B's per-core lift re-proved over the new selector — the observable order changes only through same-label deadlines (consumes CB1.9) | `SeLe4n/Kernel/InformationFlow/Projection.lean`, `SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean`, `SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean` | L |
| CB1.12 | Liveness surface restated for EDF: the band-based `WCRTHypotheses` and `bandExhaustionBound` kept for the legacy class; the EDF class's response bound stated as `edfResponseBound := domainRotationBound + period` with its hypotheses, proved as far as CB7 commits to; the lock-wait terms of `PerCoreWcrt` unchanged | `SeLe4n/Kernel/Scheduler/Liveness/WCRT.lean`, `SeLe4n/Kernel/Scheduler/Operations/PerCoreWcrt.lean` | L |
| CB1.13 | The one policy refresh: every `.expected` whose scenario has a deadline-bearing runnable thread re-cut with rationale (the SM5.K four-core golden, the main trace, the WS-RA and fault fixtures where bound threads appear), the scenario registry updated; spec §8.12.3 and §8.13 rewritten for EDF-first and deadline inheritance; evidence-index rows; Tier-3 anchors; the `CLAUDE.md`/`AGENTS.md` standing constraint | `tests/fixtures/`, `docs/spec/SELE4N_SPEC.md`, `docs/CLAIM_EVIDENCE_INDEX.md`, `scripts/test_tier3_invariant_surface.sh`, `CLAUDE.md`, `AGENTS.md` | L |

**Acceptance**: `chooseThreadEffectiveOnCore_eq_flat_of_no_deadlines`
elaborates with no hypothesis beyond the absence of deadlines;
`deadlineWindowConsistent` and `edfCurrentEarliestOnCore` are preserved by
every per-core transition; `pip_bounded_inversion` is stated over deadlines
and is not vacuous on bound threads; every refreshed fixture carries its
rationale in the fixture README.

### CB2 — The model, inert

Every definition here is unreachable from a live path until CB6; the only
behavioural change is that a boot SchedContext must be a parentless leaf,
which every existing fixture already is.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| CB2.1 | Add `parentServer`, `serverMembers`, `serverCore`, `activeDescendants` to `SchedContext` with defaults (§3.1); `MemberList` as a bounded `NoDupList SchedContextId`; `isServer`, `isLeaf`; extend the manual `BEq` instance | `SeLe4n/Kernel/SchedContext/Types.lean` | M |
| CB2.2 | Sweep every constructor-arity destructuring the build now rejects — `schedContextReferencesReservedIdleSlot`, `bootSafeSchedContextCheck` and siblings — classifying the new fields: a member or parent id naming a reserved idle object is refused, and a boot SchedContext is a parentless leaf with no active descendants | `SeLe4n/Platform/Boot.lean`, whatever else the build names | S |
| CB2.3 | Constants `maxServerDepth := 3`, `maxServerMembers := 16`, with `pathLockFootprint_le_maxLockSetSize` (the depth plus the tick's three locks stays within `maxLockSetSize`) and a docstring recording the cost of one path charge | `SeLe4n/Kernel/SchedContext/Hierarchy.lean` (new) | S |
| CB2.4 | Fuel-bounded hierarchy queries `parentChain?`, `rootOf?`, `depthOf?`, `isAncestorOf`, `schedPath?` with congruence over `getSchedContext?` and the `_of_root` simplifications (a parentless leaf's chain is empty, its path the singleton) | `SeLe4n/Kernel/SchedContext/Hierarchy.lean` | M |
| CB2.5 | Per-object well-formedness: `SchedContext.wellFormed` gains `serverMembersBounded` and `serverRoleExclusive`; `schedContextWellFormed` follows; the sixteen Z2 preservation theorems re-proved (every budget operation frames the new fields) | `SeLe4n/Kernel/SchedContext/Types.lean`, `SeLe4n/Kernel/SchedContext/Invariant/Defs.lean` | M |
| CB2.6 | The store-level bundle `schedHierarchyInvariant` (§3.2, nine conjuncts, `deadlineWindowConsistent` lifted from CB1.3), decidable where the arithmetic allows, with projections and `default_schedHierarchyInvariant` | `SeLe4n/Kernel/SchedContext/Invariant/HierarchyDefs.lean` (new) | M |
| CB2.7 | Boot: `bootSafeSchedContextCheck` requires a parentless, memberless, inactive leaf; `bootFromPlatformCheckedWithIdleThreadsFor_schedHierarchyInvariant` on the production boot path; `SchedContext.empty` and `mkChecked` produce leaves (consumes CB2.6) | `SeLe4n/Platform/Boot.lean`, `SeLe4n/Kernel/SchedContext/Types.lean` | M |
| CB2.8 | Equality pins: the `BEq` instance reads every field (a witness that two contexts differing only in `parentServer` compare unequal, the SM3.A audit-pass lesson) and a `SchedContext.ext` lemma over the full field list | `SeLe4n/Kernel/SchedContext/Types.lean` | S |
| CB2.9 | Observer projection: erase the four fields in `projectKernelObject` and the per-core observer as structural scheduling plumbing (the `boundThread` class); re-prove the projection lemmas the erasure touches; `schedContextWriteSet` stays the singleton, since a member's ancestors share its core | `SeLe4n/Kernel/InformationFlow/Projection.lean`, `SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean` | M |
| CB2.10 | Freeze mirror: `FrozenKernelObject.schedContext` carries the record verbatim, so the freeze/thaw proofs and the lock projection re-elaborate over the new fields; Tier-3 anchors for CB2; `docs/codebase_map.json` regenerated; spec §8.12.8 skeleton stating "model landed, inert" | `SeLe4n/Model/FrozenState.lean`, `SeLe4n/Model/FreezeProofs.lean`, `scripts/test_tier3_invariant_surface.sh`, `docs/spec/SELE4N_SPEC.md` | S |

**Acceptance**: `lake build` of every touched module; `crossSubsystemInvariant`
is **not** yet extended (that is CB5.13, after the refusals it depends on);
every fixture byte-identical to the post-CB1 baseline.

### CB3 — Hierarchical selection

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| CB3.1 | `pathBudgetEligible st tcb` — every context on the path has positive budget — with `pathBudgetEligible_eq_hasSufficientBudget_of_root` (consumes CB2.4) | `SeLe4n/Kernel/Scheduler/Operations/Selection.lean` | S |
| CB3.2 | `resolveEffectiveSchedPath st tcb : List SchedKey`, root-first, the leaf key lowered by `inheritedDeadline`; `resolveEffectiveSchedPath_root_eq_resolveEffectivePrioDeadline` (the singleton is CB1's pair) | `SeLe4n/Kernel/Scheduler/Operations/Selection.lean` | M |
| CB3.3 | `isBetterPath` (§3.3) over CB1.1's order with `isBetterPath_irrefl`, `_asymm`, `_trans` and `isBetterPath_singleton_eq_isBetterCandidate` | `SeLe4n/Kernel/Scheduler/Operations/Selection.lean` | M |
| CB3.4 | `chooseBestRunnableHierarchical` replacing the scan's comparator inside `chooseThreadEffectiveOnCore`, **in the same row as** `chooseThreadEffectiveOnCore_eq_flat_of_no_servers` — on a state whose contexts are all parentless the new selector is CB1.2's (consumes CB3.1–CB3.3) | `SeLe4n/Kernel/Scheduler/Operations/Selection.lean` | L |
| CB3.5 | Totality and optimality restated: `chooseBestRunnableHierarchical_always_ok` and `_optimal` (the selection is `isBetterPath`-maximal among eligible in-domain candidates), the skip-corrupt-entry contract kept | `SeLe4n/Kernel/Scheduler/Operations/PerCoreChooseThread.lean` | L |
| CB3.6 | `candidateOutranksCurrentOnCore` in path form, so `handleRescheduleSgiOnCore` decides in the selector's own order | `SeLe4n/Kernel/Scheduler/Operations/Selection.lean` | M |
| CB3.7 | `edfCurrentEarliestOnCore` in path form (the current's root key is earliest among eligible in-domain queued threads' root keys, and its leaf key among its own server's), with the flat corollary; `schedulerPriorityMatchOnCore` and `effectiveParamsMatchRunQueueOnCore` unchanged in meaning, since the bucket orders nothing | `SeLe4n/Kernel/Scheduler/Invariant/PerCore.lean` | L |
| CB3.8 | Re-prove the selection-dependent suite: `chooseThreadOnCore_ok_of_runnableTCBs`, the idle keystone (untouched — idle threads are unbound), and the `schedulerInvariantStrong_smp` preservation family for `scheduleEffectiveOnCore` and `handleRescheduleSgiOnCore` | `SeLe4n/Kernel/Scheduler/Invariant/PerCoreInvariantSuite.lean`, `SeLe4n/Kernel/Scheduler/Operations/PerCoreWake.lean` | L |
| CB3.9 | Fixtures byte-identical to the post-CB1 baseline (every `.expected`); Tier-2 scenarios on hand-built hierarchies via `StateBuilder.withServerHierarchy` — a server with the earlier deadline outranks a root leaf, two servers tie-broken by priority then `scId`, member order local; Tier-3 anchors | `tests/SmpCbsSuite.lean`, `SeLe4n/Testing/StateBuilder.lean` | M |

**Acceptance**: `chooseThreadEffectiveOnCore_eq_flat_of_no_servers` elaborates
without hypotheses beyond parentlessness; `test_tier2_trace.sh` reports every
sha256 unchanged from the post-CB1 baseline.

### CB4 — Hierarchical charging, activation and replenishment

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| CB4.1 | `chargeSchedPath st c path now : SystemState × Bool` — the §3.4 fold — with frames: `getTcb?` unchanged, every run queue unchanged, only core `c`'s replenish queue and the path's contexts written | `SeLe4n/Kernel/Scheduler/Operations/Core.lean` | M |
| CB4.2 | Generalise the three home readers to servers: `schedContextReplenishHome` (a server's home is `serverCore`), `replenishQueueAffinityConsistentOnCore` and `replenishQueueEntriesBoundOnCore` (an entry's context is bound **or** a server homed on `c`), each with its `_of_leaf` equivalence | `SeLe4n/Kernel/SchedContext/Operations.lean`, `SeLe4n/Kernel/SchedContext/ReplenishAffinity.lean`, `SeLe4n/Kernel/SchedContext/BindingAffinity.lean` | M |
| CB4.3 | `timerTickBudgetOnCore`'s bound arm charges through `chargeSchedPath`, leaf-only timeouts, preemption iff any level exhausted, **in the same row as** `timerTickBudgetOnCore_eq_flat_of_root` (a parentless leaf runs the prior body) (consumes CB4.1, CB4.2) | `SeLe4n/Kernel/Scheduler/Operations/Core.lean` | L |
| CB4.4 | Re-prove the tick preservation family over the new body — the ten `timerTickOnCore_preserves_*` structural theorems, `allThreadsTimeSlicePositive`, `schedulerInvariantStructuralRegNodup_perCore`, `deadlineWindowConsistent`, and the CBS side (`replenishQueueValidOnCore`, `replenishmentPipelineOrderOnCore`, `perCoreCbsInvariant`) — mostly by CB4.3's reduction plus CB4.1's frames | `SeLe4n/Kernel/Scheduler/Operations/PerCoreTimerTick.lean`, `SeLe4n/Kernel/Scheduler/Operations/PerCoreTickCbsPreservation.lean`, `SeLe4n/Kernel/Scheduler/Operations/PerCoreTickCbsAffinity.lean`, `SeLe4n/Kernel/Scheduler/Invariant/PerCoreInvariantSuite.lean` | XL |
| CB4.5 | Server replenishment: `replenishWakeDecision` (`.wakeThread`, `.rescheduleCore`, `.none`) replacing `replenishWakeTarget`; `processOneReplenishmentOnCore` raises the local-wake bit on `.rescheduleCore`; a server's refill re-assigns its deadline by rule (b); `cbsReplenish_server_reschedules_local`, `replenishWakeDecision_leaf_eq_target` | `SeLe4n/Kernel/Scheduler/Operations/Core.lean`, `SeLe4n/Kernel/Scheduler/Operations/PerCoreTimerTick.lean` | M |
| CB4.6 | Activation along the path: `activeDescendants` maintained where a thread becomes runnable, is dequeued for dispatch, is made current, blocks or is suspended; `cbsActivateDeadline` applied to each server whose count goes from `0` to `1` (§3.4, rule (d)); `activeDescendantsConsistent` and `deadlineWindowConsistent` preserved by every path that moves the count (consumes CB1.5, CB2.6) | `SeLe4n/Kernel/Scheduler/Operations/Selection.lean`, `SeLe4n/Kernel/Scheduler/Operations/Core.lean`, `SeLe4n/Kernel/Lifecycle/Suspend.lean` | L |
| CB4.7 | Lock footprint: `chargeSchedPath_writes_within_timerTickOnCoreLockSet` (the same three domains) and the model-level `chargeSchedPathLockSet` with `_pairwise_le` and `_size_le_maxLockSetSize` (consumes CB2.3) | `SeLe4n/Kernel/Scheduler/Operations/PerCoreTimerTick.lean` | M |
| CB4.8 | `schedHierarchyInvariant` preserved by the tick, the drain, `replenishOnCore` and the activation paths — budgets, deadlines, window starts and counts move, the tree fields are framed | `SeLe4n/Kernel/Scheduler/Operations/PerCoreTickCbsPreservation.lean` | M |
| CB4.9 | Isolation theorems: `chargeSchedPath_charges_every_ancestor`; `server_subtree_consumption_bounded` (a server's subtree consumes at most `maxReplenishments × server.budget` over any window, lifting `cbs_bandwidth_bounded`) and its tight form under `cbsWindowReplenishmentsBounded`; `member_isolation` (a member's consumption is bounded by its own leaf whatever its siblings do) | `SeLe4n/Kernel/SchedContext/Invariant/HierarchyDefs.lean` | L |
| CB4.10 | Tier-2 scenarios: two members exhaust their server and both stop; the server's replenishment resumes both with a fresh deadline; an idle server is activated by rule (d) when its first member wakes; a nested server exhausts under a live parent; golden fixture `tests/fixtures/hierarchical_server_tick.expected` with its sha256 and README row; Tier-3 anchors | `tests/SmpCbsSuite.lean`, `tests/fixtures/` | M |

**Acceptance**: `timerTickOnCore_preserves_perCoreCbsInvariant` and the
structural family elaborate over the new body; `server_subtree_consumption_bounded`
is stated over an arbitrary subtree, not a fixed depth; every pre-existing
fixture byte-identical to the post-CB1 baseline.

### CB5 — Hierarchy transitions, proven before they are reachable

Every transition here is a production definition with no caller until CB6.
The affinity refusal in CB5.8 lands before CB5.13 because the cross-subsystem
bridge for affinity is false without it.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| CB5.1 | `schedContextConfigureServer vScId core`: refuses a bound thread, an existing parent, existing members on another core, and an undeclared core (`MachineState.declaredCoreCount`, the RR5 rule); sets `serverCore`; assigns the deadline by rule (a); root admission on `core` (consumes CB2.4, CB2.6) | `SeLe4n/Kernel/SchedContext/HierarchyOperations.lean` (new) | M |
| CB5.2 | Per-core root admission: `collectRootSchedContextsOnCore`, `checkRootAdmissionOnCore`, `checkMemberAdmission`; `schedContextConfigure` and `schedContextBind` route through them — a root leaf is admitted on its thread's core at bind, `.resourceExhausted` becoming a bind refusal; `rootAdmission_sound_per_core`; negative-suite and trace-fixture updates with rationale | `SeLe4n/Kernel/SchedContext/Operations.lean`, `SeLe4n/Kernel/SchedContext/Budget.lean` | L |
| CB5.3 | `schedContextBindServer vServer vChild`: the §3.8 check list (server role, parentless child, `isAncestorOf` refusal, depth, core, domain, an empty child server, member admission), the bidirectional link, the child's count folded into the server's (consumes CB5.2) | `SeLe4n/Kernel/SchedContext/HierarchyOperations.lean` | L |
| CB5.4 | `schedContextUnbindServer vChild`: a child server with members refused; unlink; the child's count removed from the parent's; root admission on the child's core (consumes CB5.2) | `SeLe4n/Kernel/SchedContext/HierarchyOperations.lean` | M |
| CB5.5 | Hierarchy-aware `schedContextBind`: refuses a server target; checks the thread's home core against the ancestor's `serverCore`; the bound thread's runnability enters the ancestors' counts; `scThreadIndex` unchanged (consumes CB4.6) | `SeLe4n/Kernel/SchedContext/Operations.lean` | M |
| CB5.6 | Hierarchy-aware `schedContextConfigure`: the `deadline` argument stays `0`-only (CB1.3); a priority change on a server or a member is a tie-break change and needs no re-bucketing beyond the AK2-B mirror; member admission against the parent, root admission per core; reconfiguring a populated server's budget or period re-assigns its deadline by rule (a) (consumes CB5.2) | `SeLe4n/Kernel/SchedContext/Operations.lean` | M |
| CB5.7 | `schedContextUnbind` on a member leaf: today's effect plus the ancestors' counts decremented if the thread was active; `schedContextUnbindOnCore` follows | `SeLe4n/Kernel/SchedContext/Operations.lean`, `SeLe4n/Kernel/SchedContext/OperationsPerCore.lean` | S |
| CB5.8 | `setThreadCpuAffinityWithMigration` refuses a member thread with `.illegalState` before any write; `setThreadCpuAffinityWithMigration_rejects_member` | `SeLe4n/Kernel/Scheduler/Operations/Core.lean` | S |
| CB5.9 | `setPriorityOp` on a member thread changes its tie-break under the caller's MCP and nothing else: `setPriorityOp_member_preserves_schedHierarchyInvariant`; `setMCPriorityOp` unchanged | `SeLe4n/Kernel/SchedContext/PriorityManagement.lean` | S |
| CB5.10 | Donation: `donateSchedContext` refuses a member leaf whose `serverCore` differs from the donee's home core (`.illegalState`); the replenish migration inside the three donation composites is a definitional no-op for members (`member_donation_same_core`); `applyCallDonationOnCore_preserves_schedHierarchyInvariant` and its reply and replyRecv twins | `SeLe4n/Kernel/IPC/Operations/Endpoint.lean`, `SeLe4n/Kernel/IPC/Operations/Donation/Primitives.lean` | M |
| CB5.11 | Lifecycle: `lifecyclePreRetypeCleanup` refuses to retype a populated server (`.illegalState`) and unlinks a member leaf before destruction; `hierarchyBidirectional` and `activeDescendantsConsistent` preserved under retype | `SeLe4n/Kernel/Lifecycle/Operations/Cleanup.lean`, `SeLe4n/Kernel/Lifecycle/Operations/RetypeWrappers.lean` | M |
| CB5.12 | Preservation surface for CB5.1–CB5.11: each transition preserves `schedHierarchyInvariant`, `perCoreCbsInvariant`, `runQueueOnCoreWellFormed`, `queueCurrentConsistentOnCore`, `edfCurrentEarliestOnCore`, objects `invExt`, `schedContextStoreConsistent`, `schedContextNotDualBound`, `scThreadIndexConsistent` | `SeLe4n/Kernel/SchedContext/Invariant/HierarchyPreservation.lean` (new; staged until the CB6 promotion cut) | XL |
| CB5.13 | `crossSubsystemInvariant` gains `schedHierarchyInvariant` as its thirteenth conjunct **with** `schedHierarchyInvariant_fields`, the pairwise disjointness analysis redone over the full list, the projections, and every existing operation's bridge extended (consumes CB5.8, CB5.12) | `SeLe4n/Kernel/CrossSubsystem.lean` | L |
| CB5.14 | Lock sets for the three transitions — `schedContextConfigureServerLockSet`, `schedContextBindServerLockSet`, `schedContextUnbindServerLockSet` — with `_write_only`, `_pairwise_le`, `_size_le_maxLockSetSize` (consumes CB2.3) | `SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean` | M |
| CB5.15 | Frozen twins `frozenSchedContextConfigureServer`, `frozenSchedContextBindServer`, `frozenSchedContextUnbindServer` with their agreement theorems against the live transitions (the coverage-table rows follow once the ids exist, in CB6) | `SeLe4n/Kernel/FrozenOps/Operations.lean`, `SeLe4n/Kernel/FrozenOps/Agreement.lean` | M |
| CB5.16 | Tier-2 negative pins for every refusal arm of CB5.1–CB5.11 through a thin-dispatcher sub-helper `runHierarchyRefusalChecks`; Tier-3 anchors for the CB5 surface | `tests/NegativeStateSuite.lean`, `scripts/test_tier3_invariant_surface.sh` | M |

**Acceptance**: every CB5 transition has its row in CB5.12's surface;
`crossSubsystemInvariant` has thirteen conjuncts **and** thirteen field-sets;
no live path reaches any of them yet (the dispatcher's wildcard-unreachable
theorems are unchanged until CB6).

### CB6 — The syscalls, live

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| CB6.1 | `SyscallId` variants `.schedContextConfigureServer` (35), `.schedContextBindServer` (36), `.schedContextUnbindServer` (37): `toNat`, `ofNat?`, `count := 38`, `ToString`; the `DecodingSuite` boundary moves to 37/38 | `SeLe4n/Model/Object/Types.lean`, `tests/DecodingSuite.lean` | S |
| CB6.2 | The total-table sweep the new arms force before anything elaborates: `syscallRequiredRight` (`.write` ×3), `syscallChecksTargetFirst`, `syscallDelegates`, `syscallReturnShape` (`.unit` ×3), `enforcementBoundary` + `syscallIdToEnforcementName` (`.policyGated "schedContextBindServerChecked"`, `.capabilityOnly` ×2), `syscallIdToEnforcementNamePerCore`, `contentFlowClass`, `syscallRecordsDeclassification`, `refusalSeamClass`, `frozenOpCoverage` + `frozenOpCoverage_count`, `frozenOpUncheckedReason`, `lockSetForSyscall` (`none` ×3, `lockSetForSyscall_undeclared_none` restated), `capFaultReceivePhase?` (`none` ×3) (consumes CB5.15, CB6.1) | `SeLe4n/Kernel/API.lean`, `SeLe4n/Kernel/Architecture/SyscallReturn.lean`, `SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean`, `SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean`, `SeLe4n/Kernel/InformationFlow/TaintPropagation.lean`, `SeLe4n/Kernel/InformationFlow/RefusalRecord.lean`, `SeLe4n/Kernel/FrozenOps/Operations.lean`, `SeLe4n/Kernel/FrozenOps/Agreement.lean`, `SeLe4n/Kernel/Concurrency/Locks/LockSetForSyscall.lean`, `SeLe4n/Platform/FFI.lean` | M |
| CB6.3 | Arg structures and decoders: `SchedContextConfigureServerArgs` (`core`) with a checked decoder refusing `core ≥ numCores` (the declared-count check stays in the transition, where the machine state is), `SchedContextBindServerArgs` (`childCPtr`), `SchedContextUnbindServerArgs`; encoders, `_roundtrip` and `_error_iff` theorems | `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` | M |
| CB6.4 | `dispatchCapabilityOnly` arms: configureServer (cap target = the SchedContext), bindServer (cap = the server; the child CPtr resolved through the caller's CSpace with `.write` by `syscallLookupCap`, the `tcbBindNotification` pattern), unbindServer (cap = the child) — each through an `…OnCore` form so the Tier-1 per-core routing gate passes; the wildcard-unreachable proofs restated (consumes CB6.2, CB6.3) | `SeLe4n/Kernel/API.lean` | M |
| CB6.5 | Idle-reservation chokepoint: the child CPtr resolves through `syscallResolveCap`, which refuses a reserved idle object; the core operand is not an object id; `dispatchCapabilityOnly_bindServer_idle_refused` | `SeLe4n/Kernel/API.lean` | S |
| CB6.6 | Checked tier: `schedContextBindServerChecked` (the §3.7 label test, `securityFlowsTo` both ways on `objectLabelOf`), the `dispatchWithCapChecked` arms, `checkedDispatch_bindServer_eq_unchecked_when_allowed` and the two `checkedDispatch_*_eq_unchecked` equivalences for the capability-only arms; `enforcementBoundary_is_complete` re-proved (consumes CB6.4) | `SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean`, `SeLe4n/Kernel/API.lean` | M |
| CB6.7 | Dispatch payoff: per-arm `…_preserves_ipcInvariantFull` for the three arms (frames on every conjunct — no IPC state moves), extending `dispatchCapabilityOnly_preserves_ipcInvariantFull` (production) and the staged `dispatchWithCap_preserves_ipcInvariantFull` / `dispatchWithCapChecked_preserves_ipcInvariantFull`; `capabilityDispatchQuiescence` needs no new field, stated as a theorem (consumes CB6.6) | `SeLe4n/Kernel/IPC/Invariant/DispatchArmPreservation.lean`, `SeLe4n/Kernel/IPC/Invariant/DispatchPayoff.lean`, `SeLe4n/Kernel/API.lean` | L |
| CB6.8 | Rust mirrors: `sele4n-types` variants, `COUNT = 38`, `required_right`, tests; the HAL's hand-mirror enum, `from_u32`, `min_inline_args` (1, 1, 0) and the two mirror tests; `sele4n-abi` argument structs (and the configure wrapper's `deadline` field documented as `0`-only); `sele4n-sys` wrappers; conformance cases and the wrapper-length sweep; `test_aarch64_cross_build.sh` green (consumes CB6.1, CB6.3) | `rust/sele4n-types/src/syscall.rs`, `rust/sele4n-hal/src/svc_dispatch.rs`, `rust/sele4n-abi/src/args/sched_context.rs`, `rust/sele4n-sys/src/sched_context.rs`, `rust/sele4n-abi/tests/conformance.rs` | M |
| CB6.9 | ABI version decision recorded on all three sides: `SYSCALL_ABI_VERSION` stays `3` (ids appended, `0..34` unchanged in encoding and layout), with a conformance pin that every prior discriminant encodes as before | `rust/sele4n-abi/tests/conformance.rs`, `SeLe4n/Kernel/Architecture/SyscallReturn.lean` | S |
| CB6.10 | Return-shape and dispatch pins: `SyscallReturnAbiSuite` cases for the three `.unit` frames; `SyscallDispatchSuite` discriminant pins for the new refusal arms; `AbiRoundtripSuite` cases for the two decoders and the `0`-only deadline | `tests/SyscallReturnAbiSuite.lean`, `tests/SyscallDispatchSuite.lean`, `tests/AbiRoundtripSuite.lean` | M |
| CB6.11 | Staging promotion: the theorem modules CB2–CB5 staged enter the `SeLe4n.lean` closure through their production consumers; allowlist entries removed and `STATUS: staged` markers replaced in the same cut; the partition gate passes in both directions (consumes CB6.7) | `SeLe4n.lean`, `SeLe4n/Platform/Staged.lean`, `scripts/staged_module_allowlist.txt` | S |
| CB6.12 | End to end: `syscallDispatchFromAbi` scenarios (configureServer → bindServer → bind thread → ticks → unbindServer) in a new Tier-2 suite with golden fixture `tests/fixtures/hierarchical_server_syscalls.expected`; scenario-registry entries; `NegativeStateSuite` pins for each error arm through the dispatcher (consumes CB6.4, CB6.8) | `tests/HierarchicalServerSuite.lean`, `lakefile.toml`, `scripts/test_tier2_negative.sh`, `tests/fixtures/scenario_registry.yaml` | M |

**Acceptance**: the Lean and Rust id tables agree under the existing mirror
tests; the routing gate reports zero exceptions; both dispatch payoffs
elaborate over 38 arms; the end-to-end fixture is byte-verified in-suite.

### CB7 — Information flow and the CBS guarantee

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| CB7.1 | `serverMembersUniformlyLabeled ctx st`; `schedContextBindServerChecked_establishes_uniformLabels` (the only member-adding transition) and preservation by every other transition (consumes CB6.6) | `SeLe4n/Kernel/InformationFlow/Invariant/Helpers.lean` | M |
| CB7.2 | Per-core NI for the hierarchical tick: `chargeSchedPath_confined_to_label` (under uniform labels every ancestor write is same-label) and the SM8.B tick lift re-proved over the new body (consumes CB4.3, CB7.1) | `SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean`, `SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean` | L |
| CB7.3 | Projection and confinement theorems for the three arms in the SM8 style: `…_preserves_projection` for every observer and `…_confinedToCores` | `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean`, `SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean` | M |
| CB7.4 | Refusal-ledger partition: the SM9 pin `capFaultReceivePhase?_none_iff_records` restated over the wider inductive — the new arms record nothing and fault nothing | `SeLe4n/Platform/FFI.lean`, `SeLe4n/Kernel/InformationFlow/RefusalRecord.lean` | S |
| CB7.5 | Covert-channel classification: the intra-server budget channel closed by construction (`no_cross_label_server_membership`); the inter-server root channel — now a deadline-ordering channel rather than a priority-band one — identified with the class SM8.D bounds and re-derived for EDF, recorded in the lock-domain register rather than in prose | `SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean`, `SeLe4n/Kernel/InformationFlow/FineLockFlow.lean` | M |
| CB7.6 | Taint: the three arms are control-only in `contentFlowClass` (no payload crosses) and the per-arm taint family gains the three arms | `SeLe4n/Kernel/InformationFlow/TaintPropagation.lean` | S |
| CB7.7 | The CBS guarantee (§3.11): `cbs_demand_bound` (in any window of length `L`, the admitted roots of a core demand at most `L`), `edf_selects_earliest_eligible` (from CB3.5's optimality), and `server_receives_budget_within_period` — a root entity with positive budget at activation is dispatched for its remaining budget before its deadline, on a core satisfying §3.5 — with every hypothesis named; the composition lands closed, or as the externalized hypothesis `edfTraceFeasible` with the closure registered in §11 (consumes CB1.12, CB3.5, CB4.9) | `SeLe4n/Kernel/Scheduler/Liveness/EdfGuarantee.lean` (new), `SeLe4n/Kernel/Scheduler/Operations/PerCoreWcrt.lean` | XL |
| CB7.8 | Lock-domain register: `UncoveredLockDomain`'s completeness theorem re-proved — servers add no lock domain (the SchedContext kind and the per-core replenish queue cover them) — and `SchedLockId` unchanged, stated as a pin | `SeLe4n/Kernel/InformationFlow/FineLockFlow.lean` | S |
| CB7.9 | Tier-2 scenarios — a two-label deployment where bindServer across labels is refused and same-label servers pass; a tick on a hierarchy leaves the other label's observation unchanged; an admitted two-server core where each server meets its deadline over a full hyperperiod — in the information-flow and CBS suites; Tier-3 anchors for CB7 | `tests/SmpInformationFlowSuite.lean`, `tests/SmpCbsSuite.lean`, `scripts/test_tier3_invariant_surface.sh` | M |

**Acceptance**: the SM8.B per-core non-interference capstone elaborates over
the hierarchical tick with `serverMembersUniformlyLabeled` as its only new
hypothesis; `server_receives_budget_within_period` states every hypothesis it
uses, and if `edfTraceFeasible` is among them the register carries its closure
target.

### CB8 — Closure

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| CB8.1 | Specification: §8.12.8 "Hierarchical servers" complete (model, EDF-first order, deadline rules, charging, activation, admission, syscalls, refusals, isolation theorems); §8.14 gains the CBS guarantee with its hypotheses; evidence-index rows under §4 SMP | `docs/spec/SELE4N_SPEC.md`, `docs/CLAIM_EVIDENCE_INDEX.md` | M |
| CB8.2 | Theorem inventory `hierarchicalServerTheorems` with its nodup witnesses, and the census extended so a workstream inventory can be **claimed**: a workstream-keyed manifest beside the SMP phase manifest, read by the generator, so an unclaimed inventory still fails Tier 0 | `SeLe4n/Kernel/SchedContext/HierarchyInventory.lean` (new), `SeLe4n/Kernel/Concurrency/PhaseTheoremManifest.lean`, `scripts/generate_smp_theorem_manifest.py` | M |
| CB8.3 | Hardware spot-check script in the `test_qemu_smp_cbs.sh` shape — skips until SM10.1's image carries the driver and lists its formal stand-ins in the header | `scripts/test_qemu_hierarchical_servers.sh`, `scripts/test_tier4_smp_bootcheck.sh` | S |
| CB8.4 | `CLAUDE.md`/`AGENTS.md`: standing-constraint bullets (the root is EDF-first with kernel-owned deadlines; member affinity fixed; off-core member donation refused; enforcement tick-quantised) and the status row to CLOSED; large-files snapshot refreshed | `CLAUDE.md`, `AGENTS.md` | S |
| CB8.5 | Debt register: the WS-CB rows closed with versions; the §11 follow-ups registered with owners and closure targets; the registry row's span closed | `docs/REGISTERED_DEBT.md` | S |
| CB8.6 | README metrics sync and the GitBook roadmap row; `docs/codebase_map.json` regenerated; `docs/DEVELOPMENT.md` where a tier gained a suite | `README.md`, `docs/gitbook/05-specification-and-roadmap.md`, `docs/codebase_map.json`, `docs/DEVELOPMENT.md` | S |
| CB8.7 | Full validation sweep — `test_full.sh`, `test_rust.sh`, `test_aarch64_cross_build.sh`, `test_docs_sync.sh` — and the CHANGELOG closure entry | `CHANGELOG.md` | S |
| CB8.8 | Hand-off note to SM10: what §8.12.8 adds to SM10.2's documentation sweep and what CB8.3's script adds to SM10.3's hardware validation list | `docs/planning/SMP_RELEASE_CLOSURE_PLAN.md` | T |

**Acceptance**: every row of the phase map reports LANDED with a version; the
plan gate, the naming gate and the docs-sync lane pass on the closing cut.

## 7. Verification strategy

### 7.1 Per PR

* `lake build <Module>` for every touched module (the pre-commit hook), then
  `./scripts/test_smoke.sh`; `./scripts/test_full.sh` whenever a theorem or a
  Tier-3 anchor moves — which is every phase from CB1 on.
* `./scripts/test_aarch64_cross_build.sh` after any change under `rust/`
  (CB0.5, CB6.8, CB6.9).
* Stage before running Tier 0: the plan gate and the naming gate read the
  index.

### 7.2 The equivalence discipline

CB1.2 changes the root order and lands with the theorem that on a state whose
runnable threads all lack deadlines the new selector equals the old; its one
intended fixture refresh is CB1.13, each fixture with its rationale.  From then
on CB3.4 and CB4.3 change live selection and charging, and each lands with the
theorem that on a state whose contexts are all parentless the new definition
equals the CB1 one, with `./scripts/test_tier2_trace.sh` reporting every
`.expected` sha256 unchanged from the post-CB1 baseline.  A fixture that moves
in CB2–CB4 is a defect in the cut, not a fixture to refresh; the intended
moves are CB0.3's (the configure authority gate), CB1.13's (the policy), and
CB5.2's (per-core admission), plus the new fixtures CB4.10, CB6.12 and CB7.9
add.

### 7.3 What each phase proves

| Phase | Proof obligation discharged |
|-------|-----------------------------|
| CB1 | the EDF-first order is strict; the selector is total, optimal, and equal to the old one on deadline-less states; `deadlineWindowConsistent` and `edfCurrentEarliestOnCore` are invariants; inversion is bounded in deadline terms |
| CB2 | `schedHierarchyInvariant` holds of the default and boot states; the Z2 budget engine frames the hierarchy |
| CB3 | `isBetterPath` is a strict order; the hierarchical selector is total, optimal, and equal to CB1's on states without servers |
| CB4 | the tick preserves every structural and CBS invariant over path charging and activation; a server's subtree is bandwidth-bounded; a member is isolated from its siblings |
| CB5 | every hierarchy transition preserves the per-core, CBS, hierarchy and cross-subsystem bundles; every refusal is explicit |
| CB6 | the dispatcher stays total over 38 ids; `ipcInvariantFull` survives every new arm; the Lean and Rust tables agree |
| CB7 | per-core non-interference under uniform labels; the CBS guarantee with stated hypotheses |

### 7.4 What each phase validates

Tier 2: `smp_cbs_suite` (CB0.4, CB1.2, CB3.9, CB4.10, CB7.9), the new
`hierarchical_server_suite` (CB6.12), `NegativeStateSuite` (CB0.3, CB1.4,
CB5.16, CB6.12), `SmpInformationFlowSuite` (CB7.9), the decode and ABI suites
(CB6.1, CB6.10), and every refreshed golden (CB1.13).  Tier 3: anchors per
phase.  Tier 4: CB8.3's script, a skip until SM10.1 produces an image.

## 8. Risk inventory

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| CB1's fixture refresh reaches fourteen suites and the main trace, and a refreshed fixture can hide a defect behind a "policy change" rationale | HIGH | MED | CB0.4's witnesses pin the old order and are inverted deliberately; each refreshed fixture's rationale names the deadline-bearing thread whose position moved; `_eq_flat_of_no_deadlines` shows nothing else moved |
| Converting priority inheritance to deadline inheritance (CB1.6–CB1.7) is larger than estimated across the per-core and cross-core PIP surface | HIGH | MED | The priority boost is kept, not removed, so the change is additive; the donation-preservation family is re-proved by frame where the new field is untouched |
| The CBS guarantee's composition (CB7.7) does not close within its row | HIGH | MED | The algebraic core and EDF optimality land regardless; the composition lands as `edfTraceFeasible` with a registered closure, stated conditionally — the `hBandProgress` precedent |
| CB4.4's re-proof of the tick family is larger than estimated | HIGH | MED | CB4.3's no-servers theorem reduces most cases to the CB1 proof; the fold's frames (CB4.1) are proved once; split CB4.4 by theorem family if it exceeds one PR |
| Selection by scan costs `O(runnable)` per decision where the bucket-first path cost `O(bucket)` | MED | LOW | The lock-wait WCRT theorems are unaffected; the deadline-ordered index is a registered follow-up proven equal to the scan |
| Per-core admission (CB5.2) changes an existing refusal on fixtures that over-admit only in aggregate | MED | LOW | Enumerate the affected fixtures at CB5.2, refresh with rationale; no flat theorem depends on the global sum |
| The path order admits a tie the proofs cannot break (equal deadline, equal priority, distinct servers) | LOW | HIGH | D3 breaks it by `scId`; `isBetterPath_trans` is proved in CB3.3 before anything relies on the order |
| The receive-side refusal of an off-core member donation surfaces as an error to a blameless passive server | LOW | MED | Documented in §3.6 and the spec; the follow-up (per-core server replicas) removes the refusal; a Tier-2 scenario pins the behaviour |
| The workstream inventory cannot be claimed by the SMP-only manifest census | HIGH | LOW | CB8.2 extends the census rather than misfiling the inventory under SM5 |
| Overlap with WS-RR on the scheduler, `API.lean` or the flow tables | MED | MED | §2.3's partition; CB1 and CB5 onward wait for a WS-RR cut touching those files to land |

## 9. Acceptance gate

- [ ] Every CB row LANDED with a version in the phase map.
- [ ] `chooseThreadEffectiveOnCore_eq_flat_of_no_deadlines`,
      `chooseThreadEffectiveOnCore_eq_flat_of_no_servers` and
      `timerTickBudgetOnCore_eq_flat_of_root` elaborate with no hypothesis
      beyond the absence of deadlines, respectively of servers.
- [ ] `deadlineWindowConsistent` and `edfCurrentEarliestOnCore` preserved by
      every per-core transition; no caller-supplied deadline reaches a
      SchedContext.
- [ ] `server_subtree_consumption_bounded` and `member_isolation` stated over
      arbitrary subtrees within `maxServerDepth`.
- [ ] `crossSubsystemInvariant` has thirteen conjuncts and thirteen field-sets.
- [ ] Both dispatch payoffs elaborate over 38 ids; the routing gate reports
      zero exceptions; `SyscallId::COUNT` agrees on both sides.
- [ ] The SM8.B per-core non-interference capstone holds over the hierarchical
      tick under `serverMembersUniformlyLabeled`.
- [ ] `server_receives_budget_within_period` states every hypothesis it uses;
      `pip_bounded_inversion` is stated over deadlines and not vacuous.
- [ ] Every pre-existing `.expected` unchanged except CB0.3's, CB1.13's and
      CB5.2's, each refreshed with rationale; three new fixtures byte-verified.
- [ ] Zero `sorry`, zero axioms; Tier 0, docs-sync, Tier 3 and the cross build
      green on the closing cut.
- [ ] Follow-ups (§11) registered with owners.

## 10. Questions for the maintainer

Decided at planning time: **EDF-first root** (D3, D13–D15), core-homed servers,
label uniformity, the depth and member bounds, off-core donation refused,
leaf-only timeouts.  Each remaining question has a default the plan is written
against; changing one changes the rows named.

| # | Question | Default | If changed |
|---|----------|---------|------------|
| Q1 | Implicit deadlines only (`D = P`), the configure `deadline` argument `0`-only? | Yes (D13) | Constrained deadlines `D < P` need a density-based admission test in CB5.2 and a different guarantee in CB7.7 |
| Q2 | The wake-up rule resets the deadline and leaves the budget alone? | Yes (D14) | Refilling the budget at activation as Abeni–Buttazzo do double-counts against the deferred replenishment; it would need the refill scheme changed in CB1.3 |
| Q3 | Deadline inheritance stays within a member's server (no bandwidth inheritance)? | Yes (D15) | Lifting the server's deadline for a client in another server is bandwidth inheritance; CB4 and CB7.7 change shape |
| Q4 | Selection by scan now, the deadline-ordered index later? | Yes (D2) | An index in CB1 adds a per-core structure with its consistency invariant to every transition in CB1.9 and CB4.4 |
| Q5 | Open after WS-RR, or beside RR6–RR8 under §2.3's partition? | After | CB1 may start once RR7 is quiet in the scheduler; CB5 onward waits for `API.lean` |
| Q6 | Land CB0.3 as the next cut, ahead of the workstream? | Yes | The authority gap stays open until the workstream opens |
| Q7 | Retire `schedContextYieldTo`, or leave it? | Leave | Retiring it removes one proven-but-unwired helper and its cross-subsystem bridge |
| Q8 | Keep `TCB.deadline` as a dead field, or remove it in CB1.4? | Remove | Keeping it means a proof that selection never reads it, renewed at every selector change |

## 11. Cross-references and registered follow-ups

* Debt register: [`../REGISTERED_DEBT.md`](../REGISTERED_DEBT.md) — the
  WS-CB rows in the registry and in table C.
* Neighbours: [`SMP_PER_CORE_SCHEDULER_PLAN.md`](SMP_PER_CORE_SCHEDULER_PLAN.md)
  (SM5, the surface changed and generalised), [`SMP_INFORMATION_FLOW_PLAN.md`](SMP_INFORMATION_FLOW_PLAN.md)
  (SM8, the observer), [`SMP_RELEASE_READINESS_PLAN.md`](SMP_RELEASE_READINESS_PLAN.md)
  (WS-RR, the partition in §2.3), [`SMP_RELEASE_CLOSURE_PLAN.md`](SMP_RELEASE_CLOSURE_PLAN.md)
  (SM10, CB8.8's hand-off).
* Specification: `docs/spec/SELE4N_SPEC.md` §8.12 (the flat model this
  extends), §8.13 (priority inheritance, rewritten by CB1.13), §8.14 (the
  bound CB7.7 replaces for the EDF class).

Follow-ups this plan deliberately leaves for a later workstream, to be
registered by CB8.5 with owners and closure targets: constrained deadlines
(`D < P`, density admission); a per-core deadline-ordered index for selection,
proven equal to the scan; the closure of `edfTraceFeasible` if CB7.7 lands it
externalized; server migration between cores (a whole subtree re-homed,
replenishments included); per-core server replicas so a component may span
cores; bandwidth inheritance for a member blocking a client of another server;
boot-time server trees in `PlatformConfig`; a bucketed `MemberList`; sub-tick
enforcement through a one-shot timer seam.

## 12. Theorem catalogue

| Theorem | Phase | Statement |
|---------|-------|-----------|
| `isBetterCandidate_irrefl`, `_asymm`, `_transitive` (re-proved) | CB1 | the EDF-first order is strict |
| `isBetterCandidate_legacy_class_eq_fp` | CB1 | deadline-less candidates compare as before |
| `chooseThreadEffectiveOnCore_eq_flat_of_no_deadlines` | CB1 | the selector is the old one on deadline-less states |
| `deadlineWindowConsistent` (preservation family) | CB1 | every deadline is `periodStart + period`, kernel-assigned |
| `cbsActivateDeadline_noop_of_fresh` | CB1 | the wake-up rule leaves a fresh window alone |
| `edfCurrentEarliestOnCore` (preservation family) | CB1 | the current thread has the earliest eligible deadline of its domain |
| `pip_bounded_inversion` (restated) | CB1 | inversion bounded in deadline terms |
| `pathLockFootprint_le_maxLockSetSize` | CB2 | a path charge's lock footprint fits the SM3 bound |
| `default_schedHierarchyInvariant`, `bootFromPlatformCheckedWithIdleThreadsFor_schedHierarchyInvariant` | CB2 | the bundle holds of the default and production boot states |
| `pathBudgetEligible_eq_hasSufficientBudget_of_root` | CB3 | eligibility is CB1's on a parentless leaf |
| `isBetterPath_irrefl`, `isBetterPath_asymm`, `isBetterPath_trans` | CB3 | the hierarchical order is strict |
| `isBetterPath_singleton_eq_isBetterCandidate` | CB3 | the order is CB1's on singleton paths |
| `chooseThreadEffectiveOnCore_eq_flat_of_no_servers` | CB3 | the selector is CB1's on states without servers |
| `chooseBestRunnableHierarchical_always_ok`, `chooseBestRunnableHierarchical_optimal` | CB3 | totality and maximality |
| `timerTickBudgetOnCore_eq_flat_of_root` | CB4 | the tick is CB1's on a parentless leaf |
| `chargeSchedPath_charges_every_ancestor` | CB4 | one consumed tick reaches every level |
| `server_subtree_consumption_bounded`, `server_subtree_consumption_bounded_tight` | CB4 | a subtree's consumption is bounded by its server's reservation |
| `member_isolation` | CB4 | a member's consumption is bounded by its own leaf |
| `timerTickOnCore_preserves_perCoreCbsInvariant` (re-proved) | CB4 | the CBS bundle survives path charging |
| `cbsReplenish_server_reschedules_local` | CB4 | a server refill triggers the executing core's reschedule decision |
| `rootAdmission_sound_per_core` | CB5 | admitted roots on a core sum to at most the core |
| `setThreadCpuAffinityWithMigration_rejects_member` | CB5 | the refusal the cross-subsystem bridge needs |
| `member_donation_same_core` | CB5 | a member's donation never migrates replenishments |
| `applyCallDonationOnCore_preserves_schedHierarchyInvariant` (+ reply twins) | CB5 | donation keeps the tree well-formed |
| `dispatchCapabilityOnly_bindServer_idle_refused` | CB6 | the chokepoint covers the new operand |
| `checkedDispatch_bindServer_eq_unchecked_when_allowed` | CB6 | the flow gate is transparent when it permits |
| `dispatchCapabilityOnly_preserves_ipcInvariantFull` (extended) | CB6 | the production payoff over 38 arms |
| `schedContextBindServerChecked_establishes_uniformLabels` | CB7 | the only member-adding transition establishes the label rule |
| `chargeSchedPath_confined_to_label` | CB7 | path charging writes one label |
| `no_cross_label_server_membership` | CB7 | the intra-server channel is closed by construction |
| `cbs_demand_bound`, `edf_selects_earliest_eligible`, `server_receives_budget_within_period` | CB7 | the CBS guarantee: demand bound, EDF optimality, the composed statement with named hypotheses |

## Appendix A — Verification commands

```bash
source ~/.elan/env
lake build SeLe4n.Kernel.Scheduler.Operations.Selection    # CB1, CB3
lake build SeLe4n.Kernel.Scheduler.PriorityInheritance     # CB1.6–CB1.7
lake build SeLe4n.Kernel.SchedContext.Hierarchy            # CB2
lake build SeLe4n.Kernel.Scheduler.Operations.Core         # CB4
lake build SeLe4n.Kernel.API                               # CB6
lake exe smp_cbs_suite                                     # CB0.4, CB1.2, CB3.9, CB4.10, CB7.9
lake exe hierarchical_server_suite                         # CB6.12
./scripts/test_tier2_trace.sh                              # every fixture sha256
./scripts/test_full.sh                                     # Tier 0–3
./scripts/test_aarch64_cross_build.sh                      # after rust/ changes
python3 scripts/check_live_arm_per_core_routing.py         # CB6.4
python3 scripts/check_workstream_plan.py                   # this plan (stage first)
./scripts/test_docs_sync.sh                                # citations, mirrors, map
```
