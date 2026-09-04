# WS-CB — Hierarchical Constant Bandwidth Servers (HCBS)

> **Workstream**: WS-CB (constant-bandwidth server hierarchy)
> **Status**: **PLANNED** — registered at v0.34.49; no sub-task started.  Opens
> after WS-RR closes, or in parallel with RR6–RR8 under the file partition in
> §2.3.  Not a v1.0.0 blocker: SM10 may cut v1.0.0 with this workstream open,
> provided the release notes state that scheduling contexts are flat.
> **Relationship to WS-SM**: extends the SM5.H per-core CBS surface, the SM5.A
> selector and the SM8/SM9 information-flow surface; orthogonal to SM10's image
> work.  It touches no Rust HAL seam and adds no Lean upcall (§3.10).
> **Audited cut**: `v0.34.48`
> **Sub-task count**: 78 across 8 phases (CB0..CB7), each phase numbered in
> the order it is to be implemented
> **Prefix**: `CB`.  The identifier-naming gate derives its family grammar
> from the workstream registry, so the prefix had to be one whose lowercase
> form followed by a digit matches no identifier in the tree: `cb<digit>`
> matches nothing, where `hc<digit>` (the obvious abbreviation) matches two
> hypotheses in the Robin Hood preservation proofs.

## 1. Phase goal

A **Constant Bandwidth Server** (CBS) is a reservation `(Q, P)`: a budget `Q`
replenished every period `P`, whose deadline is postponed by `P` each time the
budget is exhausted, so that the server can never consume more than `Q/P` of
the processor whatever its clients do.  seLe4n already implements this per
thread: a `SchedContext` is a CBS bound to at most one thread, charged one
tick at a time by the per-core timer tick, replenished through the per-core
replenish queue, and admitted against a 100 % utilisation ceiling.

**Hierarchical** CBS (HCBS) lets a reservation contain other reservations.  A
*server* SchedContext holds no thread; it holds members — leaf SchedContexts
bound to threads, or further servers — and its budget is charged whenever any
thread in its subtree runs.  The root scheduler orders the roots of the trees
exactly as it orders threads today (fixed priority, EDF within a band, FIFO on
ties); inside a server the members are ordered by the same rule on their own
parameters; and bandwidth composes: a server's members are admitted against
the server's `Q/P`, and the roots on each core against that core's capacity.
The result is the two-level (and deeper) temporal isolation that Linux's
`SCHED_DEADLINE`-based HCBS gives control groups, expressed in seL4-MCS terms:
a component gets a fraction of a core, its threads share that fraction by
priority, and no thread outside the component can be delayed by anything the
component does beyond the fraction it was admitted for.

This workstream delivers, in order:

1. the model — server fields on `SchedContext`, bounded hierarchy queries,
   and the store-level hierarchy invariant bundle (CB1);
2. hierarchical selection and eligibility, provably identical to today's
   selector on every state with no servers (CB2);
3. hierarchical budget accounting on the per-core tick, with the CBS
   isolation theorems lifted from a single SchedContext to a subtree (CB3);
4. the hierarchy transitions — configure a server, bind and unbind a member —
   plus the hierarchy-aware forms of bind, configure, unbind, affinity,
   priority, donation and retype, each with its preservation surface (CB4);
5. three syscalls wiring those transitions live, on both sides of the ABI,
   with the `ipcInvariantFull` dispatch payoff extended over them (CB5);
6. the information-flow and liveness re-establishment: members of a server
   share a label, so a server's budget is not a cross-label channel, and the
   per-member response-time bound is stated with explicit hypotheses (CB6);
7. closure — specification, evidence index, theorem inventory, fixtures,
   registered follow-ups (CB7).

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
  `isBetterCandidate` on `resolveEffectivePrioDeadline` — higher priority,
  then earlier CBS deadline, then the incumbent — filtered by
  `hasSufficientBudget`, which reads the bound SchedContext's
  `budgetRemaining` alone.
* The per-core tick `timerTickOnCore` (`SeLe4n/Kernel/Scheduler/Operations/Core.lean`)
  drains the core's replenish queue (`processReplenishmentsDueOnCore`, waking
  a bound thread whose budget went from zero to positive), then charges the
  running thread's SchedContext one tick (`timerTickBudgetOnCore`): on
  exhaustion it schedules a replenishment of the consumed amount one period
  out (`scheduleReplenishment`, `replenishOnCore`), postpones the deadline
  (`cbsUpdateDeadline`), re-enqueues the thread, times out the threads the
  SchedContext bounds (`timeoutBlockedThreads`, via `scThreadIndex`) and
  preempts.  An exhausted thread stays queued and is skipped by eligibility.
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
  the SchedContext.  `pipBoost` composes by `Nat.max` on priority only.
* `schedContextYieldTo` is the one hook already labelled "for hierarchical
  scheduling": kernel-internal, capability-free, a budget transfer between
  two SchedContexts.  It is **not** what this workstream builds on — a budget
  transfer is not a hierarchy — and it is left in place.
* The timer seam is a fixed 1000 Hz periodic tick whose only payload is the
  core id (`per_core_timer_tick_isr`, `lean_per_core_timer_tick`).  There is
  no one-shot deadline programming anywhere in the tree.
* `schedContextConfigure` is `.capabilityOnly` under the SchedContext write
  right and applies the requested `priority` and `domain` to the bound TCB
  with **no** caller-MCP check and no domain authority — where
  `setPriorityOp` gates the same write through `validatePriorityAuthority`.
  Recorded as a pre-existing finding in §3.9; CB0.3 closes it before any
  server priority becomes a global one.

### 1.2 The consequence, stated precisely

Every reservation is a leaf.  A component with three threads cannot be given
"20 % of core 1" and left to divide it: each thread needs its own admitted
`(Q, P)`, the three sums are what the component costs whether or not the
threads are all busy, and a thread that blocks leaves its share idle rather
than lending it to a sibling.  There is no object whose exhaustion suspends a
group, no admission relation between a group and its members, and no way to
state — let alone prove — that a component's total consumption is bounded by
one reservation.  `cbs_bandwidth_bounded` bounds one SchedContext; nothing
bounds a set of them jointly.

### 1.3 What this workstream does *not* change

* The root scheduling policy.  Fixed priority with EDF tie-breaking stays;
  an EDF-first root is a registered follow-up (§11), not a phase.
* The tick rate, the HAL, the FFI seam set, `SYSCALL_ABI_VERSION`, or any
  existing syscall's encoding.  New ids are appended (§3.10).
* The 1:1 thread ↔ leaf binding.  A server is a SchedContext with members and
  no thread; a leaf is a SchedContext with at most one thread and no members.
* Flat behaviour.  Every fixture in the tree is byte-identical after CB2 and
  CB3, and each generalising sub-task carries the theorem that says so.

## 2. Scope and sequencing

### 2.1 In scope

* Server SchedContexts with bounded nesting; member leaves and member servers.
* Hierarchical ordering (§3.3), hierarchical charging and replenishment
  (§3.4), hierarchical admission (§3.5), core-homed servers (§3.6).
* Three syscalls: `schedContextConfigureServer`, `schedContextBindServer`,
  `schedContextUnbindServer`; hierarchy-aware forms of the six existing
  operations that read or write a SchedContext's role (§3.8).
* The preservation surface for every touched invariant bundle, the
  `ipcInvariantFull` dispatch payoff over the new arms, per-core
  non-interference under the label-uniformity rule, and the hierarchical
  response-time bound with its hypotheses stated.
* Tier-2 suite with golden fixture, Tier-3 anchors, ABI mirrors and
  conformance tests, specification and evidence-index rows.

### 2.2 Out of scope (registered follow-ups, §11)

Server migration between cores; members homed on several cores (Linux HCBS's
per-CPU server replicas); an EDF-first root; bandwidth inheritance (a boosted
member drawing on the blocker's server); boot-time server trees; a bucketed
member queue; sub-tick enforcement through a one-shot timer.

### 2.3 Ordering constraints and parallelism

* **Phase order is execution order.**  CB1 has no behavioural effect; CB2 and
  CB3 change live paths but only on states that CB4/CB5 cannot yet produce,
  and each carries its flat-equivalence theorem in the same row; CB4 lands
  every transition with its proofs before CB5 makes any of them reachable.
  This is the "a transition goes live only after the proofs that cover it"
  rule applied phase by phase.
* **Overlap with WS-RR.**  CB1–CB3 may run beside RR6–RR8 provided neither
  touches the other's files: WS-RR's remaining phases own the lock primitives
  and the medium sweep; WS-CB owns `SeLe4n/Kernel/SchedContext/**` and the
  scheduler's selection and tick modules.  CB4 onward edits `API.lean` and the
  flow-classification tables and must not overlap a WS-RR cut that does.
* **Within a phase the rows are sequential** unless a row says otherwise.
  A row consumes only lower-numbered rows; the plan gate enforces this.
* **SM10 independence.**  Nothing here needs the image; nothing in SM10 needs
  this.  If SM10.1 lands first, CB5's fixtures are re-cut against the live
  seams and nothing else moves.

## 3. Architectural choices

| # | Decision | Alternative rejected | Why |
|---|----------|----------------------|-----|
| D1 | A server **is** a `SchedContext` with hierarchy fields (`parentServer`, `serverMembers`, `serverCore`); a leaf is one without members | A new `KernelObject` kind | Reuses the capability target, retype tag `6`, lock kind `.schedContext` (level 7), admission arithmetic, replenish queue and every accessor; a new kind touches every exhaustive match in the tree |
| D2 | The root run queue stays a queue of **threads**; the hierarchy is an *ordering and accounting* structure read through the thread's SchedContext chain | A queue of scheduling entities (thread or server) | `RunQueue` is `ThreadId`-specialised with a thousand lines of proof; `currentOnCore` stays a thread; every per-core structural invariant survives unchanged |
| D3 | One order at every level: priority, then CBS deadline, then FIFO among leaves and ascending `scId` among distinct servers (§3.3) | FP-only local scheduling (Linux HCBS) | The existing order already carries EDF within a band, so the uniform rule is *more* faithful to CBS, not less; one strict order means one set of `irrefl`/`asymm` lemmas |
| D4 | A running thread's tick charges its leaf **and every ancestor**; exhaustion at any level makes the subtree ineligible until that level's replenishment lands; timeouts are decided by the leaf only (§3.4) | Charge the leaf and transfer budget upward lazily | Eager charging is what makes the subtree bound a theorem; lazy transfer needs a second accounting state |
| D5 | Servers are **core-homed**; every member's thread has that home core; member affinity changes, and donations of a member leaf to a thread homed elsewhere, are refused (§3.6) | Per-core server replicas | Keeps every hierarchical write inside one core's scheduler slots and the existing tick lock set; replicas are the registered extension |
| D6 | Admission is hierarchical: members ≤ server; roots **per core** ≤ 1000 ‰, replacing the flat global sum (§3.5) | Keep the global sum and add the member rule | The global sum is wrong on a multicore in both directions; per-core root admission is the natural base case of the hierarchy |
| D7 | A server's priority is immutable while it has members; a member leaf's priority is local and set through `schedContextConfigure`; `.tcbSetPriority` on a member thread is refused; PIP boosts the root key only | Re-bucket a subtree on server reconfigure | Re-bucketing a subtree is `O(subtree)` inside a syscall; immutability costs nothing at deployment time.  Bandwidth inheritance is a registered follow-up |
| D8 | Every member of a server carries the server's security label; enforced at `schedContextBindServer` in the flow-checked tier (§3.7) | Permit mixed labels and bound the channel | A shared budget lets one member starve another outright; that is not a channel to bound but a flow to forbid |
| D9 | `maxServerDepth = 3` (root server → server → leaf), `maxServerMembers = 16`; every walk is fuel-bounded by the depth | Unbounded recursion on `parentServer` | Totality with a decidable bound; the path lock footprint (`≤ 3` SchedContext locks + the tick's three) stays within `maxLockSetSize = 8` |
| D10 | Enforcement stays tick-quantised; no new upcall, no HAL change, `SYSCALL_ABI_VERSION` unchanged (ids appended) | A one-shot timer programmed to the next budget event | A new FFI seam drags in the readiness-gate derivation and a new Rust surface for a precision gain the model does not need yet |
| D11 | The boot state has no servers; a hierarchy is built at run time by the root task | Boot-time server trees in `PlatformConfig` | Keeps the boot theorems of WS-RR RR5 untouched; boot-time trees are a follow-up once a deployment asks for them |
| D12 | Transitions land in production modules from day one (unreachable until CB5 wires the arms); theorem-heavy modules are staged and promoted when a production consumer imports them | Stage everything until CB5 | A definition nobody calls changes no behaviour; staging it only defers the partition work |

### 3.1 The model

```lean
-- SeLe4n/Kernel/SchedContext/Types.lean (CB1.1)
structure SchedContext where
  ... existing fields ...
  /-- The server this context is a member of; `none` at the root level. -/
  parentServer  : Option SchedContextId := none
  /-- Members, in FIFO order; a leaf has none.  Duplicate-free by construction. -/
  serverMembers : MemberList := MemberList.empty
  /-- `some c` iff this context is a server, homed on core `c`. -/
  serverCore    : Option CoreId := none
```

`isServer sc := sc.serverCore.isSome`.  A server never binds a thread
(`serverNotThreadBound`); a leaf never has members (`leafHasNoMembers`); a
context is one or the other.  `MemberList` is a `NoDupList SchedContextId`
bounded by `maxServerMembers`, in the style of `Notification.waitingThreads`.

Bounded queries, all total, all fuel-bounded by `maxServerDepth`:
`parentChain? st scId` (the ancestors, root last; `none` on a dangling
parent or a chain longer than the bound), `rootOf?`, `depthOf?`,
`isAncestorOf`, `schedPath? st scId : Option (List SchedKey)` where
`SchedKey := Priority × Deadline × SchedContextId` read root-first.

### 3.2 The hierarchy invariant bundle (`schedHierarchyInvariant`, CB1.6)

| Conjunct | Meaning |
|----------|---------|
| `hierarchyBidirectional` | `child.parentServer = some s` ↔ `child ∈ s.serverMembers` |
| `hierarchyDepthBounded` | every context's `parentChain?` is `some` with length `≤ maxServerDepth` — which is also acyclicity |
| `serverRoleExclusive` | `serverNotThreadBound ∧ leafHasNoMembers` for every context |
| `serverCoreConsistent` | a member server's `serverCore` equals its parent's; a member leaf's bound thread has `determineTargetCore = serverCore` |
| `serverDomainConsistent` | `member.domain = server.domain` (the AE3-A rule lifted one level) |
| `serverMembersBounded` | `serverMembers.length ≤ maxServerMembers` |
| `hierarchicalAdmissionHolds` | §3.5's two inequalities, for every server and every core |
| `memberBucketConsistent` | a member leaf's bound thread has `tcb.priority = rootPriority` — the AK2-B mirror pointed at the root of the chain |

The bundle joins `crossSubsystemInvariant` as its thirteenth conjunct **with**
a `_fields` entry, because the register already records what happens when a
conjunct is appended without one.

### 3.3 The scheduling order

A runnable thread `t` bound to leaf `sc` has the key path
`schedPath? st sc = some [k_root, …, k_leaf]`.  `isBetterPath` compares two
paths lexicographically: at each position, `isBetterCandidate` on
`(priority, deadline)`; on a tie between **distinct** servers the lower
`scId` wins (deterministic, and transient — CBS postpones a deadline at every
exhaustion, so two servers tie only when replenished in the same tick); on a
tie between two leaves the incumbent is retained, which is today's FIFO.  For
a thread whose leaf has no parent the path is the singleton `k_leaf` and
`isBetterPath` **is** `isBetterCandidate` — the flat-equivalence theorem CB2.4
carries.

The bucket a member thread sits in is its **root** priority
(`memberBucketPriority`), so the bucket-first scan still finds the winning
band in `O(k)`; the path comparison runs only inside that band.  PIP composes
as today: `pipBoost` lifts the root key by `Nat.max` and the bucket with it.

Eligibility is `pathBudgetEligible`: every context on the path has
`budgetRemaining > 0`.  On a parentless leaf it is `hasSufficientBudget`.

### 3.4 Charging and replenishment

```
timerTickBudgetOnCore, bound arm (CB3.3):
  path   := leaf :: ancestors                      -- CB1.4, fuel-bounded
  for each sc in path, in leaf-to-root order:
    consumeBudget sc 1
    if exhausted:
      scheduleReplenishment sc now consumedAmount  -- into sc's own list
      cbsUpdateDeadline sc now true                -- deadline := now + period
      replenishOnCore c sc.scId (now + period)     -- core c's queue
  if leaf exhausted: timeoutBlockedThreads leaf     -- leaf only (D4)
  preempted := any level exhausted
  re-enqueue the running thread at its root bucket
```

Only consumed ticks charge ancestors: a yield that surrenders the leaf's
remaining budget surrenders nothing above it.  A server's replenishment is
drained by the same `processReplenishmentsDueOnCore`; its wake decision
(`replenishWakeDecision`, CB3.5) is "reschedule this core" rather than "wake
thread `t`", because the members never left the queue.  Since the server is
homed on the executing core, that decision is the existing local-wake bit and
no SGI is needed.

### 3.5 Admission

Utilisation stays `Bandwidth.utilization` (ceiling per-mille).  Two
inequalities, both decidable, both checked by every transition that changes a
term of either sum:

* for every server `s`:  Σ over `m ∈ s.serverMembers` of `U(m)` ≤ `U(s)`;
* for every core `c`:  Σ over root-level contexts *active on `c`* of `U` ≤ 1000,
  where a root server is active on its `serverCore` and a root leaf is active
  on its bound thread's home core (an unbound root leaf consumes nothing and
  is admitted when `schedContextBind` gives it a thread).

The RPi5 canonical deployment's `admissibleUtilisation = 750` remains a
liveness-side assumption on top of the kernel's 1000 ‰ ceiling.

### 3.6 Core-homed servers

`schedContextConfigureServer` fixes `serverCore`, refusing a core the machine
does not declare (`MachineState.declaredCoreCount`, the RR5 rule).  Binding a
member checks the core (D5); `.tcbSetAffinity` on a member thread and
`donateSchedContext` of a member leaf to a thread homed elsewhere both refuse
with `.illegalState` **before** any state is committed — the `Kernel` monad
discards the rendezvous on the call path, and the receive-side arm returns the
error to the receiver.  A member SchedContext donated to a same-core passive
server keeps its position in the tree, so the passive server runs within the
client's reservation, which is the semantics HCBS wants.

### 3.7 Information flow

`schedContextBindServer` is `.policyGated`: the checked arm requires
`securityFlowsTo(childLabel, serverLabel) ∧ securityFlowsTo(serverLabel, childLabel)`
under the installed labeling context, so every member of a server carries a
label equivalent to the server's (`serverMembersUniformlyLabeled`, CB6.1).
With that, a tick that writes a member's ancestors writes only same-label
objects and SM8.B's per-core non-interference lift goes through unchanged in
shape (CB6.2); the projection erases the three new fields as structural
scheduling plumbing, the class `boundThread` already belongs to (CB1.9).

### 3.8 The syscall surface

| Id | Syscall | Capability | Registers | Effect |
|----|---------|------------|-----------|--------|
| 35 | `schedContextConfigureServer` | SchedContext, `.write` | `MR0` = core | leaf with no thread and no parent → server on `core`; root admission on `core` |
| 36 | `schedContextBindServer` | **server** SchedContext, `.write` | `MR0` = CPtr of the child, resolved in the caller's CSpace with `.write` (the `tcbBindNotification` pattern) | link child under server: role, acyclicity, depth, core, domain, admission, label checks; re-bucket the child's thread |
| 37 | `schedContextUnbindServer` | **child** SchedContext, `.write` | none | unlink; the child becomes a root and is admitted on its core; a child server with members is refused |

Hierarchy-aware existing operations: `schedContextBind` (refuses a server;
checks the ancestor's core; buckets at the root priority; admits a root leaf
on the thread's core), `schedContextConfigure` (priority immutable on a
populated server; member admission against the parent; root admission per
core), `schedContextUnbind` (unchanged effect, restated invariants),
`.tcbSetAffinity` and `.tcbSetPriority` (refused on members),
`donateSchedContext` (§3.6), `lifecycleRetype` (a populated server is
refused; a member leaf is unlinked before destruction).

Every refusal is an explicit `KernelError` arm; none is a fault.  All three
new ids are `.unit`-shaped returns and non-blocking, so
`capFaultReceivePhase?` answers `none` for each.

### 3.9 Pre-existing finding this workstream closes first

`schedContextConfigure` writes `priority` and `domain` into the bound TCB
under the SchedContext write right alone.  A thread holding such a
capability escalates its own scheduling priority past its
`maxControlledPriority` — the very bound `setPriorityOp` enforces — and moves
itself into any of the sixteen domains.  Budgets and admission bound the
damage (a runnable thread cannot exceed its `Q/P`) but not the inversion: a
low-MCP thread with a 5 % reservation preempts every thread below 255 for
that 5 %.  Under HCBS a server priority competes for a whole core, so the gap
must close before servers exist.  CB0.3 gates the priority through
`validatePriorityAuthority` against the **caller's** MCP and refuses a domain
change on a SchedContext that is bound or a member (`.illegalAuthority`),
keeping the domain field settable only on an unbound, parentless leaf.  This
is reported to the maintainer separately as a vulnerability finding; the plan
records the remediation.

### 3.10 What stays fixed

No new `@[export]`, so `LEAN_READY_GATED_SEAMS` and the readiness derivation
are untouched; no `extern`, so the kernel-entry export gate's requirement set
is untouched.  `SYSCALL_ABI_VERSION` stays `3`: ids `0..34` keep their
encodings, the conformance suite pins that, and `SyscallId::COUNT` moves to
`38` on both sides with the existing mirror tests holding them equal.

## 4. Dependencies

* **WS-SM SM5.A/SM5.D/SM5.H** (landed): the per-core selector, tick and CBS
  surface this workstream generalises.
* **WS-SM SM8.A–D** (landed): the per-core observer and the write-set
  discipline CB1.9 and CB6 extend.
* **WS-RR RR5** (landed): the declared-core discipline CB4.1 reuses for a
  server's core, and the boot theorems CB1.7 keeps intact.
* **WS-RR RR6–RR8**: no dependency either way; §2.3 states the file partition.
* **SM10**: none.  CB5's fixtures are re-cut if the image lands first.

## 5. Phase map

| Phase | Scope (one line) | Subs | Est |
|-------|------------------|------|-----|
| CB0 | Registration, baseline verification, the pre-existing configure-authority gap, flat-behaviour witnesses | 5 | S–M |
| CB1 | Model: hierarchy fields, bounded queries, per-object and store-level invariants, boot and observer erasure — inert | 10 | M–L |
| CB2 | Hierarchical selection and eligibility, provably identical on flat states | 9 | L |
| CB3 | Hierarchical charging and replenishment on the per-core tick; the subtree isolation theorems | 9 | L–XL |
| CB4 | Hierarchy transitions and the hierarchy-aware forms of the existing operations, each with its preservation surface | 16 | XL |
| CB5 | The three syscalls on both sides of the ABI, flow classification, dispatch payoff, end-to-end fixtures | 12 | L |
| CB6 | Information-flow and liveness re-establishment | 9 | L |
| CB7 | Closure: specification, evidence, inventory, hardware spot-check script, hand-off | 8 | M |

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
| CB0.3 | Close §3.9: `schedContextConfigure` takes the caller, gates `priority` through `validatePriorityAuthority` against the caller's MCP, and refuses a `domain` change on a bound SchedContext with `.illegalAuthority`; theorems `schedContextConfigure_priority_within_caller_mcp`, `schedContextConfigure_domain_fixed_of_bound`; negative-suite pins; trace-fixture refresh with rationale | `SeLe4n/Kernel/SchedContext/Operations.lean`, `SeLe4n/Kernel/API.lean`, `tests/NegativeStateSuite.lean`, `tests/fixtures/main_trace_smoke.expected` | M |
| CB0.4 | Flat-behaviour witnesses landed **first**: Tier-2 pins of today's selection order among equal-priority SchedContext threads, the exhaustion re-enqueue, and the replenish wake — the scenarios CB2 and CB3 must keep byte-identical | `tests/SmpCbsSuite.lean` | S |
| CB0.5 | Stale-comment sweep on files this workstream edits: the Rust `SyscallId` header's variant count and Lean line references, the `dispatchCapabilityOnly` docstring's arm count, the evidence index's staged-module count | `rust/sele4n-types/src/syscall.rs`, `SeLe4n/Kernel/API.lean`, `docs/CLAIM_EVIDENCE_INDEX.md` | S |

**Acceptance**: CB0.3's two theorems elaborate; `lake exe smp_cbs_suite` runs
the CB0.4 witnesses green; Tier 0 and the docs-sync lane pass.

### CB1 — The model, inert

Every definition here is unreachable from a live path until CB5; the only
behavioural change is that a boot SchedContext must be a parentless leaf,
which every existing fixture already is.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| CB1.1 | Add `parentServer`, `serverMembers`, `serverCore` to `SchedContext` with defaults (§3.1); `MemberList` as a bounded `NoDupList SchedContextId`; `isServer`, `isLeaf`; extend the manual `BEq` instance | `SeLe4n/Kernel/SchedContext/Types.lean` | M |
| CB1.2 | Sweep every constructor-arity destructuring the build now rejects — `schedContextReferencesReservedIdleSlot`, `bootSafeSchedContextCheck` and siblings — classifying the new fields: a member or parent id naming a reserved idle object is refused, and a boot SchedContext is a parentless leaf | `SeLe4n/Platform/Boot.lean`, whatever else the build names | S |
| CB1.3 | Constants `maxServerDepth := 3`, `maxServerMembers := 16`, with `pathLockFootprint_le_maxLockSetSize` (the depth plus the tick's three locks stays within `maxLockSetSize`) and a docstring recording the cost of one path charge | `SeLe4n/Kernel/SchedContext/Hierarchy.lean` (new) | S |
| CB1.4 | Fuel-bounded hierarchy queries `parentChain?`, `rootOf?`, `depthOf?`, `isAncestorOf`, `schedPath?`, `rootPriority?` with congruence over `getSchedContext?` and the `_of_root` simplifications (a parentless leaf's chain is empty, its path the singleton) | `SeLe4n/Kernel/SchedContext/Hierarchy.lean` | M |
| CB1.5 | Per-object well-formedness: `SchedContext.wellFormed` gains `serverMembersBounded` and `serverRoleExclusive`; `schedContextWellFormed` follows; the sixteen Z2 preservation theorems re-proved (every budget operation frames the new fields) | `SeLe4n/Kernel/SchedContext/Types.lean`, `SeLe4n/Kernel/SchedContext/Invariant/Defs.lean` | M |
| CB1.6 | The store-level bundle `schedHierarchyInvariant` (§3.2), decidable where the arithmetic allows, with projections and `default_schedHierarchyInvariant` | `SeLe4n/Kernel/SchedContext/Invariant/HierarchyDefs.lean` (new) | M |
| CB1.7 | Boot: `bootSafeSchedContextCheck` requires a parentless, memberless leaf; `bootFromPlatformCheckedWithIdleThreadsFor_schedHierarchyInvariant` on the production boot path; `SchedContext.empty` and `mkChecked` produce leaves (consumes CB1.6) | `SeLe4n/Platform/Boot.lean`, `SeLe4n/Kernel/SchedContext/Types.lean` | M |
| CB1.8 | Equality pins: the `BEq` instance reads every field (a witness that two contexts differing only in `parentServer` compare unequal, the SM3.A audit-pass lesson) and a `SchedContext.ext` lemma over the full field list | `SeLe4n/Kernel/SchedContext/Types.lean` | S |
| CB1.9 | Observer projection: erase the three fields in `projectKernelObject` and the per-core observer as structural scheduling plumbing (the `boundThread` class); re-prove the projection lemmas the erasure touches; `schedContextWriteSet` stays the singleton, since a member's ancestors share its core | `SeLe4n/Kernel/InformationFlow/Projection.lean`, `SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean` | M |
| CB1.10 | Freeze mirror: `FrozenKernelObject.schedContext` carries the record verbatim, so the freeze/thaw proofs and the lock projection re-elaborate over the new fields; Tier-3 anchors for CB1; `docs/codebase_map.json` regenerated; spec §8.12.8 skeleton stating "model landed, inert" | `SeLe4n/Model/FrozenState.lean`, `SeLe4n/Model/FreezeProofs.lean`, `scripts/test_tier3_invariant_surface.sh`, `docs/spec/SELE4N_SPEC.md` | S |

**Acceptance**: `lake build` of every touched module; `crossSubsystemInvariant`
is **not** yet extended (that is CB4.13, after the refusals it depends on);
every fixture byte-identical.

### CB2 — Hierarchical selection

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| CB2.1 | `pathBudgetEligible st tcb` — every context on the path has positive budget — with `pathBudgetEligible_eq_hasSufficientBudget_of_root` (consumes CB1.4) | `SeLe4n/Kernel/Scheduler/Operations/Selection.lean` | S |
| CB2.2 | `resolveEffectiveSchedPath st tcb : List SchedKey` and `memberBucketPriority`; `resolveEffectiveSchedPath_root_eq_resolveEffectivePrioDeadline`; the PIP boost applied to the root key | `SeLe4n/Kernel/Scheduler/Operations/Selection.lean` | M |
| CB2.3 | `isBetterPath` (§3.3) with `isBetterPath_irrefl`, `_asymm`, `_trans` and `isBetterPath_singleton_eq_isBetterCandidate` | `SeLe4n/Kernel/Scheduler/Operations/Selection.lean` | M |
| CB2.4 | `chooseBestInBucketHierarchical` replacing the effective selector inside `chooseThreadEffectiveOnCore`, **in the same row as** `chooseThreadEffectiveOnCore_eq_flat_of_no_servers` — on a state whose contexts are all parentless the new selector is the old one (consumes CB2.1–CB2.3) | `SeLe4n/Kernel/Scheduler/Operations/Selection.lean` | L |
| CB2.5 | Totality and optimality restated: `chooseBestRunnableHierarchical_always_ok` and `_optimal` (the selection is `isBetterPath`-maximal among eligible in-domain candidates), the skip-corrupt-entry contract kept | `SeLe4n/Kernel/Scheduler/Operations/PerCoreChooseThread.lean` | L |
| CB2.6 | `candidateOutranksCurrentOnCore` in path form, so `handleRescheduleSgiOnCore` decides in the selector's own order; `_of_edf_earlier` restated | `SeLe4n/Kernel/Scheduler/Operations/Selection.lean` | M |
| CB2.7 | Bucket rule: `effectiveBucketPriorityHierarchical` = root priority lifted by the boost; `schedulerPriorityMatchOnCore` and `effectiveParamsMatchRunQueueOnCore` restated through it, with the flat corollaries under `boundThreadPriorityConsistent` | `SeLe4n/Kernel/Scheduler/Invariant/PerCore.lean`, `SeLe4n/Kernel/Scheduler/Invariant.lean` | L |
| CB2.8 | Re-prove the selection-dependent suite: `chooseThreadOnCore_ok_of_runnableTCBs`, the idle keystone (untouched — idle threads are unbound), and the `schedulerInvariantStrong_smp` preservation family for `scheduleEffectiveOnCore` and `handleRescheduleSgiOnCore` | `SeLe4n/Kernel/Scheduler/Invariant/PerCoreInvariantSuite.lean`, `SeLe4n/Kernel/Scheduler/Operations/PerCoreWake.lean` | L |
| CB2.9 | Fixtures byte-identical (every `.expected`); Tier-2 scenarios on hand-built hierarchies via `StateBuilder.withServerHierarchy` — a server outranks a leaf by root priority, two servers tie-broken by deadline then `scId`, member order local; Tier-3 anchors | `tests/SmpCbsSuite.lean`, `SeLe4n/Testing/StateBuilder.lean` | M |

**Acceptance**: `chooseThreadEffectiveOnCore_eq_flat_of_no_servers` elaborates
without hypotheses beyond parentlessness; `test_tier2_trace.sh` reports every
sha256 unchanged.

### CB3 — Hierarchical charging

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| CB3.1 | `chargeSchedPath st c path now : SystemState × Bool` — the §3.4 fold — with frames: `getTcb?` unchanged, every run queue unchanged, only core `c`'s replenish queue and the path's contexts written | `SeLe4n/Kernel/Scheduler/Operations/Core.lean` | M |
| CB3.2 | Generalise the three home readers to servers: `schedContextReplenishHome` (a server's home is `serverCore`), `replenishQueueAffinityConsistentOnCore` and `replenishQueueEntriesBoundOnCore` (an entry's context is bound **or** a server homed on `c`), each with its `_of_leaf` equivalence | `SeLe4n/Kernel/SchedContext/Operations.lean`, `SeLe4n/Kernel/SchedContext/ReplenishAffinity.lean`, `SeLe4n/Kernel/SchedContext/BindingAffinity.lean` | M |
| CB3.3 | `timerTickBudgetOnCore`'s bound arm charges through `chargeSchedPath`, leaf-only timeouts, preemption iff any level exhausted, **in the same row as** `timerTickBudgetOnCore_eq_flat_of_root` (a parentless leaf runs the prior body) (consumes CB3.1, CB3.2) | `SeLe4n/Kernel/Scheduler/Operations/Core.lean` | L |
| CB3.4 | Re-prove the tick preservation family over the new body — the ten `timerTickOnCore_preserves_*` structural theorems, `allThreadsTimeSlicePositive`, `schedulerInvariantStructuralRegNodup_perCore`, and the CBS side (`replenishQueueValidOnCore`, `replenishmentPipelineOrderOnCore`, `perCoreCbsInvariant`) — mostly by CB3.3's reduction plus CB3.1's frames | `SeLe4n/Kernel/Scheduler/Operations/PerCoreTimerTick.lean`, `PerCoreTickCbsPreservation.lean`, `PerCoreTickCbsAffinity.lean`, `SeLe4n/Kernel/Scheduler/Invariant/PerCoreInvariantSuite.lean` | XL |
| CB3.5 | Server replenishment: `replenishWakeDecision` (`.wakeThread`, `.rescheduleCore`, `.none`) replacing `replenishWakeTarget`; `processOneReplenishmentOnCore` raises the local-wake bit on `.rescheduleCore`; `cbsReplenish_server_reschedules_local`, `replenishWakeDecision_leaf_eq_target` | `SeLe4n/Kernel/Scheduler/Operations/Core.lean`, `SeLe4n/Kernel/Scheduler/Operations/PerCoreTimerTick.lean` | M |
| CB3.6 | Lock footprint: `chargeSchedPath_writes_within_timerTickOnCoreLockSet` (the same three domains) and the model-level `chargeSchedPathLockSet` with `_pairwise_le` and `_size_le_maxLockSetSize` (consumes CB1.3) | `SeLe4n/Kernel/Scheduler/Operations/PerCoreTimerTick.lean` | M |
| CB3.7 | `schedHierarchyInvariant` preserved by the tick, the drain and `replenishOnCore` — budgets and deadlines move, the hierarchy fields are framed | `SeLe4n/Kernel/Scheduler/Operations/PerCoreTickCbsPreservation.lean` | M |
| CB3.8 | Isolation theorems: `chargeSchedPath_charges_every_ancestor`; `server_subtree_consumption_bounded` (a server's subtree consumes at most `maxReplenishments × server.budget` over any window, lifting `cbs_bandwidth_bounded`) and its tight form under `cbsWindowReplenishmentsBounded`; `member_isolation` (a member's consumption is bounded by its own leaf whatever its siblings do) | `SeLe4n/Kernel/SchedContext/Invariant/HierarchyDefs.lean` | L |
| CB3.9 | Tier-2 scenarios: two members exhaust their server and both stop; the server's replenishment resumes both; a nested server exhausts under a live parent; golden fixture `tests/fixtures/hierarchical_server_tick.expected` with its sha256 and README row; Tier-3 anchors | `tests/SmpCbsSuite.lean`, `tests/fixtures/` | M |

**Acceptance**: `timerTickOnCore_preserves_perCoreCbsInvariant` and the
structural family elaborate over the new body; `server_subtree_consumption_bounded`
is stated over an arbitrary subtree, not a fixed depth; every pre-existing
fixture byte-identical.

### CB4 — Hierarchy transitions, proven before they are reachable

Every transition here is a production definition with no caller until CB5.
The refusals in CB4.8 and CB4.9 land before CB4.13 because the cross-subsystem
bridges for affinity and priority are false without them.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| CB4.1 | `schedContextConfigureServer vScId core`: refuses a bound thread, an existing parent, existing members on another core, and an undeclared core (`MachineState.declaredCoreCount`, the RR5 rule); sets `serverCore`; root admission on `core` (consumes CB1.4, CB1.6) | `SeLe4n/Kernel/SchedContext/HierarchyOperations.lean` (new) | M |
| CB4.2 | Per-core root admission: `collectRootSchedContextsOnCore`, `checkRootAdmissionOnCore`, `checkMemberAdmission`; `schedContextConfigure` and `schedContextBind` route through them — a root leaf is admitted on its thread's core at bind, `.resourceExhausted` becoming a bind refusal; `rootAdmission_sound_per_core`; negative-suite and trace-fixture updates with rationale | `SeLe4n/Kernel/SchedContext/Operations.lean`, `SeLe4n/Kernel/SchedContext/Budget.lean` | L |
| CB4.3 | `schedContextBindServer vServer vChild`: the §3.8 check list (server role, parentless child, `isAncestorOf` refusal, depth, core, domain, an empty child server, member admission), the bidirectional link, re-bucket of the child's bound thread at the root priority (consumes CB4.2) | `SeLe4n/Kernel/SchedContext/HierarchyOperations.lean` | L |
| CB4.4 | `schedContextUnbindServer vChild`: a child server with members refused; unlink; re-bucket at the child's own priority; root admission on the child's core (consumes CB4.2) | `SeLe4n/Kernel/SchedContext/HierarchyOperations.lean` | M |
| CB4.5 | Hierarchy-aware `schedContextBind`: refuses a server target; checks the thread's home core against the ancestor's `serverCore`; buckets through `memberBucketPriority`; `scThreadIndex` unchanged (consumes CB2.2) | `SeLe4n/Kernel/SchedContext/Operations.lean` | M |
| CB4.6 | Hierarchy-aware `schedContextConfigure`: a priority change on a populated server refused (`.illegalState`); a member leaf's priority is local, so `schedContextConfigureBoundPropagate` leaves `tcb.priority` at the root priority; member admission against the parent, root admission per core (consumes CB4.2) | `SeLe4n/Kernel/SchedContext/Operations.lean` | M |
| CB4.7 | `schedContextUnbind` on a member leaf: today's effect plus `memberBucketConsistent` maintenance (the thread leaves at its legacy priority); `schedContextUnbindOnCore` follows | `SeLe4n/Kernel/SchedContext/Operations.lean`, `SeLe4n/Kernel/SchedContext/OperationsPerCore.lean` | S |
| CB4.8 | `setThreadCpuAffinityWithMigration` refuses a member thread with `.illegalState` before any write; `setThreadCpuAffinityWithMigration_rejects_member` | `SeLe4n/Kernel/Scheduler/Operations/Core.lean` | S |
| CB4.9 | `setPriorityOp` refuses a member thread (`.illegalState`); `setMCPriorityOp` unchanged; `setPriorityOp_rejects_member` | `SeLe4n/Kernel/SchedContext/PriorityManagement.lean` | S |
| CB4.10 | Donation: `donateSchedContext` refuses a member leaf whose `serverCore` differs from the donee's home core (`.illegalState`); the replenish migration inside the three donation composites is a definitional no-op for members (`member_donation_same_core`); `applyCallDonationOnCore_preserves_schedHierarchyInvariant` and its reply and replyRecv twins | `SeLe4n/Kernel/IPC/Operations/Endpoint.lean`, `SeLe4n/Kernel/IPC/Operations/Donation/Primitives.lean` | M |
| CB4.11 | Lifecycle: `lifecyclePreRetypeCleanup` refuses to retype a populated server (`.illegalState`) and unlinks a member leaf before destruction; `hierarchyBidirectional` preserved under retype | `SeLe4n/Kernel/Lifecycle/Operations/Cleanup.lean`, `SeLe4n/Kernel/Lifecycle/Operations/RetypeWrappers.lean` | M |
| CB4.12 | Preservation surface for CB4.1–CB4.11: each transition preserves `schedHierarchyInvariant`, `perCoreCbsInvariant`, `runQueueOnCoreWellFormed`, `queueCurrentConsistentOnCore`, the hierarchical `effectiveParamsMatchRunQueueOnCore`, objects `invExt`, `schedContextStoreConsistent`, `schedContextNotDualBound`, `scThreadIndexConsistent` | `SeLe4n/Kernel/SchedContext/Invariant/HierarchyPreservation.lean` (new; staged until the CB5 promotion cut) | XL |
| CB4.13 | `crossSubsystemInvariant` gains `schedHierarchyInvariant` as its thirteenth conjunct **with** `schedHierarchyInvariant_fields`, the pairwise disjointness analysis redone over the full list, the projections, and every existing operation's bridge extended (consumes CB4.8, CB4.9, CB4.12) | `SeLe4n/Kernel/CrossSubsystem.lean` | L |
| CB4.14 | Lock sets for the three transitions — `schedContextConfigureServerLockSet`, `schedContextBindServerLockSet`, `schedContextUnbindServerLockSet` — with `_write_only`, `_pairwise_le`, `_size_le_maxLockSetSize` (consumes CB1.3) | `SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean` | M |
| CB4.15 | Frozen twins `frozenSchedContextConfigureServer`, `frozenSchedContextBindServer`, `frozenSchedContextUnbindServer` with their agreement theorems against the live transitions (the coverage-table rows follow once the ids exist, in CB5) | `SeLe4n/Kernel/FrozenOps/Operations.lean`, `SeLe4n/Kernel/FrozenOps/Agreement.lean` | M |
| CB4.16 | Tier-2 negative pins for every refusal arm of CB4.1–CB4.11 through a thin-dispatcher sub-helper `runHierarchyRefusalChecks`; Tier-3 anchors for the CB4 surface | `tests/NegativeStateSuite.lean`, `scripts/test_tier3_invariant_surface.sh` | M |

**Acceptance**: every CB4 transition has its row in CB4.12's surface;
`crossSubsystemInvariant` has thirteen conjuncts **and** thirteen field-sets;
no live path reaches any of them yet (the dispatcher's wildcard-unreachable
theorems are unchanged until CB5).

### CB5 — The syscalls, live

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| CB5.1 | `SyscallId` variants `.schedContextConfigureServer` (35), `.schedContextBindServer` (36), `.schedContextUnbindServer` (37): `toNat`, `ofNat?`, `count := 38`, `ToString`; the `DecodingSuite` boundary moves to 37/38 | `SeLe4n/Model/Object/Types.lean`, `tests/DecodingSuite.lean` | S |
| CB5.2 | The total-table sweep the new arms force before anything elaborates: `syscallRequiredRight` (`.write` ×3), `syscallChecksTargetFirst`, `syscallDelegates`, `syscallReturnShape` (`.unit` ×3), `enforcementBoundary` + `syscallIdToEnforcementName` (`.policyGated "schedContextBindServerChecked"`, `.capabilityOnly` ×2), `syscallIdToEnforcementNamePerCore`, `contentFlowClass`, `syscallRecordsDeclassification`, `refusalSeamClass`, `frozenOpCoverage` + `frozenOpCoverage_count`, `frozenOpUncheckedReason`, `lockSetForSyscall` (`none` ×3, `lockSetForSyscall_undeclared_none` restated), `capFaultReceivePhase?` (`none` ×3) (consumes CB4.15, CB5.1) | `SeLe4n/Kernel/API.lean`, `SeLe4n/Kernel/Architecture/SyscallReturn.lean`, `SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean`, `SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean`, `SeLe4n/Kernel/InformationFlow/TaintPropagation.lean`, `SeLe4n/Kernel/InformationFlow/RefusalRecord.lean`, `SeLe4n/Kernel/FrozenOps/Operations.lean`, `SeLe4n/Kernel/FrozenOps/Agreement.lean`, `SeLe4n/Kernel/Concurrency/Locks/LockSetForSyscall.lean`, `SeLe4n/Platform/FFI.lean` | M |
| CB5.3 | Arg structures and decoders: `SchedContextConfigureServerArgs` (`core`) with a checked decoder refusing `core ≥ numCores` (the declared-count check stays in the transition, where the machine state is), `SchedContextBindServerArgs` (`childCPtr`), `SchedContextUnbindServerArgs`; encoders, `_roundtrip` and `_error_iff` theorems | `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` | M |
| CB5.4 | `dispatchCapabilityOnly` arms: configureServer (cap target = the SchedContext), bindServer (cap = the server; the child CPtr resolved through the caller's CSpace with `.write` by `syscallLookupCap`, the `tcbBindNotification` pattern), unbindServer (cap = the child) — each through an `…OnCore` form so the Tier-1 per-core routing gate passes; the wildcard-unreachable proofs restated (consumes CB5.2, CB5.3) | `SeLe4n/Kernel/API.lean` | M |
| CB5.5 | Idle-reservation chokepoint: the child CPtr resolves through `syscallResolveCap`, which refuses a reserved idle object; the core operand is not an object id; `dispatchCapabilityOnly_bindServer_idle_refused` | `SeLe4n/Kernel/API.lean` | S |
| CB5.6 | Checked tier: `schedContextBindServerChecked` (the §3.7 label test, `securityFlowsTo` both ways on `objectLabelOf`), the `dispatchWithCapChecked` arms, `checkedDispatch_bindServer_eq_unchecked_when_allowed` and the two `checkedDispatch_*_eq_unchecked` equivalences for the capability-only arms; `enforcementBoundary_is_complete` re-proved (consumes CB5.4) | `SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean`, `SeLe4n/Kernel/API.lean` | M |
| CB5.7 | Dispatch payoff: per-arm `…_preserves_ipcInvariantFull` for the three arms (frames on every conjunct — no IPC state moves), extending `dispatchCapabilityOnly_preserves_ipcInvariantFull` (production) and the staged `dispatchWithCap_preserves_ipcInvariantFull` / `dispatchWithCapChecked_preserves_ipcInvariantFull`; `capabilityDispatchQuiescence` needs no new field, stated as a theorem (consumes CB5.6) | `SeLe4n/Kernel/IPC/Invariant/DispatchArmPreservation.lean`, `SeLe4n/Kernel/IPC/Invariant/DispatchPayoff.lean`, `SeLe4n/Kernel/API.lean` | L |
| CB5.8 | Rust mirrors: `sele4n-types` variants, `COUNT = 38`, `required_right`, tests; the HAL's hand-mirror enum, `from_u32`, `min_inline_args` (1, 1, 0) and the two mirror tests; `sele4n-abi` argument structs; `sele4n-sys` wrappers; conformance cases and the wrapper-length sweep; `test_aarch64_cross_build.sh` green (consumes CB5.1, CB5.3) | `rust/sele4n-types/src/syscall.rs`, `rust/sele4n-hal/src/svc_dispatch.rs`, `rust/sele4n-abi/src/args/sched_context.rs`, `rust/sele4n-sys/src/sched_context.rs`, `rust/sele4n-abi/tests/conformance.rs` | M |
| CB5.9 | ABI version decision recorded on all three sides: `SYSCALL_ABI_VERSION` stays `3` (ids appended, `0..34` unchanged), with a conformance pin that every prior discriminant encodes as before | `rust/sele4n-abi/tests/conformance.rs`, `SeLe4n/Kernel/Architecture/SyscallReturn.lean` | S |
| CB5.10 | Return-shape and dispatch pins: `SyscallReturnAbiSuite` cases for the three `.unit` frames; `SyscallDispatchSuite` discriminant pins for the new refusal arms; `AbiRoundtripSuite` cases for the two decoders | `tests/SyscallReturnAbiSuite.lean`, `tests/SyscallDispatchSuite.lean`, `tests/AbiRoundtripSuite.lean` | M |
| CB5.11 | Staging promotion: the theorem modules CB1–CB4 staged enter the `SeLe4n.lean` closure through their production consumers; allowlist entries removed and `STATUS: staged` markers replaced in the same cut; the partition gate passes in both directions (consumes CB5.7) | `SeLe4n.lean`, `SeLe4n/Platform/Staged.lean`, `scripts/staged_module_allowlist.txt` | S |
| CB5.12 | End to end: `syscallDispatchFromAbi` scenarios (configureServer → bindServer → bind thread → ticks → unbindServer) in a new Tier-2 suite with golden fixture `tests/fixtures/hierarchical_server_syscalls.expected`; scenario-registry entries; `NegativeStateSuite` pins for each error arm through the dispatcher (consumes CB5.4, CB5.8) | `tests/HierarchicalServerSuite.lean`, `lakefile.toml`, `scripts/test_tier2_negative.sh`, `tests/fixtures/scenario_registry.yaml` | M |

**Acceptance**: the Lean and Rust id tables agree under the existing mirror
tests; the routing gate reports zero exceptions; both dispatch payoffs
elaborate over 38 arms; the end-to-end fixture is byte-verified in-suite.

### CB6 — Information flow and liveness

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| CB6.1 | `serverMembersUniformlyLabeled ctx st`; `schedContextBindServerChecked_establishes_uniformLabels` (the only member-adding transition) and preservation by every other transition (consumes CB5.6) | `SeLe4n/Kernel/InformationFlow/Invariant/Helpers.lean` | M |
| CB6.2 | Per-core NI for the tick: `chargeSchedPath_confined_to_label` (under uniform labels every ancestor write is same-label) and the SM8.B tick lift re-proved over the new body (consumes CB3.3, CB6.1) | `SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean`, `SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean` | L |
| CB6.3 | Projection and confinement theorems for the three arms in the SM8 style: `…_preserves_projection` for every observer and `…_confinedToCores` | `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean`, `SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean` | M |
| CB6.4 | Refusal-ledger partition: the SM9 pin `capFaultReceivePhase?_none_iff_records` restated over the wider inductive — the new arms record nothing and fault nothing | `SeLe4n/Platform/FFI.lean`, `SeLe4n/Kernel/InformationFlow/RefusalRecord.lean` | S |
| CB6.5 | Covert-channel classification: the intra-server budget channel closed by construction (`no_cross_label_server_membership`); the inter-server root channel identified with the existing class SM8.D bounds, recorded in the lock-domain register rather than in prose | `SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean`, `SeLe4n/Kernel/InformationFlow/FineLockFlow.lean` | M |
| CB6.6 | Taint: the three arms are control-only in `contentFlowClass` (no payload crosses) and the per-arm taint family gains the three arms | `SeLe4n/Kernel/InformationFlow/TaintPropagation.lean` | S |
| CB6.7 | Liveness: `hierarchicalBandExhaustionBound` and `member_response_bounded_onCore` — a member is selected within the root band's `bandExhaustionBound` plus its local fixed-priority bound inside one server period, per core, hypotheses stated as `hBandProgress` is today and the WS-SL trace limitation cited rather than crossed (consumes CB2.5, CB3.8) | `SeLe4n/Kernel/Scheduler/Liveness/HierarchicalWcrt.lean` (new), `SeLe4n/Kernel/Scheduler/Operations/PerCoreWcrt.lean` | L |
| CB6.8 | Lock-domain register: `UncoveredLockDomain`'s completeness theorem re-proved — servers add no lock domain (the SchedContext kind and the per-core replenish queue cover them) — and `SchedLockId` unchanged, stated as a pin | `SeLe4n/Kernel/InformationFlow/FineLockFlow.lean` | S |
| CB6.9 | Tier-2 NI scenarios — a two-label deployment where bindServer across labels is refused and same-label servers pass; a tick on a hierarchy leaves the other label's observation unchanged — in the information-flow suite; Tier-3 anchors for CB6 | `tests/SmpInformationFlowSuite.lean`, `scripts/test_tier3_invariant_surface.sh` | M |

**Acceptance**: the SM8.B per-core non-interference capstone elaborates over
the hierarchical tick with `serverMembersUniformlyLabeled` as its only new
hypothesis; `member_response_bounded_onCore` states every hypothesis it uses.

### CB7 — Closure

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| CB7.1 | Specification: §8.12.8 "Hierarchical servers" complete (model, order, charging, admission, syscalls, refusals, isolation theorems); §8.14 gains the hierarchical bound with its hypotheses; evidence-index rows under §4 SMP | `docs/spec/SELE4N_SPEC.md`, `docs/CLAIM_EVIDENCE_INDEX.md` | M |
| CB7.2 | Theorem inventory `hierarchicalServerTheorems` with its nodup witnesses, and the census extended so a workstream inventory can be **claimed**: a workstream-keyed manifest beside the SMP phase manifest, read by the generator, so an unclaimed inventory still fails Tier 0 | `SeLe4n/Kernel/SchedContext/HierarchyInventory.lean` (new), `SeLe4n/Kernel/Concurrency/PhaseTheoremManifest.lean`, `scripts/generate_smp_theorem_manifest.py` | M |
| CB7.3 | Hardware spot-check script in the `test_qemu_smp_cbs.sh` shape — skips until SM10.1's image carries the driver and lists its formal stand-ins in the header | `scripts/test_qemu_hierarchical_servers.sh`, `scripts/test_tier4_smp_bootcheck.sh` | S |
| CB7.4 | `CLAUDE.md`/`AGENTS.md`: standing-constraint bullets (server priority immutable while populated, member affinity fixed, off-core member donation refused, enforcement tick-quantised) and the status row to CLOSED; large-files snapshot refreshed | `CLAUDE.md`, `AGENTS.md` | S |
| CB7.5 | Debt register: the WS-CB rows closed with versions; the §11 follow-ups registered with owners and closure targets; the registry row's span closed | `docs/REGISTERED_DEBT.md` | S |
| CB7.6 | README metrics sync and the GitBook roadmap row; `docs/codebase_map.json` regenerated; `docs/DEVELOPMENT.md` where a tier gained a suite | `README.md`, `docs/gitbook/05-specification-and-roadmap.md`, `docs/codebase_map.json`, `docs/DEVELOPMENT.md` | S |
| CB7.7 | Full validation sweep — `test_full.sh`, `test_rust.sh`, `test_aarch64_cross_build.sh`, `test_docs_sync.sh` — and the CHANGELOG closure entry | `CHANGELOG.md` | S |
| CB7.8 | Hand-off note to SM10: what §8.12.8 adds to SM10.2's documentation sweep and what CB7.3's script adds to SM10.3's hardware validation list | `docs/planning/SMP_RELEASE_CLOSURE_PLAN.md` | T |

**Acceptance**: every row of the phase map reports LANDED with a version; the
plan gate, the naming gate and the docs-sync lane pass on the closing cut.

## 7. Verification strategy

### 7.1 Per PR

* `lake build <Module>` for every touched module (the pre-commit hook), then
  `./scripts/test_smoke.sh`; `./scripts/test_full.sh` whenever a theorem or a
  Tier-3 anchor moves — which is every phase from CB1 on.
* `./scripts/test_aarch64_cross_build.sh` after any change under `rust/`
  (CB0.5, CB5.8, CB5.9).
* Stage before running Tier 0: the plan gate and the naming gate read the
  index.

### 7.2 The flat-equivalence discipline

CB2.4 and CB3.3 change live selection and charging.  Each lands with the
theorem that on a state whose contexts are all parentless the new definition
equals the old, and with `./scripts/test_tier2_trace.sh` reporting every
`.expected` sha256 unchanged.  A fixture that moves in CB2 or CB3 is a defect
in the cut, not a fixture to refresh; the only intended fixture moves are
CB0.3's (the configure authority gate), CB4.2's (per-core admission) and the
new fixtures CB3.9, CB5.12 and CB6.9 add.

### 7.3 What each phase proves

| Phase | Proof obligation discharged |
|-------|-----------------------------|
| CB1 | `schedHierarchyInvariant` holds of the default and boot states; the Z2 budget engine frames the hierarchy |
| CB2 | `isBetterPath` is a strict order; the hierarchical selector is total, optimal, and equal to the flat one on flat states |
| CB3 | the tick preserves every structural and CBS invariant over path charging; a server's subtree is bandwidth-bounded; a member is isolated from its siblings |
| CB4 | every hierarchy transition preserves the per-core, CBS, hierarchy and cross-subsystem bundles; every refusal is explicit |
| CB5 | the dispatcher stays total over 38 ids; `ipcInvariantFull` survives every new arm; the Lean and Rust tables agree |
| CB6 | per-core non-interference under uniform labels; the hierarchical response-time bound with stated hypotheses |

### 7.4 What each phase validates

Tier 2: `smp_cbs_suite` (CB0.4, CB2.9, CB3.9), the new
`hierarchical_server_suite` (CB5.12), `NegativeStateSuite` (CB0.3, CB4.16,
CB5.12), `SmpInformationFlowSuite` (CB6.9), the decode and ABI suites (CB5.1,
CB5.10).  Tier 3: anchors per phase.  Tier 4: CB7.3's script, a skip until
SM10.1 produces an image.

## 8. Risk inventory

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| CB3.4's re-proof of the tick family is larger than estimated (ten structural theorems plus the CBS side over a fold) | HIGH | MED | CB3.3's flat-equivalence theorem reduces most cases to the prior proof; the fold's frames (CB3.1) are proved once; split CB3.4 by theorem family if it exceeds one PR |
| Per-core admission (CB4.2) changes an existing refusal on fixtures that over-admit only in aggregate | MED | LOW | Enumerate the affected fixtures at CB4.2, refresh with rationale; no flat theorem depends on the global sum |
| A member thread's bucket is its root priority, so `boundThreadPriorityConsistent` reads differently for members and leaves | MED | MED | `memberBucketConsistent` is a separate conjunct; the flat corollary is stated and used where the old lemma was |
| The path-comparison order admits a tie the proofs cannot break (equal priority, equal deadline, distinct servers) | LOW | HIGH | D3 breaks it by `scId`; `isBetterPath_trans` is proved in CB2.3 before anything relies on the order |
| The receive-side refusal of an off-core member donation surfaces as an error to a blameless passive server | LOW | MED | Documented in §3.6 and the spec; the follow-up (per-core server replicas) removes the refusal; a Tier-2 scenario pins the behaviour so it cannot change silently |
| The workstream inventory cannot be claimed by the SMP-only manifest census | HIGH | LOW | CB7.2 extends the census rather than misfiling the inventory under SM5 |
| Overlap with WS-RR on `API.lean` or the flow tables | MED | MED | §2.3's partition; CB4 onward waits for a WS-RR cut touching those files to land |

## 9. Acceptance gate

- [ ] Every CB row LANDED with a version in the phase map.
- [ ] `chooseThreadEffectiveOnCore_eq_flat_of_no_servers` and
      `timerTickBudgetOnCore_eq_flat_of_root` elaborate with no hypothesis
      beyond parentlessness.
- [ ] `server_subtree_consumption_bounded` and `member_isolation` stated over
      arbitrary subtrees within `maxServerDepth`.
- [ ] `crossSubsystemInvariant` has thirteen conjuncts and thirteen field-sets.
- [ ] Both dispatch payoffs elaborate over 38 ids; the routing gate reports
      zero exceptions; `SyscallId::COUNT` agrees on both sides.
- [ ] The SM8.B per-core non-interference capstone holds over the hierarchical
      tick under `serverMembersUniformlyLabeled`.
- [ ] `member_response_bounded_onCore` states every hypothesis it uses.
- [ ] Every pre-existing `.expected` unchanged except CB0.3's and CB4.2's,
      each refreshed with rationale; three new fixtures byte-verified.
- [ ] Zero `sorry`, zero axioms; Tier 0, docs-sync, Tier 3 and the cross build
      green on the closing cut.
- [ ] Follow-ups (§11) registered with owners.

## 10. Questions for the maintainer

Each has a default the plan is written against; changing one changes the rows
named.

| # | Question | Default | If changed |
|---|----------|---------|------------|
| Q1 | Keep the root order as fixed priority with EDF tie-breaking? | Yes (D3) | An EDF-first root reorders every band; CB2 becomes a new selector rather than a generalisation |
| Q2 | Core-homed servers, members on one core? | Yes (D5) | Per-core replicas add a per-core budget slot per server and cross-core charging; CB3 and CB4 roughly double |
| Q3 | Members must carry a label equivalent to the server's? | Yes (D8) | Permitting one-way flows reopens the budget channel and CB6.2 becomes a bounded-channel argument in the SM8.D style |
| Q4 | `maxServerDepth = 3`, `maxServerMembers = 16`? | Yes (D9) | Depth 4 still fits `maxLockSetSize`; wider member lists only cost admission time |
| Q5 | Refuse off-core donation of a member leaf? | Yes (D5) | Allowing it needs cross-core ancestor charging and a remote reschedule poke on server refill |
| Q6 | Timeouts decided by the leaf only on server exhaustion? | Yes (D4) | Timing out members on server exhaustion needs a per-server blocked index |
| Q7 | Refuse `.tcbSetPriority` on member threads? | Yes (D7) | Redirecting it to the local priority changes the syscall's meaning for one class of thread |
| Q8 | Open after WS-RR, or beside RR6–RR8 under §2.3's partition? | After | CB1–CB3 may start now; CB4 onward waits for `API.lean` to be quiet |
| Q9 | Land CB0.3 as the next cut, ahead of the workstream? | Yes | The authority gap stays open until the workstream opens |
| Q10 | Retire `schedContextYieldTo`, or leave it? | Leave | Retiring it removes one proven-but-unwired helper and its cross-subsystem bridge |

## 11. Cross-references and registered follow-ups

* Debt register: [`../REGISTERED_DEBT.md`](../REGISTERED_DEBT.md) — the
  WS-CB rows in the registry and in table C.
* Neighbours: [`SMP_PER_CORE_SCHEDULER_PLAN.md`](SMP_PER_CORE_SCHEDULER_PLAN.md)
  (SM5, the surface generalised), [`SMP_INFORMATION_FLOW_PLAN.md`](SMP_INFORMATION_FLOW_PLAN.md)
  (SM8, the observer), [`SMP_RELEASE_READINESS_PLAN.md`](SMP_RELEASE_READINESS_PLAN.md)
  (WS-RR, the partition in §2.3), [`SMP_RELEASE_CLOSURE_PLAN.md`](SMP_RELEASE_CLOSURE_PLAN.md)
  (SM10, CB7.8's hand-off).
* Specification: `docs/spec/SELE4N_SPEC.md` §8.12 (the flat model this
  extends), §8.14 (the bound CB6.7 extends).

Follow-ups this plan deliberately leaves for a later workstream, to be
registered by CB7.5 with owners and closure targets: server migration between
cores (a whole subtree re-homed, replenishments included); per-core server
replicas so a component may span cores; an EDF-first root; bandwidth
inheritance for a PIP-boosted member; boot-time server trees in
`PlatformConfig`; a bucketed `MemberList`; sub-tick enforcement through a
one-shot timer seam.

## 12. Theorem catalogue

| Theorem | Phase | Statement |
|---------|-------|-----------|
| `pathLockFootprint_le_maxLockSetSize` | CB1 | a path charge's lock footprint fits the SM3 bound |
| `default_schedHierarchyInvariant`, `bootFromPlatformCheckedWithIdleThreadsFor_schedHierarchyInvariant` | CB1 | the bundle holds of the default and production boot states |
| `pathBudgetEligible_eq_hasSufficientBudget_of_root` | CB2 | eligibility is today's on a parentless leaf |
| `isBetterPath_irrefl`, `isBetterPath_asymm`, `isBetterPath_trans` | CB2 | the hierarchical order is strict |
| `isBetterPath_singleton_eq_isBetterCandidate` | CB2 | the order is today's on singleton paths |
| `chooseThreadEffectiveOnCore_eq_flat_of_no_servers` | CB2 | the selector is today's on flat states |
| `chooseBestRunnableHierarchical_always_ok`, `chooseBestRunnableHierarchical_optimal` | CB2 | totality and maximality |
| `timerTickBudgetOnCore_eq_flat_of_root` | CB3 | the tick is today's on a parentless leaf |
| `chargeSchedPath_charges_every_ancestor` | CB3 | one consumed tick reaches every level |
| `server_subtree_consumption_bounded`, `server_subtree_consumption_bounded_tight` | CB3 | a subtree's consumption is bounded by its server's reservation |
| `member_isolation` | CB3 | a member's consumption is bounded by its own leaf |
| `timerTickOnCore_preserves_perCoreCbsInvariant` (re-proved) | CB3 | the CBS bundle survives path charging |
| `cbsReplenish_server_reschedules_local` | CB3 | a server refill triggers the executing core's reschedule decision |
| `rootAdmission_sound_per_core` | CB4 | admitted roots on a core sum to at most the core |
| `setThreadCpuAffinityWithMigration_rejects_member`, `setPriorityOp_rejects_member` | CB4 | the two refusals the cross-subsystem bridges need |
| `member_donation_same_core` | CB4 | a member's donation never migrates replenishments |
| `applyCallDonationOnCore_preserves_schedHierarchyInvariant` (+ reply twins) | CB4 | donation keeps the tree well-formed |
| `dispatchCapabilityOnly_bindServer_idle_refused` | CB5 | the chokepoint covers the new operand |
| `checkedDispatch_bindServer_eq_unchecked_when_allowed` | CB5 | the flow gate is transparent when it permits |
| `dispatchCapabilityOnly_preserves_ipcInvariantFull` (extended) | CB5 | the production payoff over 38 arms |
| `schedContextBindServerChecked_establishes_uniformLabels` | CB6 | the only member-adding transition establishes the label rule |
| `chargeSchedPath_confined_to_label` | CB6 | path charging writes one label |
| `no_cross_label_server_membership` | CB6 | the intra-server channel is closed by construction |
| `member_response_bounded_onCore` | CB6 | the hierarchical response-time bound, hypotheses explicit |

## Appendix A — Verification commands

```bash
source ~/.elan/env
lake build SeLe4n.Kernel.SchedContext.Hierarchy            # CB1
lake build SeLe4n.Kernel.Scheduler.Operations.Selection    # CB2
lake build SeLe4n.Kernel.Scheduler.Operations.Core         # CB3
lake build SeLe4n.Kernel.API                               # CB5
lake exe smp_cbs_suite                                     # CB0.4, CB2.9, CB3.9
lake exe hierarchical_server_suite                         # CB5.12
./scripts/test_tier2_trace.sh                              # every fixture sha256
./scripts/test_full.sh                                     # Tier 0–3
./scripts/test_aarch64_cross_build.sh                      # after rust/ changes
python3 scripts/check_live_arm_per_core_routing.py         # CB5.4
python3 scripts/check_workstream_plan.py                   # this plan (stage first)
./scripts/test_docs_sync.sh                                # citations, mirrors, map
```
