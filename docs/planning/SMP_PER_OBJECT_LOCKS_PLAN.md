# SM3 — Per-Object Lock Fields & Hierarchical Order (WS-SM Phase 3)

> **Phase**: SM3 of WS-SM
> **Parent overview**: [`SMP_MULTICORE_COMPLETION_PLAN.md`](SMP_MULTICORE_COMPLETION_PLAN.md)
> **Audited cut**: `v0.31.2`
> **Target releases**: v0.46.0 .. v0.52.x (after SM1+SM2 complete)
> **Calendar estimate**: 8-12 weeks
> **Sub-task count**: 50-65 across ~18-26 PRs

## 1. Phase goal

SM3 wires SM2's verified RwLock primitive into the kernel by:

1. **Adding `lock : RwLock` fields** to every kernel-object
   struct (TCB, Endpoint, CNode, Notification, Reply, SchedContext,
   VSpaceRoot, Page, Untyped) plus the ObjStore.
2. **Defining `lockSet`** statically per kernel transition: a
   total function that maps `(τ, args) → Finset (LockId ×
   AccessMode)`.
3. **Two-phase locking (2PL) discipline**: every kernel
   transition acquires its lock-set in `LockId` ascending order,
   executes, then releases in reverse order.
4. **Proving deadlock-freedom** (Theorem 2.1.9): under
   hierarchical acquire + 2PL, no execution can deadlock.
5. **Proving serializability** (Theorem 2.1.10): strict-2PL is
   conflict-serializable.
6. **Proving single-core proof preservation** (Corollary 2.1.11):
   every existing single-core kernel-transition theorem remains
   valid under SMP, provided the precondition that the
   transition's lock-set is held in the declared modes.

**Closure**: SMP-C3 (formal foundation for `kernelStateRef`
safety under SMP).

## 2. Dependencies

- **SM0**: SM0.I (LockKind + LockId), SM0.E (CoreId).
- **SM2**: SM2.C.19 (Rust RwLock impl), SM2.D.2 (Lean FFI for
  RwLock), SM2.C.5+ (RwLock theorems).
- **SM1.B**: optional (`PerCpuData` for per-core lock-set
  tracking; not strictly required at SM3).

## 3. Mathematical foundations

### 3.1 Per-object lock representation

Every kernel-object struct gains a `lock : RwLock` field
(decision #10, decision #11):

    structure ThreadControlBlock where
      tid : ThreadId
      priority : Priority
      state : ThreadState
      ...                       -- existing fields
      lock : RwLock := RwLock.unheld   -- SM3.A

    structure Endpoint where
      eid : EndpointId
      ...
      lock : RwLock := RwLock.unheld

    -- and analogously for CNode, Notification, Reply,
    -- SchedContext, VSpaceRoot, Page, Untyped.

    structure ObjStore where
      table : RobinHoodHashTable ObjId KernelObject
      lock : RwLock := RwLock.unheld   -- table-level lock

The default-initialization to `RwLock.unheld` means every
freshly-allocated object starts with its lock available. The
boot sequence (`bootFromPlatform`) creates objects without
holding their locks; subsequent kernel operations acquire as
declared in `lockSet`.

### 3.2 Lock-kind hierarchy (recap)

From SM0.I:

    inductive LockKind where
      | objStore         -- level 0
      | untyped          -- level 1
      | cnode            -- level 2
      | tcb              -- level 3
      | endpoint         -- level 4
      | notification     -- level 5
      | reply            -- level 6
      | schedContext     -- level 7
      | vspaceRoot       -- level 8
      | page             -- level 9

    structure LockId where
      kind  : LockKind
      objId : ObjId

The total order is lex: `(kind.level, objId.val)`.
`LockId.le_total` is proven in SM0.I.

### 3.3 Access mode

    inductive AccessMode where
      | read
      | write
      deriving DecidableEq, Repr

    /-- Conflict relation: two access modes on the same lock
        conflict iff at least one is .write. -/
    def AccessMode.conflicts : AccessMode → AccessMode → Bool
      | .write, _ => true
      | _, .write => true
      | .read, .read => false

### 3.4 Lock-set per transition

For each kernel transition τ and arguments args, `lockSet`
declares the locks needed and their modes:

    def lockSet (τ : KernelTransition) (args : Args) :
        Finset (LockId × AccessMode)

The function is **static**: it depends only on the *shape* of
args (which ObjIds appear as capability arguments, register
values), not on data in the kernel state. This is enforced by
construction: `lockSet` is a pure function with no state
parameter.

Example for `endpointCall`:

    def lockSet_endpointCall (callerTid : ThreadId)
        (capArg : CPtr) (receiverTid : Option ThreadId) :
        Finset (LockId × AccessMode) :=
      let callerLock := (LockId.mk .tcb callerTid.toObjId, .write)
      let cnodeLock := (LockId.mk .cnode (resolveCNodeRoot capArg).toObjId, .read)
      let endpointObjId := (resolveCapAddress capArg).toObjId
      let endpointLock := (LockId.mk .endpoint endpointObjId, .write)
      let receiverLockOpt := receiverTid.map (fun rt =>
        (LockId.mk .tcb rt.toObjId, .write))
      ({callerLock, cnodeLock, endpointLock} : Finset _)
      ∪ (receiverLockOpt.toFinset)

The set is then sorted by `LockId` ascending before acquire.

### 3.5 Lock-set canonical ordering

**Theorem 3.5.1** (`lockAcquireSequence_canonical`). For any
finite set S of `(LockId × AccessMode)` pairs,
`lockAcquireSequence S` is the unique sorted permutation of S
with respect to the `LockId` order.

    def lockAcquireSequence (S : Finset (LockId × AccessMode)) :
        List (LockId × AccessMode) :=
      S.toList.qsort (fun (l₁, _) (l₂, _) => l₁ ≤ l₂)

The qsort is stable on (LockId, AccessMode) pairs because
`LockId` is total — two pairs cannot share the same `LockId`
(would be a contradiction since a lock can't have two modes
declared in the same lock-set; we enforce this).

**Proof.** `Finset.toList` returns a permutation (modulo
ordering). `List.qsort` sorts to a canonical order under a
decidable total relation. The combination is unique. □

### 3.6 Two-phase locking

The 2PL discipline:

```
withLockSet (S : Finset (LockId × AccessMode)) (action : SystemState → SystemState) :
    SystemState → SystemState
withLockSet S action s :=
  let ordered := lockAcquireSequence S
  let acquired := ordered.foldl (acquireLockOnObject) s
  let result := action acquired
  let released := ordered.reverse.foldl (releaseLockOnObject) result
  released
```

The `acquireLockOnObject` operation:
- Find the object identified by the LockId.
- Acquire its lock in the declared mode (`acquire_read` or
  `acquire_write`).
- Update the kernel state with the (now-locked) object.

The `releaseLockOnObject` operation:
- Same as above, but releases.

### 3.7 Deadlock-freedom (Theorem 2.1.9)

**Setup**. Consider an execution where multiple cores each
execute kernel transitions. Each transition τ_c on core c
acquires its lock-set in `LockId` ascending order.

**Theorem 3.7.1** (`deadlockFreedom_under_2pl_and_ordering`):
no execution can reach a state where two cores are mutually
blocked.

**Proof** (formal):

Define a "blocked" state as: core c is "blocked at lock l" iff
c has tried to acquire l, the lock is currently held in an
incompatible mode by some other core, and c is waiting.

Suppose for contradiction that two cores c₁ ≠ c₂ are both
blocked at locks l₁ ≠ l₂. Each holds some locks (acquired
earlier in its 2PL sequence) and is waiting on its current
target.

Let H_c = set of locks core c currently holds. By 2PL, H_c is
the prefix of c's `lockAcquireSequence(S_c)` that has been
acquired so far.

If c₁ is blocked at l₁, then l₁ is the next lock in c₁'s
sequence; all locks in H_c₁ have `LockId < l₁`.

Symmetric: all locks in H_c₂ have `LockId < l₂`.

For c₁ to be blocked at l₁, c₁'s target l₁ must conflict with a
lock currently held by some other core c'; let's say c' = c₂ for
the cycle to close. So c₂ holds some lock l with `LockId(l) =
LockId(l₁)`, i.e., l = l₁.

For c₂ to hold l₁, we need l₁ ∈ H_c₂, so `LockId(l₁) < l₂`.

Symmetrically, c₂ is blocked at l₂, so some lock in H_c₁ has
`LockId = LockId(l₂)`. But all of H_c₁'s locks have `LockId <
l₁ ≤ l₂` (we just established `LockId(l₁) < l₂`). So
`LockId(l₂) < l₂` — irreflexivity of `<`, contradiction. □

**Generalization** to N cores: the same argument scales. By
induction on the wait-graph cycle length, any cycle of length
k > 1 induces a contradiction with the lock-order total ordering.

In Lean:

    theorem deadlockFreedom_under_2pl_and_ordering :
        ∀ (execution : KernelExecution),
          executionFollows2PL execution →
          executionAcquiresInLockIdOrder execution →
          ¬ executionDeadlocks execution := by
      intro exec h2pl hOrdered hDeadlock
      -- Extract the cycle from hDeadlock.
      obtain ⟨c₁, c₂, l₁, l₂, hCycle⟩ := hDeadlock
      -- Apply the 2PL + ordering hypotheses.
      ...                          -- ~80 LoC of structural reasoning

The full proof is ~120 LoC.

### 3.8 Serializability (Theorem 2.1.10)

**Theorem 3.8.1** (`serializability_under_2pl`): every
interleaved execution of kernel transitions under strict-2PL is
conflict-equivalent to some serial execution.

**Proof outline** (Bernstein et al. 1987, "Concurrency Control
and Recovery in Database Systems"):

Strict 2PL (no early release) is conflict-serializable. The
serial order is given by the *commit order* — the order in which
transactions release their last lock.

For seLe4n: each kernel transition is a "transaction" that
acquires its lock-set, performs state mutations, and releases.
Strict-2PL is enforced by `withLockSet` (3.6): no lock is
released before the transition's mutation is complete.

The Lean proof:

    theorem serializability_under_2pl :
        ∀ (execution : KernelExecution),
          executionFollows2PL execution →
          ∃ (serialOrder : List KernelTransition),
            executionEquivalent execution serialOrder := by
      intro exec h2pl
      -- Construct serialOrder = transitions sorted by commit time.
      let serialOrder := exec.transitions.qsort (fun t₁ t₂ =>
        commitTime exec t₁ ≤ commitTime exec t₂)
      -- Prove equivalence by showing all conflicting pairs are
      -- ordered consistently.
      ...                          -- ~150 LoC

The proof reduces serializability to the conflict graph being
acyclic, which follows from 2PL.

### 3.9 Single-core proof preservation (Corollary 2.1.11)

**Corollary 3.9.1**. For every existing single-core
kernel-transition theorem T(s, s') of the form

    T : ∀ (s : SystemState) (op : KernelTransition) (args : Args),
        precond(s, op, args) →
        (op s args = .ok s') →
        postcondition(s, s', op, args)

the SMP analogue

    T_smp : ∀ (s : SystemState) (op : KernelTransition) (args : Args) (c : CoreId),
        precond(s, op, args) →
        lockSetHeld c (lockSet op args) s →
        (op s args = .ok s') →
        postcondition(s, s', op, args)

holds with the same proof, plus a `lockSetHeld` precondition.

**Proof**. Under `lockSetHeld c (lockSet op args) s`, the
operation `op` executes with all required locks held by c. No
other core can mutate the locked objects. The single-core
proof's reasoning — which assumes sequential operation — applies
under this precondition, because the lock-set has restricted
concurrent access exactly as the single-core proof requires. □

This is the architectural lever that keeps WS-SM's proof cost
tractable. Without it, every existing scheduler/IPC/capability
theorem would need re-proving from scratch.

## 4. Architectural choices for SM3

### 4.1 Why lock-set is static (not state-dependent)

`lockSet` is a pure function of `(τ, args)`. It does NOT read
the kernel state. This is enforced by construction.

Rationale:
- Deadlock-freedom (Theorem 3.7.1) requires knowing the lock-set
  in advance — before acquisition begins. State-dependent
  lock-set computation would require already-acquired locks to
  decide further acquisitions, which 2PL forbids.
- Verification simplicity: each transition has a single
  declarative lock-set; no runtime branching.

The tradeoff: for transitions that touch a variable number of
locks (e.g., `cspaceMove` may need 2 or 3 CNode locks depending
on path), the lock-set is the **union over all paths**. This
slightly over-locks but preserves correctness.

### 4.2 Why RwLock (not just exclusive)

Decision #11 (reader-writer locks): read-mostly objects benefit
from concurrent readers. Lookup operations (`resolveCapAddress`,
`cspaceLookupSlot`, ObjStore reads) are dominant in many
workloads. Under exclusive-only locks, every lookup serializes;
under RwLock, multiple cores can read concurrently.

Cost: SM2's RwLock has 10 theorems vs 6 for TicketLock. Worth
it.

### 4.3 Per-object vs per-subsystem (and the per-PTE rejection)

Decision #10 (per-object fine locks): each kernel-object struct
carries its own RwLock. Granularity is per-object, not
per-subsystem. Cost: every object pays 8-16 bytes for the lock
state. Benefit: maximum concurrency — two cores can operate on
different TCBs concurrently.

For 65,536 maxObjects, total lock overhead: ~1 MiB of RAM —
within budget on RPi5's 4 GB.

**Per-PTE locking is rejected** at the v1.0.0 design boundary.
seLe4n stores page mappings inline in `VSpaceRoot.mappings :
RHTable VAddr (PAddr × PagePermissions)` rather than as
first-class Page kernel objects.  A finer-grained per-page-table-
entry lock would require:

1. A lock state field on every map entry — multiplying lock
   overhead by ~`maxMappings` (typically 4×maxObjects on a
   populated system), pushing total lock memory past the per-VM
   working-set budget on memory-constrained platforms.
2. Hand-over-hand acquisition for cross-page operations (e.g.,
   PTE relocation across hash buckets during `RHTable.insert`
   probe-sequence reorganization), which the SM3.B `lockSet`
   extraction cannot pre-declare statically without locking the
   table itself first.
3. An additional lock-hierarchy level beyond `LockKind.page`
   (level 9) for the PTE granularity, which conflicts with the
   SM0.I 10-level cap.

A **single per-VSpaceRoot lock** (SM3.A.7) at hierarchy level 8
(`LockKind.vspaceRoot`) is sufficient for serializability: every
VSpace mutation (`vspaceMapPage`, `vspaceUnmapPage`) acquires the
VSpaceRoot lock in write mode; every lookup (`vspaceLookup`,
`vspaceLookupAddr`) acquires in read mode.  Concurrent reads from
different VSpaceRoots proceed in parallel; concurrent writes to
the same VSpaceRoot serialize, which matches user expectations
and matches seL4's per-PD locking discipline.  This decision is
consistent with §4.4's table-level ObjStore lock (also rejecting
finer per-bucket locking for the same Robin-Hood probe-sequence-
relocation reason).

When seLe4n adopts first-class Page kernel objects in a
post-v1.0.0 workstream (out of scope for SM3), per-Page locking
can be re-evaluated against the then-current performance budget.

### 4.4 The ObjStore table-level lock

The RobinHood hash table itself (in `ObjStore`) has a single
table-level RwLock. Reasons:
- The hash table is sharded only at the bucket level by hash
  function, but inserts/deletes can move entries across buckets.
- A per-bucket lock would require complex hand-over-hand
  acquisition for cross-bucket moves.
- The table-level lock is acquired in `read` mode for lookups
  and in `write` mode for inserts/deletes — most operations are
  lookups (read mode), so contention is modest.

### 4.5 Lock acquire order for multi-object operations

By hierarchy first, then ObjId.val within kind. Example:
`endpointCall` with caller TCB id 5, CNode id 10, endpoint id 20,
receiver TCB id 8:

| LockId | kind.level | objId.val |
|--------|-----------:|----------:|
| `cnode/10` | 2 | 10 |
| `tcb/5` | 3 | 5 |
| `tcb/8` | 3 | 8 |
| `endpoint/20` | 4 | 20 |

Sorted order: cnode/10 (write), tcb/5 (write), tcb/8 (write),
endpoint/20 (write). The acquisition sequence is unambiguous.

## 5. Detailed sub-task breakdown

### 5.1 Add `lock : RwLock` fields (SM3.A, 5 PRs, 11 sub-tasks) — LANDED

| Sub | Description | Files | Acceptance | Status |
|-----|-------------|-------|------------|--------|
| SM3.A.1 | `TCB` gains `lock : RwLockState` | `Model/Object/Types.lean` | Structure compiles; `BEq` extended; `TCB.ext` extended with `hLock` conjunct | LANDED |
| SM3.A.2 | `Endpoint` gains `lock` | `Model/Object/Types.lean` | Structure compiles; `DecidableEq` derivation preserved | LANDED |
| SM3.A.3 | `CNode` gains `lock` | `Model/Object/Types.lean` | Structure compiles; manual `BEq` extended; `freezeCNode` forwards `lock` | LANDED |
| SM3.A.4 | `Notification` gains `lock` | `Model/Object/Types.lean` | Structure compiles; `DecidableEq` derivation preserved | LANDED |
| ~~SM3.A.5~~ | ~~`Reply` gains `lock`~~ | N/A | **N/A for seLe4n** — Reply is not a kernel object (managed through TCB `blockedOnReply` state + Reply capabilities) | SKIPPED |
| SM3.A.6 | `SchedContext` gains `lock` | `Kernel/SchedContext/Types.lean` | Structure compiles; default unheld lock present | LANDED |
| SM3.A.7 | `VSpaceRoot` gains `lock` | `Model/Object/Structures.lean` | Structure compiles; manual `BEq` extended; `freezeVSpaceRoot` forwards `lock`; `beq_sound` + `beq_refl` updated for new conjunct | LANDED |
| ~~SM3.A.8~~ | ~~`Page` (PageFrame, etc.) gains `lock`~~ | N/A | **N/A for seLe4n** — pages are mapping entries (`PAddr × PagePermissions`) inside `VSpaceRoot.mappings`, not separate kernel objects.  Per-page locking is rejected by §4.3 (single VSpaceRoot lock suffices for serializability). | SKIPPED |
| SM3.A.9 | `UntypedObject` regions gain `lock` | `Model/Object/Types.lean` | Structure compiles; `DecidableEq` derivation preserved | LANDED |
| SM3.A.10 | `ObjStore` table-level `lock` + `objectLockOf` projection | `Model/State.lean`, `Model/Object/Structures.lean` | `SystemState.objStoreLock` field added; `KernelObject.objectLockOf` projection function defined with 7 per-variant `@[simp]` unfold lemmas; `FrozenSystemState.objStoreLock` forwards | LANDED |
| SM3.A.11 | `default_objects_locks_unheld` theorem | `Model/State.lean` | `default_objStoreLock_unheld` (objStore unheld at default); `default_objects_locks_unheld` (vacuous discharge — pointwise form); `default_objects_toList_empty` (computable witness); `default_objects_locks_unheld_via_toList` (toList membership variant) | LANDED |

**Skipped sub-tasks**: SM3.A.5 (Reply) and SM3.A.8 (Page) are
documented as **N/A for seLe4n** because the corresponding entities
are not kernel objects in the seLe4n model:

* **Reply**: seL4 has a first-class `Reply` object that backs reply
  capabilities; seLe4n encodes the reply discipline through TCB state
  (`ThreadIpcState.blockedOnReply`, `ThreadState.BlockedReply`,
  `TCB.pipBoost`) and capability-level reply targets.  Adding a
  separate `Reply` kernel object is a major model refactor outside
  SM3.A scope.  When seLe4n grows a `Reply` object in a future
  workstream, SM3.A.5 can be re-opened at that time.
* **Page**: seL4 has first-class page objects that back mapping
  capabilities; seLe4n stores mappings inline in
  `VSpaceRoot.mappings : RHTable VAddr (PAddr × PagePermissions)`.
  §4.3 of this plan rejects per-PTE locking as a v1.0.0 design
  decision — a single per-VSpaceRoot lock (SM3.A.7) suffices for
  serializability.  If seLe4n adopts page objects in a future
  workstream, SM3.A.8 can be re-opened.

The plan's underlying intent — "every kernel-object struct that the
SystemState models gains a `lock : RwLockState` field" — is fully
discharged.  The skipped sub-tasks correspond to seL4-specific kernel
objects that seLe4n's current model intentionally folds into other
structures.

**Default-initialization**: each lock field's default is
`SeLe4n.Kernel.Concurrency.RwLockState.unheld` (the canonical initial
state from SM2.C).  This means every freshly-allocated object starts
with its lock available.

**Type name**: the lock field type is `RwLockState`, not `RwLock`.
The plan's draft pseudocode used `RwLock` as the abstract type name;
in the actual SM2.C landing the abstract operational specification
exports `RwLockState` (an unbiased operational state record carrying
`writerHeld`, `readers`, `waiters`) as the abstract refinement target.
The Rust `RwLock` is the concrete hardware-level type; the Lean
abstract `RwLockState` is its operational refinement.

#### SM3.A.1 code skeleton (TCB)

```lean
structure ThreadControlBlock where
  tid : ThreadId
  priority : Priority
  -- existing fields ...
  state : ThreadState
  domain : DomainId
  cnodeRoot : Option ObjId
  vspaceRoot : Option ObjId
  -- ... 19 existing fields ...
  -- SM3.A.1: per-object lock
  lock : RwLock := RwLock.unheld
  deriving Repr
```

The `BEq` instance grows from 22 fields to 23. The
`storeObjectKindChecked` machinery handles the extra field
uniformly because BEq is derived structurally.

#### SM3.A.11: `default_objects_locks_unheld`

```lean
theorem default_objects_locks_unheld :
    let s := (default : SystemState)
    ∀ o : KernelObject, o ∈ s.objects.values →
      objectLockOf o = .unheld := by
  intro s o hmem
  -- Empty default state: s.objects = empty hash table.
  -- s.objects.values = [].
  -- ∀ o ∈ [], _ is vacuously true.
  cases hmem  -- empty list has no members
```

In a non-default state where `bootFromPlatform` has populated
initial objects, the analogous theorem proves that each initial
object's lock is `.unheld`.

### 5.2 LockId computation + lock-set extraction (SM3.B, 4 PRs, 9 sub-tasks) — LANDED

All 9 sub-tasks LANDED on branch `claude/affectionate-goldberg-6MNJ9`.
See CHANGELOG entry "WS-SM SM3.B LANDED" and CLAUDE.md / AGENTS.md
"Active workstream context" for the full per-sub-task description.

| Sub | Description | Files | Status |
|-----|-------------|-------|--------|
| SM3.B.1 | `LockId.fromObject` + `KernelObject.lockKind` | `Locks/LockIdProjection.lean` | LANDED |
| SM3.B.2 | `LockId.lookup` (dispatches via typed `getX?`) | `Locks/LockIdProjection.lean` | LANDED |
| SM3.B.3 | 25 per-transition `lockSet_<τ>` declarations | `Locks/LockSetTransitions.lean` | LANDED |
| SM3.B.4 | `permittedKinds` + 25 `lockSet_consistent_<τ>` | `Locks/LockSetTransitions.lean` | LANDED |
| SM3.B.5 | `LockSet` + smart constructors + `lockAcquireSequence` | `Locks/LockSet.lean` | LANDED |
| SM3.B.6 | `lockAcquireSequence_ordered` | `Locks/LockSet.lean` | LANDED |
| SM3.B.7 | `lockAcquireSequence_complete` | `Locks/LockSet.lean` | LANDED |
| SM3.B.8 | `lockAcquireSequence_canonical` | `Locks/LockSet.lean` | LANDED |
| SM3.B.9 | `tests/LockSetSuite.lean` (~600 LoC, 49 assertions) | `tests/LockSetSuite.lean` | LANDED |

**Adaptations from the pseudocode in this section**:

* `LockId.fromObject` takes `(oid : ObjId)` externally rather than
  reading `tcb.tid.toObjId`/`ep.eid.toObjId`/etc. from the
  KernelObject variant.  Only TCB and SchedContext carry inner-
  struct IDs in seLe4n; the other variants are looked up by external
  ObjId in the SystemState's RHTable.  Splitting the projection into
  `KernelObject.lockKind` (variant-only) and `LockId.fromObject (oid,
  o)` (kind + ObjId) keeps the function total over every variant.
* `LockId.lookup` is implemented as a dispatcher on `l.kind` that
  routes through the typed `getTcb?`/`getEndpoint?`/etc. accessors
  rather than performing a raw `match s.objects[l.objId]?`.  This
  keeps the AK7-cascade raw-match floor at the v0.31.2 baseline.
* `LockSet` is a `List (LockId × AccessMode)` with a `Nodup`
  proof on the projected keys (mathlib-free analog of the plan's
  `Finset`).  `insertOrMerge` uses `AccessMode.lub` to collapse
  duplicate keys per plan §4.1.
* `lockAcquireSequence` uses `List.mergeSort` (Lean core) rather
  than `List.qsort` (mathlib).
* Per-syscall lockSets take post-cap-resolution `ObjId` arguments
  rather than raw `CPtr`s — keeps the function static (no state
  parameter) per plan §4.1.

#### SM3.B.1 — `LockId.fromObject`

```lean
def LockId.fromObject (o : KernelObject) : LockId :=
  match o with
  | .tcb tcb => LockId.mk .tcb tcb.tid.toObjId
  | .endpoint ep => LockId.mk .endpoint ep.eid.toObjId
  | .cnode cn => LockId.mk .cnode cn.cnid.toObjId
  | .notification n => LockId.mk .notification n.nid.toObjId
  | .reply r => LockId.mk .reply r.rid.toObjId
  | .schedContext sc => LockId.mk .schedContext sc.scid.toObjId
  | .vspaceRoot vsr => LockId.mk .vspaceRoot vsr.vid.toObjId
  | .page p => LockId.mk .page p.pid.toObjId
  | .untyped u => LockId.mk .untyped u.uid.toObjId
```

**Acceptance**: pattern match exhaustive; each variant maps to
its hierarchical kind.

**Size**: S.

#### SM3.B.2 — `LockId.lookup`

```lean
def LockId.lookup (s : SystemState) (l : LockId) :
    Option (RwLock × KernelObject) :=
  match s.objects.find? l.objId with
  | some o =>
      if LockId.fromObject o = l then
        some (objectLockOf o, o)
      else
        none  -- lock kind mismatch (object kind differs)
  | none => none
```

**Acceptance**: returns `some` iff the object exists AND its
kind matches the LockId's kind; `none` otherwise.

**Size**: M.

#### SM3.B.3 — `lockSet τ args` definitions per transition

For each of the kernel's ~25 transitions, define its lock-set.
Examples:

```lean
def lockSet_endpointCall (callerTid : ThreadId)
    (capArg : CPtr) (msgInfo : MessageInfo) :
    Finset (LockId × AccessMode) :=
  let callerLock : LockId × AccessMode :=
    (LockId.mk .tcb callerTid.toObjId, .write)
  -- Cap lookup needs CNode root lock (read).
  -- Note: we use a placeholder ObjId for capArg's CNode; the
  -- actual lookup is path-dependent, so we use the caller's
  -- CSpace root.
  let cnodeLock : LockId × AccessMode :=
    (LockId.mk .cnode (defaultCSpaceRootObjId callerTid), .read)
  -- Endpoint lock (write): we need to write the endpoint's queue.
  let endpointLock : LockId × AccessMode :=
    (LockId.mk .endpoint (capPtrToObjId capArg), .write)
  -- Receiver TCB lock: we may need to update receiver's state.
  -- Conservatively include if a receiver is waiting; the lock-set
  -- is the union over all paths.
  let possibleReceivers : List ThreadId :=
    inferPossibleReceivers callerTid capArg
  let receiverLocks : List (LockId × AccessMode) :=
    possibleReceivers.map (fun rt =>
      (LockId.mk .tcb rt.toObjId, .write))
  ({callerLock, cnodeLock, endpointLock} ∪
    receiverLocks.toFinset)

def lockSet_endpointSend (callerTid : ThreadId)
    (capArg : CPtr) (msgInfo : MessageInfo) :
    Finset (LockId × AccessMode) :=
  -- Similar but caller is .read (we don't mutate caller's TCB).
  ...

-- ~25 lockSet_<transition> functions
```

**Acceptance**: every kernel transition has a `lockSet_<transition>`
defined.

**Size**: L (~500 LoC across many transitions).

#### SM3.B.4 — `lockSet_consistent`

**Theorem**: For every τ and args, `lockSet τ args` contains only
LockIds whose kind matches the transition's read/write footprint.

```lean
theorem lockSet_consistent :
    ∀ (τ : KernelTransition) (args : Args),
      ∀ (l, m) ∈ lockSet τ args,
        l.kind ∈ permittedKinds τ ∧
        (m = .write → τ mutates locks of l.kind)
```

**Acceptance**: pattern-matched proof per τ.

**Size**: M.

#### SM3.B.5 — `lockAcquireSequence`

```lean
def lockAcquireSequence (S : Finset (LockId × AccessMode)) :
    List (LockId × AccessMode) :=
  S.toList.qsort (fun p₁ p₂ => p₁.1 ≤ p₂.1)
```

**Acceptance**: function defined.

**Size**: M.

#### SM3.B.6 — `lockAcquireSequence_ordered`

```lean
theorem lockAcquireSequence_ordered :
    ∀ (S : Finset (LockId × AccessMode)),
      (lockAcquireSequence S).Sorted (fun p₁ p₂ => p₁.1 ≤ p₂.1)
```

Proven by `List.qsort_sorted_of_le_total` (Lean Std) applied to
`LockId.le_total` (SM0.I).

**Size**: M.

#### SM3.B.7 — `lockAcquireSequence_complete`

**Theorem**: every element of `S` appears in `lockAcquireSequence S`.

```lean
theorem lockAcquireSequence_complete :
    ∀ (S : Finset (LockId × AccessMode)) (p : LockId × AccessMode),
      p ∈ S → p ∈ lockAcquireSequence S
```

Proven by `Finset.mem_toList` + `List.mem_of_qsort`.

**Size**: M.

#### SM3.B.8 — `lockAcquireSequence_canonical`

The Theorem 3.5.1 above.

**Size**: M.

#### SM3.B.9 — Tests `tests/LockSetSuite.lean`

20+ scenarios:
- `lockSet_endpointCall` returns the expected set.
- `lockAcquireSequence` returns a sorted list.
- Per-transition lock-sets are non-empty (every transition needs
  at least one lock).
- `lockSet_consistent` proven for each transition.

**Size**: L.

### 5.3 Two-phase locking discipline (SM3.C, 4 PRs, 10 sub-tasks)

#### SM3.C.1 — `withLockSet` combinator

```lean
def withLockSet (S : Finset (LockId × AccessMode))
    (action : SystemState → BaseIO (SystemState × α))
    (s : SystemState) : BaseIO (SystemState × α) := do
  let ordered := lockAcquireSequence S
  -- Acquire in order.
  let acquired ← ordered.foldlM (fun st (l, mode) =>
    acquireLockOnObject st l mode) s
  -- Execute action with locks held.
  let (newState, result) ← action acquired
  -- Release in reverse order.
  let released ← ordered.reverse.foldlM (fun st (l, _) =>
    releaseLockOnObject st l) newState
  return (released, result)
```

**Size**: M.

#### SM3.C.2 — `acquireLockOnObject` / `releaseLockOnObject`

```lean
def acquireLockOnObject (s : SystemState) (l : LockId) (mode : AccessMode) :
    BaseIO SystemState := do
  -- Locate the object.
  match s.objects.find? l.objId with
  | some o =>
      match mode with
      | .read =>
          -- Issue FFI call to acquire read lock on this object.
          ffiAcquireReadLock (objectLockOf o)
      | .write =>
          ffiAcquireWriteLock (objectLockOf o)
  | none => return s  -- non-existent object; skip
  return s            -- state unchanged (lock state is HAL-side)
```

Note: the kernel state model treats lock acquisition as a
*non-state-mutating* operation. The actual lock state lives in
the hardware (via the AtomicU64 in RwLock). The Lean model
records "the locks for τ are held" implicitly via the
precondition on theorems.

**Size**: M.

#### SM3.C.3 — RAII discipline

```lean
def withLockSet_panicSafe (S : Finset (LockId × AccessMode))
    (action : SystemState → BaseIO (SystemState × α))
    (s : SystemState) : BaseIO (SystemState × α) := do
  let ordered := lockAcquireSequence S
  let acquired ← acquireAll ordered s
  try
    let (newState, result) ← action acquired
    releaseAll ordered.reverse newState
    return (newState, result)
  catch e =>
    -- Panic path: release all acquired locks.
    releaseAll ordered.reverse acquired
    throw e
```

The `try-catch` ensures locks are released even on panic.

**Size**: M.

#### SM3.C.4 — `lockSetHeld` predicate

```lean
/-- For the SMP-aware versions of transitions, the precondition
    that the lock-set is held by the executing core. This is
    threaded through the SMP-migrated theorems. -/
def lockSetHeld (c : CoreId) (S : Finset (LockId × AccessMode))
    (s : SystemState) : Prop :=
  ∀ (l, mode) ∈ S,
    match s.objects.find? l.objId with
    | some o =>
        match mode with
        | .read =>
            (objectLockOf o).readers.contains c ∨
            (objectLockOf o).writerHeld = some c
        | .write =>
            (objectLockOf o).writerHeld = some c
    | none => True
```

**Note**: `lockSetHeld` is a state-relative predicate. It is
used as a precondition on the SMP-migrated theorems
(`scheduler_X_smp` etc.). The combinator `withLockSet` ensures
this predicate holds at the entry to the action.

**Size**: M.

#### SM3.C.5..C.7 — Theorems

```lean
theorem lockSet_acquired_in_order :
    ∀ (S : Finset _) (s s' : SystemState),
      acquireAll (lockAcquireSequence S) s = some s' →
      ...                       -- acquisition observably in order

theorem lockSet_released_in_reverse :
    ∀ (S : Finset _) (s s' : SystemState),
      releaseAll (lockAcquireSequence S).reverse s = some s' →
      ...                       -- release in reverse

theorem lockSet_atomic_under_2pl :
    ∀ (τ : KernelTransition) (args : Args) (s s' : SystemState),
      withLockSet (lockSet τ args) (τ.body args) s = some s' →
      ...                       -- atomic from observer view (Thm 2.1.10)
```

**Size**: L total.

#### SM3.C.8 — `lockSet_invariant_preserved` (Corollary 2.1.11)

```lean
theorem lockSet_invariant_preserved :
    ∀ (τ : KernelTransition) (args : Args) (s s' : SystemState) (c : CoreId),
      precond τ args s →
      lockSetHeld c (lockSet τ args) s →
      τ.body args s = .ok s' →
      postcondition τ args s s'
```

This is the operational form of Corollary 2.1.11. It is
demonstrated for each kernel transition individually; the
aggregate theorem above is the contract.

**Size**: L (~150 LoC including the proof framework).

#### SM3.C.9 — Migrate every `@[export]` body

Every kernel `@[export]` body wraps its body in `withLockSet`.
For each transition, the migration is:

```lean
@[export sele4n_endpoint_call]
def endpointCallEntry (...args) : BaseIO UInt64 := do
  let myCore ← currentCoreId
  let s ← getKernelState
  let lockSetForCall := lockSet_endpointCall ...args
  let result ← withLockSet lockSetForCall (fun s' => do
    let outcome := endpointCall s' callerTid capArg msgInfo
    return (outcome.newState, outcome.result)
  ) s
  setKernelState result.1
  return result.2
```

There are ~25 `@[export]` bodies to migrate. SM3.C.9 spreads
this over multiple PRs (~3-5 PRs).

**Size**: L per body.

#### SM3.C.10 — Tests verify RAII discipline

```lean
-- Test: panic in body releases locks.
example : withLockSet S (fun s => do panic! "oops") s catches panic ∧
          lockSetHeld c S s = false := ...

-- Test: normal exit releases locks.
example : withLockSet S action s normal-exits ∧
          lockSetHeld c S s_after = false := ...
```

**Size**: M.

### 5.4 Deadlock-freedom (SM3.D, 3 PRs, 7 sub-tasks)

#### SM3.D.1 — `noDeadlock` predicate

```lean
def noDeadlock (execution : KernelExecution) : Prop :=
  ¬ (∃ (c₁ c₂ : CoreId) (l₁ l₂ : LockId),
      c₁ ≠ c₂ ∧
      blockedAt execution c₁ l₁ ∧
      blockedAt execution c₂ l₂ ∧
      heldBy execution c₂ l₁ ∧
      heldBy execution c₁ l₂)
```

**Size**: M.

#### SM3.D.2 — `LockId.le_total` (recap)

From SM0.I; cited here.

#### SM3.D.3 — `lockOrder_strict`

```lean
theorem lockOrder_strict :
    Irreflexive (· < · : LockId → LockId → Prop) ∧
    Transitive (· < · : LockId → LockId → Prop)
```

Both immediate from the corresponding properties of `Nat <`.

**Size**: T.

#### SM3.D.4 — Main theorem

```lean
theorem deadlockFreedom_under_2pl_and_ordering :
    ∀ (execution : KernelExecution),
      executionFollows2PL execution →
      executionAcquiresInLockIdOrder execution →
      noDeadlock execution
```

Per the proof in §3.7. Full Lean proof ~120 LoC.

**Size**: XL.

#### SM3.D.5 — Wait-graph acyclicity

```lean
theorem waitGraph_acyclic_under_2pl :
    ∀ (execution : KernelExecution),
      executionFollows2PL execution →
      executionAcquiresInLockIdOrder execution →
      Acyclic (waitGraph execution)
```

This is the dual form of deadlock-freedom: the wait graph
(directed graph where edges go from blocked cores to lock
holders) is a DAG. Sometimes the DAG form is more natural for
inductive proofs.

**Size**: L.

#### SM3.D.6 — Bounded-wait corollary

```lean
theorem boundedWait_under_2pl :
    ∀ (execution : KernelExecution) (c : CoreId),
      executionFollows2PL execution →
      executionAcquiresInLockIdOrder execution →
      ∀ (op : KernelOperation), 
        WCRT execution c op ≤ maxLockSetSize × (coreCount - 1) × T_cs
```

The `maxLockSetSize` is bounded statically (typically ≤ 4 for
most operations; ≤ 8 in worst cases).

**Size**: M.

#### SM3.D.7 — Tests

Multi-object operation scenarios verified by example:

```lean
-- Two cores trying to acquire {TCB 5, TCB 7} both succeed.
example :
    ∃ (execution : KernelExecution),
      executionFollows2PL execution ∧
      executionAcquiresInLockIdOrder execution ∧
      twoCorePathScenario execution := ...
```

**Size**: M (10+ tests).

### 5.5 Serializability (SM3.E, 3 PRs, 8 sub-tasks)

#### SM3.E.1 — `conflictOrder`

```lean
def conflictOrder (τ₁ τ₂ : KernelTransitionInstance) : Prop :=
  ∃ (l : LockId) (m₁ m₂ : AccessMode),
    l ∈ τ₁.lockSet ∧ l ∈ τ₂.lockSet ∧
    AccessMode.conflicts m₁ m₂ ∧
    -- τ₁ commits before τ₂ acquires l
    commitTime τ₁ ≤ acquireTime τ₂ l
```

**Size**: M.

#### SM3.E.2 — `serialEquivalent`

```lean
def serialEquivalent
    (interleaved : KernelExecution)
    (serial : List KernelTransitionInstance) : Prop :=
  -- Final state of interleaved = final state of serial.
  finalState interleaved = applySequential serial initialState
```

**Size**: M.

#### SM3.E.3 — Main serializability theorem

```lean
theorem serializability_under_2pl :
    ∀ (execution : KernelExecution),
      executionFollows2PL execution →
      ∃ (serial : List KernelTransitionInstance),
        serialEquivalent execution serial
```

Per the proof in §3.8. Lean proof ~150 LoC.

**Size**: XL.

#### SM3.E.4 — Strict-2PL preservation

```lean
theorem strictly_2pl_preserved :
    ∀ (execution : KernelExecution),
      ∀ τ ∈ execution.transitions,
        τ.releasesAllLocksAtCommit
```

This is preserved by the `withLockSet` discipline: all locks
acquired by a transition are released only when the body
completes.

**Size**: M.

#### SM3.E.5 — Commutativity lemmas

For each pair of "non-conflicting" operations (e.g., reads from
different objects), prove they commute:

```lean
theorem cspaceRead_commutes_with_cspaceRead_different_cnode :
    ∀ (s : SystemState) (cn1 cn2 : ObjId),
      cn1 ≠ cn2 →
      cspaceRead s cn1 |>.then (cspaceRead · cn2) =
      cspaceRead s cn2 |>.then (cspaceRead · cn1)
```

~10 commutativity lemmas covering the major non-conflicting
pairs.

**Size**: L (~10 theorems).

#### SM3.E.6 — `singleCore_proof_preservation`

The Corollary 2.1.11 in formal form:

```lean
theorem singleCore_proof_preservation :
    ∀ (τ : KernelTransition) (T : Theorem about τ in single-core),
      smpVersion T holds under lockSetHeld
```

This is a meta-theorem about the kernel proof surface. SM3.E.6
formalizes it as a higher-order statement; specific
instantiations (one per existing single-core theorem) happen
during SM4..SM6 phase migrations.

**Size**: L.

#### SM3.E.7 — Tests `tests/SerializabilitySuite.lean`

15+ scenarios:
- Two cores reading the same CNode: serializable trivially.
- Two cores writing the same TCB: serialized; one observes
  the other's post-state.
- Three cores in a chain: all serializable.

**Size**: L.

#### SM3.E.8 — Surface anchors

`#check` of 8 major theorems in `tests/SmpSurfaceAnchors.lean`.

**Size**: S.

## 6. Verification strategy for SM3

### 6.1 What SM3 proves

28 substantive theorems:

| # | Theorem | Phase sub-task |
|---|---------|----------------|
| 1 | `default_objects_locks_unheld` | SM3.A.11 |
| 2 | `LockId.fromObject_consistent` | (implicit in SM3.B.1's definition) |
| 3 | `lockSet_consistent` | SM3.B.4 |
| 4 | `lockAcquireSequence_ordered` | SM3.B.6 |
| 5 | `lockAcquireSequence_complete` | SM3.B.7 |
| 6 | `lockAcquireSequence_canonical` | SM3.B.8 |
| 7 | `lockSet_acquired_in_order` | SM3.C.5 |
| 8 | `lockSet_released_in_reverse` | SM3.C.6 |
| 9 | `lockSet_atomic_under_2pl` | SM3.C.7 |
| 10 | `lockSet_invariant_preserved` | SM3.C.8 |
| 11 | `noDeadlock_definition_decidable` | (instance) |
| 12 | `lockOrder_strict` | SM3.D.3 |
| 13 | `deadlockFreedom_under_2pl_and_ordering` | SM3.D.4 (Thm 2.1.9) |
| 14 | `waitGraph_acyclic_under_2pl` | SM3.D.5 |
| 15 | `boundedWait_under_2pl` | SM3.D.6 |
| 16 | `conflictOrder_irreflexive` | (immediate) |
| 17 | `serialEquivalent_decidable` | (instance) |
| 18 | `serializability_under_2pl` | SM3.E.3 (Thm 2.1.10) |
| 19 | `strictly_2pl_preserved` | SM3.E.4 |
| 20-27 | 8 commutativity lemmas | SM3.E.5 |
| 28 | `singleCore_proof_preservation` | SM3.E.6 (Cor 2.1.11) |

### 6.2 What SM3 assumes

- SM0's `LockId.le_total`, `LockId.le_trans`, `LockId.le_antisymm`.
- SM2's RwLock theorems (mutex, FIFO, etc.).
- Lean Std `List.qsort_sorted`, `Finset.toList`, etc.

No new Lean axioms.

### 6.3 Tests

- **Tier 3 (invariant)**: 50+ decidable examples in
  `LockSetSuite`, `SerializabilitySuite`.
- **Tier 4 (nightly)**: Stress tests on the QEMU `-smp 4` boot,
  exercising deadlock-free behavior in scheduling and IPC.

## 7. Risk inventory for SM3

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| `lockSet` extraction misses a state dependency | MED | HIGH | Per-transition review; all reads/writes traced |
| Multi-object operation exceeds 8-lock budget | MED | MED | SM6 review of IPC paths; refactor if needed |
| Deadlock-freedom proof gap | LOW | CRIT | Theorem 2.1.9 proof reviewed; wait-graph acyclicity as backup proof structure |
| Serializability proof has subtle case missed | LOW | HIGH | Bernstein's 2PL result is classical; proof mirrors textbook |
| Migration of `@[export]` bodies misses one | LOW | HIGH | grep-based audit; CI gate on missing `withLockSet` |
| `lockSetHeld` not equivalent to actual hardware state | MED | HIGH | SM2's RwLock refinement bridges abstract state to hardware |
| Lock-acquire ordering changes across kernel updates | MED | MED | LockId ordering is structurally fixed; new locks fit in the existing hierarchy |
| `withLockSet` panic path leaks a lock | LOW | CRIT | RAII discipline; SM3.C.10 tests cover panic case |
| Performance regression vs single-core (lock overhead) | HIGH | MED | Expected; benchmarked under WCRT bound |

## 8. Acceptance gate for SM3

- [ ] All kernel-object structs gain `lock : RwLock` field.
- [ ] `default_objects_locks_unheld` proven.
- [ ] `lockSet` defined for every kernel transition (~25 cases).
- [ ] `lockSet_consistent` proven.
- [ ] `lockAcquireSequence` defined and properties proven.
- [ ] `withLockSet` combinator with RAII.
- [ ] All `@[export]` bodies wrapped in `withLockSet`.
- [ ] `deadlockFreedom_under_2pl_and_ordering` proven (Theorem 2.1.9).
- [ ] `serializability_under_2pl` proven (Theorem 2.1.10).
- [ ] `singleCore_proof_preservation` proven (Corollary 2.1.11).
- [ ] 8+ commutativity lemmas proven.
- [ ] Tier 0..3 tests green.
- [ ] CHANGELOG aggregate entry.

## 9. Cross-references

- **Master overview**: [`SMP_MULTICORE_COMPLETION_PLAN.md`](SMP_MULTICORE_COMPLETION_PLAN.md)
- **Prerequisites**: [`SMP_FOUNDATIONS_PLAN.md`](SMP_FOUNDATIONS_PLAN.md), [`SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md`](SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md)
- **Next phase**: [`SMP_PER_CORE_STATE_PLAN.md`](SMP_PER_CORE_STATE_PLAN.md) — SM4 builds atop SM3's lock discipline.

## 10. Theorem catalogue for SM3

(28 theorems; full list in §6.1)

## Appendix A — Verification commands

```bash
source ~/.elan/env

# Build:
lake build SeLe4n.Kernel.Concurrency.Locks
lake build SeLe4n.Model.Object.Structures
lake build LockSetSuite
lake build SerializabilitySuite

# Tier 0..3:
./scripts/test_full.sh

# grep audit: every @[export] body has withLockSet:
grep -A 3 "^@\[export" SeLe4n/Platform/FFI.lean | grep -c withLockSet
```

## Appendix B — Sub-task dependency graph

```
SM3.A.1..A.11  (lock fields)    depend on SM2.C.16 (Lean RwLock def)
SM3.B.1..B.9   (LockId, lockSet) depend on SM0.I + SM3.A
SM3.C.1..C.10  (2PL discipline)  depend on SM3.B + SM2.D
SM3.D.1..D.7   (deadlock)        depend on SM3.B + SM3.C
SM3.E.1..E.8   (serializability) depend on SM3.D
```

---

*SM3 puts SM2's verified primitives to work. The
deadlock-freedom proof (Theorem 2.1.9) and serializability proof
(Theorem 2.1.10) are the architectural levers that let the
existing single-core proofs migrate cheaply in SM4..SM6
(Corollary 2.1.11).*
