# SM4 — Path-a Per-Core State Replacement (WS-SM Phase 4)

> **Phase**: SM4 of WS-SM
> **Parent overview**: [`SMP_MULTICORE_COMPLETION_PLAN.md`](SMP_MULTICORE_COMPLETION_PLAN.md)
> **Audited cut**: `v0.31.2`
> **Target releases**: v0.53.0 .. v0.70.x (largest phase)
> **Calendar estimate**: 20-26 weeks
> **Sub-task count**: 90-115 across ~35-50 PRs

## 1. Phase goal

SM4 implements the **path-a Vector replacement** (decision #4):
the singular SchedulerState fields become `Vector α coreCount`,
and every theorem touching them migrates to take a `c : CoreId`
parameter. This is the largest phase by LoC because the theorem
migration is mechanical but pervasive — ~5000-7000 LoC of
theorem rewrites across 60+ files.

**Concrete deliverables**:

1. **Vector helper bootstrap** (or Std import) — generic
   `Vector α n` operations + length theorems.
2. **PlatformBinding.coreCount thread-through** — every
   `numCores` usage becomes platform-parameterized.
3. **SchedulerState path-a replacement** — replace singular
   fields with `Vector α coreCount`; provide per-core accessors.
4. **Scheduler invariant migrations** — ~110 theorems migrated
   to per-core signatures.
5. **Cross-subsystem migrations** — IPC, capability, lifecycle,
   service, architecture, information-flow theorems touching
   scheduler state.
6. **Witness retirement + replacement** — retire
   `bootFromPlatform_singleCore_witness`; add
   `bootFromPlatform_smp_witness` proving the per-core shape.

**Closure**: SMP-H2 (retired — no longer applicable since per-
core fields replace the singular ones).

## 2. Dependencies

- **SM0**: SM0.E (CoreId), SM0.G (PlatformBinding.coreCount).
- **SM3** (parallel): SM3.A (per-object lock fields). SM4 can
  proceed in parallel with SM3 because the path-a rewrite is
  about field types, not lock discipline.

## 3. Mathematical foundations

### 3.1 SchedulerState path-a replacement

The singular fields **disappear** entirely; only the `Vector`-
indexed versions remain:

    structure SchedulerState where
      -- Per-core fields (Vector indexed by CoreId).
      current             : Vector (Option ThreadId) PlatformBinding.coreCount
      runQueue            : Vector RunQueue PlatformBinding.coreCount
      replenishQueue      : Vector ReplenishQueue PlatformBinding.coreCount
      activeDomain        : Vector DomainId PlatformBinding.coreCount
      domainTimeRemaining : Vector Nat PlatformBinding.coreCount
      domainScheduleIndex : Vector Nat PlatformBinding.coreCount
      lastTimeoutErrors   : Vector (List (ThreadId × KernelError)) PlatformBinding.coreCount
      -- System-wide (unchanged from single-core).
      domainSchedule         : List DomainScheduleEntry := []
      configDefaultTimeSlice : Nat := 5

Helper accessors:

    namespace SchedulerState
      def currentOnCore (s : SchedulerState) (c : CoreId) :
          Option ThreadId := s.current.get c
      def runQueueOnCore (s : SchedulerState) (c : CoreId) :
          RunQueue := s.runQueue.get c
      def replenishQueueOnCore (s : SchedulerState) (c : CoreId) :
          ReplenishQueue := s.replenishQueue.get c
      def activeDomainOnCore (s : SchedulerState) (c : CoreId) :
          DomainId := s.activeDomain.get c
      def domainTimeRemainingOnCore (s : SchedulerState) (c : CoreId) :
          Nat := s.domainTimeRemaining.get c
      def domainScheduleIndexOnCore (s : SchedulerState) (c : CoreId) :
          Nat := s.domainScheduleIndex.get c
      def lastTimeoutErrorsOnCore (s : SchedulerState) (c : CoreId) :
          List (ThreadId × KernelError) := s.lastTimeoutErrors.get c
    end SchedulerState

### 3.2 Boot-core shim (intentionally NOT provided)

Per decision #4 (path-a, no bootCore shim), SM4 does NOT
introduce a `currentOnBootCore` helper. Every theorem and
function that previously used `s.scheduler.current` becomes
explicitly `s.scheduler.currentOnCore c` for some `c : CoreId`.

For theorems that hold *for all cores*, the migration is:

    -- Single-core:
    theorem scheduler_X (s : SystemState) : ...

    -- SMP:
    theorem scheduler_X_smp (s : SystemState) (c : CoreId) : ...

For theorems that hold *only at boot core* (e.g., boot-time
properties), the migration is:

    -- SMP:
    theorem scheduler_X_smp_bootCore (s : SystemState) : ...
      -- with c implicitly fixed to bootCoreId

### 3.3 Per-core extensionality

**Theorem 3.3.1** (`SchedulerState.ext`). Two SchedulerStates are
equal iff all their per-core fields agree at every CoreId and
their system-wide fields agree:

    theorem SchedulerState.ext :
        ∀ s₁ s₂ : SchedulerState,
          (∀ c : CoreId, s₁.currentOnCore c = s₂.currentOnCore c) →
          (∀ c : CoreId, s₁.runQueueOnCore c = s₂.runQueueOnCore c) →
          (∀ c : CoreId, s₁.replenishQueueOnCore c = s₂.replenishQueueOnCore c) →
          (∀ c : CoreId, s₁.activeDomainOnCore c = s₂.activeDomainOnCore c) →
          (∀ c : CoreId, s₁.domainTimeRemainingOnCore c = s₂.domainTimeRemainingOnCore c) →
          (∀ c : CoreId, s₁.domainScheduleIndexOnCore c = s₂.domainScheduleIndexOnCore c) →
          (∀ c : CoreId, s₁.lastTimeoutErrorsOnCore c = s₂.lastTimeoutErrorsOnCore c) →
          s₁.domainSchedule = s₂.domainSchedule →
          s₁.configDefaultTimeSlice = s₂.configDefaultTimeSlice →
          s₁ = s₂

*Proof.* Vector extensionality (`Vector.ext`) applied per-field;
record-extensionality across the whole struct. ~30 LoC. □

### 3.4 Migration pattern

Every existing scheduler theorem is rewritten by the following
mechanical pattern:

**Pattern 1** (forall-core): Theorem held for the unique current
thread. Now holds for any specific core.

```
-- Before:
theorem scheduler_current_consistent (s : SystemState) :
    s.scheduler.current = some tid →
    ∃ tcb, s.objects.find? tid.toObjId = some (.tcb tcb)

-- After:
theorem scheduler_current_consistent (s : SystemState) (c : CoreId) :
    s.scheduler.currentOnCore c = some tid →
    ∃ tcb, s.objects.find? tid.toObjId = some (.tcb tcb)
```

The proof body is **identical** — the only change is the
parameter. `currentOnCore c` returns an `Option ThreadId`, same
as the singular `current` field's type.

**Pattern 2** (cross-core invariant): Theorem asserts a property
across all cores. New formulation: `∀ c, P (s, c)`.

```
theorem runQueueOnCore_wellFormed (s : SystemState) :
    ∀ c : CoreId, (s.scheduler.runQueueOnCore c).wellFormed
```

**Pattern 3** (boot-only): Theorem holds at boot time. New
formulation fixes c to bootCoreId.

```
theorem bootFromPlatform_currentIsIdle :
    let s := bootFromPlatform config
    s.scheduler.currentOnCore bootCoreId = some (idleThreadId bootCoreId)
```

### 3.5 PlatformBinding parameterization

The `coreCount` is now a typeclass field:

    class PlatformBinding where
      ...
      coreCount     : Nat
      coreCountPos  : coreCount > 0
      bootCoreId    : Fin coreCount
      sharingDomain : SharingDomain

Every theorem statement that previously used `numCores` (or the
hardcoded `4`) now uses `PlatformBinding.coreCount`. The
generality is preserved by the typeclass; specific platforms
specialize.

For RPi5: `coreCount = 4`. Theorems that need a concrete number
(e.g., `wcrt_bound_rpi5_smp = 4 × T_cs`) specialize via
`@PlatformBinding rpi5` instantiation.

### 3.6 Default-state initialization

The `default : SystemState` initializes every per-core field to
the singleton-core-equivalent default:

- `current` = `Vector.replicate coreCount none`.
- `runQueue` = `Vector.replicate coreCount RunQueue.empty`.
- `replenishQueue` = `Vector.replicate coreCount ReplenishQueue.empty`.
- `activeDomain` = `Vector.replicate coreCount ⟨0⟩`.
- `domainTimeRemaining` = `Vector.replicate coreCount 5`.
- `domainScheduleIndex` = `Vector.replicate coreCount 0`.
- `lastTimeoutErrors` = `Vector.replicate coreCount []`.

**Theorem 3.6.1** (`default_state_perCoreInitialized`).

```lean
theorem default_state_perCoreInitialized :
    ∀ c : CoreId,
      let s := (default : SchedulerState)
      s.currentOnCore c = none ∧
      s.runQueueOnCore c = RunQueue.empty ∧
      s.replenishQueueOnCore c = ReplenishQueue.empty ∧
      s.activeDomainOnCore c = ⟨0⟩ ∧
      s.domainTimeRemainingOnCore c = 5 ∧
      s.domainScheduleIndexOnCore c = 0 ∧
      s.lastTimeoutErrorsOnCore c = []
```

*Proof.* `Vector.replicate_get` (Lean Std) applied per-field. □

### 3.7 Idle thread bootstrap

Per decision #8 (per-core idle threads), `bootFromPlatform`
installs an idle TCB on each core:

    structure IdleThreadConfig where
      basePriority : Priority := ⟨0, by decide⟩   -- priority 0
      bound : Option SchedContextId := none        -- no SC binding

    def idleThreadId (c : CoreId) : ThreadId :=
      ⟨ObjId.ofNat (idleThreadIdBase + c.val), proof⟩

    def createIdleThread (c : CoreId) (config : IdleThreadConfig := default) :
        ThreadControlBlock :=
      { tid := idleThreadId c
      , priority := config.basePriority
      , state := .runnable
      , cpuAffinity := some c
      , -- other fields
      , lock := RwLock.unheld
      }

**Theorem 3.7.1** (`bootFromPlatform_all_cores_have_idle`).

```lean
theorem bootFromPlatform_all_cores_have_idle :
    ∀ (config : PlatformConfig),
      let s := bootFromPlatform config
      ∀ c : CoreId,
        ∃ tcb, s.objects.find? (idleThreadId c).toObjId = some (.tcb tcb) ∧
        tcb.priority = ⟨0, by decide⟩ ∧
        tcb.cpuAffinity = some c
```

*Proof.* The `bootFromPlatform` extension (SM4.G.3) installs
`idleThreadId c` for every `c ∈ allCores` as part of the boot
sequence. The proof unfolds the boot pipeline and applies
`Vector.get_replicate` for the per-core initialization. □

### 3.8 SMP-shape witness theorem

**Theorem 3.8.1** (`bootFromPlatform_smp_witness`). Replaces the
retired `bootFromPlatform_singleCore_witness`:

```lean
theorem bootFromPlatform_smp_witness :
    ∀ (config : PlatformConfig),
      let s := bootFromPlatform config
      ∀ c : CoreId,
        s.scheduler.currentOnCore c = some (idleThreadId c) ∨
        s.scheduler.currentOnCore c = none
```

*Proof.* At boot, each core's `currentOnCore` is initialized to
the idle thread (by SM4.G.3's boot extension), so the `some`
disjunct holds. Optionally, a pre-boot intermediate state has
`none`, captured by the second disjunct. □

The retired single-core witness:

```lean
-- BEFORE (single-core):
theorem bootFromPlatform_singleCore_witness :
    ∀ (s : SchedulerState),
      s.current = none ∨ ∃ tid : ThreadId, s.current = some tid

-- AFTER (RETIRED): replaced by bootFromPlatform_smp_witness above.
-- The single-core form is structurally too weak to characterize
-- the SMP shape; we retire it explicitly with an audit trail.
```

## 4. Architectural choices for SM4

### 4.1 Why path-a (Vector replacement) not path-b (additive)

Decision #3 chose path-a. Pros:
- Clean final state: no transitional `currentOnBootCore` shim
  lingering after migration.
- Path-a forces explicit `CoreId` reasoning at every callsite,
  surfacing implicit single-core assumptions early.
- The migration is mechanical: every `.current` becomes
  `.currentOnCore c` for some c.

Cons:
- ~5000-7000 LoC of theorem rewrites (vs ~2000 LoC for path-b
  with a bootCore shim).
- High volume of mechanical work; tedious.

Per maintainer choice (decision #4), accepted.

### 4.2 Why `Vector α n` (not `Array α` or `Fin n → α`)

| Option | Pros | Cons |
|--------|------|------|
| `Array α` | Built-in; O(1) random access | No compile-time length proof; OOB returns silent default |
| `List α` | Simple; total | O(n) random access |
| `Fin n → α` | Total function; clean math | Undecidable extensional equality; harder to compute |
| `Vector α n` | All three benefits | Need to bootstrap if not in Std |

`Vector α n` wins on compile-time length safety, O(1) access,
and decidable equality. Lean 4.28 has `List.Vector` and `Vector`
both available; SM4.A.1 picks the standard one.

### 4.3 Why retire the singleCore witness

The `bootFromPlatform_singleCore_witness` was a typed witness
that `SchedulerState.current : Option ThreadId` is a single
slot, not a per-core map. Under path-a, the field IS a per-core
map (`Vector (Option ThreadId) coreCount`). The witness becomes
trivially false (`current` is no longer `Option ThreadId`).

Per the implement-the-improvement rule, the witness MUST be
retired. The replacement `bootFromPlatform_smp_witness` proves
the new shape: every core has a currentOnCore that is either
none or `some (idleThreadId c)`.

### 4.4 Per-core lastTimeoutErrors

The existing field `lastTimeoutErrors : List (ThreadId ×
KernelError)` records diagnostic timeout errors from the most
recent `timerTick` run. Under SMP, each core runs its own timer
tick, so this becomes per-core:

    lastTimeoutErrors : Vector (List (ThreadId × KernelError)) coreCount

Cleared at the start of each per-core tick (SM5.D.9).

## 5. Detailed sub-task breakdown

### 5.1 Vector + PlatformBinding (SM4.A, 3 PRs, 8 sub-tasks)

| Sub | Description | Acceptance | Est |
|-----|-------------|------------|-----|
| SM4.A.1 | Vector bootstrap: use Lean core's `Array`-backed `Vector α n` (per §4.2 — **not** `List.Vector`, whose O(n) access would regress the trace harness) | `Prelude.lean`; compile-time length proof | M |
| SM4.A.2 | Vector helper theorems: `get_set_eq`, `get_set_ne`, `toList_length`, `replicate_get`, `ext`, `nodup_of_finRange` (6 lemmas, in `namespace SeLe4n.PerCoreVector` — a non-`Vector` namespace, so under the `open SeLe4n` every kernel file uses no member shadows core's `_root_.Vector`; the "length" lemma is named `toList_length`, not bare `length`, for semantic precision — it is a `Prop` lemma, not a count) | All proven by `simp`/`decide`/`induction`/`rw` | M |
| SM4.A.3 | Runtime efficiency check: Vector compiles to Array | Trace `lake exe sele4n` shows acceptable per-core access cost | T |
| SM4.A.4 | PlatformBinding `coreCount` field already added in SM0.G; SM4.A.4 confirms RPi5 instance | RPi5 = 4 | T |
| SM4.A.5 | Sim instance updates (single-core sim + 4-core SMP sim) | Both compile | T |
| SM4.A.6 | `CoreId := Fin PlatformBinding.coreCount` (from SM0.E) | Recap; no new code | T |
| SM4.A.7 | `bootCoreId` typeclass field (from SM0.G) | Recap | T |
| SM4.A.8 | `allCores`, `allCores_length`, `allCores_nodup` (from SM0.E) | Recap | T |

**Note**: Most SM4.A items recap SM0 deliverables. SM4.A.1 + .2
are the new Lean-side work.

**Size**: M-total (~150 LoC of new Lean across A.1 + A.2).

### 5.2 SchedulerState path-a replacement (SM4.B, 5 PRs, 15 sub-tasks)

| Sub | Description | Acceptance | Est |
|-----|-------------|------------|-----|
| SM4.B.1 | Replace `current` field with `Vector (Option ThreadId) coreCount` | Field replaced; default = `Vector.replicate _ none` | M |
| SM4.B.2 | Replace `runQueue` | Replaced | M |
| SM4.B.3 | Replace `replenishQueue` | Replaced | M |
| SM4.B.4 | Replace `activeDomain` | Replaced | S |
| SM4.B.5 | Replace `domainTimeRemaining` | Replaced | S |
| SM4.B.6 | Replace `domainScheduleIndex` | Replaced | S |
| SM4.B.7 | Replace `lastTimeoutErrors` | Replaced | S |
| SM4.B.8 | Add 7 per-core accessor helpers | All compile | M |
| SM4.B.9 | `default_state_perCoreInitialized` theorem | Per §3.6 | M |
| SM4.B.10 | `SchedulerState.ext` per-core extensionality | Per §3.3 | M |
| SM4.B.11 | `Repr` instance updated | Compiles | T |
| SM4.B.12 | `BEq` instance updated | Compiles; LawfulBEq if applicable | S |
| SM4.B.13 | `Inhabited` instance updated | Default exists | T |
| SM4.B.14 | Immediate-caller sites in `Model/State.lean` | All compile | M |
| SM4.B.15 | Regression test: single-core trace fixture preserved | `main_trace_smoke.expected` byte-identical at single-core scenario | M |

**Critical insight for SM4.B.15**: even though the type changes,
the runtime behavior at the single-core scenario (boot core only)
must produce a byte-identical trace. This is the regression
safety net.

### 5.3 Scheduler invariants migration (SM4.C, 10 PRs, 30 sub-tasks)

Each sub-task migrates ~10-30 theorems from a single Scheduler
invariant file. Pattern (from §3.4):

| Sub | File | # theorems | Est |
|-----|------|-----------:|-----|
| SM4.C.1 | `Scheduler/Invariant/CurrentThread.lean` | ~12 | L |
| SM4.C.2 | `Scheduler/Invariant/RunQueue.lean` | ~15 | L |
| SM4.C.3 | `Scheduler/Invariant/Domain.lean` | ~10 | L |
| SM4.C.4 | `Scheduler/Invariant/CBS.lean` | ~8 | L |
| SM4.C.5 | `Scheduler/Operations/Core.lean` | ~20 sites | L |
| SM4.C.6 | `Scheduler/Operations/Preservation.lean` (3779 LoC) | ~30 sites | XL |
| SM4.C.7 | `Scheduler/Operations/Selection.lean` | ~15 sites | L |
| SM4.C.8 | `Scheduler/RunQueue.lean` (883 LoC) | ~25 sites | L |
| SM4.C.9 | `Scheduler/PriorityInheritance/*.lean` | ~20 sites | L |
| SM4.C.10 | `Scheduler/SchedContext/*.lean` | ~15 sites | L |
| SM4.C.11 | `Scheduler/Liveness/*.lean` (incl. WCRT) | ~10 sites | M |
| SM4.C.12 | `Scheduler/Domain/*.lean` | ~8 sites | M |
| SM4.C.13 | `Scheduler/CBS/*.lean` | ~10 sites | M |
| SM4.C.14 | `Scheduler/Timer/*.lean` | ~12 sites | M |
| SM4.C.15 | `Scheduler/Suspend/*.lean` | ~8 sites | M |
| SM4.C.16 | `Scheduler/Yield/*.lean` | ~5 sites | S |
| SM4.C.17 | `Scheduler/RoundRobin/*.lean` | ~5 sites | S |
| SM4.C.18 | `Scheduler/PIP/Compute.lean` | ~12 sites | M |
| SM4.C.19 | `Scheduler/PIP/Discipline.lean` | ~10 sites | M |
| SM4.C.20 | `Scheduler/PIP/Liveness.lean` | ~8 sites | M |
| SM4.C.21 | `Scheduler/PIP/BlockingGraph.lean` | ~10 sites | M |
| SM4.C.22 | `Scheduler/Operations/Reschedule.lean` | ~10 sites | M |
| SM4.C.23 | `Scheduler/Operations/Wake.lean` | ~8 sites | M |
| SM4.C.24 | `Scheduler/Operations/Block.lean` | ~6 sites | S |
| SM4.C.25 | `Scheduler/Operations/Donate.lean` | ~10 sites | M |
| SM4.C.26 | `Scheduler/SchedulerState.lean` | ~12 sites | M |
| SM4.C.27 | `Scheduler/EffectivePriority.lean` | ~8 sites | M |
| SM4.C.28 | `Scheduler/EffectiveSchedParams.lean` | ~8 sites | M |
| SM4.C.29 | Aggregate invariant `schedulerInvariant_perCore` | New aggregate | L |
| SM4.C.30 | Cross-core `schedulerInvariant_perCore_pairwise` | Theorem | M |

**Migration discipline**: each PR (covering 1-3 sub-tasks)
follows the same pattern:

1. `git grep "scheduler.current"` to find single-core callsites.
2. Replace each with `scheduler.currentOnCore <c>` where `<c>`
   is the appropriate CoreId (often `bootCoreId` for boot
   theorems; `currentCoreId` for runtime theorems).
3. Update theorem signatures to take `(c : CoreId)` parameter
   where the property is per-core.
4. Run `lake build` to identify compilation errors.
5. Fix each error site.
6. Verify all preservation theorems still close.

**Total LoC for SM4.C**: ~3500-5000 LoC of mechanical rewrites
across ~30 sub-tasks. The bulk of WS-SM's tedium lives here.

### 5.4 Cross-subsystem migrations (SM4.D, 8 PRs, 22 sub-tasks)

Same migration pattern for cross-subsystem theorems reading
SchedulerState.

| Sub | File / files | # sites | Est |
|-----|--------------|--------:|-----|
| SM4.D.1 | `IPC/Operations/*.lean` (~12 sites) | 12 | L |
| SM4.D.2 | `IPC/Invariant/*.lean` | 8 | M |
| SM4.D.3 | `Capability/Operations.lean` | 5 | M |
| SM4.D.4 | `Capability/Invariant/*.lean` | 4 | M |
| SM4.D.5 | `Lifecycle/Operations.lean` | 3 | S |
| SM4.D.6 | `Lifecycle/Invariant/*.lean` | 3 | S |
| SM4.D.7 | `Service/Operations.lean` | 2 | S |
| SM4.D.8 | `Service/Invariant/*.lean` | 2 | S |
| SM4.D.9 | `Architecture/Invariant.lean` | 8 | M |
| SM4.D.10 | `Architecture/ExceptionModel.lean` | 4 | M |
| SM4.D.11 | `Architecture/InterruptDispatch.lean` | 4 | M |
| SM4.D.12 | `InformationFlow/Operations/*.lean` | 10 | L |
| SM4.D.13 | `InformationFlow/Projection.lean` | 5 | M |
| SM4.D.14 | `InformationFlow/Invariant/*.lean` | 8 | M |
| SM4.D.15 | `Model/State.lean` callsites | 15 | M |
| SM4.D.16 | `Model/FreezeProofs.lean` | 6 | M |
| SM4.D.17 | `Platform/Boot.lean` | 8 | M |
| SM4.D.18 | `Platform/FFI.lean` | 4 | S |
| SM4.D.19 | `CrossSubsystem.lean` (3309 LoC) | 12 | L |
| SM4.D.20 | `API.lean` | 6 | M |
| SM4.D.21 | `Kernel/Architecture/VSpace.lean` | 4 | M |
| SM4.D.22 | `Kernel/Architecture/SyscallEntry.lean` | 4 | M |

**Total LoC for SM4.D**: ~1500-2500 LoC of cross-subsystem
migrations.

### 5.5 Witness retirement + replacement (SM4.E, 2 PRs, 5 sub-tasks)

| Sub | Description | Acceptance | Est |
|-----|-------------|------------|-----|
| SM4.E.1 | Retire `bootFromPlatform_singleCore_witness` | Theorem deleted from `CrossSubsystem.lean` | T |
| SM4.E.2 | Add `bootFromPlatform_smp_witness` | Per §3.8 | M |
| SM4.E.3 | AN12-B inventory entry 7 (`architecture_singleCoreOnly_smpLatent`): `smpDischarge` becomes "implemented in SM4 path-a"; `sourceTheorem` points to `bootFromPlatform_smp_witness` | Inventory updated | S |
| SM4.E.4 | AN12-B inventory entry 8 (`bootFromPlatform_currentCore_is_zero_smpLatent`): same treatment | Inventory updated | S |
| SM4.E.5 | Add `smpRetiredInventory` aggregator (8 entries, all retired). Pin size at 8. | New aggregator + size witness | M |

### 5.6 Per-core invariant suite (within SM4.C.29 + .30)

Two aggregate theorems wrap the per-core invariants:

```lean
def schedulerInvariant_perCore (s : SystemState) (c : CoreId) : Prop :=
  (currentOnCore_validThreadIfSome s c) ∧
  (runQueueOnCore_wellFormed s c) ∧
  (schedContextRunQueueConsistent_perCore s c) ∧
  (priorityInheritance_perCore s c) ∧
  (activeDomainOnCore_isInDomainSchedule s c) ∧
  (replenishQueueOnCore_wellFormed s c)

theorem schedulerInvariant_perCore_aggregateForall :
    ∀ (s : SystemState),
      (∀ c : CoreId, schedulerInvariant_perCore s c) ↔
      schedulerInvariant_smp s
```

The system-wide aggregate `schedulerInvariant_smp` is the
`∀ c, ...` form; the per-core form (`schedulerInvariant_perCore
s c`) is the slice at a specific core. Both are useful: the
per-core form for proving preservation by per-core operations;
the system-wide form for cross-subsystem composition.

**Theorem**: `schedulerInvariant_perCore_pairwise`. Different
cores' per-core invariants are *independent* — proving one
doesn't constrain the other. Formally:

```lean
theorem schedulerInvariant_perCore_pairwise :
    ∀ (s : SystemState) (c₁ c₂ : CoreId),
      c₁ ≠ c₂ →
      schedulerInvariant_perCore s c₁ ↔ schedulerInvariant_perCore s c₁
      -- (Trivially true; the substantive content is that c₂'s
      -- predicate doesn't appear in c₁'s.)
```

This is essentially a documentation theorem; the per-core
fields' `Vector` indexing ensures distinctness.

## 6. Verification strategy for SM4

### 6.1 What SM4 proves

~50 substantive new/migrated theorems. Major ones:

| # | Theorem | Sub-task |
|---|---------|----------|
| 1 | `default_state_perCoreInitialized` | SM4.B.9 |
| 2 | `SchedulerState.ext` per-core | SM4.B.10 |
| 3 | `bootFromPlatform_smp_witness` | SM4.E.2 |
| 4-50 | Migrated scheduler+IPC+capability+...theorems | SM4.C, SM4.D |

### 6.2 What SM4 assumes

- Lean Std `Vector` operations and their length theorems.
- SM3's lock-set discipline (`lockSetHeld` precondition implicit
  in migrated theorems).

No new Lean axioms.

### 6.3 Tests

- **Tier 1 (build)**: `lake build` (256 jobs) green across all
  60+ migrated files.
- **Tier 2 (trace)**: `main_trace_smoke.expected` byte-identical
  at the single-core scenario (regression safety).
- **Tier 3 (invariant)**: All per-core invariant surface
  anchors.
- **Tier 4 (nightly)**: QEMU `-smp 4` boot trace
  (`smp_4core_boot.expected`).

## 7. Risk inventory for SM4

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Migration introduces a `currentOnCore` typo | HIGH | LOW (caught by build) | `lake build` catches; per-PR review |
| Single-core regression: existing scenarios diverge | LOW | HIGH | SM4.B.15 trace fixture byte-identical |
| Cross-subsystem dependency missed | MED | HIGH | grep audit + per-file build |
| Vector overhead degrades single-core perf | LOW | MED | Lean compiles Vector → Array at runtime |
| Migration exhausts maintainer capacity | HIGH | MED (calendar slip) | Phase divided into 38 sub-tasks, each independently shippable |
| Theorem migration changes proof structure | LOW | MED (re-prove) | Pattern from §3.4 is purely textual; proofs unchanged |
| `Vector.get` panics on OOB | ZERO (Fin numCores) | — | Type-system prevents OOB |
| `bootFromPlatform_smp_witness` proof needs new infrastructure | MED | LOW | Proof unfolds Vector.replicate; well-known idiom |

## 8. Acceptance gate for SM4

- [ ] Vector bootstrap with 6+ helper theorems.
- [ ] All 7 SchedulerState fields replaced with Vector.
- [ ] All 7 per-core accessors defined.
- [ ] `default_state_perCoreInitialized` proven.
- [ ] `SchedulerState.ext` per-core proven.
- [ ] All 30 SM4.C sub-tasks complete: ~110 scheduler theorems migrated.
- [ ] All 22 SM4.D sub-tasks complete: cross-subsystem migrations.
- [ ] `bootFromPlatform_singleCore_witness` retired.
- [ ] `bootFromPlatform_smp_witness` proven.
- [ ] AN12-B inventory entries 7 + 8 marked as "implemented in SM4".
- [ ] `smpRetiredInventory` aggregator added.
- [ ] Tier 1..3 green.
- [ ] Tier 2 trace byte-identical at single-core scenario.
- [ ] Aggregate SM4 closure CHANGELOG entry.

## 9. Cross-references

- **Master overview**: [`SMP_MULTICORE_COMPLETION_PLAN.md`](SMP_MULTICORE_COMPLETION_PLAN.md)
- **Prerequisites**: [`SMP_FOUNDATIONS_PLAN.md`](SMP_FOUNDATIONS_PLAN.md)
- **Parallel phase**: [`SMP_PER_OBJECT_LOCKS_PLAN.md`](SMP_PER_OBJECT_LOCKS_PLAN.md)
- **Next phase**: [`SMP_PER_CORE_SCHEDULER_PLAN.md`](SMP_PER_CORE_SCHEDULER_PLAN.md)

## 10. Theorem catalogue for SM4

~50 theorems total. Categories:

- 3 new structural theorems (default-init, extensionality, SMP witness).
- ~30 migrated scheduler invariants.
- ~17 migrated cross-subsystem invariants.

Full catalogue maintained in `docs/audits/SMP_THEOREM_INDEX.md`
once WS-SM opens.

## Appendix A — Verification commands

```bash
source ~/.elan/env

# Build:
lake build  # 256 jobs

# Tier 1..3:
./scripts/test_full.sh

# Tier 2 trace regression:
diff tests/fixtures/main_trace_smoke.expected \
     <(lake exe sele4n --single-core 2>/dev/null)

# grep audit: no remaining .current (singular):
grep -rn "scheduler.current[^O]" SeLe4n/ tests/ |
  grep -v "currentOnCore\|currentCoreId" |
  echo "Remaining sites: $(wc -l)"
```

## Appendix B — Sub-task dependency graph

```
SM4.A (Vector + Platform)    independent
SM4.B (SchedulerState shape) needs SM4.A
SM4.C (Scheduler migrations) needs SM4.B
SM4.D (Cross-subsystem)      needs SM4.B (file by file)
SM4.E (Witness retire)       needs SM4.B
```

SM4.C and SM4.D proceed in parallel after SM4.B; ~38 sub-tasks
can be done by multiple contributors concurrently (each in its
own file).

---

*SM4 is the largest WS-SM phase by LoC. The work is highly
mechanical (textual rewrites following §3.4 pattern) but the
volume is substantial. Decision #4 (path-a, no compat shim)
forces explicit CoreId reasoning at every callsite, which is the
right architectural choice but extends the timeline.*

## 11. Implementation progress + continuation (SM4.B)

### 11.1 Landed: SM4.B foundation (green checkpoint)

The SM4.B foundation has landed as the first green checkpoint of the
path-a migration (`SeLe4n/Model/State.lean` +
`tests/PerCoreSchedulerStateSuite.lean`):

- **SM4.B.8** — the seven per-core accessors (`currentOnCore`,
  `runQueueOnCore`, `replenishQueueOnCore`, `activeDomainOnCore`,
  `domainTimeRemainingOnCore`, `domainScheduleIndexOnCore`,
  `lastTimeoutErrorsOnCore`), each `(s : SchedulerState) → (c : CoreId) → …`.
- **SM4.B.9** — `default_state_perCoreInitialized` (plan §3.6).
- **SM4.B.10** — `SchedulerState.ext_perCore` (plan §3.3; named `ext_perCore`
  to avoid the structure's auto-generated `SchedulerState.ext`).
- Tier-2 runtime suite (`lake exe per_core_scheduler_state_suite`) + Tier-3
  surface anchors, both wired.

### 11.2 Execution model: two-phase, green-checkpoint, bottom-up

A literal field-type replacement (`Option ThreadId → Vector … numCores`)
is a single global break: ~700 reads + ~72 record-update writes + the
entire scheduler/IPC/info-flow/lifecycle/arch proof surface (~58 files)
go red at once. To keep every commit green (decision: green-checkpoint
commits), the migration is split:

- **Phase 1 (read migration, green-incremental).** The accessors are first
  introduced as **scalar wrappers** (the `c : CoreId` argument is ignored
  while the underlying field is still scalar), tagged `@[simp]`. Every
  `s.scheduler.<field>` read migrates to `s.scheduler.<field>OnCore bootCoreId`
  (single-core ⇒ boot core). Because the wrapper is *definitionally equal*
  to the field, this phase is **soundness-safe**: no proof's meaning can
  change, only build-greenness — so a regression is always a build failure,
  never a silent incorrectness.
- **Phase 2 (field flip, localized).** Flip the seven field *types* to
  `Vector α numCores`; change only the 14 accessor/setter definitions
  (`fieldOnCore s c := s.field.get c`); fix the ~72 record-update writes
  (`{ s with field := s.field.set bootCoreId.val v bootCoreId.isLt }`);
  re-discharge B.9/B.10 substantively via `PerCoreVector.replicate_get` /
  `.ext`; retire `bootFromPlatform_singleCore_witness` and add
  `bootFromPlatform_smp_witness` (SM4.E); restore the byte-identical
  single-core trace (SM4.B.15).

### 11.3 Validated migration recipe (per file, phase 1)

1. Add `open SeLe4n.Kernel.Concurrency (bootCoreId)` to the file.
2. Migrate **statement-level** reads: `EXPR.scheduler.<field>` →
   `EXPR.scheduler.<field>OnCore bootCoreId`. Parenthesise when the result
   is further projected: `EXPR.scheduler.runQueue.insert …` →
   `(EXPR.scheduler.runQueueOnCore bootCoreId).insert …`.
3. Leave `.runnable` (the `runQueue.toList` abbrev) **unchanged** — its
   definition absorbs the boot-core slice in phase 2 (≈336 callsites need
   no edit).
4. Repair proofs: where a migrated hypothesis (`…OnCore bootCoreId`) meets a
   still-scalar operation body, add `simp only [SchedulerState.<field>OnCore]`
   to normalise both sides to the scalar field. Leave proof-internal reads
   that are *coupled to an un-migrated operation body's shape* (e.g. a
   `show` whose `rw` lemma pins the queue via a generated `hNotMem`) — those
   align once the operation body migrates.
5. `lake build <Module>` green before moving on.

### 11.4 Ordering + cascade (empirical)

- Migrate **bottom-up** (providers before consumers): a consumer's migrated
  goal (`…OnCore`) only matches a provider's lemma once the provider's
  statement is migrated.
- The cascade per migrated file is **small**: most consumers use a migrated
  lemma via `exact`/`apply` (defeq-safe, unaffected); only syntactic
  `rw`/`simp [lemma]` consumers break. A pilot migration of
  `IPC/Operations/SchedulerLemmas.lean` broke exactly **one** consumer
  (`IPC/Invariant/EndpointPreservation.lean`).
- The first *scheduler-subsystem* checkpoint is necessarily large: the
  lowest files (`Scheduler/Operations/Core.lean`,
  `Scheduler/Invariant.lean`) have the widest consumer fan-out
  (`Scheduler/Operations/Preservation.lean` ≈227 refs, then IPC/lifecycle),
  so that checkpoint should be planned as a coupled unit, not file-by-file.

### 11.5 Remaining read-migration set (bottom-up, by subsystem)

~58 files, ≈700 reads. Heaviest: `Scheduler/Operations/Preservation.lean`
(227), `InformationFlow/Invariant/Operations.lean` (58),
`Scheduler/Operations/Core.lean` (37), `Scheduler/Invariant.lean` (29),
`Scheduler/PriorityInheritance/Preservation.lean` (24),
`Testing/MainTraceHarness.lean` (23). Suggested layer order: Model
(`Builder`, `FrozenState`, `FreezeProofs`, the `allTablesInvExtK` reads in
`State`) → Scheduler (`Operations/*`, `Invariant`, `PriorityInheritance/*`,
`Liveness/*`) → SchedContext → IPC → Lifecycle → Capability → Architecture →
InformationFlow → Service → CrossSubsystem → API → Platform → Testing →
`tests/`.

### 11.6 Execution refinements discovered in-flight (SM4.C grind)

The global read-migration (all 56 files in one consistent pass) was applied
with a UTF-8-safe, always-parenthesising transform:

```
# read-migration (per file): projected gets parens+.method, terminal gets parens.
RC="(\([^()]*\)|[A-Za-z_][A-Za-z0-9_.'₀₁₂₃₄₅₆₇₈₉ₐₑₒₓₕₖₗₘₙₚₛₜ′]*)"
FLD="(current|runQueue|replenishQueue|activeDomain|domainTimeRemaining|domainScheduleIndex|lastTimeoutErrors)"
perl -CSD -Mutf8 -i -pe \
  "s/${RC}\\.scheduler\\.${FLD}\\.(?=[A-Za-z])/(\$1.scheduler.\$2OnCore bootCoreId)./g; \
   s/${RC}\\.scheduler\\.${FLD}\\b(?!\\.)/(\$1.scheduler.\$2OnCore bootCoreId)/g;" FILE
```

Always-parenthesise (terminal too): argument position cannot be detected
from following context (e.g. `exact lemma st.scheduler.current` at line end),
so `(EXPR.fieldOnCore bootCoreId)` is the only universally-correct output.
The Unicode subscript class is required for `s₁`/`s₂` receivers in
information-flow proofs (Perl `\w` excludes subscripts). Each file also gets
`open SeLe4n.Kernel.Concurrency (bootCoreId)`.

**Binding decision — accessors are NOT `@[simp]`.** Empirically, `@[simp]`
on the seven accessors gives *more* breakage in the reduction-heavy
operation files (Preservation: 165 errors with `@[simp]` vs 61 without),
because it unfolds the accessor in goals while leaving explicit
`…OnCore`-stated hypotheses/`cases`-scrutinees folded, causing type
mismatches / dependent-elimination / function-expected failures. Plain
`def` accessors keep goals folded (so hypotheses match natively) and the
fixes are the simpler "add the accessor to the `simp` set" kind. This also
matches the phase-2 end state (the accessor is a folded abstraction).

**Proof-repair fix patterns (no-`@[simp]`):**
1. *Reduction proof* (`simp [pred]` where `pred` reads an accessor and the
   match must reduce): add `SchedulerState.<field>OnCore` to the `simp`.
2. *`simp [queueCurrentConsistent, hCur]`* (or any scalar predicate vs an
   `…OnCore`-stated hypothesis): normalise the hypothesis first —
   `simp only [SchedulerState.currentOnCore] at hCur` — so it matches the
   scalar predicate body.
3. *`cases hPick : <op with …OnCore args>`* then `simp [hPick]`: normalise
   `hStep` to scalar first (`simp only [SchedulerState.runQueueOnCore,
   SchedulerState.activeDomainOnCore] at hStep`) and `cases` on the scalar
   form; the cases scrutinee is proof-internal (phase-2 reproves it).
4. *Bare-binder reads* (`s.current` inside a `(s : SchedulerState)`
   predicate such as `queueCurrentConsistent`) and the **freeze path**
   (`freezeScheduler` reading `sched.current` to populate the scalar
   `FrozenSchedulerState`): LEAVE scalar in phase-1. Migrating
   `queueCurrentConsistent`'s body rippled to 165 Preservation proofs — its
   bare-binder read is a phase-2 item (with `FrozenSchedulerState`'s own
   per-core treatment, SM4.D.16). Consumers with `…OnCore` hypotheses are
   fixed by pattern 2, not by migrating the predicate.
5. *`rw [← hCur] at hStep`* and similar reverse-rewrites / `omega` /
   dependent-elimination failures: genuinely data-flow-dependent; require
   per-proof analysis (not a mechanical accessor-add). These are the
   slow core of the SM4.C grind.

**Status at this checkpoint:** foundation committed (SM4.B.8/9/10 + suite);
the global read-migration is applied in the working tree; the Model layer
(`State`, `FrozenState`) and Scheduler core
(`Invariant`, `Operations/Selection`, `Projection`, `RuntimeContract`,
`IPC/Operations/SchedulerLemmas`) are green; `Operations/Preservation.lean`
has ~40 remaining proof-repairs (mix of patterns 1–3 and the hard pattern-5
cases), and the IPC/Lifecycle/Capability/InformationFlow/Service/
CrossSubsystem/API/Platform/Testing/`tests/` layers are not yet built. Per
the entanglement (§11.4), the working tree is uncompilable until the whole
read-migration is green; the recipe above makes re-derivation fast if the
tree is lost.

### 11.7 In-progress migration WIP patch (resumption)

Because the migration is uncommittable-until-fully-green (§11.4) yet the
working tree must be clean between sessions, the exact in-progress state is
preserved as a re-appliable patch:
`docs/dev_history/SM4B_phase1_migration.wip.patch` (56 files; the global
read-migration + `@[simp]`-off + all lower-layer proof fixes). To resume:

```
git apply docs/dev_history/SM4B_phase1_migration.wip.patch
```

State captured in the patch: Model + Scheduler-core green; `Operations/
Preservation.lean` reduced to ~35 proof-repairs remaining (the hard core —
`rw [← hCur]` reverse-rewrites, `omega`, `Type mismatch`, the line-1833
multi-goal cluster); the IPC/Lifecycle/Capability/InformationFlow/Service/
CrossSubsystem/API/Platform/Testing/`tests/` layers not yet built. Delete
this patch once the migration lands green. (The §11.6 recipe regenerates the
mechanical bulk if the patch is ever lost.)

> **SUPERSEDED (phase 1 LANDED — see §11.8).** The WIP patch above
> captured a mid-grind red state and is now obsolete: phase 1 is fully
> green and committed, so the in-tree source is the canonical record.
> The patch file may be deleted.

### 11.8 Phase 1 LANDED (green checkpoint — accessor read-migration)

Phase 1 (per §11.2 — introduce the per-core accessors as scalar wrappers
and route every scheduler-field *read* through them; field types stay
scalar) is **complete and green**.  Committed + pushed to branch
`claude/sharp-carson-V2Y59`:

- `760ecea` — the read-migration across all 56 affected `.lean` files
  (Model, Scheduler, IPC, Lifecycle, Capability, Architecture,
  InformationFlow, SchedContext, Service, Platform, FrozenOps, Testing,
  and the `tests/` suites).
- `2c2cc8e` — regenerated `docs/codebase_map.json` (docs-sync gate green).

**Validation at the checkpoint**: whole tree green — 320 default-build
jobs + every modified module + the staged anchor (`Platform.Staged`) +
179 test-module jobs, all zero-error.  Tier 0–2 smoke: hygiene + build +
trace fixture (**227/227 matched** — runtime behaviour byte-identical,
confirming the accessors are faithful scalar wrappers) + every Tier-2
suite + Rust conformance, all green.  Pre-commit hook (43 modules built +
sorry check) passed; version-sync gate passed (26 sites, v0.31.11).

**Two decisions resolved during the phase-1 grind** (both phase-2-correct,
so they carry forward unchanged):

1. **`queueCurrentConsistent` migrated to accessor form**
   (`match s.currentOnCore bootCoreId with …`), matching its sibling
   bundle invariants (`currentThreadValid`, `currentThreadIpcReady`,
   `currentNotEndpointQueueHead`) and every `*_scheduler_current`
   rewrite lemma.  Earlier attempts left it scalar (an "island") which
   forced scalar↔accessor bridging at every IPC boundary; migrating it
   is both less code and the shape phase-2 requires.  Consumer/builder
   sites that pattern-match on it now use `simp [queueCurrentConsistent,
   SchedulerState.currentOnCore, …]` (builders) or drop the prior
   `simp only [SchedulerState.currentOnCore] at hCur` normalize
   (consumers — `hCur` stays accessor).
2. **Frozen-state false positives corrected.** The bulk migration perl
   matched `.scheduler.current` etc. on `FrozenSystemState` /
   `FrozenSchedulerState` values too, but the frozen variant has **no**
   per-core accessors (its fields are `current`, `activeDomain`, …).
   Reverted to the raw frozen fields in `Model/FreezeProofs.lean`,
   `Kernel/FrozenOps/{Core,Operations}.lean`, and the frozen-state test
   suites (`FrozenStateSuite`, `FreezeProofSuite`, `TwoPhaseArchSuite`,
   `FrozenOpsSuite`).  Rule for phase 2: frozen state is **not** part of
   the per-core `Vector` flip — `FrozenSchedulerState` stays scalar.

**Phase 2 (remaining for full SM4.B — the field-type flip).** Still to do
to reach the path-a end state (per §3.1–§3.4):

- Flip the 7 `SchedulerState` fields from scalar to `Vector α numCores`
  (`current`, `runQueue`, `activeDomain`, `domainTimeRemaining`,
  `domainScheduleIndex`, `replenishQueue`, `lastTimeoutErrors`); keep
  `domainSchedule` / `configDefaultTimeSlice` system-wide.
- Re-point each accessor from the scalar wrapper
  (`def currentOnCore s _c := s.current`) to the indexed form
  (`s.current.get c`), and introduce the per-core **setters**
  (`setCurrentOnCore` etc.) the operation bodies' record-updates flip to.
- Re-prove the `get_set_eq` / `get_set_ne` reductions at every literal
  the phase-1 proofs currently discharge by record-update iota (the
  `SeLe4n.PerCoreVector` lemmas land this: §3.2).
- Rework the `SchedulerState.runnable` abbrev (currently `s.runQueue.toList`
  on the raw field) to `(s.runQueueOnCore bootCoreId).toList`.
- SM4.E witness retire/replace; byte-identical trace fixture
  (single-core boot must still emit 227/227); full doc sync + the PR
  version bump.

The phase-1 accessor seam means phase 2 touches the 9 `SchedulerState`
field sites + the accessor/setter defs + the per-literal `get_set`
reductions — the ~768 read sites do **not** change again (they already
route through the accessors).

### 11.9 Phase 2 in progress — foundation LANDED, proof cascade pending

Phase 2 (the field-type flip from scalar to `Vector α numCores`) has its
**foundation complete and green**; the remaining work is the (mechanical
but voluminous) proof-cascade re-prove.  The in-progress migration is
preserved as a re-appliable patch:
`docs/dev_history/SM4B_phase2_migration.wip.patch` (~1038 lines, 12
files).  To resume:

```
git apply docs/dev_history/SM4B_phase2_migration.wip.patch
```

**Foundation LANDED (green in the patch)**:

- **`SeLe4n/Model/State.lean`**: the 7 per-core `SchedulerState` fields
  flipped scalar → `Vector α numCores` with `Vector.replicate numCores
  <neutral>` defaults (`runQueue`, `current`, `activeDomain`,
  `domainTimeRemaining`, `domainScheduleIndex`, `replenishQueue`,
  `lastTimeoutErrors`; `domainSchedule` / `configDefaultTimeSlice` stay
  system-wide).  Accessors flipped scalar-wrapper → `s.field.get c`.
  Added 7 per-core **setters** `set<Field>OnCore (c) (v) := { s with
  field := s.field.set c.val v c.isLt }` (the clean write API).
  `ext_perCore` re-proved via `PerCoreVector.ext`; `runnable` →
  `(s.runQueueOnCore bootCoreId).toList`; `Inhabited` → `{}`;
  `default_state_perCoreInitialized` via `PerCoreVector.replicate_get`.
- **The 63-lemma `@[simp]` store/load algebra** (State.lean): for each
  (setter, accessor) pair, `set<X>OnCore_<x>OnCore_self : (s.set<X>OnCore
  c v).<x>OnCore c = v` (7) + cross-field `set<X>OnCore_<y>OnCore :
  (s.set<X>OnCore c v).<y>OnCore c' = s.<y>OnCore c'` (42) +
  system-wide-field preservation (14).  Plus `PerCoreVector.get_set_eq`
  / `replicate_get` promoted to `@[simp]`.  This is the lever that makes
  post-write reads reduce automatically under `simp`.
- **Operation bodies migrated to setters (green)**: `setCurrentThread`
  (State), `removeRunnable` + `ensureRunnable` (Endpoint),
  `contextSwitchState` (Adapter), `updatePipBoost` (Propagate),
  `freezeScheduler` reads → accessors (FrozenState), and **all** of
  `Scheduler/Operations/Core.lean` (`schedule`, `handleYield`,
  `timerTick`, `timerTickWithBudget`, `processReplenishmentsDue`,
  `switchDomain` 5-field chain, `scheduleDomain`).
- **Green modules**: `Model.State`, `Scheduler.Operations.Core`,
  `IPC.Operations.SchedulerLemmas` (all frame lemmas re-proved via the
  algebra + `removeRunnable_runQueueOnCore` frame lemma),
  `Platform.RPi5.RuntimeContract`, `Scheduler.PriorityInheritance.Propagate`,
  `Model.FrozenState`, `Kernel.Architecture.Adapter`,
  `Kernel.InformationFlow.Projection`, `Kernel.Scheduler.Invariant`
  (the directly-State-importing frontier).

**Remaining (the proof cascade)**:

- `Scheduler/Operations/Preservation.lean` (~103 errors): the phase-1
  preservation proofs reduced record-update *literals* via `simp only
  [<accessor>]` + iota.  With setter-states the reduction needs the
  `@[simp]` algebra — change those `simp only [<accessor>]` to `simp
  [<accessor>]` (full simp picks up the algebra) or add the specific
  `set<X>OnCore_<y>OnCore` lemma.  All proof-side scheduler *literals*
  in this file are already converted to setter form in the patch; the
  residue is reduction-tactic updates.
- The downstream cascade: `Lifecycle/Operations/CleanupPreservation`,
  `PriorityInheritance/Preservation`, then (bottom-up) the
  IPC/Lifecycle/Capability/InformationFlow/Service/SchedContext/
  CrossSubsystem/API/Platform/Testing/`tests/` layers — each re-proving
  its scheduler-touching proofs via the same pattern (and converting any
  residual write sites to setters).

**Recipe** (per file): (1) convert any `{ X.scheduler with field := V }`
write to `X.scheduler.set<Field>OnCore bootCoreId (V)` (single-line — the
structure-update parser stops a multi-line value indented below the
value-start column); (2) for proofs that read a setter-written field,
prefer `simp [...]` over `simp only [...]` so the `@[simp]` algebra fires,
or add the explicit `set<X>OnCore_<y>OnCore` / `get_set_eq` lemma.

**SM4.E + closure** (after the cascade is green): retire
`bootFromPlatform_singleCore_witness`, add `bootFromPlatform_smp_witness`,
confirm the byte-identical single-core trace fixture (227/227), full doc
sync + version bump.
