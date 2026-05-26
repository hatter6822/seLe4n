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
| SM4.A.2 | Vector helper theorems: `get_set_eq`, `get_set_ne`, `toList_length`, `replicate_get`, `ext`, `nodup_of_finRange` (6 lemmas; the "length" lemma was implemented as `toList_length`, not bare `length`, so it does not make `v.length` resolve to a `Prop` under the `open SeLe4n` every kernel file uses) | All proven by `simp`/`decide`/`induction`/`rw` | M |
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
