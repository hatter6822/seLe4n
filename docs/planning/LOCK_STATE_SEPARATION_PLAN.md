# WS-LS — Lock state separated from kernel state

> **Workstream**: WS-LS (the lock words leave the kernel state; the bracket
> becomes a ghost the compiled kernel never runs)
> **Status**: **IN FLIGHT** — registered at `v0.36.60`; LS0.1 at `v0.36.62`;
> LS1.1 at `v0.36.63` (the ghost module beside the per-object layer).
> Decided by the maintainer on 2026-10-07 ("separate by type"; "if there is a
> better option, go that route" — §2 records the option taken and the ones
> not).  Runs beside WS-CV (disjoint files: WS-CV owns the register context
> and the entry/exit wrappers' *context* arguments; WS-LS owns the brackets
> and the lock words) and before WS-CB, whose lock-set rows (CBS plan §4.12)
> then declare footprints into the ghost layer rather than into object fields.
> **Audited cut**: the local head after CV0 (`v0.36.59`), from which every
> figure and `file:line` below was read; a row re-reads what it depends on
> when it starts.
> **Phases**: LS0..LS3, numbered in execution order; the rows are §4 and no
> count of them is written anywhere else.  **Prefix**: `LS` (`ls<digit>`
> matches no identifier under `SeLe4n/`, `tests/`, `rust/`, `scripts/` at the
> audited cut).
> **Layout**: §1 what and why; §2 the decision; **§3 the specification the
> rows point into**; §4 the schedule; §5 proof obligations; §6 risks and the
> decisions not taken; §7 the anchors touched.

## 1. Goal

Every committed kernel entry today runs its transition inside a lock bracket
that writes lock words into the kernel state and never reaches the hardware:

- The syscall seam runs `Concurrency.runBracketed objectLockBracketDomain`
  (`SyscallDispatchEntry.lean:645-660`): resolve the footprint
  (`declaredUnifiedLockSetForAbiEntry`, `SyscallSchedFootprint.lean:2679`),
  acquire it, re-resolve, check it is held, run the step, unwind
  (`LockBracket.lean:123-135`).  The timer tick and the reschedule entries run
  the same bracket (`SchedLockBracket.lean:204,212`); `suspend_thread_cross_core`
  runs `withLockSet` (`SyscallDispatchEntry.lean:1098-1105`,
  `WithLockSet.lean:1150-1157`).  The fault entries bracket nothing.
- Acquire and release are object rewrites: `LockId.lookup`
  (`LockIdProjection.lean:350`), then `updateObjectAt` with
  `KernelObject.updateLock` (`WithLockSet.lean:173-185,319,339-343`) — a copy
  of the object with a new `lock : RwLockState` and a table reinsert, per
  member, twice per syscall.  Twelve object structures carry that field
  (`Model/Object/Types.lean:1075,2014,2100,2134,2196`,
  `Model/Object/Structures.lean:238,619,658`, `Model/Object/Reply.lean:93`,
  `SchedContext/Types.lean:243`, `Model/FrozenState.lean:275,310`), and the
  state carries `objStoreLock` (`Model/State.lean:1006`) and `schedulerLocks`
  (`:1028`, two `Vector RwLockState numCores`).
- No Rust code reads any of it.  Exclusion is the global kernel-entry ticket
  lock (`rust/sele4n-hal/src/kernel_entry.rs:160,295`); the HAL's lock pool
  (`lock_bridge.rs:228`) and its Lean wrappers (`Concurrency/LockBridge.lean`)
  are reached by no transition (`Platform/Staged.lean:130` and tests only).
- Measured on the local `heap-allocations-per-syscall` exerciser (one
  notification-signal round trip, QEMU `virt`), LS0.1's reading at
  `v0.36.62`: **387** allocations per syscall after CV1.1, of which about
  **250** are the bracket, by function (the table is the `v0.36.62`
  CHANGELOG entry): the object reinserts its `updateObjectAt` causes (56),
  `LockId.lookup` (24), `KernelObject.updateLock` (18), the footprint
  resolver's arms and `resolveCapAddress` walks (about 40), `insertOrMerge`
  and the acquisition sort (24), the scheduler domain's folds and
  decidables (about 30), `RwLockState` (15), the refusal arm compiled beside
  the committing path (18), and the per-lock primitives.

Under the entry lock every acquire is granted and every release restores the
word, so the bracket's net effect on the state is nothing; its cost is about
two thirds of the allocations per syscall, a bigger object for every kind,
and a refusal arm (`syscallBracketRefusalResult`, `SyscallDispatchEntry.lean:598`)
that stages an `illegalState` frame to the caller if a lock word is ever found
held at entry — an outcome only corrupt bookkeeping can produce.

The goal: **the kernel state carries no lock words, a transition cannot read
or write one by type, and the bracket is a ghost whose kernel projection is
the transition by definition.**  The compiled seam runs the transition alone.
The 2PL, deadlock-freedom, serializability and refinement results keep
describing the executed path, because the executed path is the kernel half of
the pair they are stated over, and the ghost lock state is the specification
the hardware locks refine when fine-lock Track D makes them real.

### 1.1 Acceptance (measured, not stated)

- The per-syscall allocation delta of CV0's exerciser, read before LS2 and
  after LS3 at the same head of everything else, falls by every site the trace
  attributes to the functions §3.3 deletes (the list above, re-read by name
  from the symbolised trace at LS0.1).  Sites of other owners cancel in the
  difference, as in WS-CV §1.1.
- `main_trace_smoke.expected` is byte-identical at every row.
- The kernel image's size, read from the archive lane's `[BUILD] Kernel
  image:` line, at LS0.1 and LS3.3, recorded in the CHANGELOG — a figure, not
  a budget: the ghost layer stays compiled (§3.1) and the linker decides what
  it keeps.
- No state-committing `@[export]` reaches the ghost layer: `ExportCommitDisciplineCensus`
  asserts it as a derived negative (§3.2), and the existing positive, that
  every such export runs through a bracket, keeps holding — about
  `BracketSpec.run`.

## 2. The decision

The maintainer chose "separate by type" (option A of the options note) and
asked for a better route if one exists.  Read against the tree, A is the
route, and it is **cheaper and stronger than the note estimated**, in three
ways the rows below build on:

1. **The ghost table is one total function, not per-object fields moved
   elsewhere.**  `LockState := LockKey → RwLockState`, where `LockKey` is the
   object locks (`LockId`), the table lock and the two per-core scheduler
   locks (`SchedLockId`'s shape, `PerCoreChooseThread.lean:281`).  A ghost
   lock exists for every key, so acquisition is a function update and
   "held" is a function read.  Everything that existed only because the words
   lived inside objects — `LockId.lookup`'s pair, `updateObjectAt`,
   `updateObjectLockAt`, `KernelObject.updateLock` / `setLock` / `eraseLock` /
   `objectLockOf`, `PerObjectLockInventory.lean`, the lock erasure in the
   information-flow projection (`InformationFlow/Projection.lean:217-386`),
   `lockWritesOnly` and its ten producers (`FineLockFlow.lean:214,462-550`),
   and every `*_preserves_invExt` / `_scheduler` / `_projection` /
   `_machine_eq` frame over a lock write (`WithLockSet.lean:537-978`,
   `Serializability.lean:1524-1558`, `NonInterferencePerCore.lean:2696-2961`)
   — **is deleted, not restated**.  The note's "40,000-line proof tree
   restated" was wrong: of the 40,111 lines under `Concurrency/Locks/`, about
   31,000 (the `RwLock`/`TicketLock` specifications and their three
   refinements, `Deadlock`, `Kind`, `LockSet`, `LockSetTransitions`,
   `LockSetForSyscall`, `ResolvedFootprintBounds`) never mention a state lock
   word and do not change.  What changes is about 8,500 lines there
   (`WithLockSet`, `LockSetHeld`, `LockSet2PL`, `LockBracket`,
   `LockIdProjection`, `DynamicChainExtension`, the `withLockSet` half of
   `Serializability`, the two inventories) and about 7,000 outside
   (`SyscallLockBracket`, `SchedLockBracket`, `SchedLockSet`,
   `FineLockFlow`, `NonInterferencePerCore` §6, the object structures), most
   of it by deletion.
2. **The bracket is a record whose proof field is the coverage.**  A seam
   runs its step through `BracketSpec.run`, and a `BracketSpec` cannot be
   built without the theorem that the declared footprint covers the step's
   writes (§3.2).  The export census then asks one question of the elaborated
   environment — does this committing export reach `BracketSpec.run`? — and
   the type answers the other two (is a footprint declared, is it proved to
   cover) by construction.  Today the census accepts a body that reaches
   `runUnderDeclaredLockSet` or `withLockSet`
   (`Testing/ExportCommitDisciplineCensus.lean:30,92-94,164`), and coverage is
   a separate theorem a seam can lack.
3. **The refusal arm is retired.**  The ghost acquire models the **blocking**
   FIFO lock the refinement already proves admits in order
   (`QueuedRwLockRefinement.lean:4225,4249`; `RwLock.lean:2247,2422,2483`):
   after the growing phase the core holds the footprint, as a theorem over
   the ghost state, not as a guard the kernel decides.  Under the entry lock
   the footprint is free at every entry (§5 O3); under fine locks the HAL's
   acquire waits its turn.  Neither regime has a refusal outcome, so the arm,
   `syscallBracketRefusalResult` and the `.illegalState` frame it staged go.
   The re-resolve-and-retry that fine locks need between an unlocked
   resolution and a granted footprint is Track D's HAL obligation (§3.4),
   not a kernel outcome.

Also considered, and not taken:

- **Keep the words in `SystemState` as one field and prove each transition
  lock-oblivious.**  The kernel projection of the bracket would then equal
  the step only under a per-transition frame theorem, which is the
  conditional equation option B rejected: the compiled seam could run the
  step alone only through an unproved `implemented_by`.  The type split is
  what makes the equation `rfl`.
- **Delete the lock-word model and keep only the static order and the
  coverage theorems.**  Cheaper still, but it discards the operational 2PL
  statements, `lockSetHeld`, and the refinement's target: Track D needs a
  specification its hardware acquire sequence refines, and the ghost table
  is exactly that, at the cost of about 1,500 lines (§3.1).
- **Keep running the bracket on a separate table and fixed arrays (option
  C).**  About 40 allocations per syscall would remain for bookkeeping with
  no effect, and the objects' size would not shrink.
- **Make the ghost layer `noncomputable`.**  It would make "never executes"
  a compiler fact rather than a census fact, but the Tier 2 suites execute
  the lock semantics (`with_lock_set_suite`, `lock_set_suite`,
  `deadlock_freedom_suite`, `serializability_suite`;
  `scripts/test_tier2_negative.sh:192-231`) and a `decide` proof over a
  concrete ghost state needs the functions reducible.  The layer stays
  computable; the census carries the negative (§3.2), derived from the
  environment as the positive is today.

## 3. Implementation specification

### 3.1 The ghost lock state (LS1)

New module `SeLe4n/Kernel/Concurrency/Locks/LockState.lean`:

- `inductive LockKey | object (l : LockId) | objStore | runQueue (c : CoreId) | replenishQueue (c : CoreId)`
  with `DecidableEq`, and an order extending `LockId`'s (`Kind.lean:163-170`):
  `objStore` first (it is `LockKind.level 0` today), objects by `LockId`,
  then the scheduler keys by core, in the order `SchedLockSet.lockAcquireSequence`
  sorts today (`SchedLockSet.lean:445`).  One key type, one order, one
  acquisition sequence; `SchedLockId` is retired into it.
- `def LockState := LockKey → RwLockState`, `LockState.unheld := fun _ => .unheld`.
- `acquire (L) (c) (k) (m)`, `release`, `cancel` as function updates through
  `RwLockState.applyOp` (`RwLock.lean:635`) with the ops `AccessMode.toAcquireOp`
  / `toReleaseOp` / `toCancelOp` give today (`WithLockSet.lean:100-129`);
  `acquireAll` / `releaseAll` / `cancelAll` / `unwindAll` as the same folds
  over `List (LockKey × AccessMode)` (`WithLockSet.lean:847-903`).
- `lockSetHeld (c) (S) (L)` as `LockSetHeld.lean:233` reads, over `L`.
- `LockSet.lockAcquireSequence` keeps its type and its sort
  (`LockSet.lean:614`); a `LockSet` is a set of `LockKey`s after this row, and
  `SchedLockSet` (`SchedLockSet.lean:347`) is retired into it, its sixteen
  declared arms (`SyscallSchedContainment.lean:77-551`) re-keyed, not
  re-proved.
- The theorems of `WithLockSet.lean`, `LockSetHeld.lean` and `LockSet2PL.lean`
  that are about the ghost (`unheld_acquire_grants`, `..._roundtrip`,
  `acquireAll_establishes_lockSetHeld`, `unwindAll_leaves_no_queued_request`,
  `lockSet_acquired_in_order`, `lockSet_released_in_reverse`) restated over
  `LockState`; `acquireAll_establishes_lockSetHeld` loses its object-presence
  hypothesis (a ghost lock exists for every key).
- The refinement lift: a `LockState` is the product of per-key specifications,
  so the per-key chain `queuedRwLock_refines_rwLockSpec` lifts to "the ghost
  op sequence a bracket applies to key `k` is a `RwLockOp` list the per-lock
  refinement covers" — one lemma, no change to the 4,263-line file.
- `LockKind.objStore` stays a kind until LS3.1: the per-object primitives
  dispatch on it, and `LockKey.ofLockId` folds every `.objStore`-kind `LockId`
  onto the `objStore` constructor meanwhile, so the ghost has one spelling of
  the table lock while the words still have many.  LS3.1 deletes the kind with
  the word it named (the ladder becomes nine object levels under the table
  key), and `ofLockId` becomes `LockKey.object`.

### 3.2 The bracket (LS2)

- `structure LockedSystemState where kernel : SystemState; locks : LockState`.
  Transitions stay typed over `SystemState`; nothing that is typed over it
  can name a lock word after LS3, because none exists there.
- ```
  structure BracketSpec (α : Type) where
    declared : SystemState → Option LockSet
    step     : SystemState → α × SystemState
    covers   : ∀ st S, declared st = some S → footprintCoversWrites S st (step st).2
  @[inline] def BracketSpec.run (b : BracketSpec α) : SystemState → α × SystemState := b.step
  def BracketSpec.runGhost (b : BracketSpec α) (c : CoreId) (s : LockedSystemState) :
      α × LockedSystemState :=
    match b.declared s.kernel with
    | none   => let (v, k) := b.step s.kernel; (v, ⟨k, s.locks⟩)
    | some S => let seq := S.lockAcquireSequence
                let (v, k) := b.step s.kernel
                (v, ⟨k, unwindAll c seq.reverse (acquireAll c seq s.locks)⟩)
  theorem BracketSpec.runGhost_kernel (b) (c) (s) : (b.runGhost c s).2.kernel = (b.run s.kernel).2 := rfl
  ```
  `footprintCoversWrites` (`Locks/BracketSpec.lean`) is the predicate that
  was `schedFootprintCoversWrites` (`SchedLockBracket.lean`) until LS2.1
  moved and renamed it; the object-domain members
  keep their by-membership statements (`LockSetForSyscall.lean:676-1080`) as
  lemmas feeding it.  The step runs from `s.kernel`, which is the state the
  growing phase ended in — the growing phase changes only `locks`, by type,
  which is the fact `runBracketed`'s re-resolution guarded by computation
  (`LockBracket.lean:123-135`).  `withLockSet` becomes `runGhost` on a spec
  whose `declared` is constant; its `_unfold` / `_eq_decomposition` / `_fst`
  / `_snd` and the `*_atomic_under_lockSet` theorems
  (`NotificationSignal.lean:872,889`, `EndpointCall.lean:1021`,
  `EndpointReply.lean:2876`, `Cancellation.lean:2956-3050`) stay `rfl`.
- One `BracketSpec` per committing seam: the syscall seam over
  `declaredUnifiedLockSetForAbiEntry` with `unifiedLockSetForSyscall_coversWrites`
  (`SyscallSchedFootprint.lean:2656`); the timer tick with
  `perCoreTimerTickStep_coversWrites` (`SchedLockTimerContainment.lean:145`);
  the reschedule entries with `perCoreRescheduleStep_coversWrites`
  (`SchedLockBracket.lean:458`); suspend with `tcbSuspend_covers_victim` /
  `_cancellation` (`LockSetForSyscall.lean:1356,1376`).  The exported bodies
  call `.run`; `syscallDispatchCrossCoreBracketedStep` loses its `match` on
  the outcome; `LockBracketOutcome`, `runBracketed`, `LockBracketDomain`,
  `objectLockBracketDomain`,
  `runUnderDeclaredLockSet`, `syscallBracketRefusalResult` and the Tier 2
  check that exercised a refusal are deleted.
- `runChainExtension` / `withDynamicChainExtension` /
  `withPipChainSchedExtension` (`LockBracket.lean:277`,
  `DynamicChainExtension.lean:453`, `Scheduler/PriorityInheritance/ChainFootprint.lean:451`; no export
  reaches them) become a ghost extension of `declared` — the chain footprint
  is a function of the kernel state since RR7.40, so a spec declares the
  union — or are deleted with their consumers; the row decides each by its
  consumers at the time, which it lists.
- `ExportCommitDisciplineCensus`: *bracketed* means the body reaches
  `BracketSpec.run`; a second derived assertion, that no state-committing
  export reaches `BracketSpec.runGhost`, `LockState.acquire`, `release`,
  `cancel` or `acquireAll`, fails the build on the day a seam runs the ghost.
  `LockFootprintBoundCensus` and `SchedFootprintCensus`
  (`scripts/test_tier1_build.sh:114-137`) re-keyed.

### 3.3 What leaves the kernel state (LS3)

The twelve `lock` fields, `objStoreLock`, `schedulerLocks` and
`SchedulerLockState` with its four accessors (`Model/State.lean:887-892,
1610-1647`), `FrozenSystemState.objStoreLock` (`FrozenState.lean:536`), and
with them: every definition §2 item 1 lists; the `BEq` / equality lemmas
that mention `lock` (`Types.lean`, `Reply.lean`, `SchedContext/Types.lean`);
`KernelObject.updateLock_not_identity`; the `objStoreLock` / `schedulerLocks`
frame conjuncts in `ReschedulePending.lean:342-593` and
`CrossSubsystem.lean:1343-1344`; `scripts/lean_store_read_census.py`'s
exemption of `WithLockSet.updateObjectAt` (`:1569,1597`); and the debt row
"`ipcInvariantFull_perCore` is not carried through the runtime `withLockSet`
bracket" (`docs/REGISTERED_DEBT.md:217`), which closes by
`BracketSpec.runGhost_kernel`: the bundle's preservation by the transition is
its preservation through the bracket, with no congruence layer.  The
information-flow projections no longer erase a field that does not exist;
`nonInterference_perCore_underLockSet` and `syscallEntryUnderLockSet`
(`FineLockFlow.lean:2149`) restate over the pair and reduce to the step's
results by the same `rfl`.

### 3.4 What Track D inherits

Fine-lock Track D (`SMP_FINE_LOCK_MIGRATION_PLAN.md` §Track D) is re-pointed
by LS3.4, in its own file: the HAL's per-object acquire sequence refines
`acquireAll` over the ghost `LockState` (the lift of §3.1); the runtime
footprint resolution moves into the HAL seam when it goes live and must then
be allocation-free (a `maxLockSetSize`-bounded array, `LockSet.lean:1080`,
not a `List` and a `mergeSort`); and the resolve–acquire–re-resolve loop
lives there, establishing the guard `BracketSpec.runGhost` takes as a
hypothesis (§5 O4) before the step runs.  Until Track D, the resolution is
ghost too, which is why §1's figure includes the resolver's walks.

### 3.5 Measurement (LS0, LS3)

CV0's exerciser and the symbolised allocation trace (the WS-CV §3.6
procedure) read at LS0.1 with the lock-model functions' sites attributed by
name, and again at LS3.3; the two readings and the image sizes are the
CHANGELOG entry's figures.

## 4. Schedule — phases and sub-tasks, in execution order

One PR per row; each row bumps the version, carries its CHANGELOG entry, its
documentation (§4's per-row list) and its Tier 3 anchor sweep (§7), and runs
`test_full.sh` (theorems change in every row).

### LS0 — baseline (nothing in the model changes)

| Row | Does | Done when |
|---|---|---|
| LS0.1 (**done `v0.36.62`**) | Reads CV0's exerciser delta and the symbolised trace at the plan's head and attributes every site to its function; records the image size.  Fixes the three prose inconsistencies found while auditing: `WORKSTREAM_CONTEXT.md:2081,2156` and `CLAIM_EVIDENCE_INDEX.md:227` say the scheduler entries bracket nothing (they have since RR7.39, `SchedLockBracket.lean:204,212`); `scripts/test_tier1_build.sh:89` says two seams bracket (five do). | The attributed table is in the CHANGELOG entry; §1's figure is replaced by the reading, or confirmed.  Done: 387 per syscall, about 250 the bracket's (the reinserts its lock writes cause were under the store's row at the 572 reading); image 8,884,824 bytes; the three prose sites fixed; the serializability-premise debt row registered. |

### LS1 — the ghost lock state (§3.1): the kernel state is untouched

| Row | Does | Done when |
|---|---|---|
| LS1.1 (**done `v0.36.63`**) | `LockKey`, its order, `LockState` and the per-key ops and folds (`SeLe4n/Kernel/Concurrency/Locks/LockState.lean`); `heldAll` over `LockState`; the ghost theorems of §3.1 restated (`acquireAll_unheld_held`, `unwindAll_not_queued`, `acquireAll_unwindAll_unheld`, `lockAcquireSequence_ordered`); the refinement lift lemma (`applySeq_unheld_key_refines`, obligation O5, through `applySeq_key`; stated in `Locks/Refinement.lean`, the staged bridge hub, so the ghost module itself pulls no bridge into the production closure).  Split from the re-keying (LS1.2) when the row started: the ghost compiles alone beside the per-object layer, and the re-keying touches every footprint declaration (249 `LockId × AccessMode` sites in 19 files at this head), so each row lands as its own cut. | Done: `lake build SeLe4n` green with the old brackets untouched; `with_lock_set_suite` executes acquire, contention, withdrawal and unwind against `LockState` (eleven runtime checks) and `#check`s every new name; Tier 3 pins the ten load-bearing ones. |
| LS1.2 (**done `v0.36.64`**) | `LockSet` re-keyed over `LockKey` (`pairs : List (LockKey × AccessMode)`, `lockAcquireSequence` pointed at §3.1's sort, `lockSetHeld c S L` over `LockState` beside the per-object form until LS3); `SchedLockSet` and `SchedLockId` retired into it, `canonicalSchedLockOfObject` and its four congruences deleted with them, the sixteen arms' declarations (`SyscallSchedContainment.lean:77-551`) and the unified footprint (`SyscallSchedFootprint.lean`) re-keyed, not re-proved; the two Tier 1 footprint censuses re-keyed.  The old brackets fold over `LockKey` through the primitives `schedAcquireLock` dispatches today, so `runBracketed` keeps running until LS2.2. | `lake build SeLe4n` green; `rg -n 'SchedLockId\|SchedLockSet' SeLe4n tests scripts` empty; `main_trace_smoke.expected` unchanged; `lock_set_suite` and `smp_foundations_suite` execute against the re-keyed set. |

### LS2 — the bracket (§3.2): the seams switch, the old bracket is deleted

| Row | Does | Done when |
|---|---|---|
| LS2.1 (**done `v0.36.65`**) | `LockedSystemState`, `BracketSpec`, `run`, `runGhost`, `runGhost_kernel`; `withLockSet` as `runGhost` of a constant spec; the `*_atomic_under_lockSet`, 2PL and observer theorems restated over the pair; `applySequentialWithLockSet` and `syscallEntryUnderLockSet` over the pair. | Every theorem §7 lists under 2PL, serializability and `withLockSet` elaborates; the old `runBracketed` is still the seams' bracket.  Done: `Locks/BracketSpec.lean` holds the pair, `footprintCoversWrites` (moved from `SchedLockBracket.lean`), `withLockSetGhost` (the ghost bracket; LS3.1 renames it `withLockSet`), `BracketSpec` with O1 (`rfl`), O3 and O4 (`guard`, `guard_of_unheld`, `not_guard_of_contended`); the word-level `withLockSet` stays because the suspend seam executes it until LS2.2.  Every restated theorem keeps its name; the hypotheses dropped are the lock-insensitivity ones (an observer's acquire/unwind insensitivity, the `invExt` guard on object-store observers, the three per-primitive invariant preservations) — strengthenings, O6.  Deleted with nothing left to prove: `AcquireInsensitive`/`UnwindInsensitive` and their `On` forms, the per-fold invisibility lemmas, `lockSet_observer_atomic_on` / `_of_objectStoreObserver` (collapsed into `lockSet_observer_atomic`), `lockSet_invariant_preserved` and its worked instantiation, Serializability §8b/§8c/§9b, `ActionPiCongr`, FineLockFlow's `lockSetAcquiredState` and grant lemmas (now `guard_of_unheld` / `not_guard_of_contended`), the six cancellation insensitivity lemmas. |
| LS2.2 | The four seams' `BracketSpec`s (§3.2) and their exported bodies calling `.run`; `runBracketed`, its domains, `runUnderDeclaredLockSet`, `LockBracketOutcome`, `syscallBracketRefusalResult` and the refusal test deleted; the chain-extension combinators decided (§3.2); the export census re-pointed and its negative added; the two footprint censuses re-keyed.  **The first row that changes the compiled kernel**, and it lands after LS2.1's proofs. | Exerciser delta read and recorded; `main_trace_smoke.expected` unchanged; the census fails if a seam is pointed at `runGhost` (tested by breaking the relation). |
| LS2.3 | The resolved scheduler footprints and write sets of `SeLe4n/Kernel/SyscallSchedFootprint.lean` move beside their transitions.  Their placement had one reason — `LockKey` was declared in `PerCoreChooseThread.lean`, above the transition modules — and LS1.2 removed it (`LockKey` is in `Concurrency/Locks/LockKey.lean`, below all of them); the module's own docstring says so.  `unifiedLockSetForSyscall` and the ABI-entry declarations stay. | Every moved footprint is cited by its consumers at the new path; the two footprint censuses and the export census pass; a Tier 3 negative anchor holds `SyscallSchedFootprint.lean` to no per-transition resolved footprint; the `REGISTERED_DEBT.md` row LS1.2 registered is closed. |

### LS3 — the words leave the kernel state (§3.3)

| Row | Does | Done when |
|---|---|---|
| LS3.1 | The twelve `lock` fields, `objStoreLock`, `schedulerLocks`, their accessors, the frozen mirrors, and every definition and lemma §2 item 1 and §3.3 list, deleted; `lockWritesOnly` consumers reduced to kernel equality; the projections' erasure removed. | `lake build SeLe4n` green; `rg -n 'lock : RwLockState\|objStoreLock\|schedulerLocks' SeLe4n tests` empty. |
| LS3.2 | `FineLockFlow.lean` and `NonInterferencePerCore.lean` §6 restated over the pair (`nonInterference_perCore_underLockSet`, `syscallEntryUnderLockSet`, `withLockSet_noUnpermittedWrite` reduce to the step's results); `PerObjectLockInventory.lean` and the two lock inventories updated to what exists. | The Tier 3 NI anchors (§7) pass on the restated names. |
| LS3.3 | The debt row `REGISTERED_DEBT.md:217` closed with its proof name; the second exerciser reading and image size; the spec passages §7 names, `CLAIM_EVIDENCE_INDEX.md` rows 113–130 and §8 row 227 re-read against the tree. | Acceptance §1.1 met and recorded. |
| LS3.4 | `SMP_FINE_LOCK_MIGRATION_PLAN.md` Track D re-pointed per §3.4; the CBS plan's lock-set rows (§4.12 and the resolver table at `HIERARCHICAL_CBS_PLAN.md:1533-1537`) re-read for `LockKey`; this plan moved to `docs/dev_history/planning/` and its `WORKSTREAM_CONTEXT.md` section to the closed file. | WS-LS closed in the workstream registry. |

Rows are sequential; no two run in parallel.  LS1.1 and LS1.2 are two rows
because the ghost compiles alone and the re-keying is a sweep of every
declaration site; LS2.1 and LS2.2 are two rows
because each compiles alone (LS2.1 adds beside the old bracket; LS2.2
switches and deletes); LS2.3 is a move with no proof content and follows
LS2.2 so the footprints move once, into the seams' final shape; LS3.1 cannot precede LS2.2 (the old bracket writes
the fields it deletes).

## 5. Proof obligations

| | Obligation | Where |
|---|---|---|
| O1 | `BracketSpec.runGhost_kernel : (b.runGhost c s).2.kernel = (b.run s.kernel).2` — `rfl`. The executed path is the kernel projection of the proven one. | LS2.1 |
| O2 | `BracketSpec.covers` for each of the four seams, from the four existing coverage theorems §3.2 names, re-keyed. | LS2.2 |
| O3 | `runGhost_locks_of_unheld : s.locks = .unheld → (b.runGhost c s).2.locks = .unheld` and `lockSetHeld c S (acquireAll c S.lockAcquireSequence .unheld)` — under the entry lock every entry starts free and ends free, and the step ran held; the refusal arm's replacement. | LS1.1 over the pair list (`LockState.acquireAll_unheld_held`, `LockState.acquireAll_unwindAll_unheld`), LS2.1 at the spec |
| O4 | The ghost bracket's guard as a hypothesis for Track D: `declared s.kernel = some S ∧ lockSetHeld c S (acquireAll …)` is what the HAL's resolve–acquire–re-resolve loop must establish; stated once, consumed by no kernel code. | LS2.1 |
| O5 | The refinement lift of §3.1. | LS1.1 (`LockState.applySeq_unheld_key_refines`, in `Locks/Refinement.lean` beside the bridges, which are staged) |
| O6 | Every restated 2PL, serializability, deadlock-grounding and NI theorem keeps its name or is renamed with its anchor; none is weakened (a statement that drops a hypothesis is recorded as strengthened, with the hypothesis named). | every row |

## 6. Risks, and decisions deliberately not taken

- **A ghost lock exists for a key with no object.**  Today a footprint member
  whose object is absent is never written and the guard refuses
  (`updateObjectLockAt`'s `none` arm, `WithLockSet.lean:339-343`); after
  LS1 it is granted and the step decides.  The resolver names only objects it
  read, so the cell is unreachable from a declared footprint; LS2.2 states
  it as a lemma over `declaredUnifiedLockSetForAbiEntry` or records the
  resolver arm that cannot.
- **Serializability's commutation premise is never discharged from
  coverage** (`Serializability.lean:749,939`: `outOfOrderCommute` and
  `hNonConflictCommute` are hypotheses, instantiated only by the toy
  instances at `:979-1030,1850-1866`).  Found while auditing, pre-existing,
  not closed here: "footprint covers writes ⇒ disjoint footprints commute"
  for real transitions is Track D's footprint-local commit theorem.  LS0.1
  registers it as a debt row with that owner, so the claim index does not
  carry serializability as an unconditional result.
- **Tier 2 suites.**  `per_object_lock_suite` (1,106 lines) tests the object
  fields and goes with them at LS3.1; the ghost cases of `with_lock_set_suite`
  and `lock_set_suite` move to `LockState` at LS1.1; `deadlock_freedom_suite`
  and `serializability_suite` are over the abstract models and keep.
- **Image size** may not fall: the ghost layer compiles, and the archive
  links what its modules reference.  Recorded, not budgeted (§1.1).
- **Not taken**: making the ghost `noncomputable` (§2); deleting the ghost
  (§2); changing `LockSet`'s representation or `maxLockSetSize` (Track D's,
  §3.4); touching `RwLock.lean`, `TicketLock.lean` or the refinements.
- **Not a security change**: nothing here alters exclusion, which is the
  entry lock before and after; the model loses a dead refusal arm.

## 7. Tier 3 anchors touched (pin at the audited cut; LS0.1 re-reads)

`scripts/test_tier3_invariant_surface.sh`: the `#check` blocks for 2PL
(`:14094-14271`), serializability (`:14385-14515`), the bracket
(`:9405-9412`, `:7104-7114`), the coverage theorems (`:9280-9293`,
`:10178-10179`, `:15727`, `:21051-21074`, `:21288-21289`); the `rg` anchors
for the `withLockSet` frames (`:5264-5265`, `:6107-6157`), the lock erasure
(`:6206-6207`), `_atomic_under_lockSet` (`:4524-4527`), the IPC bundle
(`:742-789`, `:858`, `:4491-4498`), `maxLockSetSize` (`:982`, `:2311-2319`,
unchanged).  Untouched: the RwLock, TicketLock and refinement blocks
(`:13064-13789`), LockSet (`:13945-14088`), deadlock (`:14277-14378`).
`tests/SmpSurfaceAnchors.lean:478-505` unchanged.
`scripts/check_ipc_invariant_dethreading.py:261-352` (the lock inventory
registrations) re-pointed at LS3.2.  Spec: `SELE4N_SPEC.md` §6.4 item 2's
SM3.C passages (`:2647-2858`) and §6.8 items 2.11–2.12 (`:3947-4218`); the
scheduler bracket passages (`:6627,6717,6763`).
