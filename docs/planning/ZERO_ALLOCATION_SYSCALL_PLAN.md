# WS-ZA — A syscall that allocates nothing

> **Workstream**: WS-ZA (every heap allocation on the continuing syscall round
> trip is removed; seL4 allocates none).
> **Status**: **IN FLIGHT** — registered at `v0.36.72`; at `v0.36.73` ZA1.1–ZA1.6
> landed with ZA2.1–ZA2.3 and the signal path's parts of ZA2.4 and ZA2.5,
> beside WS-CV CV2.1–CV2.2, as one PR (the rows were measured one at a time
> on the signal round trip, which read 118 → 13); at `v0.36.74` WS-CV's CV3.1
and the save-and-stage half of CV4.4 took it to 9, with the overflow-word
cell (this plan's) and the entry's record of the committed current thread; at
> `v0.36.75` the signal round trip reads 0 (§1).  Asked for by the
> maintainer on 2026-10-07 ("get the allocation number down to 0").
> Runs beside WS-CV: WS-CV keeps the register-context sites its plan already
> owns (`CONTEXT_BY_VALUE_PLAN.md` §1.1, first table); this plan owns every
> other site and the three entries WS-CV keeps.  Before WS-CB.
> **Audited cut**: `v0.36.71` (`93f76643`), from which every figure and
> `file:line` below was read; a row re-reads what it depends on when it starts.
> **Phases**: ZA1..ZA4 in execution order; the rows are §4.  **Prefix**: `ZA`
> (`za<digit>` matches nothing under `SeLe4n/`, `tests/`, `rust/`, `scripts/`
> at the audited cut).

## 1. Goal and measurement

The `heap-allocations-per-syscall` exerciser (Tier 4 QEMU `virt`, Lean-linked
image, `rust/sele4n-hal/src/smp_exercisers.rs`) runs one continuing
`NotificationSignal` from an EL0 frame on core 0 with IRQs masked and reads
the per-core heap counter across it.  At the audited cut it reads **118**.
A second round trip on the same boot also reads 118, so every allocation is
paid per syscall; none is a first-touch cost.  Since `v0.36.73` the exerciser
runs two round trips and reports the second (the first also reads boot-built
objects for the first time): **13** at `v0.36.73`, **9** at `v0.36.74`.  The 9: the decode's
argument array (its 104-byte copy and its `mapM` cell) and its two records
(32 and 64 bytes); the arm's result (24) and its `Except` (16); the return
frame (56) and its `.returns` outcome (16); and the restore target crossing
the commit (40, ZA3.1).  At `v0.36.75` it reads **0** (5 on the first call
after boot): the unit-shape outcome is a static, the restore target crosses the
inlined commit as words, the signal arm and the first resolution level are
inlined into the entry, and the entry routes a signal whose arguments all sit in
registers on the register file itself (now `registerRoutedSyscall`), before any
decode record or message array exists.  At `v0.36.76` (ZA4.1, ZA4.2 for the
wait) a notification wait that consumes a pending badge reads **0** in steady
state, down from 48 (only the first scenario's first call is measured, being
the one first touch of the boot's objects): the entry routes it on the
register file as it routes a signal, the consumed notification and the woken
TCB are written in their slots, and the step answers the outcome as its seven
boundary words, so no return frame record is built.  A signal with a badge
`≥ 2^63` reads 4, its heap numbers (R1).  The scheduler's restore of a
switched-in thread now writes its words into the core's own register file
(`restoreIncomingContextOnCore_eq_impl`): it had shared the thread's file with
the bank, so a syscall after a thread switch copied it once, which only an
untraced build showed.  At `v0.36.77` (ZA4.2 for the wide badge, with ZA2.3's
type change) the badge is a machine word and the notification holds its
pending badge as a flag and a word: the wide-badge signal reads **0**, the
signal and the wait still read 0, and the signal's first call after boot reads
2.

**Acceptance**: the exerciser reads **0** for every scenario of ZA4.1, and
from ZA4.12 on it fails on any non-zero delta (a check on the kernel's
behaviour, not on prose).  Every row records its reading in `CHANGELOG.md`,
taken on an archive whose provenance record matches the tree
(`build_lean_aarch64_archive.py --check-fresh`).

**How the sites were found**: a debug build of the HAL heap records the link
register and size of every allocation in the round trip; the addresses are
symbolized against the image and each is matched to its line in the
generated C (`.lake/build/ir/**.c`).  117 of the 118 were captured; the
118th is outside the traced window and is found by ZA4.1's re-trace.
The instrumentation is a debug patch, never committed.

## 2. Where the 118 come from (the audited cut)

Five root causes.  Each site is listed once, with the row that removes it.

### 2.1 Owned by WS-CV (55 sites)

| Sites | Construct | WS-CV row |
|---|---|---|
| `ffi_trap_context` 2, `lean_syscall_dispatch_cross_core` 12 (11 boxed words, the 152-byte action closure), `writeFfiRegistersToTcb` 2, `lookupThreadRegisterContext` 2, `decodeSyscallArgsFromState` 2, `Array.mapMUnsafe` 1, one 104-byte array copy on the decode path | the per-trap context object, the boxed argument words, the argument spill and its read-back | CV3.1 |
| `registerFileOfTrapContext` 1, `trapContextOfRegisterFile` 1 | the two `TrapContext` ↔ `RegisterFile` conversions | CV2.1 |
| `overflowWordsOrFaulted` 1 | the overflow read's result | CV4.3 |
| `saveTrapFrameOnCore` 3, `restartAtSvc` 1, `setGprOfByte` 1, `RegisterFile.stageReturnFrame` 2, `TCB.withReturnFrame` 1, `writeReturnFrameToTcb` 1, `stageCallerReturnFor` 1 (an `instDecidableEqThreadId` closure) | TCB, register-file and state copies taken because the object is shared between the TCB and the core bank | CV4.4 |
| `syscallDispatchCrossCoreStep` 8, `threadTranslationOperands` 6, `fpLiveFor` 2, `restoreTargetOnCore` 2, `shootdownRoundWindowFrom` 1, `readReturnFrame` 1 | the step's nested result tuple and the restore operands; `restoreTargetOnCore` runs **twice** per syscall | CV4.5 |

After CV4.5 the CV plan keeps three entries by name (its §1.1): the commit
record, the `modifyGet` pair and the optional `KernelObject` re-wrap.  ZA3
removes them.

### 2.2 Owned by this plan (62 sites)

| Sites | Construct | Cause | Row |
|---|---|---|---|
| `copy_expand_array` 3 (280 bytes: a 32-slot table) | the slot arrays of `objects`, `objectIndexSet` and `lifecycle.objectTypes`, copied whole at the arm's `storeObject` | **the pre-state is kept alive across the arm**, so every table the arm writes is shared and copied: `dispatchSyscallChecked` passes `st` to `applySyscallTaint (syscallTaintPlan st tid decoded) st stPost` after the arm (`API.lean:4727`, again at `:5265`), and the arm's error branches return `st` after its first write (`NotificationSignal.lean:89–94`, `:112–113`).  The copy is `O(capacity)` per table per syscall: on a full object table it is the dominant cost of the syscall, not only an allocation | ZA1.1 |
| `insertLoop` 3 per insert × the arm's 3 inserts, `insertNoResize` 3 | per `RHTable.insert`: the new `RHEntry` (32 bytes), its `some` (16), the loop's `Array × Bool` result (24); on a size-changing path the table record (32) | `insertLoop` (`RobinHood/Core.lean:130–160`) reads `slots[i]`, which shares the entry it then rebuilds, and returns a pair | ZA1.2 |
| `storeObject` 3 | the state record (216), the lifecycle record, the `KernelObject` wrapper | `storeObject` (`Model/State.lean:1795–1813`) rewrites four tables for any object, including an in-place update of an object whose key, type and ASID role are unchanged | ZA1.4 |
| `resolveCapAddress` 8, `CNode.lookup` 4, `syscallResolveCap` 1 | `Except`/`SlotRef`/`Option` results of the CSpace walk | **the operand is resolved four times**: once by the gate, then three more times by the taint plan (`contentFlowEdges`, `contentFlowClears`, `contentFlowBypassed`, each through `syscallOperandCap?`, `TaintPropagation.lean:519–528`) | ZA2.1 |
| `dispatchSyscallChecked` 4 | the `SyscallGate` record (48), `some tid` for `currentOnCore executingCore ≠ some tid` (`API.lean:4702`), an `instDecidableEq` closure, one record (64) | value built to be compared; equality through a closure | ZA2.2 |
| `notificationSignalOnCore` 3, `decodeNotificationSignalArgs` 1, `clearWokenReceiverStash` 2 | the `Notification` record (40), `some mergedBadge`, the `.notification` wrapper; the decoded-args record; the stash's `Option` round trip | object rebuilt instead of updated in place; an `Option` field written `some` on every signal | ZA2.3 |
| `residentElsewhere` λ 3, `deferResidentElsewhere` 1 | `some tid` built once per other core for `residentOnCore c' == some tid` (`PerCore.lean:1582`); the deferral's record | value built to be compared | ZA2.2 |
| `signalTaintEdges` 2, `syscallTaintPlan` 1, `DeclassificationTaint.instDecidableEq` 1, `applySyscallTaint` 1 | the edge list cell and record, the plan record, an equality closure, the state record rebuilt for the taint field | the plan is materialised as lists and a record, and the state is rebuilt even when no taint changes | ZA2.4 |
| `ipcBufferWalkPlan` 2, `syscallReturnOutcome` 1 | the walk plan's `Option`/record for a message with no overflow words; the `.returns` outcome | by-product returned as a value | ZA2.5 |
| `insertLoop` 3 per insert × 3 TCB writes (`saveTrapFrameOnCore`, `writeFfiRegistersToTcb`, `writeReturnFrameToTcb`) | as row 2 | as row 2 | ZA1.2 |

The rows sum to 62.

### 2.3 What the counts say

- **One cause dominates cost, not count**: the retained pre-state (ZA1.1)
  costs three allocations at this table size and three whole-table copies at
  every size.  It is the first row.
- **Duplicate work**: the operand resolved four times, the restore target
  computed twice, three table inserts to update one object in place.
  Removing the duplicates removes allocations and work together.
- **No allocation comes from the lock model** (WS-LS) or from a first touch.

### 2.4 The IPC and blocking paths (ZA4.1's re-trace)

Traced at `v0.36.77` on top of ZA4.1's scenarios, core 0 only, steady state
(the traced build reads a few more than the untraced one: 112/110/209/121
against 100/102/190/112).  Each class is the row that owns it.

| Class (sites) | receive blocks | send to receiver | call | reply | Row |
|---|---|---|---|---|---|
| Run queue: `RunQueue.insert`/`remove` rebuild a bucket `List`, the `membership` set, the `threadPriority` table and `flat`; `setRunQueueOnCore` rebuilds the per-core array | 33 | 21 | 53 | 21 | ZA4.5 |
| Object store: `storeObjectImpl` → `RHTable.insert` instead of `modify` on the IPC arms | 15 | 17 | 33 | 21 | ZA4.7 |
| Entry and decode: `syscallEntryChecked`'s message array, `ipcBufferWalkPlan`, the taint plan and edges, `dispatchWithCapChecked`, `resolveExtraCaps`, `snapshotInto` | 13 | 20 | 25 | 22 | ZA4.9 |
| Shared arrays copied whole (`copy_expand_array`) | 12 | 9 | 21 | 10 | the row whose write shares them |
| Endpoint queue and transfer (`endpointQueueEnqueue`/`PopHead`, the message record) | 12 | 12 | 13 | 1 | ZA4.7 |
| Capability resolution (`resolveCapAddress`, `syscallOperandCap?`) | 11 | 11 | 11 | 11 | ZA4.9 (ZA2.1's form) |
| Priority inheritance: `waitersOf` scans every object and builds a `List` | 0 | 0 | 16 | 13 | ZA4.6 |
| TCB record rebuilt (`tcbWithQueueLinks`, `enqueueRunnableOnCore`, `storeTcbIpcStateAndMessage`) | 3 | 5 | 15 | 6 | ZA4.7 |
| `lookupTcb`'s `Option` | 7 | 3 | 8 | 1 | ZA4.7 (D2) |

`waitersOf` (`PriorityInheritance/BlockingGraph.lean:42`) is also a time
cost: every call and reply walks the whole object index.

The yield (ZA4.3) reads 49, traced and untraced alike, after ZA4.3 removed
its own sites (the charge writes the SchedContext and TCB in place; a refusal
is the state it was handed, so no table is shared).  Every remaining site is
the scheduling point the yield ends in:

| Class (sites) | yield | Row |
|---|---|---|
| Run queue: `RunQueue.insert` (the `membership` and `threadPriority` inserts, each copying a shared slot array, the bucket list, the record) | 19 | ZA4.5 |
| Run queue: `RunQueue.remove` (three erases, each copying a shared slot array, `recomputeMaxPriority`, the `flat` filter, the record) | 13 | ZA4.5 |
| Selection by-products: `chooseBestInBucketEffective`/`chooseBestRunnableEffective` candidate records and a boxed `UInt64` | 7 | ZA4.5 |
| Switch write: `modifyObject` under `updateTcbImpl` copies the shared object slot array (280 B) and rebuilds the TCB and state records | 7 | ZA4.5 |
| The state record rebuilt before `scheduleEffectiveOnCore` (reset/reuse does not fire across the arm's join point) | 1 | ZA4.5 |
| `RegisterFile.overwriteWith` (the switched-in thread's registers) and `setReschedulePendingOnCore`'s per-core vector | 2 | ZA4.5 |

## 3. Design

Five rules.  Every row applies them to its own sites; none adds a gate.

- **D1 Ownership.**  No state value is used after a later state has been built
  from it, so every table and object the syscall writes has one reference and
  the runtime's in-place branch is taken.  Concretely: what the taint step
  reads from the pre-state (the plan, the audit epoch and log length, the
  pre-state taint table) is captured before the arm runs; an arm checks every failure
  condition before its first write, so a refusal returns the state it was
  handed without that state being held across a write (seL4's decode/perform
  split); objects are updated by take-modify-put on their table slot
  (`RHTable.modify`, ZA1.2), never by a read followed by an insert.
- **D2 No by-product values.**  A function on the path returns the state, a
  scalar, or nothing.  A lookup its caller immediately matches is written in
  continuation form (`@[specialize]` over the success and failure
  continuations) so the `Option`/`Except`/record it would build cancels at the
  call site; what the step must report back is written into the state and read
  after the commit (ZA3.1).
- **D3 Compare without constructing.**  `x == some y` becomes a `match`;
  equality of typed identifiers compares their `.toNat`, with no instance
  closure.
- **D4 One question, one computation.**  The operand is resolved once and its
  slot reference handed to the taint plan; the restore target is computed
  once (CV4.5).
- **D5 Specification unchanged, implementation proven equal.**  Each faster
  function is registered with `@[csimp]` against the specification function
  it replaces, with the equality proved; theorems keep citing the
  specification.  Where removing an allocation needs a different *type* (an
  `Option` field written `some` on the path), the row names the type change
  and carries its proof migration in the same row (§6, R2).

## 4. Schedule — phases and sub-tasks, in execution order

Each row: one PR, the patch version bumped, the exerciser read on a fresh
archive and recorded, every tier its files reach green.

### ZA1 — ownership and the object table (no dependency on WS-CV)

| Row | Work | Files |
|---|---|---|
| ZA1.1 | **The pre-state is released before the arm.**  `dispatchSyscallChecked` (both sites, `API.lean:4727`, `:5265`) binds the taint plan and the three pre-state reads `applySyscallTaint` makes (`declassificationAuditEpoch`, the audit log's length, `declassificationTaint`; `TaintPropagation.lean:1257–1260`, `:1439–1453`) before running the arm; `applySyscallTaint` gains a form over those captures, `applySyscallTaintCaptured`, with `applySyscallTaint_eq_captured` proving the two equal, so the theorems at `API.lean:6595`, `:6619`, `:6753` are untouched.  The notification arm's refusals move before its first write (D1).  Then the generated C of the arm is read for any remaining shared write (another retainer is fixed in this row, not deferred).  Expected: the three slot-array copies gone at every table size | `Kernel/API.lean`, `InformationFlow/TaintPropagation.lean`, `IPC/CrossCore/NotificationSignal.lean` |
| ZA1.2 | **`RHTable` writes in place.**  `RHTable.modify` (take the slot's entry out with `Array.modify`, update, put back; the present-key case of an insert) and an `insert` implementation that probes for the key first — present: `modify`; absent: the displacement loop returning the array alone (the size grows by one, known before the loop) — registered `@[csimp]` against today's `insert`, with `insertImpl_eq_insert`.  `RHTable.modify` is the primitive WS-CV's CV4.4 `modifyTcbExclusive` uses | `Kernel/RobinHood/Core.lean`, `RobinHood/Bridge.lean` (the `modify` lemmas) |
| ZA1.3 | **A refusal carries the state it was refused in.**  ZA1.1 left one retainer: `syscallDispatchFromAbi` (`Platform/FFI.lean`) answers a refused syscall from the register-spilled state (the cap-fault delivery and the refusal record), and `Kernel` drops the state on `.error`, so that state stays shared across the whole dispatch and every table the syscall writes is copied whole.  `RefusalCarrying α := SystemState → Except (KernelError × SystemState) (α × SystemState)` (`Model/State.lean`) and `RefusalCarrying.ofKernel`, which attaches the input state to each refusal.  `syscallEntryCheckedR`, `dispatchSignalCheckedR`, `signalOperandArmThenTaintR` and `notificationSignalCheckedArmR` (`Kernel/RefusalCarryingDispatch.lean`) each proven `= ofKernel` of the specification; the signal and the wait whose arguments all sit in registers, routed by the entry on the register file (`registerRoutedSyscall`; the signal since `v0.36.75`, the wait since `v0.36.76`), check before they write, every other path is `ofKernel` of the specification.  `syscallDispatchFromAbiImpl` reads the refusal's state, `@[csimp]` against the specification.  Decision (2026-10-07): where a syscall's refusal today follows a write, the syscall is restructured so its checks precede its first write and the refusal reports the state it was refused in; the IPC-buffer TLB fill, the one write before the checks, stays on a refused call.  Each later syscall joins the entry's register-file routing with its own operand reader and equality | `Model/State.lean`, `Kernel/RefusalCarryingDispatch.lean`, `Platform/FFI.lean` |
| ZA1.4 | **`storeObject` writes only what changes.**  When the key is present, the object type unchanged and neither the old nor the new object a VSpace root, only `objects` changes: `storeObject_eq_of_inPlace` proves the other three fields equal, and a `@[csimp]` implementation takes that branch (one probe instead of four tables) | `Model/State.lean` |
| ZA1.5 | **The entry step takes the state.**  `modifyGetKernelState` is inlined, so each entry's step runs on the state taken out of the kernel's cell and no closure carries it | `Platform/FFI.lean` |
| ZA1.6 | **Objects update in their slot.**  `RHTable.modify` (`@[csimp]` to an implementation that takes the slot's entry out with `Array.modify`, applies `f` and puts it back), `SystemState.modifyObject`, and `updateTcb` compiled through them, so on an exclusively owned state neither the object nor its `KernelObject` cell is rebuilt | `RobinHood/Core.lean`, `Model/State.lean`, `IPC/CrossCore/NotificationSignal.lean` |

### ZA2 — the dispatcher's own values (no dependency on WS-CV)

| Row | Work | Files |
|---|---|---|
| ZA2.1 | **Resolve once.**  The gate's resolution produces the slot reference the taint plan consumes; `contentFlowEdges`, `contentFlowClears` and `contentFlowBypassed` take it instead of calling `syscallOperandCap?`, with the planner's theorems restated over a resolved reference and one lemma tying it to `syscallOperandCap?`.  `resolveCapAddress` and `CNode.lookup` gain continuation forms (D2) proven equal to the `Except`/`Option` forms | `Capability/Operations.lean`, `Model/Object/*`, `Kernel/API.lean`, `InformationFlow/TaintPropagation.lean` |
| ZA2.2 | **Compare without constructing** (D3) on the path: `dispatchSyscallChecked`'s current-thread check, `residentElsewhere`, and the `instDecidableEq` closures the reading finds; the `SyscallGate` record passed as its fields | `Kernel/API.lean`, `Scheduler/PriorityInheritance/PerCore.lean` |
| ZA2.3 | **The notification arm updates in place**: the notification taken out with `RHTable.modify`, its fields written; `Notification.pendingBadge : Option Badge` becomes two scalar fields, `hasPendingBadge : Bool` and `pendingWord : Badge`, read through the derived `Notification.pendingBadge` (done at `v0.36.77`: an `Option` around the machine-word badge is a boxed cell, one allocation per signal that left a badge pending).  The flag is kept instead of reading presence off `state = .active` so the derived view equals the old field on every notification, the ill-formed ones included: no invariant becomes vacuous and the reads keep their statements; every write site is restated over the two fields; the decoded-arguments record and the stash's `Option` round trip removed by D2 | `IPC/CrossCore/NotificationSignal.lean`, `Model/Object/Types.lean`, the notification invariants, `Kernel/API.lean` |
| ZA2.4 | **Taint without values**: the plan's edges applied by a function of the syscall class and the resolved reference instead of a list; the state rebuilt only when the taint table changes (`applySyscallTaint` returns `post` itself when no edge source and no origin carries a tag, proved); the equality closure removed by D3 | `InformationFlow/TaintPropagation.lean`, `InformationFlow/Taint.lean` |
| ZA2.5 | **Report through the state**: `ipcBufferWalkPlan` for a message with no overflow words and `syscallReturnOutcome`'s `.returns` value (D2) | `Architecture/IpcBufferTlbFill.lean`, `Platform/FFI.lean` |

WS-CV's rows CV1.2 through CV4.5 run here, as its plan orders them; they
remove §2.1's 55 sites.  ZA3 consumes CV4.5.

### ZA3 — the entries WS-CV keeps (consumes CV4.5)

| Row | Work | Files |
|---|---|---|
| ZA3.1 | **The commit record is written into the state.**  The step's report (outcome, return words, restore kind, `tableBase`, `asid`, `fpLive`, shootdown window, SGI and maintenance lists) becomes a per-core field of the kernel state the step overwrites in place; the HAL reads it after the commit through scalar `@[export]` getters that borrow the state and allocate nothing; CV4.5's record and `commit_restore_eq_restoreTargetOnCore` restated over the field.  At `v0.36.75` the syscall entry needs no field: its restore target crosses the inlined commit as four words read off the committed state (`restoreCommitKindOnCore` and its siblings, each proven equal to the field of `restoreTargetOnCore`) and its unit-shape outcome is a static, which reads 0; the timer, reschedule, fault and secondary entries still pass the `RestoreTarget` record and take the same form here | `SyscallDispatchEntry.lean`, `Model/State.lean`, `Platform/FFI.lean`, `rust/sele4n-hal/src/ffi.rs`, `rust/sele4n-lean-boundary/tests/layout.rs` |
| ZA3.2 | **No pair at the entry.**  With ZA3.1 the step returns the state alone; `modifyGetKernelState` (`FFI.lean:1124`) is `@[inline]` and the entry specialised over its step (CV3.1), so the `(result, state)` pair cancels; the generated C of `lean_syscall_dispatch_cross_core` read for it | `Platform/FFI.lean`, `SyscallDispatchEntry.lean` |
| ZA3.3 | **The re-wrap never fires**: with ZA1.2's `RHTable.modify` under CV4.4's `modifyTcbExclusive`, the `KernelObject` cell is exclusive on every continuing path; the generated C read to confirm the fresh branch is unreachable there | `Model/State.lean` |

### ZA4 — coverage and closure

| Row | Work | Files |
|---|---|---|
| ZA4.1 | **Scenarios beyond one signal**: the exerciser gains a continuing endpoint send/receive rendezvous, a call/reply pair, a yield, a notification wait that consumes a badge, and a signal with a badge `≥ 2^63`; the instrumentation re-run over each, every site recorded in this plan's §2 with its row (a site no row owns gets a row here before any fix).  The yield scenario lands with the yield syscall (ZA4.3).  The partner scenarios need a second thread, an endpoint and a reply object that the root task cannot make (untyped retype carves frames, page tables, untypeds and address spaces only), so the QEMU `virt` deployment configures them (`qemuVirtPartnerTcbId`, `.Inactive` until the exerciser resumes it; the RPi5 deployment is unchanged).  Each partner sequence opens with a step that blocks the current thread, so the next step runs as the other.  First readings (steady state, untraced): receive that blocks 100, send to a waiting receiver 102, wait that blocks 55, signal to a waiter 58, receive holding a reply capability 107, call 190, reply 112 | `smp_exercisers.rs`, `scripts/qemu_exerciser_lib.sh`, `Platform/QemuVirt/Deployment.lean`, this plan |
| ZA4.2 | The rows ZA4.1 adds, each read to zero.  Done for the pending-badge wait at `v0.36.76`: `registerRoutedSyscall` routes it to `dispatchWaitCheckedR`; the consumed notification is written in its slot when `RHTable.findsInPlace` shows the write keeps the table's layout (`notificationWaitOnCore_eq_impl`); `syscallDispatchCrossCoreBracketedStepWords` answers the outcome's tag and six return words, staged by `stageCallerReturnWords`.  Done for the wide-badge signal at `v0.36.77`: `Badge` holds a `UInt64` (R1), the register decode reads it with `readRegWord`, a signal with no waiter merges into the pending word in place (`signalPendingObject`), and the wait returns the word itself (`returnFrameOfBadge`) | per row |
| ZA4.3 | **A yield syscall** (`SyscallId.yield`, 41; seL4 MCS `seL4_Yield`), on the executing core.  Decision (2026-10-11): yield forfeits the budget.  A caller bound to a SchedContext gives up its remaining budget until its next refill, through the same function the timer's budget-exhausted arm uses (factored out of `timerTickBudgetOnCore` and proven to leave that arm unchanged); an unbound caller goes to the back of its priority queue with a fresh time slice.  The per-core non-interference and invariant-preservation theorems land in the same row as the arm.  Its own sites read zero: the charge writes the SchedContext and the TCB in place (`spendBudgetOnCore`, `sliceExpireOnCore` through `modifyObject`, each proven equal to its specification), and a refusal is the state it was handed (`yieldOnCoreR`, proven equal to `yieldOnCore`), which needs the scheduling point to be total (`scheduleEffectiveOnCore_ne_error`, from `RunQueue.bucket_wf`).  The exerciser gains the yield scenario; the 49 it still reads are the scheduling point's (§2.4), read to zero by ZA4.5 | `Model/Object/Types.lean`, `Scheduler/Operations/Core.lean`, `Kernel/API.lean`, the per-syscall tables (lock sets, taint class, return shape, frozen agreement), `rust/sele4n-abi`, `rust/sele4n-sys`, `smp_exercisers.rs` |
| ZA4.4 | **Notification waiters link through the TCB.**  Decision (2026-10-11): `Notification.waitingThreads : List ThreadId` becomes head and tail fields linked through the waiting TCBs' queue links, as endpoint queues are; the notification invariants restated over the intrusive queue (R2).  Two parts, in order.  (1) **Queue links are scalar codes.**  A link written `some t` is a fresh cell (`lean_alloc_ctor(1, 1, 0)`, 53 constructor sites in `DualQueue/Core.c`), so an intrusive queue over `Option` fields allocates on every enqueue, more than the list cell it replaces.  The TCB's `queuePrev`, `queueNext` and `queuePPrev` are stored as one `Nat` each (`0` for `none`, `t + 1` for `some t`; `QueuePPrev` adds the head as `1` and `tcbNext t` as `t + 2`), a bijection with the old type, so each old field is a derived view with the same value on every TCB and the reads keep their statements; the write sites go through setters with `@[simp]` view lemmas.  A queue's boundaries stored in an object are two such codes, read through a derived `IntrusiveQueue`.  (2) **The notification queue.**  `Notification` holds the wait queue's head and tail codes; a wait appends at the tail and a signal wakes the head, first in first out as seL4's `tcbEPAppend`/`tcbEPDequeue` (the list was last in first out); cancellation unlinks in place.  The queue links through a pair of TCB fields of its own (`ntfnPrev`, `ntfnNext`, codes as above) rather than the endpoint links seL4 shares: a thread waits on at most one object either way (its `ipcState` names it), the two extra words per TCB cost nothing on the path, and the endpoint-queue invariants (`dualQueueSystemInvariant`, the `queueNext` blocking conjuncts) then read no notification and keep their statements and proofs.  The notification queue carries its own invariants, stated as the endpoint ones are: link integrity and acyclicity over `ntfnNext`/`ntfnPrev`, the boundaries (head without predecessor, tail without successor, both blocked on that notification), every link joining two threads blocked on the same notification, a thread on no notification queue holding no notification links, and membership (`blockedOnNotification n` iff reachable from `n`'s head), which replaces `tid ∈ ntfn.waitingThreads` in every statement that read the list.  The wait and signal arms write the notification and the TCBs in place (`modifyObject`, fast forms proven equal to the specification), so a wait that blocks and a signal that wakes a waiter make no allocation outside the scheduling point, whose sites are ZA4.5's.  Landed at `v0.36.82`: the links (`TCB.ntfnPrevCode`/`ntfnNextCode`, `Notification.waitHeadCode`/`waitTailCode`), the first-in-first-out wait and wake, cancellation by an O(1) unlink, `NoDupList` deleted, and `notificationWaiterConsistent` restated as the queue's link integrity (ends blocked on the notification, tail without successor, each blocked TCB the head or linked back from its predecessor, each successor blocked on the same notification and naming it back) and membership (a thread blocked on a notification is reached from its head along the successor links, `notificationQueueReaches`; the converse is `notificationQueueReaches_blocked`), preserved by the wait, the signal and the reply transitions, with acyclicity proven from them (`notificationQueue_acyclic`: no waiter follows itself); the boundary and off-queue clauses (a head without predecessor, a thread on no notification queue holding no links) landed in the same version (PR #932 review), where the signal's pop and the cancellation unlink clear the dequeued thread's links and the new head's predecessor; the blocking wait and the waking signal write in place (`notificationWaitOnCore_block_inPlace_eq`, `notificationSignalOnCore_wake_inPlace_eq`), 55 → 42 and 58 → 44, the rest the scheduling point's and the badge message's. | `Model/Object/Types.lean`, `IPC/CrossCore/Notification*.lean`, the notification invariants |
| ZA4.5 | **The run queue links through the TCB**, as seL4's `tcbSchedNext`/`tcbSchedPrev` with a priority bitmap: a bucket is a head and tail per priority, a thread's links and band are TCB fields, and `RunQueue`'s `byPriority` lists, `membership` set, `threadPriority` table and `flat` list are replaced by them (R2: the scheduler invariants restated over the intrusive queue, `flat` kept as a derived view where a theorem reads it).  Enqueue, dequeue and rotate write two or three TCB fields in place.  The row also owns the rest of the scheduling point (§2.4's yield table): selection returns the chosen thread without candidate records, the switch writes the TCB and the per-core slots in place, and the switched-in registers are copied into the core's file without a fresh one.  The yield scenario reads zero.  Two parts, in order.  (1) **Linked lists, scheduling point in place**, landed at `v0.36.82`: the queue is a doubly linked list per core with a list per priority, its links in a per-core table (`RunQueue.links`) and its ends in the queue record, which carries the proof that they describe one queue (`RunQueue.Layout`); enqueue, dequeue and rotation write the record and the touched entries in place (`insertImpl`, `removeImpl`, `rotateToBackImpl`); selection scans the links (`chooseOnLinksCode`); the scheduling point returns the state with no result cell (`scheduleEffectiveOnCoreTotalImpl`) and reuses the current thread's cell (`setCurrentSomeOnCore`); the reschedule flags are one word (`PerCoreFlags`), so the entry's snapshot shares nothing with the state.  Yield reads 0 on a normal build.  (2) **The links move into the TCB.**  Decision (2026-10-12): as seL4, a thread's run-queue links and band are TCB fields, stored as codes as ZA4.4's are, and the per-core queue keeps its ends.  The layout proof can no longer ride in the queue record, so it becomes a system invariant over the objects and the scheduler, proven preserved by every transition that writes a TCB or the scheduler; yield stays at 0.  Landed at `v0.36.82`: six run-link TCB fields and per-core `RunQueueEnds`; the abstract queue stays as an `Erased` ghost and one invariant, `runQueueRefined`, relates it to the links (as seL4 relates its abstract ready queues to the C ones), so the scheduler theorems kept their statements; executable reads walk the links (`queuedOn`, `runQueueWalk`, `runMaxBucketWalk`), each proven equal to the ghost read; yield reads 0 | `Scheduler/RunQueue.lean`, `Model/State.lean`, the scheduler invariants |
| ZA4.6 | **Priority inheritance without a scan**: the threads blocked on a server are reached through a queue linked through their TCBs (the same links as ZA4.4), so the maximum waiter priority is computed from that queue and `waitersOf` becomes a derived view proven equal to it; no object-index walk and no `List` on call or reply.  Landed at `v0.36.84`: four TCB fields (`replyWaiterPrevCode`, `replyWaiterNextCode`, `replyWaitersHeadCode`, `replyWaitersCount`, codes as ZA4.4's), linked last in the call rendezvous and the receive of a call, unlinked by reply, cancellation and timeout; `waitersOf` reads the queue and the compiled maximum walks the codes; `replyWaitersConsistent` joins `ipcReachable`, preserved by every IPC arm the dispatcher runs; the lock footprints declare the linked TCBs (`maxLockSetSize` 24 → 27); destroying a server with reply waiters is refused.  Call 184 → 166, reply 112 → 94 | `Scheduler/PriorityInheritance/*`, `Model/Object/Types.lean` |
| ZA4.7 | **IPC copies registers.**  Decision (2026-10-11): send, receive, call, reply and reply-receive copy the sender's message words straight from its register file into the receiver's, with no message record or word array on the path; the `IpcMessage` specification stays, the copy proven equal to it (D5).  The IPC arms' object writes go through `RHTable.modify` (ZA1.6), the TCB fields are written in place instead of the record rebuilt, and `lookupTcb` takes the continuation form (D2) (§2.4's rows for this class).  The endpoint scenarios read to zero.  Two parts, in order.  (1) **In-place rendezvous**, landed at `v0.36.85`: send, receive, call and reply are routed on the register file (`RegisterRoutedSyscall`), each checked arm decides every refusal on the pre-state and then writes a state nothing else holds (`storeSendRendezvous`, `storeCallRendezvous`, `storeReplyRendezvous`), proven equal to the specification arm (`callDispatchChecked_inPlace`, `replyTransferChecked_inPlace`); the reply-waiter link and unlink rebuild the state record once. Normal build: receive that blocks 5, send to a waiting receiver 15, call 16, reply 9.  (2) **The message lives where seL4 keeps it.**  What part 1 leaves is mostly the delivered message: the entry builds a word array, delivery keeps an `IpcMessage` record in the receiver's `pendingMessage`, and the return frame is built from it.  A state that holds a fresh array cannot be produced without allocating, so this part changes the model type (R2).  Decision (2026-10-14, seL4's default taken): a delivered message lives in the receiver's saved registers and IPC buffer.  Three steps, in order.  (a) **The receiver side**, landed at `v0.36.86`: delivery writes the frame into the receiver's register file and clears `pendingMessage` (`stageDeliveredMessage` through `writeDeliveredFrameToTcb`; the IPC bundle lets a `.ready` thread drop its message, `pendingMessageReadAgrees`); call, reply and a send to a waiting receiver read a message of at most four words from the sender's registers (`RegisterMessage.lean`) and write it as six words (`performCallDelivered`, `performReplyDelivered`, `performSendDelivered`), each proven equal to the staged rendezvous through the commutation of a message-slot write with every write in between (`DeliveryCommute.lean`), no invariant threaded.  Normal build: send to a waiting receiver 3, call 8, reply 1.  (b) **Fields as codes.**  What the paths still allocate (traced at `v0.36.86`) is a constructor cell per field written with a payload: `TCB.ipcState` (`.blockedOnReceive ep`, `.blockedOnReply ep (some r)`), `TCB.replyObject`, `Reply.caller`, the endpoint queue ends (`IntrusiveQueue` and its `some t`), the priority walk's `Option Priority` maximum and the per-core current thread (`reuseSome`).  Each becomes scalar codes with a derived view of the old name, as ZA4.4's links did, so reads keep their statements and only writes change (through setters with `@[simp]` view lemmas).  `ThreadIpcState` takes two codes, the object and a state code that carries the tag and the reply target, chosen so that every pair of words decodes to a state and every state encodes to one pair, a bijection with no invariant and no canonicity field.  In order: (b1) endpoint queue ends, landed at `v0.36.87`: the endpoint keeps its four queue ends as codes (`Endpoint.sendQ`/`receiveQ` derived views), the rendezvous and blocking stores write them in place and take a queue successor or tail as its code, and the taint step holds the thread it reaches across the arm as a code; the 32-byte cell the entry built on these paths was the `MessageInfo` record, so the register fast paths take the message length and the record is built only on the general reply path.  Normal build: reply 1 → 0, send to a waiting receiver 3 → 1, receive that blocks 5 → 3, call 8 → 7.  (b2) `ipcState`, landed at `v0.36.88`: the TCB stores `ipcObjectCode` and `ipcStateCode` (`(0, 0)` ready, `(o + 1, 0)` blocked sending on `o`, `(o, 1)`/`(o, 2)`/`(o, 3)` blocked receiving, on a notification and on a call, `(o, c + 4)` blocked on a reply with target code `c`); `TCB.ipcState` is the derived view and every write goes through `TCB.setIpcState`.  Deciding `ipcState = .ready` through the derived `DecidableEq` built the state to compare it, so the kernel decides it on the words (`ThreadIpcState.decEqOfCodes`), the return path asks whether the caller blocked from the codes (`tcbBlocksReturn`), and the blocking receive's guard reads the receive queue's tail code (`receiveBlocksInPlaceCode`), the last of b1's views built on a path.  Normal build: receive that blocks 3 → 1, call 7 → 5, wait that blocks 6 → 5.  (b3) `replyObject`, `pendingReceiveReply` and `Reply.caller`, landed at `v0.36.89`: the TCB stores `replyObjectCode` and `pendingReceiveReplyCode` and the reply object `callerCode` (`ReplyId.optCode`/`ThreadId.optCode`, the old names derived views), the more-than-four-word call branch is its own function so its `some` is no longer hoisted ahead of the length test, and the receive resolves its reply capability in continuation form (`resolveRecvReplyK`), taking the reply object as its code through the block guard (`replyStashValidCode`) and the blocking store.  Normal build: call 5 → 2, receive naming a reply object 6 → 1.  (b4) the per-core current and the priority maximum, landed at `v0.36.90`: the scheduler and machine keep the per-core current and resident threads as code vectors (`currentCode`, `residentCode`; `reuseSome` retired), a TCB keeps its boost as `pipBoostCode` (the waiter walk returns `computeMaxWaiterCode`), the words step hands the entry the committed current thread as its code (`currentAsCode`), and the resident settle writes its word in place.  Normal build: call 2 → 0, receive for a call 1 → 0, receive that blocks 1 → 0, wait that blocks 5 → 4.  Before (c), landed at `v0.36.91`: the wait that blocks writes its state and queue link in place (`waitBlocksInPlace`, `storeWaitBlocked`, the tail taken as its code), and the signal that wakes a waiter writes the badge into the waiter's register file (`performSignalWokenDelivered`, equal to the general arm by `signalWoken_eq_delivered`), the waiter, its successor and the taint case crossing the arm as codes; the exerciser gains a send that blocks and a receive from a blocked sender.  Normal build: send to a waiting receiver 1 → 0, wait that blocks 4 → 0, signal that wakes a waiter 9 → 0, send that blocks 27, receive from a blocked sender 52.  (c) **Blocked senders**, landed at `v0.36.92`: a sender that blocks keeps its message in its own registers and IPC buffer, read at the rendezvous (`blockedSenderMessage`), so `pendingMessage` leaves the sender side too; the badge, grant right and fault flag move into the sender's TCB (`TCB.setSendCap`).  Decision (2026-10-15, seL4's semantics): its extra capabilities are looked up in its CSpace at the rendezvous (`blockedSenderCapRequest`), so a capability revoked while the sender waits is never transferred; this retires the parked capability list, the pending-transfer delete guard and the revoke filter.  The send that blocks enqueues and parks in place (`storeSendBlock`, sharing `endpointEnqueue_inPlace_eq` with the receive that blocks), and the receive that takes a blocked sender's message pops, wakes and writes the frame's words, read from the sender's registers before any write, into the receiver's (`performReceiveDelivered`, equal to the general arm by `endpointReceiveTakeR_eq`).  Normal build: send that blocks 27 → 0, receive from a blocked sender 52 → 0.  (d) **Reply-receive**, landed at `v0.36.93`: the entry decodes a reply-receive straight from the register file (`decodeSyscallArgsFromState_of_routedReplyRecv`), and one whose reply is at most four words and whose receive leg blocks runs the reply's in-place writes followed by the receive's (`replyRecvOnCore_blocks_inPlace`, `replyRecvOnCore_blocks_delivered`), proven equal to the specification arm (`endpointReplyRecvCheckedArmR_eq`, `dispatchReplyRecvCheckedR_eq`).  Every check of the receive leg is read on the pre-state and carried across the reply leg (`storeReplyRendezvous_receiveGuard`), including the scan for a stashed reply, which reads one code per object (`stashCode`) that no write of the reply leg moves (`replyIsStashed_of_stashView`, through `RHTable.fold_eq_of_slotView`); whether the consumed reply is free is read off its links (`Reply.consumedIsFree`).  Normal build: reply-receive 118 → 0.  A reply-receive whose receive leg finds a sender already waiting runs the general arm; the exerciser does not yet measure it, and it is measured with ZA4's remaining scenarios. | `IPC/DualQueue/*`, `IPC/Operations/Endpoint.lean`, `Kernel/API.lean`, `Platform/FFI.lean` |
| ZA4.8 | **Capability pointers are machine words** (R1): `CPtr` holds a `UInt64`, the decode reads it with `readRegWord`, the theorems restated (R2).  The exerciser gains a capability address `≥ 2^63`, read to zero | `Prelude.lean`, `Capability/Operations.lean`, the decode, `smp_exercisers.rs` |
| ZA4.9 | **Every other syscall** joins the entry's register-file routing (ZA1.3) and is read to zero; a site no earlier row owns is fixed here | per site |
| ZA4.10 | **Every other kernel entry.**  Decision (2026-10-11): the zero rule covers every entry, not only syscalls.  The timer tick, the IRQ entry and the fault entry take ZA3.1's form; the exerciser drives each and reads it to zero | `SyscallDispatchEntry.lean`, `Platform/FFI.lean`, `rust/sele4n-hal/src/ffi.rs`, `smp_exercisers.rs` |
| ZA4.11 | **The first entry after boot allocates nothing**: boot ends by making every object the kernel state holds exclusively owned (one copy, at boot), so the first entry finds nothing shared.  First call after boot reads zero | `Platform/Boot.lean`, `Platform/FFI.lean` |
| ZA4.12 | **The rule is enforced**: the exerciser fails on a non-zero delta for every scenario and every entry, and `CLAUDE.md` gains the standing rule that a kernel entry allocates nothing | `smp_exercisers.rs`, `scripts/qemu_exerciser_lib.sh`, `CLAUDE.md` |
| ZA4.13 | Closure: the reading recorded in `CHANGELOG.md`, `WORKSTREAM_CONTEXT.md` section moved to the closed-workstream file, this plan archived | docs |

## 5. Proof obligations

Every row keeps the specification functions and their theorems unchanged and
adds one equality per replaced function (`@[csimp]`), or one capture lemma
(ZA1.1, ZA2.1).  A row that changes a model type (R2: ZA2.3, ZA4.4, ZA4.5, ZA4.6, ZA4.8) restates the
theorems over it and lands with them.  No `sorry`, no axiom, no `implemented_by`.

## 6. Risks, and decisions deliberately not taken

- **R1 Big words.**  `CPtr` and the message words are `Nat`-backed; a value
  `≥ 2^63` is a heap number in Lean's runtime, so a high-bit operand
  allocates whatever this plan does.  CV4.3 removes it for message words.
  For badges and capability pointers ZA4.1's high-bit scenarios measure it,
  and the row ZA4.2 adds for it carries the type change (the word as a
  `UInt64` field), before ZA4.12 makes a non-zero reading fail.  `Badge` holds
  a `UInt64` since `v0.36.77`; `CPtr` follows in ZA4.8 with its scenario.
- **R2 Type changes cost proofs.**  Decision (2026-10-11): where a model
  type's shape forces an allocation on the path (an `Option` field written
  `some`, a list or array built per call), the type changes and the row that
  changes it restates the theorems over the new type.  `pendingBadge` (ZA2.3)
  was the first; ZA4.4, ZA4.5, ZA4.6 and ZA4.8 are the next.
- **R3 `@[csimp]` hides the fast path from proofs.**  The equality is the
  contract; the specification stays the reference and the host test suites
  run the compiled path.
- **R4 Compiler behaviour.**  In-place reuse and constructor cancellation are
  properties of Lean 4.28's code generator, not of the source; every row reads
  the generated C and the measurement, never the source alone, and a
  toolchain bump re-reads ZA4.1's scenarios.
- **Not taken: a mutable kernel state behind `IO.Ref` fields.**  It would
  remove the copies by giving up the pure transition every theorem is about.
- **Not taken: allocate from a per-syscall arena and reset it.**  It hides the
  allocations instead of removing them, and the time they cost stays.
