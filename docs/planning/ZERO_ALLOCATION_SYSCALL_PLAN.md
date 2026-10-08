# WS-ZA — A syscall that allocates nothing

> **Workstream**: WS-ZA (every heap allocation on the continuing syscall round
> trip is removed; seL4 allocates none).
> **Status**: **IN FLIGHT** — registered at `v0.36.72`; at `v0.36.73` ZA1.1–ZA1.6
> landed with ZA2.1–ZA2.3 and the signal path's parts of ZA2.4 and ZA2.5,
> beside WS-CV CV2.1–CV2.2, as one PR (the rows were measured one at a time
> on the signal round trip, which read 118 → 13).  Asked for by the
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
objects for the first time): **13** at `v0.36.73`.  The 13: the per-trap
context object and its `some` (CV3.1), one return-frame copy of the context
the TCB and the core bank share (CV4.4), the overflow-word cell, the decode
record and its argument array (five), the arm's result cells (two), the
return frame and its outcome (two), and the restore target crossing the
commit (ZA3.1).

**Acceptance**: the exerciser reads **0** for every scenario of ZA4.1, and
from ZA4.3 on it fails on any non-zero delta (a check on the kernel's
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
| ZA1.3 | **A refusal carries the state it was refused in.**  ZA1.1 left one retainer: `syscallDispatchFromAbi` (`Platform/FFI.lean`) answers a refused syscall from the register-spilled state (the cap-fault delivery and the refusal record), and `Kernel` drops the state on `.error`, so that state stays shared across the whole dispatch and every table the syscall writes is copied whole.  `RefusalCarrying α := SystemState → Except (KernelError × SystemState) (α × SystemState)` (`Model/State.lean`) and `RefusalCarrying.ofKernel`, which attaches the input state to each refusal.  `syscallEntryCheckedR`, `dispatchSyscallCheckedR`, `signalArmThenTaintR` and `notificationSignalCheckedArmR` (`Kernel/RefusalCarryingDispatch.lean`) each proven `= ofKernel` of the specification; the signal on a call with no overflow words checks before it writes, every other path is `ofKernel` of the specification.  `syscallDispatchFromAbiImpl` reads the refusal's state, `@[csimp]` against the specification.  Decision (2026-10-07): where a syscall's refusal today follows a write, the syscall is restructured so its checks precede its first write and the refusal reports the state it was refused in; the IPC-buffer TLB fill, the one write before the checks, stays on a refused call.  Each later syscall joins `dispatchSyscallCheckedR` with its own equality | `Model/State.lean`, `Kernel/RefusalCarryingDispatch.lean`, `Platform/FFI.lean` |
| ZA1.4 | **`storeObject` writes only what changes.**  When the key is present, the object type unchanged and neither the old nor the new object a VSpace root, only `objects` changes: `storeObject_eq_of_inPlace` proves the other three fields equal, and a `@[csimp]` implementation takes that branch (one probe instead of four tables) | `Model/State.lean` |
| ZA1.5 | **The entry step takes the state.**  `modifyGetKernelState` is inlined, so each entry's step runs on the state taken out of the kernel's cell and no closure carries it | `Platform/FFI.lean` |
| ZA1.6 | **Objects update in their slot.**  `RHTable.modify` (`@[csimp]` to an implementation that takes the slot's entry out with `Array.modify`, applies `f` and puts it back), `SystemState.modifyObject`, and `updateTcb` compiled through them, so on an exclusively owned state neither the object nor its `KernelObject` cell is rebuilt | `RobinHood/Core.lean`, `Model/State.lean`, `IPC/CrossCore/NotificationSignal.lean` |

### ZA2 — the dispatcher's own values (no dependency on WS-CV)

| Row | Work | Files |
|---|---|---|
| ZA2.1 | **Resolve once.**  The gate's resolution produces the slot reference the taint plan consumes; `contentFlowEdges`, `contentFlowClears` and `contentFlowBypassed` take it instead of calling `syscallOperandCap?`, with the planner's theorems restated over a resolved reference and one lemma tying it to `syscallOperandCap?`.  `resolveCapAddress` and `CNode.lookup` gain continuation forms (D2) proven equal to the `Except`/`Option` forms | `Capability/Operations.lean`, `Model/Object/*`, `Kernel/API.lean`, `InformationFlow/TaintPropagation.lean` |
| ZA2.2 | **Compare without constructing** (D3) on the path: `dispatchSyscallChecked`'s current-thread check, `residentElsewhere`, and the `instDecidableEq` closures the reading finds; the `SyscallGate` record passed as its fields | `Kernel/API.lean`, `Scheduler/PriorityInheritance/PerCore.lean` |
| ZA2.3 | **The notification arm updates in place**: the notification taken out with `RHTable.modify`, its fields written; `Notification.pendingBadge : Option Badge` becomes `pendingBadge : Badge`, presence carried by `state = .active` (already the notification invariant, `IPC/Invariant/Defs.lean:81`), the 152 reads migrated; the decoded-arguments record and the stash's `Option` round trip removed by D2 | `IPC/CrossCore/NotificationSignal.lean`, `Model/Object/Types.lean`, the notification invariants, `Kernel/API.lean` |
| ZA2.4 | **Taint without values**: the plan's edges applied by a function of the syscall class and the resolved reference instead of a list; the state rebuilt only when the taint table changes (`applySyscallTaint` returns `post` itself when no edge source and no origin carries a tag, proved); the equality closure removed by D3 | `InformationFlow/TaintPropagation.lean`, `InformationFlow/Taint.lean` |
| ZA2.5 | **Report through the state**: `ipcBufferWalkPlan` for a message with no overflow words and `syscallReturnOutcome`'s `.returns` value (D2) | `Architecture/IpcBufferTlbFill.lean`, `Platform/FFI.lean` |

WS-CV's rows CV1.2 through CV4.5 run here, as its plan orders them; they
remove §2.1's 55 sites.  ZA3 consumes CV4.5.

### ZA3 — the entries WS-CV keeps (consumes CV4.5)

| Row | Work | Files |
|---|---|---|
| ZA3.1 | **The commit record is written into the state.**  The step's report (outcome, return words, restore kind, `tableBase`, `asid`, `fpLive`, shootdown window, SGI and maintenance lists) becomes a per-core field of the kernel state the step overwrites in place; the HAL reads it after the commit through scalar `@[export]` getters that borrow the state and allocate nothing; CV4.5's record and `commit_restore_eq_restoreTargetOnCore` restated over the field | `SyscallDispatchEntry.lean`, `Model/State.lean`, `Platform/FFI.lean`, `rust/sele4n-hal/src/ffi.rs`, `rust/sele4n-lean-boundary/tests/layout.rs` |
| ZA3.2 | **No pair at the entry.**  With ZA3.1 the step returns the state alone; `modifyGetKernelState` (`FFI.lean:1124`) is `@[inline]` and the entry specialised over its step (CV3.1), so the `(result, state)` pair cancels; the generated C of `lean_syscall_dispatch_cross_core` read for it | `Platform/FFI.lean`, `SyscallDispatchEntry.lean` |
| ZA3.3 | **The re-wrap never fires**: with ZA1.2's `RHTable.modify` under CV4.4's `modifyTcbExclusive`, the `KernelObject` cell is exclusive on every continuing path; the generated C read to confirm the fresh branch is unreachable there | `Model/State.lean` |

### ZA4 — coverage and closure

| Row | Work | Files |
|---|---|---|
| ZA4.1 | **Scenarios beyond one signal**: the exerciser gains a continuing endpoint send/receive rendezvous, a call/reply pair, a yield, a notification wait that consumes a badge, and a signal with a badge `≥ 2^63`; the instrumentation re-run over each, every site recorded in this plan's §2 with its row (a site no row owns gets a row here before any fix) | `smp_exercisers.rs`, `scripts/qemu_exerciser_lib.sh`, this plan |
| ZA4.2 | The rows ZA4.1 adds, each read to zero | per row |
| ZA4.3 | **The exerciser refuses a non-zero delta** for every scenario (it printed the number; now it fails on it) | `smp_exercisers.rs` |
| ZA4.4 | Closure: the reading recorded in `CHANGELOG.md`, `WORKSTREAM_CONTEXT.md` section moved to the closed-workstream file, this plan archived | docs |

## 5. Proof obligations

Every row keeps the specification functions and their theorems unchanged and
adds one equality per replaced function (`@[csimp]`), or one capture lemma
(ZA1.1, ZA2.1).  The type change of ZA2.3 is the one row that restates
theorems; it lands with them.  No `sorry`, no axiom, no `implemented_by`.

## 6. Risks, and decisions deliberately not taken

- **R1 Big words.**  `Badge`, `CPtr` and the message words are `Nat`-backed;
  a value `≥ 2^63` is a heap number in Lean's runtime, so a high-bit operand
  allocates whatever this plan does.  CV4.3 removes it for message words.
  For badges and capability pointers ZA4.1's high-bit scenarios measure it,
  and the row ZA4.2 adds for it carries the type change (the word as a
  `UInt64` field), before ZA4.3 makes a non-zero reading fail.
- **R2 Type changes cost proofs.**  `pendingBadge` (ZA2.3) is the one model
  type this plan changes at its cut; a row that finds another `Option` field
  written `some` on the path decides it the same way in its own row.
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
