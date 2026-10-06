# WS-CV — The register context by value

> **Workstream**: WS-CV (one fixed-width register context, stored by value,
> handed over by reference)
> **Status**: **PLANNED** — registered at `v0.36.50`; no sub-task started.
> Opens **before WS-CB** (maintainer's decision, 2026-10-05): a representation
> change is cheapest with the fewest consumers, and WS-CB adds consumers of the
> saved context (budget-expiry preemption saves and restores it).  Its one
> prerequisite, the FFI slice-2 cut (`v0.36.48`, PR #913), has landed; the
> KSC-1 reschedule-SGI accumulator (`docs/REGISTERED_DEBT.md`) is **not** one —
> CV4.4 reads the caller it needs itself (§3.5), whichever of the two lands
> first.
> **Relationship to WS-BP**: closes the last row the `v0.36.47` audit of PR
> #912 left open (`docs/REGISTERED_DEBT.md`, "The register file is
> `Nat`-backed") and the design that row records: the TCB stores a thread's
> context as the boundary's own fixed-width structure, and the HAL hands each
> core's in-flight context over without allocating.  Unlike WS-CB it **does**
> touch the Rust HAL seam (§3) and changes a Lean upcall's answer type.
> **Audited cut**: `v0.36.48` (PR #913 head), from which every figure, path
> and count below was measured (the inventory is reproduced in §1.2).
> **Phases**: CV0..CV5, each numbered in the order it is to be implemented;
> the sub-task rows are §4, and no count of them is written anywhere else.
> **Prefix**: `CV`.  `cv<digit>` matches no identifier in the tree (measured
> at `v0.36.48` over `SeLe4n/`, `tests/`, `rust/` and `scripts/`, `Cargo.lock`
> excluded), so the identifier-naming gate can enforce the family.
> **Document layout**: §1–§2 say what and why; **§3 is the implementation
> specification** every sub-task row points into; §4 is the schedule; §5 the
> proof obligations; §6 the risks and the decisions deliberately not taken.

## 1. Phase goal

Every kernel entry today converts the thirty-five words the HAL hands over
(`Architecture.TrapContext`, 35 `UInt64` fields, one constructor object of 280
scalar bytes) into the model's `RegisterFile` — `{ pc sp : RegValue, gpr :
RegName → RegValue, pstate tpidr : RegValue }` with `RegValue := ⟨Nat⟩` — and
converts back on the way out.  The conversion in is not a copy: compiled,
`registerFileOfTrapContext` builds a `RegisterFile` whose `gpr` is a **closure
capturing the context object** (`TrapFrameSave.c`: `lean_alloc_closure(…
TrapContext_word___boxed, 2, 1)`), and `saveCapturedSyscallFrame` stores that
`RegisterFile` in the caller's TCB.  So:

1. **A saved context is a pointer into the trap-context object it was captured
   from.**  The HAL must therefore allocate a fresh object per trap; a per-core
   buffer reused across traps would rewrite every context saved from it —
   register corruption across threads and a cross-domain channel.  The
   optimisation the maintainer asked for (one context object per core,
   reused) is unsound until the model stores contexts by value.
2. **The entry/exit path allocates about forty heap objects per syscall** at
   `v0.36.47`, each a trip through the heap's ticket lock: the HAL's context
   and `some` wrapper (2); the Lean closures and the `RegisterFile` (3) and
   four boxed `UInt64`s on the way in; on restore `trapContextOfRegisterFile`
   applies the `gpr` closure thirty-one times, each application boxing a
   `UInt64` (`lean_box_uint64`, 16 bytes) to unbox it again, plus the fresh
   context `ofWords` builds.  The `v0.36.48` cheap wins (`TrapContext.word` as
   a jump table, the bracketed step on the whole `TrapContext`) remove the
   boxed round trips the entry side paid; the restore side still pays its
   thirty-one until the closure is gone.
3. **The word bound is a carried invariant rather than a type.**
   `registerContextsWordBounded` (`RegisterContextBounded.lean`, 30 theorems,
   one per writer) exists only because `RegValue` is an unbounded `Nat`; with a
   `UInt64` carrier the property is the type and the file retires.

The goal is one representation: the TCB's `registerContext`, the per-core
banks and the boundary all carry the **same 35-`UInt64` structure**, so that
capture is a copy of 280 bytes into the model (one allocation, or none when the
thread merely continues), restore is a borrow of the TCB's own object (no
conversion, no allocation), and the HAL hands its in-flight context over as a
**persistent per-core object** the model can never retain, by type.

### 1.1 Acceptance (measured, not stated)

- **The allocation budget, by construction.**  Heap allocations per syscall
  entry+exit on the kernel runtime itself — the Tier 4 QEMU `virt` lane, where
  the HAL's `lean_heap` is the allocator the compiled Lean runs on — are
  counted by that heap's per-core allocation counter, the boot core's slot
  read with IRQs masked across the round trip (CV0.1; the host boundary crate
  links the toolchain's `libleanshared`, so it cannot see the kernel heap,
  §3.6).  The acceptance is not a number but this list, each entry owned by
  the row that leaves it or removes it, and the measured delta on a syscall
  whose caller continues must equal the entries present on that path:
  1. the snapshot — `InFlightContext.snapshot`, one 280-byte constructor
     (CV3.1), the one allocation the design keeps;
  2. the `KernelObject` wrapper the TCB's slot re-wraps when constructor reuse
     does not fire (CV4.4) — present or absent per path, never more than one;
  3. nothing else: the exception classifier's `ExceptionContext` — one
     constructor on every synchronous exception before routing, outside the
     entry lock — is removed by CV0.4; the TCB record and its `RegisterFile`
     update in place because CV4.4 makes them uniquely referenced at the
     write; and **no boxed `UInt64` or closure** is allocated on the
     entry/exit path — the generated C of `Platform/FFI.c`,
     `SyscallDispatchEntry.c`, `TrapFrameSave.c`, `ContextRestore.c` and
     `FaultEntry.c` contains no `lean_alloc_closure`, no `lean_box_uint64` and
     no `lean_alloc_ctor` reachable from the entry functions other than the
     snapshot's (read at CV5.1, not scanned).
  A delta above the list is a failed acceptance traced to its allocation
  site, not a cost recorded as the new figure.
- The HAL's `ffi_trap_context` allocates nothing (`lean_heap` counter
  unchanged across the call; Rust unit test, CV3.4).
- The two-trap hazard test (CV0.2, re-run at CV3.5): two traps on one core,
  the first's context saved into a TCB **through the real save path**
  (`saveCapturedSyscallFrame`, reached through the exported entry wrapper, by
  a syscall whose outcome is `.blocks`, so the stage rewrites no word of it),
  the second's words all distinct from the first's and published into the
  same per-core object — the TCB's saved context, read back from the state
  after the second trap, is the first trap's, word for word.
- Every tier green; every Tier 3 anchor scoped to a touched file executed.

### 1.2 The surface, measured at `v0.36.48`

| What | Where | Count |
|---|---|---|
| `RegisterFile` references | 70 files / 816 lines (`SeLe4n/` 43 / 347, `tests/` 8 / 44, `docs/` 12 / 361, `rust/` 5 / 20) | |
| `RegValue` references | 50 files / 586 lines (`SeLe4n/` 22 / 218) | |
| `registerContext` | 70 files / 541 lines | |
| `regsOnCore` / `setRegsOnCore` | 31 / 310 and 25 / 148 | |
| `TrapContext` | 29 files / 313 lines | |
| `.gpr` reads | 17 files / 91 lines (`SeLe4n/` 55, `tests/` 33) | |
| `writeReg` call sites | 6 files / 33 lines in `SeLe4n/` (+ 7 in `tests/DecodingSuite.lean`) | |
| `gpr := fun …` literal constructions | 49 sites, almost all in tests and the trace harness | |
| Theorems mentioning a register term | 292 in 49 files (`RegisterFile` 118, `regsOnCore` 91, `RegValue` 86, `contextMatchesCurrent` 86, `registerContext` 77, `wordBounded` 41, `RegName` 39, `gpr` 17, `writeReg` 12, `funext` over registers 3) | |
| Tier 3 anchor lines touching register terms | 78 (`contextMatchesCurrent` 18, `saveOutgoingContext` 13, `registerContext` 11, `writeReturnFrameToTcb` 9, `FaultRegisterWindow`/`spill` 7, `writeFaultRegistersToTcb` 6, `writeFfiRegistersToTcb` 6, …; none on `writeReg`, `readReg`, `RegName`) | |

Stores: `TCB.registerContext : RegisterFile := default`
(`Model/Object/Types.lean:1007`, the only TCB register field); `MachineState.coreRegs
: Vector RegisterFile numCores` (`Machine.lean:836`) with `regsOnCore` /
`setRegsOnCore`; `FrozenSystemState` shares `MachineState` and `TCB`;
`ObservableState.machineRegs : Option RegisterFile` (`InformationFlow/Projection.lean:82`);
`RestoreTarget.user (context : RegisterFile)` (`ContextRestore.lean:131`).
Writers: the trap-frame saves (`saveTrapFrameOnCore`, `saveVacatedFrameOnCore`,
`saveCapturedTrapFrame`/`SyscallFrame`), `stageReturnFrame` → `writeReturnFrameToTcb`
(~14 `API.lean` sites), `stageRestartFrame` → `writeRestartFrameToTcb`,
`FaultRegisterWindow.spill` → `writeFaultRegistersToTcb`, `writeFfiRegistersToTcb`,
the scheduler's `saveOutgoingContext(OnCore)` / `restoreIncomingContext…`,
`Adapter.writeRegisterState`, `setPC`.  Readers: `decodeSyscallArgs` (`readReg`),
`readReturnFrame`, `readReturnValue`, `RestoreTarget.deliveredFrame?`,
`FaultContext.ofRegisterFile`, the information-flow projections and their
unwinding relations (`machineRegs` compared by the non-lawful `BEq`), the
runtime contracts (`registerContextStableCheck(OnCore)`).  Invariants:
`contextMatchesCurrent` (`machine.regs == tcb.registerContext`, a conjunct of
`schedulerInvariantBundleFull` and `ipcSchedulerCouplingInvariantBundle`) and its
per-core form; `registerContextsWordBounded` (no bundle); `ipcInvariantFull` has
no register conjunct (writers discharge it by TCB-field-update frames).

## 2. Design decisions

**D1 — one structure, the model's name.**  `SeLe4n.RegisterFile` becomes the
35-field `UInt64` structure that `Architecture.TrapContext` is today (`x0`–`x30`,
`sp`, `pc`, `pstate`, `tpidr`, in the trap-frame layout's order), and
`TrapContext` is retired: the boundary type *is* the model type, so
`registerFileOfTrapContext` / `trapContextOfRegisterFile` and their round-trip
theorems have nothing left to say and are deleted with it.  The name
`RegisterFile` stays because it is the proofs' vocabulary (118 theorems); the
layout is `TrapContext`'s because the HAL, the boundary layout test
(`rust/sele4n-lean-boundary`) and the `const` asserts already pin it.  The
accessors keep their call syntax as definitions, so readers do not change
shape: `rf.pc`, `rf.sp`, `rf.pstate`, `rf.tpidr` are fields; `rf.gpr r` is a
definition (`RegisterFile.gpr (rf) (r : RegName) : RegValue := ⟨(rf.word r.val).toNat⟩`,
with `word` the byte-indexed jump table `v0.36.48` introduced); `readReg` is
`gpr`; `writeReg rf r v` is a `match` on `r.val` writing the field, a no-op for
`r.val ≥ 31` (`x31` is the zero register; today's lambda stores the write and
`readReg_writeReg` reads it back, which no hardware does).  `RegValue` stays as
the type of a register *value* where arrays of them live (`IpcMessage.registers`,
`SyscallDecodeResult.msgRegs`, `replyRegisters`, `FaultReply`) until CV4.3
retypes those arrays to `UInt64`; `RegValue.valid` stays with them until then.  `writeReg` takes a `UInt64`-valued argument where every live
writer already has one (`stageReturnFrame`, `spill`, `writeFfiRegistersToTcb`
are fed `UInt64`s and wrap them today); the one writer handed an arbitrary
`RegValue`, `Adapter.writeRegisterState` (and `adapterWriteRegister` above
it), is **retyped to take a `UInt64`**: neither carries a validity hypothesis
today (`adapterWriteRegister` checks only `registerContextStable`), so a
`.toUInt64` narrowing would truncate a value `≥ 2^64` silently; with the
argument a `UInt64` no such value can be passed, nothing narrows, and the
theorems over the pair (`ProofHooks`, `CrossSubsystemPerCorePreservation`,
the reachability census) are restated over the word.

**D2 — both stores stay.**  The TCB's `registerContext` and the per-core bank
`machine.coreRegs` both become the new `RegisterFile`; `contextMatchesCurrent`
(`machine.regs == tcb.registerContext`) keeps its statement and becomes
decidable equality, because the structure derives `DecidableEq` and the
`BEq` is lawful — `RegisterFile.not_lawfulBEq` and `TCB.not_lawfulBEq` retire
at CV1.1, and the `beq_*` lemmas that stood in for `LawfulBEq` are kept there
as one-line corollaries and retire with their last consumer at CV1.2.  Collapsing the bank into
the TCB (the physical registers *are* the current thread's context) would
delete `setRegsOnCore` (148 lines), `contextMatchesCurrent` (86 theorems) and
the information-flow `machineRegs` projection's independent source; it is a
second model change with its own unwinding-relation rework and is **not** this
workstream (§6).

**D3 — the in-flight context is a persistent per-core object of its own type.**
The HAL owns one 288-byte Lean object per core (`HEADER_BYTES + 280`), header
`m_rc = 0` (persistent: `lean_inc`/`lean_dec` are no-ops, it is never freed,
`lean_is_exclusive` is false so compiled Lean never updates it in place), tag 0,
no object fields, plus one persistent `some` wrapper per core pointing at it.
`ffi_trap_context` writes the trap frame's 35 words into the core's object and
returns the core's wrapper: **no allocation**.  On the Lean side its type is
`Architecture.InFlightContext`, a structure with the same 35 `UInt64` fields
but a different name, with one way out: `InFlightContext.snapshot : InFlightContext
→ RegisterFile`, a structure literal of the 35 fields, which compiles to one
`lean_alloc_ctor(0, 0, 280)` and 35 reads and writes — the copy.  `SystemState`
has no field of type `InFlightContext` and `snapshot` is its only consumer
outside the entry wrappers, so the model **cannot** retain the per-core buffer:
that is a fact of the types, not a convention.  The entry wrappers read
arguments (`x0`–`x7`, `pc`, `pstate`, `sp`, `x30`) from the `InFlightContext`
directly (fields, no allocation) and snapshot once, where today's
`saveCapturedSyscallFrame` saves the frame.

**D4 — restore borrows the TCB's context.**  `RestoreTarget.user` carries the
TCB's `registerContext` and `restoreTrapFrame` passes it to
`ffiRestoreStageContext : (@& RegisterFile) → BaseIO Unit` unchanged — no
`trapContextOfRegisterFile`, no fresh object.  The HAL's `trap_context_of_lean`
accepts the executing core's own in-flight object by address (its shape is
known) and any other pointer by the exact-size and header refusal it applies
today; the staging copy, the `SPSR` sanitising and the halts are unchanged.

**D5 — the word bound is the type.**  `RegisterFile.wordBounded`,
`machineWordBounded`, `registerContextsWordBounded` and the 30 preservation
theorems of `RegisterContextBounded.lean` retire with the `Nat` carrier, as do
the `_wordBounded` lemmas beside the pure writers; `RegValue.valid` stays only
where `RegValue` stays (D1).

## 3. Implementation specification

### 3.1 `SeLe4n/Machine.lean` — the carrier (CV1)

- `structure RegisterFile` with fields `x0 … x30 sp pc pstate tpidr : UInt64`,
  `deriving Repr, DecidableEq, Inhabited`; `default` is every field `0` (a fresh
  thread), as today.  Field order is the trap-frame layout, so the compiled
  object is byte-identical to today's `TrapContext` (280 scalar bytes, field `i`
  at `8 · i`); the layout constants (`trapFrameSpWord = 31`, `…PcWord = 32`,
  `…PstateWord = 33`, `…TpidrWord = 34`, `trapFrameWordCount = 35`) move here
  from `TrapFrameSave.lean`.
- `RegisterFile.wordOfByte : RegisterFile → UInt8 → UInt64` and `word : Nat →
  UInt64` (the `v0.36.48` jump table) move here; `ofWords`, `ofWords_word`,
  `word_ofWords`, `word_of_ge` with them.
- `RegisterFile.gpr (rf) (r : RegName) : RegValue := ⟨(rf.word r.val).toNat⟩`
  for `r.val < 31`, `⟨0⟩` otherwise (the zero register; `arm64GPRCount` stays
  32 and `RegName.isValid` stays `< 32`, so no `RegName` consumer moves).
- `readReg rf r := rf.gpr r`.  `writeReg (rf) (r : RegName) (v : UInt64) :
  RegisterFile` — a `match` on `r.val` over `0 … 30`, identity otherwise.
  `readReg_writeReg_eq` (under `r.val < 31`), `readReg_writeReg_ne`,
  `writeReg_zero_register` (`r.val ≥ 31 → writeReg rf r v = rf`) replace today's
  two lemmas; `writeReg_wordBounded` and `writeReg_uint64_wordBounded` retire.
- `RegisterFile.ext` becomes the derived structure extensionality; the
  `funext hgpr` form and `not_lawfulBEq` retire (`BEq` is `DecidableEq`'s and
  lawful); `RegisterFile.beq_self/_def/_symm/_trans` are re-proved as
  corollaries of `LawfulBEq` and kept until CV1.2 retires them with their last
  consumer.
- `wordBounded`, `default_wordBounded`, `machineWordBounded`,
  `machineWordBounded_default` retire (D5).  `setPC` writes `pc` as a `UInt64`.
- `MachineState.coreRegs : Vector RegisterFile numCores` and `regsOnCore` /
  `setRegsOnCore` keep their statements; their simp algebra is unchanged.

### 3.2 The writers and readers (CV1, same cut as 3.1)

- `RegisterFile.stageReturnFrame` (`SyscallReturn.lean:552`): six `writeReg`
  calls on `UInt64`s — the `⟨(…).toNat⟩` wrappers go.  `stageRestartFrame`,
  `FaultRegisterWindow.spill` (`Model/Fault.lean:263`, today a whole-`gpr`
  lambda: becomes a structure update of `x0`–`x7`, `x30`, `sp`),
  `writeFfiRegistersToTcb`, `restartAtSvc` (`pc - 4` in `UInt64`, wrapping
  subtraction stated and proved harmless under `pc ≥ 4` for a frame from an
  `SVC`), `Adapter.writeRegisterState` and `adapterWriteRegister` (retyped to take a
  `UInt64`; nothing narrows — §3.1).
- `FaultContext.ofRegisterFile`, `decodeSyscallArgs` / `readReg`,
  `readReturnFrame`, `readReturnValue`, `RestoreTarget.deliveredFrame?`: read
  through `gpr` as today (`RegValue` out), or through the field where the
  consumer wants a `UInt64` (`decodeSyscallArgs` does: it narrows every
  argument today).
- The 49 `gpr := fun …` literals (tests, `MainTraceHarness`, two Lean-side
  witnesses) become structure literals or `ofWords`; the `MainTraceHarness`
  output must not change — `tests/fixtures/main_trace_smoke.expected` is the
  check, and a change to it needs its rationale.
- `contextMatchesCurrent` / `OnCore`, `registerContextStableCheck(OnCore)`,
  `lowEquivalentSliceOnCoreCheckWithRegs`: statements unchanged; the `==` is
  now lawful, so the proofs that routed around `not_lawfulBEq` simplify.

### 3.3 The boundary (CV2)

- `Architecture.TrapContext` deleted; `Platform.FFI.ffiRestoreStageContext :
  (@& RegisterFile) → BaseIO Unit`; `restoreTrapFrame` stages `ctx` directly;
  the entry binding becomes `Platform.FFI.ffiTrapContext : BaseIO (Option
  RegisterFile)` for this phase (the HAL writes the 35 words into a
  `RegisterFile` object; `syscallEntryContextOrFaulted` and the entry wrappers
  read it directly) — a temporary, still-allocating binding that §3.4 replaces.
- `registerFileOfTrapWords`, `registerFileOfTrapContext`,
  `trapWordsOfRegisterFile`, `trapContextOfRegisterFile`, both round-trip
  theorems and `registerFileOfTrapContext_wordBounded` deleted; their Tier 3
  anchors (`ContextRestore` `:4358`, `TrapFrameSave` `:4342–4343`) deleted or
  retargeted to `snapshot` (§3.4).
- `Kernel.faultEntryFrame?` answers `Option (RegisterFile × ExceptionContext ×
  FaultRegisterWindow)` from the `Option RegisterFile` binding in this phase;
  CV3.1 moves its input to `InFlightContext` with the `RegisterFile` taken by
  `snapshot` (§3.4).
- `SeLe4n/Testing/BoundaryProbes.lean` and `rust/sele4n-lean-boundary/tests/layout.rs`
  retarget: the probes export `RegisterFile.word` / `ofWords`; the Rust side's
  `TRAP_CONTEXT_*` constants are unchanged (35 words).  The `snapshot` export
  and the "a snapshot of an in-flight object is a *different* object with the
  same 35 words" test are CV3.3's (§3.4).
- `scalar_words_of_lean::<35>` / `trap_context_of_lean` keep their exact-size
  refusal for heap objects.

### 3.4 The in-flight object (CV3)

- Rust: `trap::InFlightContextObjects` — per core, a 288-byte 8-aligned static
  (`[u64; 36]`-shaped, header word first) and a 16-byte `some` wrapper, both
  initialised at the core's Lean-runtime bring-up with `lean_set_persistent`
  semantics (`m_rc = 0`, `m_cs_sz = 0`, `m_other = 0`, `m_tag = 0` for the
  context; tag 1, one object field for the wrapper).  `ffi_trap_context` writes
  the frame's 35 words into the core's object and returns the core's wrapper,
  or `lean_box(0)` when no frame is published.  `trap_context_of_lean`: `o ==
  in_flight_object(core) → Some(words)`; otherwise today's path.
- Lean: `Architecture.InFlightContext` (35 `UInt64` fields, same order;
  `deriving Repr, DecidableEq`), `InFlightContext.snapshot`, theorem
  `snapshot_word : (c.snapshot).word i = c.word i`; `Platform.FFI.ffiTrapContext
  : BaseIO (Option InFlightContext)`; `syscallEntryContextOrFaulted` over
  `Option InFlightContext`; the entry wrappers read arguments from the
  `InFlightContext`'s fields and snapshot once into `saveCapturedSyscallFrame`.
  `SystemState` and every object type stay free of `InFlightContext` — checked
  by the type checker (no field of that type exists), stated in the docstring.
- Rust tests: the per-core object's header after `lean_dec` is unchanged
  (persistence); `ffi_trap_context` leaves CV0.1's monotone `allocations`
  counter unchanged — not the `live_allocations` census, which a temporary
  object allocated and freed inside the call would leave equal too; two traps on one core with distinct words, a snapshot of the first
  taken in between, the snapshot unchanged after the second (a unit test of
  the compiled `snapshot`, beside — not instead of — the hazard test of CV0.2,
  which drives the real save path and reads the TCB back, re-run at CV3.5); the by-address acceptance in `trap_context_of_lean` and its
  refusal of a *different* core's object.

### 3.5 Restore and the return frame (CV4)

- `restoreTargetOnCore` carries `tcb.registerContext`; `restoreTrapFrame`
  borrows it (D4).  `stageReturnFrame` on the TCB's context is a structure
  update, and compiled Lean updates in place only an object with one
  reference.  The entry wrapper already commits through
  `Platform.FFI.modifyGetKernelState` (`syscallDispatchCrossCoreEntry`,
  `SyscallDispatchEntry.lean`; `IO.Ref.modifyGet` takes the cell, so the step
  owns the state's only reference, and the one `getKernelState` on the path,
  `readCallerOverflowWords`, releases its reference before the step runs), so
  the second references are below the state, on the path from the state to
  the context — the derivation is a reading of that path, `objects` to the
  TCB to `registerContext` and the bank, for every holder of each object —
  and CV4.4 removes each: `updateTcb` / `modifyTcb` (`Model/State.lean`, `IPC/Operations/Endpoint.lean`)
  read the TCB record out of the table and insert `f t` while the slot still
  holds `t`, so `f` always sees a shared record and the compiled update copies
  it and the `RegisterFile` under it; `saveTrapFrameOnCore`
  (`Architecture/TrapFrameSave.lean`) stores one `rf` object in the TCB **and**
  in the bank `machine.coreRegs`, and `stageCallerReturn`
  (`Architecture/ContextRestore.lean`) updates the TCB's copy and then the
  bank's separately, so at the write the object is shared by its two holders
  (D2 keeps both holders; it does not need two objects); and
  `stageCallerReturn` takes the **pre-state** to read the caller's id, so the
  pre-state's table keeps the old records alive across the stage.  CV4.4 gives the save and the stage a take-based
  `SystemState.modifyTcbExclusive` — the slot's value swapped out, `f` run on a
  uniquely referenced record, the result swapped back, `rewriteObject`'s
  witnessed admissibility kept — **takes the context out of both holders**
  before the stage (the bank slot and the TCB field swapped with the shared
  `default` constant, a closed term the runtime allocates once), updates the
  one object in place and stores it back into both, so `contextMatchesCurrent`
  holds with one object behind two holders, and hands the stage the caller as
  a `ThreadId` read from `st.scheduler.currentOnCore execCore` before the arm
  runs, instead of the pre-state (the KSC-1 accumulator's seam switch captures
  the same value; CV4.4 reads the slot itself and takes that capture's field
  if it has landed, so neither workstream waits on the other) — so
  exclusivity is the path's construction, and CV0.1's counter checks it
  (§1.1).
- `ffiSyscallReturnFrame` (the six return registers to the HAL's mailbox) is
  unchanged.

### 3.6 Measurement (CV0, CV5)

- `lean_heap::HeapStats` gains a monotone `allocations` counter **per core**
  (`allocations_by_core : [u64; CORE_COUNT]`, indexed by `current_core_id`,
  the total being their sum), incremented
  at **one** point per successful allocation: in `Heap::alloc_small`, and in
  `Heap::alloc` only on its large-object arm (`Heap::alloc` forwards every
  request that fits a small class to `alloc_small`, which already counts it,
  so counting in both would double every forwarded allocation and the
  "at most two" acceptance of §1.1 would misread); the counter is read **on the kernel runtime, in the
  Tier 4 QEMU `virt` lane**, in the `per_core_stats` exerciser pattern
  (`rust/sele4n-hal/src/smp_exercisers.rs`, `scripts/qemu_exerciser_lib.sh`):
  a `heap_allocations_per_syscall` exerciser reads the counter on the boot
  core, drives one syscall round trip through the Lean kernel, reads it again
  and prints the delta on its UART line, which the lane's library extracts.
  The heap is one for every core (`lean_heap.rs`'s concurrency note: the
  exception classifier and a secondary core's bring-up probe allocate outside
  the kernel-entry lock), so a heap-wide delta would charge another PE's
  allocation to the boot core's syscall; the exerciser reads **its own core's**
  slot and masks IRQs on the boot core across the two reads (the round trip
  needs none; a pended tick is taken after the second read), so the delta is
  the syscall's and nothing else's.  CV3.4's host unit test is single-threaded
  and reads the total.
  The host boundary crate cannot carry this measurement: it links the compiled
  Lean archive against the toolchain's `libleanshared` and deliberately not
  against `sele4n-hal`, whose `lean_runtime` would be a second definition of
  every `lean_*` symbol (`rust/sele4n-lean-boundary/Cargo.toml`), so on the
  host the allocations go through the upstream runtime where no counter
  exists.  The baseline is recorded at CV0.1 and the result at CV5.1 in the
  CHANGELOG.  No gate pins the number: it is evidence, read by review (the
  exerciser's verdict is only that the two reads happened and the delta is a
  word).

## 4. Schedule — phases and sub-tasks, in execution order

Sequential unless a row says otherwise.  A row's proofs land in the same
sub-task as the definition they cover, or in the lower-numbered row it cites.

### CV0 — baseline and fixtures (nothing in the model changes)

| # | Sub-task | Output |
|---|---|---|
| CV0.1 | The per-core heap allocation counter (§3.6) and the QEMU-lane round-trip measurement (`heap_allocations_per_syscall` exerciser, Tier 4 `virt`, Lean-linked image); record the baseline per syscall at the plan's opening version in `CHANGELOG.md` | `lean_heap.rs`, `rust/sele4n-hal/src/smp_exercisers.rs`, `scripts/qemu_exerciser_lib.sh`, one Tier 4 script |
| CV0.2 | The two-trap hazard test written against today's code, **expected to pass today** (every trap allocates), **through the real TCB save path**: the boundary crate publishes trap 1's words, calls the exported entry wrapper so `saveCapturedSyscallFrame` stores the first context into a TCB of a probe state — with a syscall whose outcome is `.blocks` (a Receive on an endpoint no sender waits on), because `stageCallerReturn … .blocks = post` (`stageCallerReturn_blocks`, `Architecture/ContextRestore.lean`) stages nothing, while a returning syscall's stage rewrites `x0`–`x5` in the TCB and the bank (`stageFrameRegs`) and a word-for-word comparison would then fail for a reason that is not the hazard — publishes trap 2's words (all distinct) through the same per-core path, then reads that TCB's saved context back through a `BoundaryProbes` export and compares it word for word to trap 1's (§1.1) — a standalone snapshot comparison would still pass if an entry wrapper retained the reusable object, skipped the snapshot at the save site or stored the wrong context, so it is not the acceptance; this test is the regression test CV3 must keep green | `rust/sele4n-lean-boundary/tests/`, `SeLe4n/Testing/BoundaryProbes.lean` |
| CV0.3 | Sweep the 78 Tier 3 anchor lines of §1.2 into a list in this plan's §7, each with the sub-task that retargets or deletes it | §7 below |
| CV0.4 | The exception classifier classifies the `ESR_EL1` word, not a context: `Architecture.classifySynchronousExceptionOfEsr : UInt64 → SynchronousExceptionClass` (the body of today's `classifySynchronousException`, which reads only `extractExceptionClass ectx.esr`), with `classifySynchronousException ectx := classifySynchronousExceptionOfEsr ectx.esr` by definition so every theorem over the context form is unchanged, and the export `lean_classify_synchronous_exception` (`Kernel/FaultEntry.lean`) calls the word form — its generated C then builds no `ExceptionContext`, so the one upcall outside the entry lock that allocated on every synchronous exception (`trap.rs`, `build.rs`'s `LEAN_UPCALLS_OUTSIDE_THE_ENTRY_LOCK` justification, `lean_heap.rs`'s concurrency note) allocates nothing; the three notes rewritten to say so (the heap's lock stays load-bearing for the secondary core's bring-up probe), `classifySynchronousExceptionExport_def` restated over the word form, the Rust mirror pin unchanged; the generated C of `FaultEntry.c` read for the export's body; CV0.1's exerciser delta read before and after (§1.1 entry 3; consumes CV0.1) | `SeLe4n/Kernel/Architecture/Fault.lean`, `SeLe4n/Kernel/FaultEntry.lean`, `rust/sele4n-hal/src/trap.rs`, `rust/sele4n-hal/build.rs`, `rust/sele4n-hal/src/lean_heap.rs` | S |

### CV1 — the carrier (§3.1, §3.2): the bulk of the work, one PR per row, each with its own documentation

| # | Sub-task | Output |
|---|---|---|
| CV1.1 | `RegisterFile` as the 35-field `UInt64` structure with `gpr`, `readReg`, `writeReg`, `word`, `ofWords` and their lemmas; `TrapContext`'s layout constants move; `wordBounded` retires; the three `not_lawfulBEq` witnesses (§6) are deleted — they are false on a lawful carrier and only prose cites them — while `RegisterFile.beq_self` / `beq_def` / `beq_symm` and the other `beq_*` lemmas are **kept as compatibility lemmas**, re-proved as one-line corollaries of `LawfulBEq`, so their consumers in the scheduler, architecture and information-flow files compile unchanged in this row; **in the same row, because nothing compiles beyond `Machine.lean` without them**: the writers of §3.2 on the new carrier (`stageReturnFrame`, `stageRestartFrame`, `spill`, `writeFfiRegistersToTcb`, `restartAtSvc`, `writeRegisterState`, `setPC`), the 49 literals, `Repr`; the `_wordBounded` lemmas and `RegisterContextBounded.lean` deleted; `contextMatchesCurrent` proofs simplified to decidable equality; **every one of the 292 register theorems compiles**; fixture `main_trace_smoke.expected` unchanged or its change justified; **the documentation of the change in the same PR** (the repository rule): the register-file passages of `docs/spec/SELE4N_SPEC.md` (the carrier, the `x31` semantics), `docs/DEVELOPMENT.md` §5 if a file moved, `WORKSTREAM_CONTEXT.md`, the `v0.36.47` debt row shortened to CV2–CV4, the evidence-index rows of the retired theorems, the CHANGELOG entry | `SeLe4n/Machine.lean`, the 43 `SeLe4n/` files, the 8 test suites, docs |
| CV1.2 | The information-flow surface: `ObservableState.machineRegs`, the per-core fragments and `lowEquivalentSliceOnCoreCheckWithRegs` on lawful equality; the `machineRegs` unwinding relations re-proved where they cited `beq_*`; then the `beq_*` compatibility lemmas of CV1.1 are **retired with their last consumer** — every citing site (the scheduler and architecture files included, enumerated by the build when the lemmas are deleted) rewritten to `beq_iff_eq` / decidable equality — so the lemmas are never deleted while a consumer remains; the spec's information-flow equality passages and the evidence-index rows of the re-proved unwinding relations in the same PR (consumes CV1.1) | `InformationFlow/*`, `Machine.lean`, the remaining `beq_*` consumers, docs |

### CV2 — one boundary type (§3.3)

| # | Sub-task | Output |
|---|---|---|
| CV2.1 | `TrapContext` deleted; `ffiRestoreStageContext` over `RegisterFile`; `restoreTrapFrame` stages the TCB context; conversions and round-trip theorems deleted; `faultEntryFrame?` on `RegisterFile`; **the entry binding retyped in the same row**: `Platform.FFI.ffiTrapContext : BaseIO (Option RegisterFile)` — the HAL's `ffi_trap_context` writes the 35 words into a `RegisterFile` object (the layout constants CV1.1 moved), `registerFileOfTrapContext` goes with the conversions, and `syscallEntryContextOrFaulted` and the entry wrappers read the `RegisterFile` directly — a **temporary** binding that still allocates per trap, replaced by `Option InFlightContext` in CV3.1 (consumes CV1.1); anchors retargeted | `Architecture/TrapFrameSave.lean`, `ContextRestore.lean`, `Platform/FFI.lean`, `FaultEntry.lean`, `SyscallDispatchEntry.lean` |
| CV2.2 | `BoundaryProbes.lean` and `layout.rs` retargeted to `RegisterFile.word` / `ofWords`; the Rust constants unchanged; Tier 1 lane green | `SeLe4n/Testing/`, `rust/sele4n-lean-boundary/` |

### CV3 — the persistent in-flight object (§3.4)

| # | Sub-task | Output |
|---|---|---|
| CV3.1 | `Architecture.InFlightContext`, `snapshot`, `snapshot_word`; `ffiTrapContext : BaseIO (Option InFlightContext)` replacing CV2.1's temporary `Option RegisterFile` binding; `syscallEntryContextOrFaulted` and the entry wrappers on it; `SystemState` stays free of the type (consumes CV2.1) | Lean |
| CV3.2 | `trap::InFlightContextObjects`: per-core persistent object and wrapper, initialised at runtime bring-up; `ffi_trap_context` writes and returns without allocating; `trap_context_of_lean` accepts the executing core's object by address | `rust/sele4n-hal/src/trap.rs`, `ffi.rs`, `lean_runtime/` |
| CV3.3 | The cross-language test extended: a snapshot is a different object with the same words; the probes export `snapshot` | `rust/sele4n-lean-boundary/` |
| CV3.4 | Rust unit tests: persistence after `lean_dec`, zero allocations across `ffi_trap_context` read from CV0.1's monotone `allocations` counter (§3.4; the live census cannot see an allocation freed before return), by-address acceptance, refusal of another core's object | `ffi.rs` tests |
| CV3.5 | The hazard test of CV0.2 re-run against the reused object — trap 1 saved through `saveCapturedSyscallFrame` into the probe TCB, trap 2 published into the same persistent per-core object, the TCB read back — must still pass; it is the acceptance test of D3 (§1.1), and fails if an entry wrapper retains the object, skips the snapshot at the save site or stores the wrong context (consumes CV0.2, CV3.1, CV3.2) | boundary crate |
| CV3.6 | QEMU `virt` four-PE boot (Tier 4 lane) green with the persistent objects: every core traps, snapshots, restores | CI |

### CV4 — restore borrows, return frame updates in place (§3.5)

| # | Sub-task | Output |
|---|---|---|
| CV4.1 | `restoreTargetOnCore` / `restoreTrapFrame` on the TCB's object; `RestoreTarget.user (context : RegisterFile)` unchanged in statement | `ContextRestore.lean`, `FFI.lean` |
| CV4.2 | `stageReturnFrame` as a structure update on the TCB's context; measured allocation count per syscall recorded | `SyscallReturn.lean`, measurement |
| CV4.3 | `IpcMessage.registers : Array RegValue` → an **unboxed** word carrier, `MessageWords`, a `ByteArray` of `8 · len` bytes (`len ≤ maxMessageRegisters = 120`) with `get i` / `set i v` assembling and splitting the word through `uget` / `uset` (eight scalar byte operations per word, no object per element), with `SyscallDecodeResult.msgRegs`, `replyRegisters` and `FaultReply`'s register arrays where they feed it, **and the fault encoder**: `Architecture.encodeFault` (`Kernel/Architecture/Fault.lean`) returns `Array RegValue` built through `regOf` (`UInt64.toNat`, a bignum for a high-bit word) and `makeFaultMessage` (`Kernel/IPC/Operations/Fault.lean`) assigns it to `IpcMessage.registers`, so a conversion at the assignment would compile while fault entry kept the input-dependent allocations — **and the fault window itself**: `FaultContext.gprs` and `FaultRegisterWindow.gprs` (`Model/Fault.lean`) are `Array UInt64`, eight boxed words per fault built by `ofRegisterFile`'s `Array.map` over `rf.gpr` and read back by `gprAt` and `spill`, and become eight scalar fields `x0`–`x7` of each structure (`gprAt` a `match`, `spill` the structure update §3.2 already gives it), the encoder reading the fields — the carrier set being derived by a search for `Array UInt64`, `Array RegValue` and `RegValue` on the entry, decode, fault-encode and return paths, these being the members at `v0.36.50`; the encoder and the fault-reply reader construct and read `MessageWords` directly, `regOf` retiring with `RegValue.valid` — **not `Array UInt64`**, whose every push boxes its element through `lean_box_uint64` (a heap object for the word, so the input-dependent allocation would survive and contradict §1.1's zero-`lean_box_uint64` read) — and **not measurement-gated**: a message register is any user `UInt64`, and one `≥ 2^63` read as a `Nat` allocates a bignum whatever CV4.2's workload happens to carry, so the input-dependent allocation goes by construction; `RegValue.valid` retires with its last array; the decode and return-frame readers restated over `MessageWords`; the generated C of `RegisterDecode.c`, `SyscallArgDecode.c` and both `Fault.c` (`Model/`, `Kernel/Architecture/`) read for `lean_box_uint64` on the decode and fault-encode paths as §1.1 reads the entry modules, with the high-bit case; a Tier 2 case sends a high-bit word (`≥ 2^63`) through the IPC path for the semantics (the word arrives intact) and a second delivers a VM fault at an address `≥ 2^63`, from a thread whose `x0`–`x7` are all `≥ 2^63`, to a fault handler (the fault address and the eight window words arrive intact), and the allocation evidence is the kernel lane's: CV0.1's `heap_allocations_per_syscall` exerciser gains a high-bit IPC scenario (a send whose message registers carry `≥ 2^63`) and a high-bit fault scenario (a user load from an address `≥ 2^63`, its fault message read by the handler) whose deltas are read beside the plain round trip, since the host Lean runtime has no counter (§3.6) | `Model/Object/Types.lean`, `Architecture/SyscallArgDecode.lean`, `Kernel/Architecture/Fault.lean`, `Kernel/IPC/Operations/Fault.lean`, `Model/Fault.lean`, decode/return-frame readers, two Tier 2 cases |
| CV4.4 | **Exclusivity by ownership** (§3.5): the entry wrapper's `modifyGetKernelState` already gives the step the state's only reference, so the work is below it: `SystemState.modifyTcbExclusive` — the TCB's slot value taken out of `objects` (the `Array.modify` swap pattern over an `RHTable` take), `f` run on a uniquely referenced record, the result swapped back under `rewriteObject`'s witnessed admissibility — carries `saveCapturedSyscallFrame` and `stageReturnFrame`, with the snapshot binding dead at the save; the stage **takes the context out of both holders** — the bank slot (`machine.coreRegs`) and the TCB field swapped with the shared `default` constant — updates the one object in place and stores it back into both, since `saveTrapFrameOnCore` stores one object behind two holders and `stageCallerReturn` today updates the two copies separately (`contextMatchesCurrent` keeps its statement: one object, two holders); `stageCallerReturn` receives the caller as a `ThreadId` read from the core's current slot before the arm at its four call sites in `SyscallDispatchEntry.lean`, not the pre-state (independent of the KSC-1 accumulator's seam switch, whose capture carries the same value once it has landed); `modifyTcbExclusive_eq_updateTcb` says the two are the same function; the kernel-lane exerciser's continuing-syscall delta is read against the budget of §1.1, and one host Lean test holds a second reference to the TCB record across `stageReturnFrame` and observes the copy, so the relation, not the token, is what the check sees (consumes CV4.2) | `Model/State.lean`, `Architecture/TrapFrameSave.lean`, `Architecture/ContextRestore.lean`, `Architecture/SyscallReturn.lean`, `SyscallDispatchEntry.lean`, one host Lean test |

### CV5 — closure

| # | Sub-task | Output |
|---|---|---|
| CV5.1 | The measurement re-run and recorded against CV0.1's baseline; the generated C of the four entry/exit modules read for `lean_alloc_closure` / `lean_box_uint64` on the entry path (§1.1) and the finding recorded in the CHANGELOG — the acceptance measurement, before anything is archived | `CHANGELOG.md` |
| CV5.2 | `HIERARCHICAL_CBS_PLAN.md` re-verified against the tree WS-CV leaves (its preemption rows save and restore the new `RegisterFile`), while this plan is still at its live path (consumes CV5.1) | `docs/planning/HIERARCHICAL_CBS_PLAN.md` |
| CV5.3 | Closure, last: the `v0.36.47` register-file debt row deleted; `WORKSTREAM_CONTEXT.md` section moved to `docs/dev_history/planning/CLOSED_WORKSTREAM_CONTEXT.md`; this plan moved to `docs/dev_history/planning/`; WS-CB opens (consumes CV5.2) | docs |

## 5. Proof obligations

| Obligation | Where discharged |
|---|---|
| `readReg (writeReg rf r v) r = ⟨v.toNat⟩` for `r.val < 31`; `readReg (writeReg rf r v) r' = readReg rf r'` for `r' ≠ r`; `writeReg rf r v = rf` for `r.val ≥ 31` | CV1.1 |
| `ofWords_word`, `word_ofWords`, `word_of_ge` on `RegisterFile` (moved, unchanged) | CV1.1 |
| Every `_preserves_ipcInvariantFull`, scheduler-bundle and information-flow theorem over a register writer compiles with the new carrier (292 theorems) | CV1.1, CV1.2 |
| `contextMatchesCurrent` decidable: `(a == b) = true ↔ a = b` | CV1.1 (derived) |
| `snapshot_word`; `snapshot` injective on words | CV3.1 |
| The restore path stages exactly the TCB's words: `restoreTargetOnCore st c = .user ctx … → ctx = tcb.registerContext` (today's `restoreTargetOnCore_user_roundTrip` without the conversion) | CV4.1 |

## 6. Risks, and decisions deliberately not taken

- **Semantics of out-of-range registers changes** (`writeReg` to `r.val ≥ 31`
  is a no-op; `gpr ⟨31⟩` reads `0`).  Every live consumer of an index ≥ 31 is a
  `not_lawfulBEq` witness that retires (`Machine.lean:393`, `Types.lean:1585`,
  `ObservableStatePerCore.lean:754`); `tests/SmpSwitchToThreadSuite.lean:453/:589`
  already expect `gpr ⟨31⟩ = 0`.  Stated in CV1.1's docstring and CHANGELOG.
- **`restartAtSvc` subtracts in `UInt64`**: wrapping at `pc < 4` is impossible
  for a frame an `SVC` produced (`ELR_EL1 ≥ 4`); proved as `restartAtSvc_pc`
  under that hypothesis, with the hypothesis discharged where the frame comes
  from `trapFromEl0`.
- **Exclusivity of the TCB object at the return-frame write** is established
  by CV4.4's ownership discipline (§3.5) and checked by CV0.1's counter; a
  second reference reaching the TCB at that point costs one more 280-byte copy
  per syscall, which is why the row removes every source rather than measuring
  whether one happened to be live.
- **`IpcMessage.registers` becomes the unboxed `MessageWords` at CV4.3**,
  after the entry/exit path (CV1–CV4.2) rather than with it, because the
  arrays have their own readers; a `UInt64` word ≥ 2^63 read as a `Nat`
  allocates a bignum on an input the user chooses, which no workload
  measurement can rule out, so the retype is unconditional and the high-bit
  case is a test.  `Array UInt64` is not the carrier: Lean boxes every
  `UInt64` array element (`lean_box_uint64` allocates a heap object), so it
  would move the allocation, not remove it; a fixed 120-field scalar structure
  would be unboxed too but copies 960 bytes per update, which the `ByteArray`
  avoids.
- **The acceptance is a budget, not a figure.**  §1.1 lists every allocation
  the path keeps with the row that owns it, and the measurement checks the
  list; an allocation nobody listed shows as a delta and is traced to its
  site rather than recorded as the new number — which is how the classifier's
  `ExceptionContext` (CV0.4) was found while planning, by reading the path,
  rather than while measuring.
- **Collapsing the per-core bank into the TCB** (D2) is not this workstream.
  It would remove `contextMatchesCurrent` and `setRegsOnCore`, change the
  information-flow projection's source and every unwinding relation that reads
  `machineRegs`; it is registered as a candidate in `docs/REGISTERED_DEBT.md`
  when CV5 closes, with no owner.
- **Persistent objects and the heap's liveness record.**  `trap_context_of_lean`
  gates every dereference on the heap's record today; a persistent static is
  outside that record, which is why the acceptance is **by address against the
  executing core's own object** and nothing else — a pointer equal to another
  core's object is refused like any other pointer.
- **Prefix collision**: `cv<digit>` matches no identifier at `v0.36.48`; the
  registry row (CV0's PR) brings it under the naming gate.

## 7. Tier 3 anchors touched (filled by CV0.3)

To be filled by CV0.3 from the 78 lines §1.2 counts, one row per anchor:
anchor line, the definition it pins, the sub-task that retargets or deletes it.
