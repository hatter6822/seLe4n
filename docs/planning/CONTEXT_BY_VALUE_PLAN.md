# WS-CV — The register context by value

> **Workstream**: WS-CV (one fixed-width register context, stored by value,
> handed over by reference)
> **Status**: **IN FLIGHT** — registered at `v0.36.50`; CV0 landed at `v0.36.59`, CV1.1 at `v0.36.61`, CV2.1 at `v0.36.73`; CV3.1–CV3.5 and the save-and-stage half of CV4.3 at `v0.36.74`.  Re-read against the tree at `v0.36.205` (WS-ZA ZA6.36): CV4.1, CV4.2 and the rest of CV4.3 had landed by other constructions and are recorded so; WS-ZA made the word carrier and the measured difference unnecessary, so the old CV4.3 and CV5.1 are deleted and the rows after them renumbered (CHANGELOG entries before `v0.36.205` cite the old numbers: CV4.4 there is CV4.3 here, CV4.5 is CV4.4, CV5.2 is CV5.1, CV5.3 is CV5.2; CV2.2 is merged into CV2.1).  CV4.4 landed in WS-ZA ZA3 at `v0.36.75`, with no commit record.  **Open**: CV1.2, then the closure CV5.2.
> Opens **before WS-CB** (maintainer's decision, 2026-10-05): a representation
> change is cheapest with the fewest consumers, and WS-CB adds consumers of the
> saved context (budget-expiry preemption saves and restores it).  Its one
> prerequisite, the FFI slice-2 cut (`v0.36.48`, PR #913), has landed; the
> KSC-1 reschedule-SGI accumulator (`docs/REGISTERED_DEBT.md`) was never one
> and landed at `v0.36.55`.
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
capture is a copy of 280 bytes **into the TCB's own context object** — in
place, with no allocation, when that object is exclusively owned, which CV4.3
makes it — restore is a borrow of that object (no conversion, no
allocation), and the HAL hands its in-flight context over as a
**persistent per-core object** the model can never retain, by type.

### 1.1 Acceptance (measured, not stated)

- **The allocation budget is 0, and a gate holds it.**  At `v0.36.50` this
  bullet enumerated, from the generated C of the call graph walked from
  `lean_syscall_dispatch_cross_core`, every allocating site on the
  register-context path (first table) and the other owners' sites on the same
  round trip (second table), and the acceptance was the old CV5.1's reading of the
  difference.  Both tables are retired at `v0.36.205` (WS-ZA ZA6.36): every
  site they listed is gone, by this plan's rows or by WS-ZA's
  (`ZERO_ALLOCATION_SYSCALL_PLAN.md`, which owns every site this plan did
  not), and since ZA6.35 the `heap-allocations-per-syscall` exerciser fails
  on any non-zero reading of any entry (`scripts/qemu_exerciser_lib.sh`;
  CLAUDE.md, *Key conventions*).  The budget a remaining row is held to is
  therefore 0 per scenario, first call and steady, read by that gate, not a
  difference of two readings.
- The HAL's `ffi_trap_context` allocates nothing (`lean_heap` counter
  unchanged across the call; Rust unit test, CV3.3).
- The two-trap hazard test (CV0.2, flipped at CV1.1 — earlier than the CV3.4
  the plan scheduled, because the 35-word carrier made the save a copy before
  the in-flight object existed; CV2.1 suspends its reuse half, since the save
  then stores the fresh object the HAL hands over, and CV3.4 restores it over
  the reused object and `snapshotInto`): two traps on one core,
  the first's context saved into a TCB **through the real save path** —
  `saveCapturedSyscallFrame`, called by a pure `BoundaryProbes` export on a
  probe state, since the host lane links no HAL (§3.6) — the second's words
  all distinct from the first's and written into the same object.  At CV0.2
  the test pins what the tree does today (before the overwrite the saved
  context equals trap 1's words; after it the thirty-one general registers,
  read through the closure of the `v0.36.47` debt row, equal trap 2's and the
  four words read eagerly at the save still equal trap 1's); from CV1.1 on
  (`v0.36.61`) the TCB's saved context, read back from the state after the
  second trap, is the first trap's, word for word
  (`a_saved_context_survives_its_object_being_rewritten`, `save_hazard.rs`).
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
(`Model/Object/Types.lean:1007` then, `:1597` at `v0.36.205`, the only TCB register field); `MachineState.coreRegs
: Vector RegisterFile numCores` (`Machine.lean:836` then, `:924` at `v0.36.205`) with `regsOnCore` /
`setRegsOnCore`; `FrozenSystemState` shares `MachineState` and `TCB`;
`ObservableState.machineRegs : Option RegisterFile` (`InformationFlow/Projection.lean:82` then, `:84` at `v0.36.205`);
`RestoreTarget.user (context : RegisterFile)` (`ContextRestore.lean:131` then, `:250` at `v0.36.205`).
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
`SyscallDecodeResult.msgRegs`, `replyRegisters`, the fault reply's registers), which stay
specification: the compiled paths copy register words (WS-ZA ZA4.7, ZA6.31;
§6), so no row retypes them and `RegValue.valid` stays with them.  `writeReg` takes a `UInt64`-valued argument where every live
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
The HAL owns one 288-byte Lean object per core (`HEADER_BYTES + 280`), with the
non-heap header §3.4 states (never freed; `lean_is_exclusive` is false, so
compiled Lean never updates it in place), tag 0, no object fields, plus one
persistent `some` wrapper per core pointing at it.
`ffi_trap_context` writes the trap frame's 35 words into the core's object and
returns the core's wrapper: **no allocation**.  (As built, `v0.36.74`: the
headers are constant-initialised statics rather than written at bring-up, and
a full-field update does **not** write its destination — the compiler drops a
destination whose every field is replaced and builds a new object — so
`snapshotInto` tests `rf.x0` against `c.x0` and replaces the remaining fields
in either branch, which keeps the destination's constructor live for reuse;
`snapshot` is defined directly, and both are `snapshotInto_eq` equal.)  On the
Lean side its type is
`Architecture.InFlightContext`, a structure with the same 35 `UInt64` fields
but a different name, with one way out: `InFlightContext.snapshotInto :
InFlightContext → RegisterFile → RegisterFile`, a full-field structure update
`{ rf with x0 := c.x0, …, tpidr := c.tpidr }` of the destination, which
compiles to 35 reads and writes **into the destination object** when it is
exclusively owned (`lean_is_exclusive`), and to one `lean_alloc_ctor(0, 0, 280)`
plus the writes only in the copy branch the runtime takes on a shared
destination — so the capture into the TCB's own context, which CV4.3 owns,
allocates nothing on a continuing syscall; `snapshot c := c.snapshotInto
default` is the derived form the probes and tests use.  `SystemState` has no
field of type `InFlightContext` and `snapshotInto` (with `snapshot` derived
from it) is its only consumer outside the entry wrappers, so the model
**cannot** retain the per-core buffer:
that is a fact of the types, not a convention.  The entry wrappers read
arguments (`x0`–`x7`, `pc`, `pstate`, `sp`, `x30`) from the `InFlightContext`
directly (fields, no allocation) and write the words once into the TCB's
context through `snapshotInto`, where today's `saveCapturedSyscallFrame`
saves the frame.

**D4 — restore borrows the TCB's context.**  `RestoreTarget.user` carries the
TCB's `registerContext` and `restoreTrapFrame` passes it to
`ffiRestoreStageContext : (@& RegisterFile) → BaseIO Unit` unchanged — no
`trapContextOfRegisterFile`, no fresh object.  The HAL's `trap_context_of_lean`
applies the exact-size and header refusal it applies today to every pointer:
the in-flight object never reaches it, because the restore's argument is a
`RegisterFile` and the in-flight object's type is not one (D3).  So the restore
has no case for the in-flight object: a pointer to it is refused like any
pointer outside the heap's record, and the type rules out the call that would
pass one (`v0.36.74`, which replaced the by-address acceptance first planned
here: that acceptance would have let a restore stage the core's in-flight
words, and the type now forbids the restore that needed it).  The staging
copy, the `SPSR` sanitising and the halts are unchanged.

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

- `RegisterFile.stageReturnFrame` (`SyscallReturn.lean:552` then, `:593` at `v0.36.205`): six `writeReg`
  calls on `UInt64`s — the `⟨(…).toNat⟩` wrappers go.  `stageRestartFrame`,
  `FaultRegisterWindow.spill` (`Model/Fault.lean:263` then, `:302` at `v0.36.205`, today a whole-`gpr`
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
  retargeted to `snapshotInto` (§3.4).
- `Kernel.faultEntryFrame?` answers `Option (RegisterFile × ExceptionContext ×
  FaultRegisterWindow)` from the `Option RegisterFile` binding in this phase;
  CV3.1 moves its input to `InFlightContext` with the `RegisterFile` taken by
  `snapshotInto` (§3.4).
- `SeLe4n/Testing/BoundaryProbes.lean` and `rust/sele4n-lean-boundary/tests/layout.rs`
  retarget: the probes export `RegisterFile.word` / `ofWords`; the Rust side's
  `TRAP_CONTEXT_*` constants are unchanged (35 words).  The `snapshotInto` and
  `snapshot` exports and the test that `snapshotInto` writes the 35 words into
  the object it is given while `snapshot` yields a *different* object with the
  same words are CV3.2's (§3.4).
- `scalar_words_of_lean::<35>` / `trap_context_of_lean` keep their exact-size
  refusal for heap objects.

### 3.4 The in-flight object (CV3)

- Rust: `trap::InFlightContextObjects` — per core, a 288-byte 8-aligned static
  (`[u64; 36]`-shaped, header word first) and a 16-byte `some` wrapper, both
  initialised at the core's Lean-runtime bring-up with
  `lean_set_non_heap_header` (`lean.h` 4.28: `m_rc = 0`, so `lean_inc` /
  `lean_dec` skip the object and `lean_is_exclusive` is false, and `m_cs_sz`
  = the object's byte size, which a non-heap object carries there because no
  allocator page records it — 288 for the context, 16 for the wrapper;
  `m_tag = 0` and `m_other = 0` for the context, tag 1 and `m_other = 1` for
  the wrapper).  The header is stated here once; D3 and CV3.1 cite it.
  `ffi_trap_context` writes the frame's 35 words into the core's object and
  returns the core's wrapper,
  or `lean_box(0)` when no frame is published.
- Lean: `Architecture.InFlightContext` (35 `UInt64` fields, same order;
  `deriving Repr, DecidableEq`), `InFlightContext.snapshotInto` and the
  derived `snapshot`, theorems `snapshotInto_word : (c.snapshotInto rf).word i
  = c.word i` and its instance `snapshot_word`; `Platform.FFI.ffiTrapContext
  : BaseIO (Option InFlightContext)`, the `some` being the core's persistent
  wrapper above, so the binding allocates nothing per trap;
  `syscallEntryContextOrFaulted` matches that `Option` directly instead of
  building an `Except` around the context (its `.ok` in §1.1's table goes);
  the entry wrappers read arguments from the
  `InFlightContext`'s fields and write the words once into the TCB's context
  with `snapshotInto` in `saveCapturedSyscallFrame`.
  `SystemState` and every object type stay free of `InFlightContext` — checked
  by the type checker (no field of that type exists), stated in the docstring.
- Rust tests: the per-core object's header after `lean_dec` is unchanged
  (persistence); `ffi_trap_context` leaves CV0.1's monotone `allocations`
  counter unchanged — not the `live_allocations` census, which a temporary
  object allocated and freed inside the call would leave equal too; two traps on one core with distinct words, a snapshot of the first
  taken in between, the snapshot unchanged after the second (a unit test of
  the compiled `snapshot`, beside — not instead of — the hazard test of CV0.2,
  which drives the real save path and reads the TCB back, re-run at CV3.4); the core's objects are not another core's (D4: no
  by-address acceptance exists to test).

### 3.5 Restore and the return frame (CV4)

- **Landed** (CV4.1–CV4.3; re-read at `v0.36.205`): `restoreTargetOnCore`
  carries `tcb.registerContext` and the HAL borrows it (D4); `stageReturnFrame`
  is a six-field structure update.  The second references this section
  planned to remove with a take-from-both-holders `modifyTcbExclusive` were
  removed otherwise: each holder (the TCB and the core's bank) keeps a file of
  its own, written in its slot (`saveCapturedFrameImpl`,
  `stageCurrentCallerReturn`), the TCB through WS-ZA ZA1.6's `RHTable.modify`,
  and the stage reads the caller from the core's current slot as a code, not
  from the pre-state.  §4's rows cite the sites.
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
  the syscall's and nothing else's.  CV3.3's host unit test is single-threaded
  and reads the total.
  The host boundary crate cannot carry this measurement: it links the compiled
  Lean archive against the toolchain's `libleanshared` and deliberately not
  against `sele4n-hal`, whose `lean_runtime` would be a second definition of
  every `lean_*` symbol (`rust/sele4n-lean-boundary/Cargo.toml`), so on the
  host the allocations go through the upstream runtime where no counter
  exists.  The baseline was recorded at CV0.1 in the CHANGELOG.  Since WS-ZA ZA6.35
  the lane's library fails on any non-zero delta of any scenario (§1.1).

## 4. Schedule — phases and sub-tasks, in execution order

Sequential unless a row says otherwise.  A row's proofs land in the same
sub-task as the definition they cover, or in the lower-numbered row it cites.

### CV0 — baseline and fixtures (nothing in the model changes)

| # | Sub-task | Output |
|---|---|---|
| CV0.1 | The per-core heap allocation counter (§3.6) and the QEMU-lane round-trip measurement (`heap_allocations_per_syscall` exerciser, Tier 4 `virt`, Lean-linked image); record the baseline per syscall at the plan's opening version in `CHANGELOG.md`, beside §1.1's walk at that head (landed `v0.36.59`) | `lean_heap.rs`, `rust/sele4n-hal/src/smp_exercisers.rs`, `scripts/qemu_exerciser_lib.sh`, one Tier 4 script |
| CV0.2 | The two-trap hazard test **through the real TCB save path, as a pure probe in the host boundary crate**: the crate links the compiled Lean archives against `libleanshared` and no HAL (§3.6; its `shim.c` defines no `ffi_*` symbol), so it cannot call `lean_syscall_dispatch_cross_core`, whose object pulls the HAL's trap-context, core-id, kernel-state, lock, SGI and restore-staging externs.  The test calls three `BoundaryProbes` exports — one building a probe state with one TCB current on core 0, one running `saveCapturedSyscallFrame st core0 (some (registerFileOfTrapContext tc))` on it (today's binding shape; CV3.5 retypes the probe with CV3.1's), one reading that TCB's saved context word `i` — and the Rust side builds trap 1's object from a seed (`sele4n_probe_trap_context_of_seed`), saves it, overwrites the same object's 35 words in place with trap 2's, all distinct (`sele4n_boundary_ctor_set_u64`, which is what the HAL does to a reused per-core object), and reads the TCB back.  **Today the read splits at word 31**, because `registerFileOfTrapWords` (`TrapFrameSave.lean:77–82` at `v0.36.48`; deleted at CV2.1) reads `sp`, `pc`, `pstate` and `tpidr` (words 31–34) eagerly when the file is built and keeps only `gpr` (words 0–30) as a closure over the object's `word` accessor (`registerFileOfTrapContext`, the `v0.36.47` debt row), so this row pins that as the witness, as a relation and not a presence: before the overwrite the TCB's 35 words equal trap 1's; after it words 0–30 equal trap 2's and words 31–34 still equal trap 1's, word for word (an `assert_ne` against trap 1 would pass on a default or partly wrong save too); CV3.5 flips the post-overwrite assertion to all 35 words equal to trap 1's.  An entry wrapper retaining the object is excluded by type (D3: no `SystemState` field of the in-flight type), not by this test, which the host lane cannot drive through the wrappers | `rust/sele4n-lean-boundary/tests/`, `SeLe4n/Testing/BoundaryProbes.lean` |
| CV0.3 | Sweep the 78 Tier 3 anchor lines of §1.2 into a list in this plan's §7, each with the sub-task that retargets or deletes it | §7 below |
| CV0.4 | The exception classifier classifies the `ESR_EL1` word, not a context: `Architecture.classifySynchronousExceptionOfEsr : UInt64 → SynchronousExceptionClass` (the body of today's `classifySynchronousException`, which reads only `extractExceptionClass ectx.esr`), with `classifySynchronousException ectx := classifySynchronousExceptionOfEsr ectx.esr` by definition so every theorem over the context form is unchanged, and the export `lean_classify_synchronous_exception` (`Kernel/FaultEntry.lean`) calls the word form — its generated C then builds no `ExceptionContext`, so the one upcall outside the entry lock that allocated on every synchronous exception (`trap.rs`, `build.rs`'s `LEAN_UPCALLS_OUTSIDE_THE_ENTRY_LOCK` justification, `lean_heap.rs`'s concurrency note) allocates nothing; the three notes rewritten to say so (the heap's lock stays load-bearing for the secondary core's bring-up probe), `classifySynchronousExceptionExport_def` restated over the word form, the Rust mirror pin unchanged; the generated C of `FaultEntry.c` read for the export's body; CV0.1's exerciser delta read before and after (§1.1 entry 3; consumes CV0.1) | `SeLe4n/Kernel/Architecture/Fault.lean`, `SeLe4n/Kernel/FaultEntry.lean`, `rust/sele4n-hal/src/trap.rs`, `rust/sele4n-hal/build.rs`, `rust/sele4n-hal/src/lean_heap.rs` | S |

### CV1 — the carrier (§3.1, §3.2): the bulk of the work, one PR per row, each with its own documentation

| # | Sub-task | Output |
|---|---|---|
| CV1.1 | `RegisterFile` as the 35-field `UInt64` structure with `gpr`, `readReg`, `writeReg`, `word`, `ofWords` and their lemmas; `TrapContext`'s layout constants move; `wordBounded` retires; the three `not_lawfulBEq` witnesses (§6) are deleted — they are false on a lawful carrier and only prose cites them — while `RegisterFile.beq_self` / `beq_def` / `beq_symm` and the other `beq_*` lemmas are **kept as compatibility lemmas**, re-proved as one-line corollaries of `LawfulBEq`, so their consumers in the scheduler, architecture and information-flow files compile unchanged in this row; **in the same row, because nothing compiles beyond `Machine.lean` without them**: the writers of §3.2 on the new carrier (`stageReturnFrame`, `stageRestartFrame`, `spill`, `writeFfiRegistersToTcb`, `restartAtSvc`, `writeRegisterState`, `setPC`), the 49 literals, `Repr`; the `_wordBounded` lemmas and `RegisterContextBounded.lean` deleted; `contextMatchesCurrent` proofs simplified to decidable equality; **every one of the 292 register theorems compiles**; fixture `main_trace_smoke.expected` unchanged or its change justified; **the documentation of the change in the same PR** (the repository rule): the register-file passages of `docs/spec/SELE4N_SPEC.md` (the carrier, the `x31` semantics), `docs/DEVELOPMENT.md` §5 if a file moved, `WORKSTREAM_CONTEXT.md`, the `v0.36.47` debt row shortened to CV2–CV4, the evidence-index rows of the retired theorems, the CHANGELOG entry | `SeLe4n/Machine.lean`, the 43 `SeLe4n/` files, the 8 test suites, docs  **Landed `v0.36.61`.** |
| CV1.2 | The information-flow surface: `ObservableState.machineRegs`, the per-core fragments and `lowEquivalentSliceOnCoreCheckWithRegs` on lawful equality; the `machineRegs` unwinding relations re-proved where they cited `beq_*`; then the `beq_*` compatibility lemmas of CV1.1 are **retired with their last consumer** — every citing site (the scheduler and architecture files included, enumerated by the build when the lemmas are deleted) rewritten to `beq_iff_eq` / decidable equality — so the lemmas are never deleted while a consumer remains; the spec's information-flow equality passages and the evidence-index rows of the re-proved unwinding relations in the same PR.  **Zero allocation**: the row changes proofs and the test-side `…CheckWithRegs` comparison, no compiled entry, so the gate's every scenario keeps reading 0 (consumes CV1.1) | `InformationFlow/*`, `Machine.lean`, the remaining `beq_*` consumers, docs |

### CV2 — one boundary type (§3.3)

| # | Sub-task | Output |
|---|---|---|
| CV2.1 | `TrapContext` deleted; `ffiRestoreStageContext` over `RegisterFile`; `restoreTrapFrame` stages the TCB context; the conversions — `trapContextOfRegisterFile`, §1.1's one 280-byte object and thirty-one boxed words per restore, and `registerFileOfTrapContext`, its closures per capture — and their round-trip theorems deleted; `faultEntryFrame?` on `RegisterFile`; **the entry binding retyped in the same row**: `Platform.FFI.ffiTrapContext : BaseIO (Option RegisterFile)` — the HAL's `ffi_trap_context` writes the 35 words into a `RegisterFile` object (the layout constants CV1.1 moved), and `syscallEntryContextOrFaulted` and the entry wrappers read the `RegisterFile` directly — a **temporary** binding that still allocates per trap, replaced by the persistent `InFlightContext` in CV3.1 (consumes CV1.1); anchors retargeted; **and in the same row**, since `BoundaryProbes.lean` names `TrapContext` and does not compile without the retarget, `BoundaryProbes.lean` and `layout.rs` retargeted to `RegisterFile.word` / `ofWords`, the Rust constants unchanged, Tier 1 lane green (the old CV2.2, merged here at `v0.36.205`: the two landed as one PR).  **Landed `v0.36.73`** | `Architecture/TrapFrameSave.lean`, `ContextRestore.lean`, `Platform/FFI.lean`, `FaultEntry.lean`, `SyscallDispatchEntry.lean`, `SeLe4n/Testing/`, `rust/sele4n-lean-boundary/` |

### CV3 — the persistent in-flight object (§3.4)

| # | Sub-task | Output |
|---|---|---|
| CV3.1 | `Architecture.InFlightContext`, `snapshotInto` (a full-field update, in place on an exclusively owned destination), the derived `snapshot`, `snapshotInto_word`; `ffiTrapContext : BaseIO (Option InFlightContext)` — the `some` being the core's persistent wrapper (§3.4), so the binding allocates nothing per trap — replacing CV2.1's temporary `Option RegisterFile` binding, with `syscallEntryContextOrFaulted` matching the `Option` directly in place of building an `Except` around the context (its `.ok` in §1.1's table goes); the entry wrappers on it — the wrappers hand the `InFlightContext` to `syscallDispatchCrossCoreBracketedStep`, which is `@[specialize]`d over its step and reads the argument words from the context's fields, so the seventeen `lean_box_uint64` and two closures of §1.1's table, `syscallWindow`'s eight boxes and the entry action's closure (`modifyGetKernelState` specialised over its action the same way) are gone, and the plan decodes the argument words from the object's fields instead of spilling them into the TCB and looking them up; `SystemState` stays free of the type; **in the same row as the HAL objects it binds to**, since the Lean binding promises a persistent wrapper the CV2 HAL does not have and the HAL objects have no Lean reader before the binding: `trap::InFlightContextObjects`, the per-core persistent object and wrapper, initialised at runtime bring-up with the non-heap header of §3.4 (`lean_set_non_heap_header`, the byte size in `m_cs_sz`), `ffi_trap_context` writing the core's object and returning its wrapper without allocating, `trap_context_of_lean` unchanged, refusing the in-flight object like any non-heap pointer, which the restore's `RegisterFile` argument never carries (D4) | Lean; `rust/sele4n-hal/src/trap.rs`, `ffi.rs`, `lean_runtime/` |
| CV3.2 | The cross-language test extended: `snapshotInto` writes the words into the object it is given and `snapshot` yields a different one with the same words; the probes export both | `rust/sele4n-lean-boundary/` |
| CV3.3 | Rust unit tests: both headers read back through `lean.h`'s accessors (`m_rc = 0`, `m_cs_sz` 288 and 16, the tags and field counts of §3.4); persistence after `lean_dec`, zero allocations across `ffi_trap_context` read from CV0.1's monotone `allocations` counter (§3.4; the live census cannot see an allocation freed before return); each core's objects its own | `ffi.rs` tests |
| CV3.4 | CV0.2's hazard test (already flipped at CV1.1, `v0.36.61`, when the save became a copy; its reuse half suspended at CV2.1, `v0.36.73`, when the save began storing the HAL's fresh object) retyped and its reuse half restored: the save probe retyped over `InFlightContext` (trap 1's object is the one the probe hands to `saveCapturedSyscallFrame`, whose `snapshotInto` copies its words into the TCB's context), trap 2's words written into the same object, the TCB read back — the saved context is trap 1's, word for word; it is the acceptance test of D3 (§1.1) and fails if the save site skips `snapshotInto` or stores the wrong context (consumes CV0.2, CV3.1) | boundary crate |
| CV3.5 | QEMU `virt` four-PE boot (Tier 4 lane) green with the persistent objects: every core traps, snapshots, restores.  **Landed `v0.36.74`**: the Lean-linked image boots four PEs on them in every Tier 4 run since (`scripts/test_qemu_smp_bringup.sh`), and the exerciser traps through every entry on core 0 (`smp_exercisers.rs`) | CI |

### CV4 — restore borrows, return frame updates in place (§3.5)

| # | Sub-task | Output |
|---|---|---|
| CV4.1 | `restoreTargetOnCore` / `restoreTrapFrame` on the TCB's object; `RestoreTarget.user (context : RegisterFile)` unchanged in statement.  **Landed by CV2.1 (`v0.36.73`) and WS-ZA ZA3.1 (`v0.36.75`)**: `restoreTargetOnCore` names `tcb.registerContext` itself (`ContextRestore.lean:266`), with §5's obligation as `restoreTargetOnCore_user` (`ContextRestore.lean:306`); the commit hands the HAL that file through `restoreContextOnCore` (`ContextRestore.lean:360`) and the borrowed `ffiRestoreStageContext : (@& RegisterFile) → BaseIO Unit` (`Platform/FFI.lean:3844`) | `ContextRestore.lean`, `FFI.lean` |
| CV4.2 | `stageReturnFrame` as a structure update on the TCB's context; measured allocation count per syscall recorded.  **Landed by CV1.1 (`v0.36.61`) and CV4.3 (`v0.36.74`)**: `RegisterFile.stageReturnFrame` is the six-field update `{ rf with x0 := f.x0, … }` (`SyscallReturn.lean:593`), staged in each holder's slot (`stageCurrentCallerReturn`, `ContextRestore.lean:89`); the count is the gate's (§1.1) | `SyscallReturn.lean`, measurement |
| CV4.3 | **Exclusivity by ownership** (§3.5).  **The save and the stage landed at `v0.36.74` with CV3.1, by a different construction**: each holder keeps a file of its own — `saveCapturedFrameImpl` writes the in-flight words into the TCB's context in its object slot (`SystemState.modifyObject`, ZA1.6's swap-out `RHTable.modify`) and into the bank in its slot (`MachineState.modifyRegsOnCore`, `Array.modify`), and `stageCurrentCallerReturn` stages each the same way — so neither is ever shared with the other on the continuing path, both are written in place, and no take-from-both-holders swap is needed; `contextMatchesCurrent` is word equality and holds unchanged.  **The rest landed by WS-ZA, and the take-from-both-holders design is not built** (re-read at `v0.36.205`): no holder shares a file with the other, so no swap is needed; the TCB is written in its slot through ZA1.6's `RHTable.modify` (`SystemState.updateTcb`, behind `writeReturnFrameToTcb`, `SyscallReturn.lean:752`), so no `modifyTcbExclusive` exists; the stage takes the caller from the core's current slot before the arm, as a code (`stageCallerReturnWords`, `ContextRestore.lean:149`), not the pre-state; the thread-id test is `Option.isEqSome`, with no `instDecidableEqThreadId` closure (`stageCallerReturnForImpl`, `ContextRestore.lean:98`, WS-ZA ZA2.2); `fpReleaseNeeded` is compiled through `fpReleaseNeeded_eq_impl` (WS-ZA ZA6.31).  Every syscall scenario reads 0 (§1.1) | `Model/State.lean`, `Architecture/TrapFrameSave.lean`, `Architecture/ContextRestore.lean`, `Architecture/SyscallReturn.lean`, `SyscallDispatchEntry.lean` |
| CV4.4 | **Landed in WS-ZA, with no commit record.**  The syscall entry's commit allocates nothing since `v0.36.75` (`ZERO_ALLOCATION_SYSCALL_PLAN.md` ZA3): the restore target's parts and the outcome's words are read off the committed state inside the inlined step, so neither the `SyscallCommit` record this row planned nor the `modifyGet` pair is built.  The record is not taken: it would be one allocation per syscall where the words cost none.  The timer, reschedule and secondary entries' restore targets are words since `v0.36.164` (that plan's ZA6.1), and the fault entries' are its ZA6.31 | — |

### CV5 — closure

| # | Sub-task | Output |
|---|---|---|
| CV5.1 | `HIERARCHICAL_CBS_PLAN.md` re-verified against the tree WS-CV leaves (its preemption rows save and restore the new `RegisterFile`), while this plan is still at its live path.  **Landed at `v0.36.205` by WS-ZA ZA6.36**, which re-read that plan against the tree both workstreams leave; CV1.2, the one row still open, changes proofs over `machineRegs` and no register write the CBS plan names | `docs/planning/HIERARCHICAL_CBS_PLAN.md` |
| CV5.2 | Closure, last: the `v0.36.47` register-file debt row deleted; `WORKSTREAM_CONTEXT.md` section moved to `docs/dev_history/planning/CLOSED_WORKSTREAM_CONTEXT.md`; this plan moved to `docs/dev_history/planning/`, and in the same row every live document that links this plan by path (at `v0.36.205`: `HIERARCHICAL_CBS_PLAN.md`'s header and §5, `ZERO_ALLOCATION_SYSCALL_PLAN.md`, `docs/REGISTERED_DEBT.md`, `WORKSTREAM_CONTEXT.md`; the derivation is a search for `CONTEXT_BY_VALUE_PLAN` outside `docs/dev_history/`) repointed to cite it by workstream ID, as CLAUDE.md requires of an archived plan; §6's bank-collapse candidate registered; WS-CB opens (consumes CV1.2, CV5.1) | docs |

## 5. Proof obligations

| Obligation | Where discharged |
|---|---|
| `readReg (writeReg rf r v) r = ⟨v.toNat⟩` for `r.val < 31`; `readReg (writeReg rf r v) r' = readReg rf r'` for `r' ≠ r`; `writeReg rf r v = rf` for `r.val ≥ 31` | CV1.1 |
| `ofWords_word`, `word_ofWords`, `word_of_ge` on `RegisterFile` (moved, unchanged) | CV1.1 |
| Every `_preserves_ipcInvariantFull`, scheduler-bundle and information-flow theorem over a register writer compiles with the new carrier (292 theorems) | CV1.1, CV1.2 |
| `contextMatchesCurrent` decidable: `(a == b) = true ↔ a = b` | CV1.1 (derived) |
| `snapshotInto_word`, `snapshot_word`; `snapshot` injective on words | CV3.1 |
| The restore path stages exactly the TCB's words: `restoreTargetOnCore st c = .user ctx … → ctx = tcb.registerContext` (today's `restoreTargetOnCore_user_roundTrip` without the conversion) | CV4.1 |

## 6. Risks, and decisions deliberately not taken

- **Semantics of out-of-range registers changes** (`writeReg` to `r.val ≥ 31`
  is a no-op; `gpr ⟨31⟩` reads `0`).  Every live consumer of an index ≥ 31 is a
  `not_lawfulBEq` witness that retires (`Machine.lean:393`, `Types.lean:1585`,
  `ObservableStatePerCore.lean:754` at `v0.36.48`; all three deleted at CV1.1); `tests/SmpSwitchToThreadSuite.lean:453/:589`
  already expect `gpr ⟨31⟩ = 0`.  Stated in CV1.1's docstring and CHANGELOG.
- **`restartAtSvc` subtracts in `UInt64`**: wrapping at `pc < 4` is impossible
  for a frame an `SVC` produced (`ELR_EL1 ≥ 4`); proved as `restartAtSvc_pc_toNat`
  under that hypothesis, with the hypothesis discharged where the frame comes
  from `trapFromEl0`.
- **Exclusivity of the TCB object at the return-frame write** is established
  by CV4.3's ownership discipline (§3.5) and checked by CV0.1's counter; a
  second reference reaching the TCB at that point costs one more 280-byte copy
  per syscall, which is why the row removes every source rather than measuring
  whether one happened to be live.
- **No word carrier for messages** (the old CV4.3, deleted at `v0.36.205`).
  The plan retyped `IpcMessage.registers` to a `ByteArray`-backed
  `MessageWords` so a word `≥ 2^63` could not box.  WS-ZA removed the need: a
  message is copied from the sender's register file to the receiver's as
  `UInt64` words and the `IpcMessage` record stays specification only
  (ZA4.7), and a fault's window and record are words in the TCB
  (`ThreadFaultWords`, ZA6.31); the high-bit scenarios (`signal-wide-badge`,
  the capability fault at `2^63 + 31`) read 0.
- **The acceptance is the gate's.**  §1.1's tables listed every allocation
  the path kept, with its owner, so a delta could be traced rather than
  recorded; the dispatcher's and the other owners' allocations were outside
  the budget.  WS-ZA took every one of them to 0, so the budget is 0 for the
  whole entry, the dispatcher included.
- **Collapsing the per-core bank into the TCB** (D2) is not this workstream.
  It would remove `contextMatchesCurrent` and `setRegsOnCore`, change the
  information-flow projection's source and every unwinding relation that reads
  `machineRegs`; it is registered as a candidate in `docs/REGISTERED_DEBT.md`
  by CV5.2, with no owner.
- **Persistent objects and the heap's liveness record.**  `trap_context_of_lean`
  gates every dereference on the heap's record; a persistent static is
  outside that record and is refused like any other pointer — which is never
  exercised, since the in-flight object's type keeps it from the restore (D4).
- **Prefix collision**: `cv<digit>` matches no identifier at `v0.36.48`; the
  registry row (CV0's PR) brings it under the naming gate.

## 7. Tier 3 anchors touched (filled by CV0.3)

**The set is a derivation, re-run by every row that changes a register term**:
the anchor lines of `scripts/test_tier3_invariant_surface.sh`
(`^run_(check|negative_check|prose_check|prose_negative_check) `) whose text
matches `RegisterFile|RegValue|registerContext|regsOnCore|setRegsOnCore|TrapContext|\bgpr\b|writeReg|readReg|RegName|contextMatchesCurrent|saveOutgoingContext|restoreIncomingContext|writeReturnFrameToTcb|writeRestartFrameToTcb|FaultRegisterWindow|spill|writeFaultRegistersToTcb|writeFfiRegistersToTcb|wordBounded|machineRegs|registerContextStableCheck|registerContextsWordBounded|trapWords|stageReturnFrame|readReturnFrame|RestoreTarget|coreRegs`.
At `v0.36.57` it is **57 lines**, not §1.2's 78: anchors retired between
`v0.36.48` and that head took the rest.  The rows below are that cut's pin; a
row's anchor line numbers drift, so each is named by what it pins.  "Kept"
means the anchor's text survives the workstream: the definition or theorem
keeps its name and the pinned shape, and only its types change underneath (the
row that changes the type re-runs the anchor, as CLAUDE.md's refactor sweep
requires).

| Anchor (what it pins) | Lines at `v0.36.57` | Sub-task |
|---|---|---|
| `registerContextStableDecidable` field (`Architecture/Assumptions.lean`) | 218 | kept |
| `saveOutgoingContext` / `…OnCore` / `…Checked` bodies through `updateTcb` / `getTcbWitnessed?`, and their three `objects.insert` negatives | 3061–3063, 3072, 3073, 3076 | kept |
| `writeReturnFrameToTcb`, `writeRestartFrameToTcb`, `writeFaultRegistersToTcb` (`spill` into `registerContext`), `writeFfiRegistersToTcb` bodies, their `objects.insert` / `getTcb?` negatives and their three `_id_when_not_tcb` proofs | 3229–3235, 3238–3240 | kept |
| `pstate : RegValue := ⟨0⟩` (`Machine.lean`) | 4308 | **CV1.1** retargets (`pstate : UInt64`) — **done `v0.36.61`**, with the trap-frame layout anchors (word count, tpidr word, the tpidr arm, the restore's word read, the structural equality) re-pointed at `Machine.lean` and `ContextRestore.lean` |
| `saveTrapFrameOnCore_contextMatchesCurrentOnCore` | 4343 | kept (restated over `snapshotInto` at CV3.1) |
| `ffiRestoreStageContext (trapContextOfRegisterFile ctx)` (`Platform/FFI.lean`) | 4358 | **CV2.1** retargets (`trapContextOfRegisterFile` deleted; the TCB's context is staged) |
| `RestoreTarget.deliveredFrame?`, `switchToThreadOnCore_delivers_readReturnFrame`, `abortPendingIpcOnEndpoint_readReturnFrame` | 4397, 4398, 4400 | kept |
| `let trapped ← Platform.FFI.ffiTrapContext` (`SyscallDispatchEntry.lean`) | 4674 | kept (the binding's type changes at CV2.1 and CV3.1) |
| `writeFaultRegistersToTcb` at fault entry, `faultContextOfThread_writeFaultRegistersToTcb` | 4977, 4980 | kept |
| `ofRegisterFile_spill` (`Model/Fault.lean`) | 4981 | kept (the old CV4.3 is deleted) |
| `machineRegs_beq_self` | 5825 | **CV1.2** deletes (the `beq_*` lemmas retire with their last consumer) |
| `onCore_machineRegs`, `onCore_setRegsOnCore_ne` | 5849, 5888 | kept |
| `machineRegs_beq_not_injective` | 5879 | **CV1.1** deletes (a `not_lawfulBEq` witness, §6) — **done `v0.36.61`**, replaced by `machineRegs_beq_iff` |
| `saveOutgoingContext_confinedToCore`, `restoreIncomingContext_confinedToBootCore` | 6018, 6019 | kept |
| `recordPhysicalWrites (writeReturnFrameToTcb …)` in the receive path | 7714 | kept |
| `saveVacatedFrameOnCore`'s `registerContext := saved` arm | 7740 | **CV3.1** retargets (the save is `snapshotInto`) |
| `.user tcb.registerContext ops.1 ops.2 (fpLiveFor st c tid)` (`ContextRestore.lean`) | 7783 | kept: `restoreTargetOnCore` stays the specification the commit's words are proven equal to (WS-ZA ZA3.1) |
| `recordSyscallRefusal_readReturnFrame_eq`, `restoreToReadyCancelled_readReturnFrame` | 8365, 9498 | kept |
| `contextMatchesCurrent`: its definition, its two bundle conjuncts, `EndpointReplyAndLifecycle`'s conjunct, `schedulerInvariantBundleFull_to_contextMatchesCurrent`, `switchDomain_preserves_contextMatchesCurrent` | 10375, 10376, 10380, 10384, 10389, 10447 | kept (lawful equality from CV1.1; the statement is unchanged) |
| `writeRegisterState_preserves_registerDecodeConsistent`, `lookupThreadRegisterContext_preserves_lowEquivalent` | 10507, 10512 | kept |
| `msgRegs.*Array.*RegValue` (`Model/Object/Types.lean`) | 10541 | kept (the old CV4.3 is deleted; the array is specification only, WS-ZA ZA4.7) |
| `writeFfiRegistersToTcb`, `writeReturnFrameToTcb`, `readReturnFrame` definitions; `readReturnFrame_writeReturnFrame`, `readReturnValue_eq_readReturnFrame_x0`, `writeReturnFrameToTcb_preserves_projection`, `writeFfiRegistersToTcb_id_when_not_tcb` | 10624, 10978–10980, 10999, 11000, 11050 | kept |
| `saveOutgoingContext_effectiveBucketPriority_eq`'s congruence | 20102 | kept |
| `replyRegisters : Option (Array SeLe4n.RegValue) := none` (`Locks/LockSetForSyscall.lean`) | 20902 | kept (the old CV4.3 is deleted) |
| `scheduleEffectiveOnCore`'s `saveOutgoingContextOnCore` composition | 22094 | kept |

Five anchors change: CV1.1 two, CV1.2 one, CV2.1 one, CV3.1 one — each in the row named, with the row's own anchors re-swept.
