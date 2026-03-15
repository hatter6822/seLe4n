# seLe4n Workstream Plan — Register-Indexed Authoritative Namespaces (WS-J1)

**Version target:** v0.14.10+
**Status:** Completed (v0.15.10)
**Priority:** High
**Estimated effort:** 5–8 days
**Dependencies:** WS-I1..WS-I4 complete baseline, no additional blockers
**Primary scope:** Replace `RegName := Nat` / `RegValue := Nat` with typed
register identifiers that index authoritative kernel namespaces directly,
close the syscall-argument decode gap between the model and real hardware,
and integrate with the existing proof surface.

---

## 1. Executive summary

`SeLe4n/Machine.lean` currently defines register names and values as bare
`Nat` abbreviations (`abbrev RegName := Nat`, `abbrev RegValue := Nat`).
The syscall API layer (`Kernel/API.lean`) accepts pre-typed Lean parameters
(`ObjId`, `CPtr`, `ThreadId`) directly — it never extracts these identifiers
from the machine register file. This means the model omits the entire
**syscall argument decode path** that real hardware mandates: on ARM64, syscall
arguments arrive in general-purpose registers x0–x7, and the kernel must
decode raw register words into typed kernel references before any authority
check can proceed.

This workstream closes that gap by:

1. Replacing `RegName` and `RegValue` with typed wrapper structures that
   carry namespace semantics at the type level.
2. Introducing a **register decode layer** that converts raw register words
   into typed kernel identifiers with total, deterministic error handling.
3. Wiring the syscall API wrappers (`api*` functions) through the decode
   layer so that authority flows from machine registers through decode into
   typed kernel operations.
4. Proving decode correctness, invariant preservation, and non-interference
   properties for the new path.

The migration is staged into six small, independently reviewable units (A–F)
to limit proof churn and keep CI feedback fast at every step.

---

## 2. Problem analysis (code-level audit findings)

### 2.1 Finding: bare `Nat` aliases bypass type safety

**Location:** `SeLe4n/Machine.lean:14–17`

```lean
abbrev RegName := Nat    -- line 14
abbrev RegValue := Nat   -- line 17
```

Every other kernel-facing identifier in the codebase is a typed wrapper
structure with `DecidableEq`, `Hashable`, `LawfulHashable`, `Repr`,
`ToString`, and sentinel support (`ObjId`, `ThreadId`, `CPtr`, `DomainId`,
`Priority`, `Deadline`, `Irq`, `ServiceId`, `Slot`, `Badge`, `ASID`,
`VAddr`, `PAddr` — 13 types defined in `Prelude.lean:29–448`).

`RegName` and `RegValue` are the **only** `abbrev Nat` types that flow into
authority-sensitive operations. While `CdtNodeId := Nat` also exists
(`Model/Object/Structures.lean:554`), it is internal to CDT bookkeeping
and never crosses a trust boundary.

**Consequence:** A `Nat` value intended as a `RegName` can be silently used
as a `RegValue` or as an index into any other `Nat`-typed field. The type
checker provides no defense against namespace confusion.

### 2.2 Finding: syscall arguments bypass the register file

**Location:** `SeLe4n/Kernel/API.lean:138–149` (`SyscallGate` structure)

```lean
structure SyscallGate where
  callerId     : SeLe4n.ThreadId
  cspaceRoot   : SeLe4n.ObjId
  capAddr      : SeLe4n.CPtr
  capDepth     : Nat
  requiredRight : AccessRight
```

In real seL4 (and on real ARM64 hardware), these fields come from machine
registers:
- `x0` carries the destination capability pointer
- `x1` carries the message info word (encodes message length, extra caps,
  label)
- `x2–x5` carry inline message registers
- `x7` carries the syscall number

The seLe4n model passes `SyscallGate` fields as direct Lean function
arguments. The machine register file (`MachineState.regs`) is only used for
context save/restore during thread switching (`saveOutgoingContext`/
`restoreIncomingContext` in `Kernel/Scheduler/Operations/Core.lean:215–233`).
No operation ever *reads* a syscall argument from the register file.

**Consequence:** The model cannot express or prove properties about the
decode path — the moment where untrusted user-space register values become
trusted kernel references. This is exactly the boundary where real-world
confusion attacks (wrong register, truncated value, stale capability pointer)
occur.

### 2.3 Finding: `CdtNodeId` also lacks typed wrapping

**Location:** `SeLe4n/Model/Object/Structures.lean:554`

```lean
abbrev CdtNodeId := Nat
```

Used as a `HashMap` key in `SystemState` (`cdtSlotNode`, `cdtNodeSlot`,
`cdtNextNode` at `Model/State.lean:141–143`). While it inherits `Nat`'s
`Hashable`, it lacks explicit `Hashable`, `LawfulHashable`, `EquivBEq`,
and `LawfulBEq` instances — inconsistent with every other HashMap key type
in the codebase. This workstream wraps `CdtNodeId` as a secondary cleanup
item (WS-J1-F).

### 2.4 Finding: `RegisterFile.gpr` is unbounded

**Location:** `SeLe4n/Machine.lean:40–58`

```lean
structure RegisterFile where
  pc : RegValue
  sp : RegValue
  gpr : RegName → RegValue
```

The `gpr` field is a total function `Nat → Nat` — conceptually infinite
registers. The `BEq` instance compares only the first 32 GPRs (ARM64
convention), but nothing in the type system prevents reading `gpr 999`.

**Consequence:** Proofs about register operations do not carry architectural
bounds. The read-after-write lemmas (`readReg_writeReg_eq/ne`) are correct
but apply to an unbounded register space, which is strictly weaker than the
bounded 31-register space (x0–x30) of real ARM64.

### 2.5 Summary of gaps

| Gap | Location | Severity | Impact |
|-----|----------|----------|--------|
| Bare `Nat` register types | `Machine.lean:14–17` | Medium | Type confusion possible |
| No syscall decode path | `API.lean:138–149` | High | Authority boundary unmodeled |
| Unbounded register space | `Machine.lean:43` | Low | Proofs weaker than hardware |
| `CdtNodeId` inconsistency | `Structures.lean:554` | Low | Missing type-safety instances |

---

## 3. Design: typed register namespace indexing

### 3.1 Design principles

1. **Register values are the authoritative source.** Syscall arguments must
   originate from the current thread's register file, not from direct Lean
   parameters.
2. **Decode is total and deterministic.** Every decode from register word to
   typed reference returns `ok` or an explicit `KernelError`.
3. **Typed identifiers at every boundary.** `RegName` and `RegValue` become
   wrapper structures consistent with the 13 existing typed identifiers.
4. **Backward compatibility via shims.** Existing `readReg`/`writeReg`
   lemmas continue to work through compatibility conversions during the
   migration period.
5. **Bounded register space.** `RegName` carries a proof-relevant bound
   (`n < 32` for ARM64 GPRs), eliminating the infinite-register fiction.

### 3.2 New core types

All names are semantics-first (no workstream IDs in identifiers).

#### 3.2.1 `RegName` — bounded register index

```lean
/-- Bounded general-purpose register index.
    ARM64: 31 GPRs (x0–x30), plus pc and sp as separate fields. -/
structure RegName where
  val : Nat
  deriving DecidableEq, Repr, Hashable
```

The `MachineConfig.registerCount` field (new) provides the architectural
bound. Syscall decode operations that reference out-of-bounds register
names return `KernelError.invalidRegister` (new error variant).

#### 3.2.2 `RegValue` — machine word with namespace decode

```lean
/-- Register-width machine word. Carries the raw numeric value from which
    typed kernel references are decoded at syscall boundaries. -/
structure RegValue where
  val : Nat
  deriving DecidableEq, Repr, Hashable
```

#### 3.2.3 `SyscallRegisterLayout` — register-to-argument mapping

```lean
/-- Mapping from ARM64 syscall convention registers to typed arguments.
    Encodes the real hardware convention:
    - x0: destination capability pointer (CPtr)
    - x1: message info word (length, extra caps, label)
    - x2–x5: inline message registers
    - x7: syscall number -/
structure SyscallRegisterLayout where
  capPtrReg      : RegName   -- x0
  msgInfoReg     : RegName   -- x1
  msgRegs        : Array RegName  -- x2–x5
  syscallNumReg  : RegName   -- x7
```

A default ARM64 layout is provided as a constant. The platform
`MachineConfig` can override for alternative ABI conventions.

#### 3.2.4 `SyscallDecodeResult` — decoded syscall arguments

```lean
/-- Result of decoding raw register values into typed syscall arguments.
    Total: always returns either a valid decode or a specific error. -/
structure SyscallDecodeResult where
  capAddr   : CPtr
  msgInfo   : MessageInfo
  syscallId : SyscallId
```

The `MessageInfo` and `SyscallId` types are new, lightweight structures
encoding the seL4 message-info word layout and syscall numbering.

### 3.3 Register decode layer

A new module `SeLe4n/Kernel/Architecture/RegisterDecode.lean` provides:

```lean
/-- Decode a raw register value into a capability pointer.
    Returns illegalArgument if the value exceeds the CPtr address space. -/
def decodeCapPtr (rv : RegValue) : Except KernelError CPtr

/-- Decode a raw register value into a message info word.
    Extracts length, extra caps count, and label from bit fields. -/
def decodeMsgInfo (rv : RegValue) : Except KernelError MessageInfo

/-- Decode the syscall number register into a typed syscall identifier. -/
def decodeSyscallId (rv : RegValue) : Except KernelError SyscallId

/-- Extract typed syscall arguments from the current thread's register file
    using the platform's register layout convention.
    This is the single authoritative decode entry point. -/
def decodeSyscallArgs
    (layout : SyscallRegisterLayout)
    (regs : RegisterFile) : Except KernelError SyscallDecodeResult
```

Each decode function is total with explicit error returns. The module also
provides:

- **Round-trip lemmas:** `decodeCapPtr (encodeCapPtr c) = .ok c`
- **Determinism theorem:** decode of the same register values always
  produces the same result.
- **Error exclusivity:** each error variant maps to exactly one failure mode.

### 3.4 Syscall gate integration

The existing `SyscallGate` structure is preserved but its construction
changes. Today, callers pass typed arguments directly:

```lean
-- Current (bypasses registers):
apiEndpointSend gate epId msg
```

After WS-J1, the canonical syscall entry point reads from the current
thread's register context:

```lean
/-- Decode syscall arguments from the current thread's register file
    and dispatch to the appropriate kernel operation. -/
def syscallEntry (layout : SyscallRegisterLayout) : Kernel Unit :=
  fun st =>
    match st.scheduler.current with
    | none => .error .illegalState
    | some tid =>
      match lookupThreadRegisterContext tid st with
      | .error e => .error e
      | .ok regs =>
        match decodeSyscallArgs layout regs with
        | .error e => .error e
        | .ok decoded =>
          -- Route to the appropriate api* wrapper based on decoded.syscallId
          dispatchSyscall decoded tid st
```

The existing `api*` functions remain as the **internal kernel API** (typed
arguments, no decode). `syscallEntry` is the **new user-space entry point**
that models the real hardware decode path. This preserves backward
compatibility: all existing tests and proofs that call `api*` directly
continue to work unchanged.

### 3.5 `CdtNodeId` typed wrapper (secondary)

Replace:
```lean
abbrev CdtNodeId := Nat
```

With:
```lean
structure CdtNodeId where
  val : Nat
  deriving DecidableEq, Repr, Hashable
```

Add `LawfulHashable`, `EquivBEq`, `LawfulBEq`, `ToString`, `ofNat`/`toNat`
instances matching the pattern in `Prelude.lean`.

### 3.6 Architecture diagram

```
User space
    │
    ▼ (hardware trap: arguments in x0–x7)
┌────────────────────────────────────────────┐
│  RegisterDecode.decodeSyscallArgs          │
│  ┌─────────────────────────────────────┐   │
│  │ raw RegValue → CPtr                │   │
│  │ raw RegValue → MessageInfo          │   │
│  │ raw RegValue → SyscallId            │   │
│  └─────────────────────────────────────┘   │
│            │ typed decode result            │
│            ▼                                │
│  syscallEntry: route to api* wrapper       │
│            │                                │
│            ▼                                │
│  SyscallGate: capability resolution        │
│  (resolveCapAddress → lookupSlotCap)       │
│            │                                │
│            ▼                                │
│  api* wrapper: authority + operation       │
│  (apiEndpointSend, apiCspaceMint, ...)     │
│            │                                │
│            ▼                                │
│  Internal kernel operation                 │
│  (endpointSendDual, cspaceMint, ...)       │
└────────────────────────────────────────────┘
```

---

## 4. Scope and non-goals

### In scope

- `RegName` and `RegValue` as typed wrapper structures with full instance
  suite (`DecidableEq`, `Hashable`, `LawfulHashable`, `EquivBEq`,
  `LawfulBEq`, `Repr`, `ToString`, `ofNat`/`toNat`).
- `SyscallRegisterLayout`, `SyscallDecodeResult`, `MessageInfo`, `SyscallId`.
- `RegisterDecode.lean` module with total decode functions and round-trip
  lemmas.
- `syscallEntry` as the register-sourced syscall dispatch path.
- `CdtNodeId` typed wrapper with full instance suite.
- New `KernelError` variants: `invalidRegister`, `invalidSyscallNumber`,
  `invalidMessageInfo`.
- Invariant updates for decode path preservation.
- NI bridge lemmas for register-observable decode behavior.
- Negative tests for every decode error path.
- Trace scenarios for register-sourced syscall execution.
- Documentation sync across all canonical sources and GitBook.

### Out of scope (this workstream)

- Full ARM64 ISA binary encoding for all system registers (SPSR, ESR, etc.).
- Multi-core per-CPU register banks.
- Floating-point / SIMD register state (D0–D31, V0–V31).
- Hardware MMU page-table register integration (TTBR0/TTBR1).
- MCS scheduling context register usage.

---

## 5. Work breakdown structure

### WS-J1-A — Typed register wrappers and compatibility bridge

**Goal:** Replace `abbrev Nat` with wrapper structures. Zero behavior change.

**Tasks:**

1. Define `RegName` and `RegValue` as wrapper structures in `Machine.lean`.
   Add `DecidableEq`, `Hashable`, `Repr`, `ToString`, `ofNat`/`toNat`.
2. Add `LawfulHashable`, `EquivBEq`, `LawfulBEq` instances in
   `Prelude.lean` following the existing pattern for the 13 typed identifiers.
3. Update `RegisterFile.gpr` signature: `RegName → RegValue`.
4. Update `readReg`/`writeReg` to use wrapper types.
5. Re-prove all 10 existing machine lemmas (`readReg_writeReg_eq/ne`,
   `writeReg_preserves_pc/sp`, `writeMem_preserves_regs/timer`,
   `setPC_preserves_memory/timer`, `tick_preserves_regs/memory`,
   `tick_timer_succ`).
6. Add compatibility conversion functions: `RegName.ofNat`/`.toNat`,
   `RegValue.ofNat`/`.toNat`.
7. Fix all downstream compilation errors from the type change (systematic:
   grep for `RegName` and `RegValue` usage across 18 files).

**Exit criteria:**
- `lake build` passes with zero errors.
- `./scripts/test_smoke.sh` passes (existing tests unchanged).
- Zero `sorry`/`axiom` introduced.

**Files modified:**
- `SeLe4n/Machine.lean` — type definitions, operations, lemmas
- `SeLe4n/Prelude.lean` — lawful instances
- `SeLe4n/Kernel/Architecture/Adapter.lean` — type annotations
- `SeLe4n/Kernel/Architecture/Assumptions.lean` — contract signatures
- `SeLe4n/Kernel/Scheduler/Operations/Selection.lean` — context switch
- `SeLe4n/Kernel/Scheduler/Operations/Core.lean` — save/restore
- `SeLe4n/Platform/Sim/RuntimeContract.lean` — contract predicates
- `SeLe4n/Platform/RPi5/RuntimeContract.lean` — contract predicates
- `SeLe4n/Testing/MainTraceHarness.lean` — trace construction

---

### WS-J1-B — Register decode layer

**Goal:** Introduce the decode module that converts raw register words into
typed kernel references.

**Tasks:**

1. Add `SyscallId` inductive in `Model/Object/Types.lean` covering the
   modeled syscall set (send, receive, call, reply, cspaceMint, cspaceCopy,
   cspaceMove, cspaceDelete, lifecycleRetype, vspaceMap, vspaceUnmap,
   serviceStart, serviceStop).
2. Add `MessageInfo` structure encoding seL4 message-info word layout
   (length, extraCaps, label fields).
3. Add `SyscallRegisterLayout` structure and `arm64DefaultLayout` constant.
4. Create `SeLe4n/Kernel/Architecture/RegisterDecode.lean`:
   - `decodeCapPtr : RegValue → Except KernelError CPtr`
   - `decodeMsgInfo : RegValue → Except KernelError MessageInfo`
   - `decodeSyscallId : RegValue → Except KernelError SyscallId`
   - `decodeSyscallArgs : SyscallRegisterLayout → RegisterFile → Except KernelError SyscallDecodeResult`
5. Add round-trip lemmas (`decodeCapPtr_roundtrip`, etc.).
6. Add determinism theorem for `decodeSyscallArgs`.
7. Add new `KernelError` variants: `invalidRegister`,
   `invalidSyscallNumber`, `invalidMessageInfo`.

**Exit criteria:**
- `lake build` passes.
- Round-trip and determinism lemmas proved (zero `sorry`).
- `./scripts/test_smoke.sh` passes.

**Files modified:**
- `SeLe4n/Model/Object/Types.lean` — `SyscallId`, `MessageInfo`
- `SeLe4n/Model/State.lean` — new `KernelError` variants
- `SeLe4n/Kernel/Architecture/RegisterDecode.lean` — **new file**
- `SeLe4n/Machine.lean` — `SyscallRegisterLayout`, `arm64DefaultLayout`

---

### WS-J1-C — Syscall entry point and dispatch

**Goal:** Wire the decode layer into a register-sourced syscall entry point.

**Tasks:**

1. Add `lookupThreadRegisterContext : ThreadId → Kernel RegisterFile` that
   extracts the current thread's register context from `SystemState`.
2. Add `dispatchSyscall : SyscallDecodeResult → ThreadId → Kernel Unit`
   that routes decoded arguments to the appropriate `api*` wrapper.
3. Add `syscallEntry : SyscallRegisterLayout → Kernel Unit` as the
   top-level user-space entry point.
4. Prove `syscallEntry_requires_valid_decode`: if `syscallEntry` succeeds,
   the register values decoded successfully.
5. Prove `syscallEntry_implies_capability_held`: if `syscallEntry` succeeds
   for a capability-gated operation, the caller held the required right
   (threading through existing `syscallInvoke_requires_right`).
6. Add `MachineConfig.registerCount` field (default 32 for ARM64).

**Exit criteria:**
- `lake build` passes.
- Soundness theorems proved (zero `sorry`).
- `./scripts/test_smoke.sh` passes.

**Files modified:**
- `SeLe4n/Kernel/API.lean` — `syscallEntry`, `dispatchSyscall`, soundness
  theorems
- `SeLe4n/Machine.lean` — `MachineConfig.registerCount`

---

### WS-J1-D — Invariant and information-flow integration

**Goal:** Extend the proof surface to cover the decode path.

**Tasks:**

1. Add `registerDecodeConsistent` predicate to
   `proofLayerInvariantBundle`: decoded register values that produce typed
   references must index into valid kernel state.
2. Prove `syscallEntry_preserves_proofLayerInvariantBundle` for both
   success and error paths.
3. Extend `NonInterferenceStep` with decode-related constructors
   (`syscallDecode`, `syscallDispatch`).
4. Prove NI for the decode path: register contents in the current
   thread's domain are not observable by threads in other domains
   (threading through existing `projectStateFast` with domain-gated
   `machineRegs`).
5. Add composition coverage for the new `NonInterferenceStep` constructors
   in `composedNonInterference_trace`.

**Exit criteria:**
- `./scripts/test_full.sh` passes.
- NI theorem surface remains zero `sorry`/`axiom`.
- Tier 3 anchor checks pass with new theorem names.

**Files modified:**
- `SeLe4n/Kernel/Architecture/Invariant.lean` — decode consistency predicate
- `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean` — NI theorems
- `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean` — composition
- `SeLe4n/Kernel/InformationFlow/Projection.lean` — projection updates
- `scripts/test_tier3_invariant_surface.sh` — new anchor entries

---

### WS-J1-E — Testing and trace evidence

**Goal:** Complete test coverage for decode paths.

**Tasks:**

1. Add negative decode tests to `tests/NegativeStateSuite.lean`:
   - Invalid register index (out of bounds)
   - Invalid syscall number
   - Malformed message info word
   - Decode of zero-valued registers
2. Add register-sourced syscall trace scenarios to
   `SeLe4n/Testing/MainTraceHarness.lean`:
   - Successful register decode → capability check → kernel operation
   - Failed register decode → explicit error return
   - Register decode with namespace mismatch
3. Add operation-chain tests to `tests/OperationChainSuite.lean`:
   - Multi-syscall sequence via register decode
   - Register decode followed by IPC with message transfer
4. Update `tests/fixtures/main_trace_smoke.expected` with new scenarios.
5. Update `tests/fixtures/scenario_registry.yaml` with new scenario IDs.
6. Add Tier 3 anchors for new theorem and definition names.

**Exit criteria:**
- `./scripts/test_smoke.sh` passes.
- `./scripts/test_full.sh` passes.
- All new tests produce deterministic output.

**Files modified:**
- `tests/NegativeStateSuite.lean` — decode error tests
- `SeLe4n/Testing/MainTraceHarness.lean` — trace scenarios
- `tests/OperationChainSuite.lean` — chain tests
- `tests/fixtures/main_trace_smoke.expected` — fixture update
- `tests/fixtures/scenario_registry.yaml` — scenario ID mappings
- `scripts/test_tier3_invariant_surface.sh` — anchors

---

### WS-J1-F — CdtNodeId cleanup and documentation sync

**Goal:** Wrap `CdtNodeId`, remove all compatibility shims, synchronize
documentation.

**Tasks:**

1. Replace `abbrev CdtNodeId := Nat` with typed wrapper structure in
   `Model/Object/Structures.lean`.
2. Add `DecidableEq`, `Hashable`, `LawfulHashable`, `EquivBEq`,
   `LawfulBEq`, `Repr`, `ToString`, `ofNat`/`toNat` instances.
3. Fix all downstream compilation from `CdtNodeId` type change (HashMap
   key usage in `State.lean:141–143`, CDT operations in
   `Capability/Operations.lean`).
4. Remove any temporary compatibility shims from WS-J1-A that are no
   longer needed.
5. Synchronize documentation:
   - `README.md` — metrics via `codebase_map.json`
   - `docs/spec/SELE4N_SPEC.md` — architecture section
   - `docs/DEVELOPMENT.md` — baseline contracts
   - `docs/WORKSTREAM_HISTORY.md` — WS-J1 entry
   - `docs/CLAIM_EVIDENCE_INDEX.md` — register decode claims
   - `docs/gitbook/03-architecture-and-module-map.md` — module updates
   - `docs/gitbook/04-project-design-deep-dive.md` — design section
   - `docs/gitbook/05-specification-and-roadmap.md` — milestone history
   - `docs/gitbook/12-proof-and-invariant-map.md` — new theorems
6. Regenerate `docs/codebase_map.json`.

**Exit criteria:**
- `./scripts/test_full.sh` passes.
- Zero `sorry`/`axiom` in production.
- All documentation synchronized.
- Tier 0 hygiene passes (website links, fixture validation).

**Files modified:**
- `SeLe4n/Model/Object/Structures.lean` — `CdtNodeId` wrapper
- `SeLe4n/Prelude.lean` — lawful instances for `CdtNodeId`
- `SeLe4n/Model/State.lean` — HashMap key type updates
- `SeLe4n/Kernel/Capability/Operations.lean` — CDT operations
- All documentation files listed above

---

## 6. File impact map

### Core model and machine
| File | Change |
|------|--------|
| `SeLe4n/Machine.lean` | `RegName`/`RegValue` wrappers, `SyscallRegisterLayout`, `MachineConfig.registerCount` |
| `SeLe4n/Prelude.lean` | Lawful instances for `RegName`, `RegValue`, `CdtNodeId` |
| `SeLe4n/Model/Object/Types.lean` | `SyscallId`, `MessageInfo` |
| `SeLe4n/Model/Object/Structures.lean` | `CdtNodeId` wrapper |
| `SeLe4n/Model/State.lean` | New `KernelError` variants, `CdtNodeId` key updates |

### New module
| File | Contents |
|------|----------|
| `SeLe4n/Kernel/Architecture/RegisterDecode.lean` | Decode functions, round-trip lemmas, determinism |

### Kernel transition surfaces
| File | Change |
|------|--------|
| `SeLe4n/Kernel/API.lean` | `syscallEntry`, `dispatchSyscall`, soundness theorems |
| `SeLe4n/Kernel/Architecture/Adapter.lean` | Type annotation updates |
| `SeLe4n/Kernel/Architecture/Assumptions.lean` | Contract signature updates |
| `SeLe4n/Kernel/Scheduler/Operations/Selection.lean` | Context switch type updates |
| `SeLe4n/Kernel/Scheduler/Operations/Core.lean` | Save/restore type updates |
| `SeLe4n/Kernel/Capability/Operations.lean` | CDT `CdtNodeId` updates |

### Proof surfaces
| File | Change |
|------|--------|
| `SeLe4n/Kernel/Architecture/Invariant.lean` | `registerDecodeConsistent` predicate |
| `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean` | Decode NI theorems |
| `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean` | New step constructors |
| `SeLe4n/Kernel/InformationFlow/Projection.lean` | Projection updates |

### Platform contracts
| File | Change |
|------|--------|
| `SeLe4n/Platform/Sim/RuntimeContract.lean` | Type annotation updates |
| `SeLe4n/Platform/Sim/ProofHooks.lean` | Type annotation updates |
| `SeLe4n/Platform/RPi5/RuntimeContract.lean` | Type annotation updates |
| `SeLe4n/Platform/RPi5/ProofHooks.lean` | Type annotation updates |

### Test surfaces
| File | Change |
|------|--------|
| `SeLe4n/Testing/MainTraceHarness.lean` | Register decode trace scenarios |
| `tests/NegativeStateSuite.lean` | Decode error negative tests |
| `tests/OperationChainSuite.lean` | Register-sourced chain tests |
| `tests/fixtures/main_trace_smoke.expected` | Updated fixture |
| `tests/fixtures/scenario_registry.yaml` | New scenario IDs |

### Documentation surfaces
| File | Change |
|------|--------|
| `README.md` | Metrics sync |
| `docs/DEVELOPMENT.md` | Baseline contracts |
| `docs/spec/SELE4N_SPEC.md` | Architecture section |
| `docs/WORKSTREAM_HISTORY.md` | WS-J1 entry |
| `docs/CLAIM_EVIDENCE_INDEX.md` | Decode claims |
| `docs/gitbook/03-architecture-and-module-map.md` | Module map |
| `docs/gitbook/04-project-design-deep-dive.md` | Design section |
| `docs/gitbook/05-specification-and-roadmap.md` | Milestone history |
| `docs/gitbook/12-proof-and-invariant-map.md` | Theorem inventory |

---

## 7. Risk register and mitigations

| # | Risk | Severity | Mitigation |
|---|------|----------|------------|
| 1 | **Proof churn from type change** — replacing `abbrev Nat` with wrapper structures will break every file that uses `RegName`/`RegValue` | High | WS-J1-A introduces types with zero behavior change; downstream fixes are mechanical. Compatibility `ofNat`/`toNat` conversions ease migration. |
| 2 | **Scheduler preservation re-proof** — the `Preservation.lean` file (2170 lines) contains register-related proofs that must be re-proved | High | Read-after-write lemmas are re-proved first in WS-J1-A; scheduler proofs only need `simp` hint updates pointing to new wrapper lemmas. |
| 3 | **Decode layer over-coupling** — making the decode layer subsystem-aware could create unwanted dependencies | Medium | `RegisterDecode.lean` depends only on `Machine.lean` and `Model/Object/Types.lean`. It does not import any kernel subsystem. Subsystems consume decoded results, not the decode module. |
| 4 | **Trace fixture instability** — new trace scenarios change expected output | Medium | Fixture updates staged in WS-J1-E with explicit diff rationale. Determinism test (`test_tier2_determinism.sh`) catches non-deterministic output. |
| 5 | **NI composition expansion** — adding `NonInterferenceStep` constructors requires re-proving `composedNonInterference_trace` | Medium | The decode path is pure and domain-local; NI proofs follow the existing per-constructor pattern with minimal new proof obligations. |
| 6 | **`CdtNodeId` migration ripple** — wrapping `CdtNodeId` touches CDT operations in capability and lifecycle modules | Low | CDT operations use `CdtNodeId` as a HashMap key; the wrapper's `Hashable` instance makes this transparent. Migration is mechanical. |

---

## 8. Validation plan

### Per-slice minimum gate

```bash
./scripts/test_smoke.sh   # Tier 0+1+2: hygiene + build + trace + negative
```

### Required for theorem/invariant slices (WS-J1-D)

```bash
./scripts/test_full.sh    # Tier 0-3: + invariant surface anchors
```

### Nightly confidence (optional for NI composition changes)

```bash
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh
```

### Workstream-specific validation

| Category | Test |
|----------|------|
| Decode correctness | Round-trip lemmas for each decode function |
| Decode determinism | `decodeSyscallArgs` produces identical results on identical inputs |
| Error completeness | Every `KernelError` decode variant exercised by negative test |
| Syscall soundness | `syscallEntry_requires_valid_decode` theorem |
| Authority chain | `syscallEntry_implies_capability_held` theorem |
| NI coverage | Decode-related `NonInterferenceStep` constructors in composition |
| Fixture stability | `test_tier2_determinism.sh` double-run diff |

---

## 9. Completion evidence checklist

- [x] `RegName` and `RegValue` are typed wrapper structures (not `abbrev Nat`) — v0.15.4
- [x] Full instance suite: `DecidableEq`, `Hashable`, `LawfulHashable`,
      `EquivBEq`, `LawfulBEq`, `Repr`, `ToString` — v0.15.4
- [x] All 10 existing machine lemmas re-proved with typed registers — v0.15.4
- [x] `RegisterDecode.lean` module merged with round-trip and determinism
      lemmas (zero `sorry`/`axiom`) — v0.15.5
- [x] `syscallEntry` wired through decode layer to `api*` wrappers — v0.15.6
- [x] `syscallEntry` soundness theorems proved — v0.15.6
- [x] `registerDecodeConsistent` invariant predicate added and preserved — v0.15.8
- [x] NI theorems cover decode path via new `NonInterferenceStep` constructors — v0.15.8
- [x] `CdtNodeId` converted to typed wrapper with full instance suite — v0.15.10
- [x] Negative tests for every decode error path — v0.15.9
- [x] Trace scenarios for register-sourced syscall execution — v0.15.9
- [x] Fixtures updated with rationale — v0.15.9
- [x] All canonical docs and GitBook mirrors synchronized — v0.15.10
- [x] `./scripts/test_full.sh` passes — verified
- [x] Zero `sorry`/`axiom` in production proof surface — verified

---

## 10. Relationship to prior work

### WS-I5 Part A (R-12)

WS-I5 Part A documented the `abbrev Nat` choice as a deliberate
simplification. WS-J1 supersedes that simplification by converting
`RegName`/`RegValue` to typed wrappers and introducing the decode layer.
The prior justification was valid at its stage — register types were internal
to the abstract machine and did not cross authority boundaries. WS-J1
changes this by making registers the authoritative source of syscall
arguments, which requires type-level namespace discrimination.

### WS-H12c (per-TCB register context)

WS-H12c added `registerContext : RegisterFile` to TCB and proved
`contextMatchesCurrent` (machine registers equal current thread's saved
context). WS-J1 builds on this by reading syscall arguments from the
same `registerContext`, making the WS-H12c invariant a prerequisite for
decode correctness.

### WS-H15c (syscall capability-checking wrappers)

WS-H15c introduced `SyscallGate` and the `api*` wrappers. WS-J1 adds the
missing layer *below* `SyscallGate` — the decode from raw registers into
the typed parameters that construct a `SyscallGate`. The `api*` wrappers
continue to serve as the internal kernel API; `syscallEntry` becomes the
new user-space entry point.

### WS-H14 (type safety and Prelude foundations)

WS-H14 established the pattern for typed identifier instances (`EquivBEq`,
`LawfulBEq`, `LawfulHashable`, roundtrip lemmas). WS-J1 follows this exact
pattern for `RegName`, `RegValue`, and `CdtNodeId`.
