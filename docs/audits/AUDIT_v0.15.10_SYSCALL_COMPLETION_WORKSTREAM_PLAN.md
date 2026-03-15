# seLe4n Workstream Plan — Full Syscall Dispatch Completion (WS-K)

**Version target:** v0.16.1–v0.16.8
**Base version:** v0.15.10
**Status:** In progress — K-A completed (v0.16.0), K-B completed (v0.16.1), K-C completed (v0.16.2), K-D completed (v0.16.3), K-E completed (v0.16.4)
**Priority:** Critical
**Estimated effort:** 12–18 days
**Dependencies:** WS-J1 (completed v0.15.10)

---

## 1. Executive summary

WS-J1 established the typed register decode layer (`RegisterDecode.lean`),
syscall entry point (`syscallEntry`), and 13-case capability-gated dispatch.
However, 7 of 13 syscalls return `.illegalState` because their arguments arrive
in message registers (x2–x5) that are validated at the register-bound level but
**not extracted** into `SyscallDecodeResult`. Two additional service syscalls
use `(fun _ => true)` policy stubs. IPC send/call/reply pass empty message
bodies (`registers := #[]`).

This workstream completes the syscall surface:

1. **WS-K-A** — Extend `SyscallDecodeResult` with message register values and
   update the decode layer.
2. **WS-K-B** — Define per-syscall argument structures and typed extraction
   functions from raw message register values.
3. **WS-K-C** — Wire CSpace syscalls (mint, copy, move, delete) through
   dispatch with decoded arguments.
4. **WS-K-D** — Wire Lifecycle and VSpace syscalls (retype, map, unmap)
   through dispatch with decoded arguments.
5. **WS-K-E** — Replace service policy stubs with configuration-sourced
   predicates and populate IPC message bodies from register contents.
6. **WS-K-F** — Round-trip proofs, preservation theorems, and NI integration
   for all new decode and dispatch paths.
7. **WS-K-G** — Comprehensive testing: negative-state, trace, determinism,
   and invariant surface anchors for every new path.
8. **WS-K-H** — Documentation sync, GitBook update, and workstream closeout.

**Design principle:** Each phase is independently buildable and testable. No
phase introduces `sorry` or `axiom`. Every new dispatch path gets a
corresponding NI constructor or proof obligation. The syscall argument decode
is total with explicit `Except` error returns, maintaining the project's
deterministic-semantics invariant.

---

## 2. Problem analysis (code-level audit findings)

### 2.1 Finding: SyscallDecodeResult lacks message register values

**Location:** `SeLe4n/Model/Object/Types.lean:846–850`
**Current:**
```lean
structure SyscallDecodeResult where
  capAddr   : SeLe4n.CPtr      -- x0
  msgInfo   : MessageInfo       -- x1
  syscallId : SyscallId         -- x7
```
**Consequence:** `decodeSyscallArgs` (RegisterDecode.lean:81–95) validates
message register bounds (lines 89–90) but discards their values. All 7
register-dependent syscalls cannot extract arguments from the decode result.

**Severity:** Critical — blocks 7/13 syscall implementations.

### 2.2 Finding: 7 syscalls return `.illegalState` unconditionally

**Location:** `SeLe4n/Kernel/API.lean:390–399`
```lean
| .cspaceMint    => fun _ => .error .illegalState
| .cspaceCopy    => fun _ => .error .illegalState
| .cspaceMove    => fun _ => .error .illegalState
| .cspaceDelete  => fun _ => .error .illegalState
| .lifecycleRetype => fun _ => .error .illegalState
| .vspaceMap     => fun _ => .error .illegalState
| .vspaceUnmap   => fun _ => .error .illegalState
```
**Consequence:** These syscalls are modeled at the kernel-operation level
(CSpace, Lifecycle, VSpace modules) but unreachable from the register-sourced
entry point. The end-to-end chain `register → decode → dispatch → operation`
is broken for over half the syscall set.

**Severity:** Critical — the syscall surface is incomplete.

### 2.3 Finding: Service policy stubs accept all entries

**Location:** `SeLe4n/Kernel/API.lean:403, 408`
```lean
serviceStart (ServiceId.ofNat objId.toNat) (fun _ => true)
serviceStop  (ServiceId.ofNat objId.toNat) (fun _ => true)
```
**Consequence:** The `ServicePolicy` predicate (`ServiceGraphEntry → Bool`)
is designed to gate service operations based on configuration or caller
authority, but the dispatch path bypasses it entirely. Any thread with a
capability to the service object can start/stop it unconditionally.

**Severity:** High — weakens the service isolation model.

### 2.4 Finding: IPC messages carry empty register payloads

**Location:** `SeLe4n/Kernel/API.lean:368, 380, 385`
```lean
endpointSendDual epId tid { registers := #[], caps := #[], badge := cap.badge }
endpointCall epId tid     { registers := #[], caps := #[], badge := cap.badge }
endpointReply tid target  { registers := #[], caps := #[], badge := cap.badge }
```
**Consequence:** The IPC subsystem supports message register transport (the
`IpcMessage.registers` field carries `Array RegValue`), but the dispatch path
never populates it. Message data carried in x2–x5 is lost at the syscall
boundary.

**Severity:** High — IPC message payloads are non-functional.

### 2.5 Summary of gaps

| # | Gap | Location | Severity | Blocks |
|---|-----|----------|----------|--------|
| G1 | No msgRegs in SyscallDecodeResult | Types.lean:846 | Critical | G2–G4 |
| G2 | CSpace dispatch stubs | API.lean:390–393 | Critical | — |
| G3 | Lifecycle+VSpace dispatch stubs | API.lean:396–399 | Critical | — |
| G4 | Empty IPC message bodies | API.lean:368,380,385 | High | — |
| G5 | Service policy stubs | API.lean:403,408 | High | — |
| G6 | No per-syscall argument decode | — | Critical | G2–G3 |
| G7 | No round-trip proofs for msgRegs | — | Medium | — |
| G8 | No NI coverage for new dispatch paths | — | Medium | — |

---

## 3. Design

### 3.1 Design principles

1. **Total decode with explicit errors.** Every new decode function returns
   `Except KernelError T`. No partial functions, no `Option.get!`, no panics.

2. **Per-syscall argument structures.** Each syscall family gets a dedicated
   argument structure decoded from message registers, keeping dispatch type-safe
   and self-documenting.

3. **Minimal SyscallDecodeResult extension.** Add a single `msgRegs` field
   (an array of `RegValue`) to the existing structure. Per-syscall argument
   extraction is a second layer on top of the raw values.

4. **Backward-compatible dispatch.** The `dispatchWithCap` signature gains
   access to `SyscallDecodeResult` (not just `SyscallId`), but existing IPC
   dispatch paths continue to work unchanged.

5. **Incremental NI coverage.** New dispatch paths use existing
   `NonInterferenceStep` constructors where possible. New constructors are added
   only when the existing set cannot express the domain-separation hypothesis.

6. **Service policy from system state.** Replace `(fun _ => true)` with a
   policy derived from `SystemState.serviceConfig` or an equivalent
   configuration record, making the policy auditable and verifiable.

### 3.2 New core types

```lean
-- Extended decode result (WS-K-A)
structure SyscallDecodeResult where
  capAddr   : SeLe4n.CPtr
  msgInfo   : MessageInfo
  syscallId : SyscallId
  msgRegs   : Array RegValue    -- NEW: raw values from layout.msgRegs
  deriving Repr, DecidableEq

-- Per-syscall argument structures (WS-K-B)
structure CSpaceMintArgs where
  srcSlot   : Slot
  dstSlot   : Slot
  rights    : AccessRightSet
  badge     : Option Badge
  deriving Repr, DecidableEq

structure CSpaceCopyArgs where
  srcSlot   : Slot
  dstSlot   : Slot
  deriving Repr, DecidableEq

structure CSpaceMoveArgs where
  srcSlot   : Slot
  dstSlot   : Slot
  deriving Repr, DecidableEq

structure CSpaceDeleteArgs where
  targetSlot : Slot
  deriving Repr, DecidableEq

structure LifecycleRetypeArgs where
  targetObj : ObjId
  newType   : Nat          -- object type tag decoded from register
  size      : Nat          -- object size hint
  deriving Repr, DecidableEq

structure VSpaceMapArgs where
  asid  : ASID
  vaddr : VAddr
  paddr : PAddr
  perms : Nat              -- raw permissions word
  deriving Repr, DecidableEq

structure VSpaceUnmapArgs where
  asid  : ASID
  vaddr : VAddr
  deriving Repr, DecidableEq
```

### 3.3 Decode architecture

```
Register File (x0–x7)
    │
    ├── x0 → decodeCapPtr     → CPtr        ─┐
    ├── x1 → decodeMsgInfo    → MessageInfo   ├── SyscallDecodeResult
    ├── x7 → decodeSyscallId  → SyscallId     │
    └── x2–x5 → readReg       → Array RegValue┘
                                    │
                        ┌───────────┴───────────┐
                   decodeCSpaceMintArgs    decodeVSpaceMapArgs
                   decodeCSpaceCopyArgs    decodeVSpaceUnmapArgs
                   decodeCSpaceMoveArgs    decodeLifecycleRetypeArgs
                   decodeCSpaceDeleteArgs
                        │                       │
                   CSpaceMintArgs          VSpaceMapArgs
                        │                       │
                   dispatchWithCap ─────── uses args to call operations
```

### 3.4 Service policy design

```lean
-- Configuration record in SystemState (WS-K-E)
structure ServiceConfig where
  allowStart : ServicePolicy    -- default: all allowed
  allowStop  : ServicePolicy    -- default: all allowed
  deriving Inhabited

-- dispatchWithCap reads policy from state
| .serviceStart =>
    match cap.target with
    | .object objId =>
        fun st => serviceStart (ServiceId.ofNat objId.toNat)
                    st.serviceConfig.allowStart st
    | _ => fun _ => .error .invalidCapability
```

### 3.5 IPC message population design

```lean
-- In dispatchWithCap (WS-K-E), IPC syscalls populate message body:
| .send =>
    match cap.target with
    | .object epId =>
        let msgBody := extractMessageRegisters decoded.msgRegs decoded.msgInfo
        endpointSendDual epId tid { registers := msgBody, caps := #[], badge := cap.badge }
    | _ => fun _ => .error .invalidCapability
```

Where `extractMessageRegisters` reads up to `msgInfo.length` values from the
decoded message register array, capped by `maxMessageRegisters`.

---

## 4. Scope and non-goals

### In scope
- Extend `SyscallDecodeResult` with `msgRegs` field
- Per-syscall argument decode functions (total, with `Except` errors)
- Full dispatch for all 13 syscalls through `dispatchWithCap`
- Service policy from system-state configuration
- IPC message body population from message registers
- Round-trip proofs for message register extraction
- Determinism proofs for all new decode paths
- NI integration for new dispatch paths
- Negative-state tests for all new error paths
- Trace tests for all 13 syscalls through register-sourced entry
- Documentation and GitBook sync

### Non-goals
- Hardware platform binding (RPi5 runtime contracts)
- Extra capability transfer through IPC (cap field population)
- Multi-level page table walk implementation
- GIC-400 interrupt routing
- Boot sequence verification
- Changes to `NonInterferenceStep` constructor count beyond what new
  dispatch paths require

---

## 5. Work breakdown structure

### WS-K-A — Message Register Extraction into SyscallDecodeResult

**Goal:** Extend `SyscallDecodeResult` with a `msgRegs : Array RegValue` field
and update `decodeSyscallArgs` to populate it from the layout's message
register array. This is the foundational change that unblocks all subsequent
WS-K phases (B through G), since per-syscall argument decode and IPC message
population both depend on having raw message register values available in the
decode result.

**Design rationale:**

The existing `decodeSyscallArgs` (RegisterDecode.lean:81–95) already validates
message register bounds (layout.msgRegs entries checked against regCount) but
**discards** the values — the `for r in layout.msgRegs` loop validates bounds
only, then the result is constructed without the values. The fix reads and stores
the values in a single pass after bounds validation, preserving the existing
validation semantics while capturing the data.

The new `msgRegs` field uses a default value of `#[]` to ensure backward
compatibility: all existing call sites that construct `SyscallDecodeResult`
without specifying `msgRegs` compile unchanged. This eliminates migration risk
and allows incremental adoption.

**Subtasks:**

#### K-A.1 — Structure extension (Types.lean)
Add `msgRegs : Array RegValue := #[]` field to `SyscallDecodeResult` in
`Model/Object/Types.lean`. The default value `#[]` ensures backward
compatibility with all existing construction sites (tests, fixtures, proof
references). Verify that `DecidableEq` and `Repr` deriving still synthesize
correctly with the new field. No other file changes needed for this subtask.

**File:** `SeLe4n/Model/Object/Types.lean` (line ~846)
**Acceptance:** `lake build` passes; `grep -n 'msgRegs' SeLe4n/Model/Object/Types.lean` shows the field.

#### K-A.2 — Decode function update (RegisterDecode.lean)
Update `decodeSyscallArgs` to populate the `msgRegs` field. The existing
bounds validation loop (`for r in layout.msgRegs do validateRegBound r regCount`)
is replaced with a combined validate-and-read pass using `Array.mapM`:
```lean
let msgRegVals ← layout.msgRegs.mapM fun r => do
  validateRegBound r regCount
  pure (readReg regs r)
pure { capAddr, msgInfo, syscallId, msgRegs := msgRegVals }
```
This is semantically equivalent to the existing bounds check followed by a
separate read pass, but avoids iterating twice. The `mapM` short-circuits on
the first out-of-bounds register, preserving the existing `invalidRegister`
error behavior.

**File:** `SeLe4n/Kernel/Architecture/RegisterDecode.lean` (lines 81–95)
**Acceptance:** `decodeSyscallArgs` returns `SyscallDecodeResult` with populated `msgRegs`; existing tests still pass.

#### K-A.3 — Encoding helper for message registers (RegisterDecode.lean)
Add `encodeMsgRegs` helper that converts an array of `RegValue` back to raw
register values (identity for the abstract model, but stated explicitly for
proof surface completeness):
```lean
@[inline] def encodeMsgRegs (regs : Array RegValue) : Array RegValue := regs
```
This trivial encoding mirrors the existing `encodeCapPtr`/`encodeMsgInfo`/
`encodeSyscallId` helpers and serves as the left half of the round-trip proof.

**File:** `SeLe4n/Kernel/Architecture/RegisterDecode.lean`
**Acceptance:** Definition compiles; used in round-trip lemma (K-A.5).

#### K-A.4 — Length invariant lemma (RegisterDecode.lean)
Prove `decodeMsgRegs_length`: when `decodeSyscallArgs` succeeds, the result's
`msgRegs.size` equals `layout.msgRegs.size`. The proof unfolds the `mapM`
definition and uses `Array.size_mapM` (or equivalent) to show the output array
has the same length as the input layout array.
```lean
theorem decodeMsgRegs_length
    (layout : SyscallRegisterLayout) (regs : RegisterFile) (regCount : Nat)
    (decoded : SyscallDecodeResult)
    (hOk : decodeSyscallArgs layout regs regCount = .ok decoded) :
    decoded.msgRegs.size = layout.msgRegs.size
```
This lemma is critical for K-B: per-syscall decode functions check
`msgRegs.size ≥ N` and need to know the relationship between the result size
and the platform layout.

**File:** `SeLe4n/Kernel/Architecture/RegisterDecode.lean`
**Acceptance:** Theorem stated and proved (zero sorry). Used in K-B decode functions.

#### K-A.5 — Round-trip lemma for message register values (RegisterDecode.lean)
Prove that encoding then decoding message register values preserves the
original array. Since `encodeMsgRegs` is identity, this is a structural proof:
```lean
theorem decodeMsgRegs_roundtrip (vals : Array RegValue) :
    encodeMsgRegs vals = vals
```
Additionally, extend `decode_components_roundtrip` to include the `msgRegs`
component, showing that the full four-component round-trip holds:
```lean
theorem decode_components_roundtrip (decoded : SyscallDecodeResult) ... :
    decodeCapPtr (encodeCapPtr decoded.capAddr) = .ok decoded.capAddr ∧
    decodeMsgInfo (encodeMsgInfo decoded.msgInfo) = .ok decoded.msgInfo ∧
    decodeSyscallId (encodeSyscallId decoded.syscallId) = .ok decoded.syscallId ∧
    encodeMsgRegs decoded.msgRegs = decoded.msgRegs
```

**File:** `SeLe4n/Kernel/Architecture/RegisterDecode.lean`
**Acceptance:** Both theorems proved (zero sorry). Round-trip surface complete for all decode components.

#### K-A.6 — Determinism extension (RegisterDecode.lean)
Verify that the existing `decodeSyscallArgs_deterministic` theorem still holds
with the updated function (it should, since the proof is `rfl` and the function
remains pure). No changes expected, but explicit verification is required.

**File:** `SeLe4n/Kernel/Architecture/RegisterDecode.lean`
**Acceptance:** `decodeSyscallArgs_deterministic` compiles unchanged.

#### K-A.7 — Test call site updates
Update all test files that directly construct `SyscallDecodeResult` or call
`decodeSyscallArgs` to account for the new `msgRegs` field:

- **`tests/NegativeStateSuite.lean`**: The 5 existing `decodeSyscallArgs` tests
  (J1-NEG-13 through J1-NEG-17) call `decodeSyscallArgs` which now returns a
  result with `msgRegs`. Tests that check `.error` results need no changes.
  The J1-NEG-17 success test should verify `msgRegs.size = 4` (matching
  `arm64DefaultLayout.msgRegs.size`).
- **`SeLe4n/Testing/MainTraceHarness.lean`**: The RDT trace scenario at line
  ~1232 calls `decodeSyscallArgs` and uses the result. Verify it compiles;
  optionally add a trace line showing `msgRegs.size`.
- **`tests/InvariantSurfaceSuite.lean`**: Add `#check` anchors for the new
  `decodeMsgRegs_length` and `decodeMsgRegs_roundtrip` theorems.

**Files:**
- `tests/NegativeStateSuite.lean`
- `SeLe4n/Testing/MainTraceHarness.lean`
- `tests/InvariantSurfaceSuite.lean`

**Acceptance:** All tests compile; `test_smoke.sh` passes.

#### K-A.8 — Build and smoke verification
Run `lake build` and `./scripts/test_smoke.sh` to confirm:
- Zero compilation errors
- Zero `sorry` or `axiom` in production code
- All Tier 0–2 tests pass
- Fixture output matches (or fixture updated if trace output changed)

**Acceptance:** `test_smoke.sh` exits 0.

**Exit criteria:**
- `SyscallDecodeResult` includes `msgRegs : Array RegValue := #[]` field.
- `decodeSyscallArgs` reads and stores message register values in single pass.
- `decodeMsgRegs_length` lemma proved: `decoded.msgRegs.size = layout.msgRegs.size`.
- `decodeMsgRegs_roundtrip` and extended `decode_components_roundtrip` proved.
- `decodeSyscallArgs_deterministic` compiles unchanged.
- All test call sites updated and passing.
- `lake build` passes; `test_smoke.sh` passes.
- Zero `sorry`/`axiom` in production proof surface.

**Files modified:**
- `SeLe4n/Model/Object/Types.lean` — Add `msgRegs` field with default to structure.
- `SeLe4n/Kernel/Architecture/RegisterDecode.lean` — Update decode function,
  add `encodeMsgRegs`, add length/round-trip lemmas.
- `tests/NegativeStateSuite.lean` — Verify/update decode tests for msgRegs.
- `SeLe4n/Testing/MainTraceHarness.lean` — Verify/update trace scenarios.
- `tests/InvariantSurfaceSuite.lean` — Add Tier 3 anchors for new theorems.

**Version target:** v0.16.0

---

### WS-K-B — Per-Syscall Argument Decode Layer

**Goal:** Define typed argument structures for each syscall family and total
decode functions that extract them from `SyscallDecodeResult.msgRegs`. This is
the second decode layer: `RegisterDecode.lean` converts raw registers into a
flat `SyscallDecodeResult` (layer 1); this module converts the `msgRegs` array
within that result into per-syscall typed argument structures (layer 2).

**Design rationale:**

The ARM64 syscall convention packs up to 4 message register values in x2–x5.
After K-A, these arrive as `decoded.msgRegs : Array RegValue` with
`decoded.msgRegs.size = layout.msgRegs.size` (guaranteed by
`decodeMsgRegs_length`). Each syscall family requires a different number of
message registers and interprets them differently:

| Syscall family | Min regs | Register mapping |
|---|---|---|
| CSpace mint | 4 | x2=srcSlot, x3=dstSlot, x4=rights bitmask, x5=badge |
| CSpace copy/move | 2 | x2=srcSlot, x3=dstSlot |
| CSpace delete | 1 | x2=targetSlot |
| Lifecycle retype | 3 | x2=targetObj, x3=newType tag, x4=size hint |
| VSpace map | 4 | x2=asid, x3=vaddr, x4=paddr, x5=perms word |
| VSpace unmap | 2 | x2=asid, x3=vaddr |

A shared `requireMsgReg` helper provides safe indexing with a uniform error
(`invalidMessageInfo`) on insufficient registers. All decode functions are
pure `Except KernelError T` — no state access, no side effects.

**Subtasks:**

#### K-B.1 — Module skeleton and safe indexing helper (SyscallArgDecode.lean)

Create `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` with:
- Module docstring describing the two-layer decode architecture.
- Imports: `SeLe4n.Model.State` only (same dependency discipline as
  `RegisterDecode.lean`).
- Shared `requireMsgReg` helper:
  ```lean
  @[inline] def requireMsgReg (regs : Array RegValue) (idx : Nat)
      : Except KernelError RegValue :=
    if h : idx < regs.size then .ok regs[idx]
    else .error .invalidMessageInfo
  ```
  This provides bounds-checked indexing with the canonical error. Every
  per-syscall decode function delegates to this, avoiding duplicated bounds
  logic.
- Determinism theorem for `requireMsgReg` (trivially `rfl`).
- Error-exclusivity theorem for `requireMsgReg`:
  ```lean
  theorem requireMsgReg_error_iff (regs : Array RegValue) (idx : Nat) :
      requireMsgReg regs idx = .error .invalidMessageInfo ↔ ¬(idx < regs.size)
  ```

**File:** `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` (new)
**Acceptance:** `lake build` passes; `requireMsgReg` compiles with theorems.

#### K-B.2 — CSpace argument structures (SyscallArgDecode.lean)

Define the four CSpace argument structures:
```lean
structure CSpaceMintArgs where
  srcSlot : Slot
  dstSlot : Slot
  rights  : AccessRightSet
  badge   : Badge
  deriving Repr, DecidableEq

structure CSpaceCopyArgs where
  srcSlot : Slot
  dstSlot : Slot
  deriving Repr, DecidableEq

structure CSpaceMoveArgs where
  srcSlot : Slot
  dstSlot : Slot
  deriving Repr, DecidableEq

structure CSpaceDeleteArgs where
  targetSlot : Slot
  deriving Repr, DecidableEq
```

Design notes:
- `CSpaceMintArgs.badge` uses `Badge` (not `Option Badge`) because the raw
  register always carries a value; the dispatch path can choose to pass
  `some badge` or `none` based on a zero-check at the call site (K-C).
- `CSpaceCopyArgs` and `CSpaceMoveArgs` are structurally identical but
  semantically distinct — keeping them separate avoids accidental confusion
  at dispatch call sites and makes the decode layer self-documenting.
- All structures use typed identifiers (`Slot`, `AccessRightSet`, `Badge`)
  — never raw `Nat`.

**File:** `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean`
**Acceptance:** All 4 structures compile with `DecidableEq` and `Repr`.

#### K-B.3 — CSpace decode functions (SyscallArgDecode.lean)

Implement decode functions for each CSpace argument structure:
```lean
def decodeCSpaceMintArgs (decoded : SyscallDecodeResult)
    : Except KernelError CSpaceMintArgs := do
  let r0 ← requireMsgReg decoded.msgRegs 0
  let r1 ← requireMsgReg decoded.msgRegs 1
  let r2 ← requireMsgReg decoded.msgRegs 2
  let r3 ← requireMsgReg decoded.msgRegs 3
  pure { srcSlot := Slot.ofNat r0.val
         dstSlot := Slot.ofNat r1.val
         rights  := ⟨r2.val⟩
         badge   := Badge.ofNat r3.val }

def decodeCSpaceCopyArgs (decoded : SyscallDecodeResult)
    : Except KernelError CSpaceCopyArgs := do
  let r0 ← requireMsgReg decoded.msgRegs 0
  let r1 ← requireMsgReg decoded.msgRegs 1
  pure { srcSlot := Slot.ofNat r0.val, dstSlot := Slot.ofNat r1.val }

def decodeCSpaceMoveArgs (decoded : SyscallDecodeResult)
    : Except KernelError CSpaceMoveArgs := do
  let r0 ← requireMsgReg decoded.msgRegs 0
  let r1 ← requireMsgReg decoded.msgRegs 1
  pure { srcSlot := Slot.ofNat r0.val, dstSlot := Slot.ofNat r1.val }

def decodeCSpaceDeleteArgs (decoded : SyscallDecodeResult)
    : Except KernelError CSpaceDeleteArgs := do
  let r0 ← requireMsgReg decoded.msgRegs 0
  pure { targetSlot := Slot.ofNat r0.val }
```

Each function short-circuits via `do` notation on the first insufficient
register, producing `invalidMessageInfo`. The `do` desugaring of `Except`
ensures left-to-right evaluation with early exit on error.

**File:** `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean`
**Acceptance:** All 4 decode functions compile; `lake build` passes.

#### K-B.4 — Lifecycle and VSpace argument structures (SyscallArgDecode.lean)

Define the remaining 3 argument structures:
```lean
structure LifecycleRetypeArgs where
  targetObj : ObjId
  newType   : Nat          -- object type tag decoded from register
  size      : Nat          -- object size hint
  deriving Repr, DecidableEq

structure VSpaceMapArgs where
  asid  : ASID
  vaddr : VAddr
  paddr : PAddr
  perms : Nat              -- raw permissions word (decoded to PagePermissions at dispatch)
  deriving Repr, DecidableEq

structure VSpaceUnmapArgs where
  asid  : ASID
  vaddr : VAddr
  deriving Repr, DecidableEq
```

Design notes:
- `LifecycleRetypeArgs.newType` stays as `Nat` because the type-tag →
  `KernelObject` mapping is a dispatch-layer concern (K-D `objectOfTypeTag`),
  not a decode-layer concern. The decode layer converts raw bits to typed
  identifiers but does not interpret domain semantics.
- `VSpaceMapArgs.perms` stays as `Nat` for the same reason — `PagePermissions`
  construction with W^X validation happens at the dispatch boundary.
- `VSpaceUnmapArgs` needs only 2 registers (ASID + vaddr).

**File:** `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean`
**Acceptance:** All 3 structures compile with `DecidableEq` and `Repr`.

#### K-B.5 — Lifecycle and VSpace decode functions (SyscallArgDecode.lean)

Implement decode functions for the remaining structures:
```lean
def decodeLifecycleRetypeArgs (decoded : SyscallDecodeResult)
    : Except KernelError LifecycleRetypeArgs := do
  let r0 ← requireMsgReg decoded.msgRegs 0
  let r1 ← requireMsgReg decoded.msgRegs 1
  let r2 ← requireMsgReg decoded.msgRegs 2
  pure { targetObj := ObjId.ofNat r0.val
         newType   := r1.val
         size      := r2.val }

def decodeVSpaceMapArgs (decoded : SyscallDecodeResult)
    : Except KernelError VSpaceMapArgs := do
  let r0 ← requireMsgReg decoded.msgRegs 0
  let r1 ← requireMsgReg decoded.msgRegs 1
  let r2 ← requireMsgReg decoded.msgRegs 2
  let r3 ← requireMsgReg decoded.msgRegs 3
  pure { asid  := ASID.ofNat r0.val
         vaddr := VAddr.ofNat r1.val
         paddr := PAddr.ofNat r2.val
         perms := r3.val }

def decodeVSpaceUnmapArgs (decoded : SyscallDecodeResult)
    : Except KernelError VSpaceUnmapArgs := do
  let r0 ← requireMsgReg decoded.msgRegs 0
  let r1 ← requireMsgReg decoded.msgRegs 1
  pure { asid  := ASID.ofNat r0.val
         vaddr := VAddr.ofNat r1.val }
```

**File:** `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean`
**Acceptance:** All 3 decode functions compile; `lake build` passes.

#### K-B.6 — Determinism theorems (SyscallArgDecode.lean)

Add a determinism theorem for each of the 7 decode functions. Since all
functions are pure with no state access, these are trivially `rfl`:
```lean
theorem decodeCSpaceMintArgs_deterministic (d : SyscallDecodeResult) :
    decodeCSpaceMintArgs d = decodeCSpaceMintArgs d := rfl
-- ... (analogous for all 7)
```

These are stated explicitly for proof-surface anchoring — the invariant
surface tests (Tier 3) reference them to ensure no regression introduces
non-determinism.

**File:** `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean`
**Acceptance:** All 7 theorems compile (zero sorry).

#### K-B.7 — Error-exclusivity theorems (SyscallArgDecode.lean)

For each decode function, prove that decode fails **if and only if** the
`msgRegs` array has insufficient entries. This establishes the precise error
contract that dispatch paths (K-C, K-D) and negative tests (K-G) rely on.

```lean
theorem decodeCSpaceMintArgs_error_iff (d : SyscallDecodeResult) :
    (∃ e, decodeCSpaceMintArgs d = .error e) ↔ d.msgRegs.size < 4

theorem decodeCSpaceCopyArgs_error_iff (d : SyscallDecodeResult) :
    (∃ e, decodeCSpaceCopyArgs d = .error e) ↔ d.msgRegs.size < 2

theorem decodeCSpaceMoveArgs_error_iff (d : SyscallDecodeResult) :
    (∃ e, decodeCSpaceMoveArgs d = .error e) ↔ d.msgRegs.size < 2

theorem decodeCSpaceDeleteArgs_error_iff (d : SyscallDecodeResult) :
    (∃ e, decodeCSpaceDeleteArgs d = .error e) ↔ d.msgRegs.size < 1

theorem decodeLifecycleRetypeArgs_error_iff (d : SyscallDecodeResult) :
    (∃ e, decodeLifecycleRetypeArgs d = .error e) ↔ d.msgRegs.size < 3

theorem decodeVSpaceMapArgs_error_iff (d : SyscallDecodeResult) :
    (∃ e, decodeVSpaceMapArgs d = .error e) ↔ d.msgRegs.size < 4

theorem decodeVSpaceUnmapArgs_error_iff (d : SyscallDecodeResult) :
    (∃ e, decodeVSpaceUnmapArgs d = .error e) ↔ d.msgRegs.size < 2
```

Proof strategy: unfold the decode function and `requireMsgReg`, then use
`simp` with `Array.size` lemmas to reduce the goal to a comparison on
`msgRegs.size`. The `do`-notation desugars to nested `Except.bind` calls
that short-circuit on the first `requireMsgReg` failure — the proof proceeds
by case-splitting on whether each index is in bounds.

**File:** `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean`
**Acceptance:** All 7 theorems compile (zero sorry).

#### K-B.8 — API import and build verification

1. Add `import SeLe4n.Kernel.Architecture.SyscallArgDecode` to
   `SeLe4n/Kernel/API.lean` so the dispatch layer (K-C) can reference
   decode functions.
2. Run `lake build` to verify zero compilation errors.
3. Run `./scripts/test_smoke.sh` to verify all Tier 0–2 tests pass.
4. Verify zero `sorry` in the new file:
   `grep -c 'sorry' SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` → 0.

**Files modified:**
- `SeLe4n/Kernel/API.lean` — Add import.

**Acceptance:** `lake build` and `test_smoke.sh` pass; zero `sorry`.

**Exit criteria:**
- All 7 argument structures defined with `DecidableEq`, `Repr`.
- All 7 decode functions are total with explicit `Except` error returns.
- Shared `requireMsgReg` helper with bounds-checked indexing.
- 7 determinism theorems proved (trivially `rfl`).
- 7 error-exclusivity theorems proved (decode fails iff regs insufficient).
- `requireMsgReg` error-exclusivity theorem proved.
- API import added; `lake build` and `test_smoke.sh` pass.
- Zero `sorry`/`axiom` in production proof surface.

**Files created:**
- `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean`

**Files modified:**
- `SeLe4n/Kernel/API.lean` — Import new module.

**Version target:** v0.16.1

---

### WS-K-C — CSpace Syscall Dispatch

**Goal:** Wire `cspaceMint`, `cspaceCopy`, `cspaceMove`, `cspaceDelete`
through `dispatchWithCap` using decoded message register arguments. Replace
all 4 CSpace `.illegalState` stubs with real dispatch paths that decode
per-syscall arguments from `SyscallDecodeResult.msgRegs` and delegate to the
existing kernel-level CSpace operations.

**Design rationale:**

The `dispatchWithCap` function currently takes `SyscallId` as its first
parameter and matches on it. CSpace syscalls need access to the full
`SyscallDecodeResult` (specifically `msgRegs`) to extract slot indices,
rights, and badge values. The signature change from `SyscallId` to
`SyscallDecodeResult` is minimal: the match still dispatches on
`decoded.syscallId`, but CSpace arms can now invoke `decodeCSpaceMintArgs`,
`decodeCSpaceCopyArgs`, etc. on the full decode result.

**Badge handling:** `CSpaceMintArgs.badge` is a `Badge` (always populated
from the raw register), but `cspaceMint` accepts `Option Badge`. The dispatch
layer converts using a zero-check: `if args.badge.val = 0 then none else
some args.badge`. This mirrors seL4's convention where badge=0 means "no
badge".

**Soundness theorem impact:** The `dispatchSyscall_requires_right` theorem
at API.lean:515 passes `dispatchWithCap decoded.syscallId tid` to
`syscallInvoke_requires_right`. After the signature change, this becomes
`dispatchWithCap decoded tid`. The theorem proof relies only on
`syscallInvoke_requires_right` (which proves capability lookup succeeded)
and does not inspect `dispatchWithCap`'s body, so it composes unchanged —
the call site update in `dispatchSyscall` is the only change needed.

**Subtasks:**

#### K-C.1 — Signature change: `dispatchWithCap` accepts `SyscallDecodeResult`

Change the first parameter of `dispatchWithCap` from `SyscallId` to
`SyscallDecodeResult`. Update the match to dispatch on `decoded.syscallId`.
All existing arms (IPC, service) continue to work because they only use
`cap` and `tid`, not `decoded.msgRegs`. The signature becomes:
```lean
private def dispatchWithCap (decoded : SyscallDecodeResult)
    (tid : SeLe4n.ThreadId) (cap : Capability) : Kernel Unit :=
  match decoded.syscallId with
  ...
```

Update the call site in `dispatchSyscall` (API.lean:431) from
`dispatchWithCap decoded.syscallId tid` to `dispatchWithCap decoded tid`.

**File:** `SeLe4n/Kernel/API.lean` (lines 363, 431)
**Acceptance:** `lake build` passes; IPC and service dispatch unaffected.

#### K-C.2 — Wire `cspaceMint` dispatch

Replace the `.cspaceMint` stub (currently `fun _ => .error .illegalState`)
with a full dispatch path:
```lean
| .cspaceMint =>
    match cap.target with
    | .object cnodeId =>
        fun st => match decodeCSpaceMintArgs decoded with
        | .error e => .error e
        | .ok args =>
            let src : CSpaceAddr := { cnode := cnodeId, slot := args.srcSlot }
            let dst : CSpaceAddr := { cnode := cnodeId, slot := args.dstSlot }
            let badge : Option SeLe4n.Badge :=
              if args.badge.val = 0 then none else some args.badge
            cspaceMint src dst args.rights badge st
    | _ => fun _ => .error .invalidCapability
```

The capability's target must be an `.object` pointing to the CNode where
source and destination slots live. This matches seL4's design: the invoked
capability targets the CNode, and message registers specify slot indices
within that CNode. The `decodeCSpaceMintArgs` call extracts all 4 message
register values (srcSlot, dstSlot, rights, badge).

**File:** `SeLe4n/Kernel/API.lean` (line ~391)
**Acceptance:** `lake build` passes; `.cspaceMint` no longer returns `.illegalState`.

#### K-C.3 — Wire `cspaceCopy` dispatch

Replace the `.cspaceCopy` stub with:
```lean
| .cspaceCopy =>
    match cap.target with
    | .object cnodeId =>
        fun st => match decodeCSpaceCopyArgs decoded with
        | .error e => .error e
        | .ok args =>
            let src : CSpaceAddr := { cnode := cnodeId, slot := args.srcSlot }
            let dst : CSpaceAddr := { cnode := cnodeId, slot := args.dstSlot }
            cspaceCopy src dst st
    | _ => fun _ => .error .invalidCapability
```

`cspaceCopy` takes only `(src dst : CSpaceAddr)` — no rights attenuation or
badge, making this the simplest wiring after delete.

**File:** `SeLe4n/Kernel/API.lean` (line ~392)
**Acceptance:** `lake build` passes; `.cspaceCopy` no longer returns `.illegalState`.

#### K-C.4 — Wire `cspaceMove` dispatch

Replace the `.cspaceMove` stub with:
```lean
| .cspaceMove =>
    match cap.target with
    | .object cnodeId =>
        fun st => match decodeCSpaceMoveArgs decoded with
        | .error e => .error e
        | .ok args =>
            let src : CSpaceAddr := { cnode := cnodeId, slot := args.srcSlot }
            let dst : CSpaceAddr := { cnode := cnodeId, slot := args.dstSlot }
            cspaceMove src dst st
    | _ => fun _ => .error .invalidCapability
```

`cspaceMove` has the same signature as `cspaceCopy` (`src dst : CSpaceAddr`).
The kernel operation handles atomicity: it inserts into dst, then deletes
src, and transfers CDT edges. The dispatch layer is responsible only for
address construction from decoded registers.

**File:** `SeLe4n/Kernel/API.lean` (line ~393)
**Acceptance:** `lake build` passes; `.cspaceMove` no longer returns `.illegalState`.

#### K-C.5 — Wire `cspaceDelete` dispatch

Replace the `.cspaceDelete` stub with:
```lean
| .cspaceDelete =>
    match cap.target with
    | .object cnodeId =>
        fun st => match decodeCSpaceDeleteArgs decoded with
        | .error e => .error e
        | .ok args =>
            let addr : CSpaceAddr := { cnode := cnodeId, slot := args.targetSlot }
            cspaceDeleteSlot addr st
    | _ => fun _ => .error .invalidCapability
```

Delete requires only 1 message register (the target slot). The invoked
capability's target identifies the CNode, and the decoded `targetSlot`
specifies which slot within it to delete.

**File:** `SeLe4n/Kernel/API.lean` (line ~394)
**Acceptance:** `lake build` passes; `.cspaceDelete` no longer returns `.illegalState`.

#### K-C.6 — Verify existing soundness theorems compile unchanged

After K-C.1–K-C.5, verify that all three existing soundness theorems still
compile without modification:

1. **`dispatchSyscall_requires_right`** (API.lean:495): The proof calls
   `syscallInvoke_requires_right` with `dispatchWithCap decoded tid` (updated
   from `dispatchWithCap decoded.syscallId tid`). Since
   `syscallInvoke_requires_right` quantifies over any `op : Capability →
   Kernel α`, the proof composes regardless of `dispatchWithCap`'s internal
   changes.

2. **`syscallEntry_implies_capability_held`** (API.lean:531): Threads through
   `dispatchSyscall_requires_right`. No direct reference to `dispatchWithCap`.

3. **`syscallEntry_requires_valid_decode`** (API.lean:467): Does not reference
   `dispatchWithCap` at all — only proves decode succeeded.

**File:** `SeLe4n/Kernel/API.lean` (lines 495, 531, 467)
**Acceptance:** All three theorems compile (zero sorry); `lake build` passes.

#### K-C.7 — Add CSpace delegation theorems

Add four delegation theorems proving each CSpace dispatch path correctly
delegates to the corresponding kernel operation. These theorems establish
that when `dispatchWithCap` succeeds for a CSpace syscall, the underlying
kernel operation was invoked with the correctly decoded arguments:

```lean
/-- K-C: When cspaceMint dispatch succeeds, the kernel-level `cspaceMint`
was invoked with the decoded source slot, destination slot, rights, and
badge from message registers. -/
theorem dispatchWithCap_cspaceMint_delegates
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (cap : Capability) (cnodeId : SeLe4n.ObjId) (args : CSpaceMintArgs)
    (hSyscall : decoded.syscallId = .cspaceMint)
    (hTarget : cap.target = .object cnodeId)
    (hDecode : decodeCSpaceMintArgs decoded = .ok args) :
    dispatchWithCap decoded tid cap =
      let src : CSpaceAddr := { cnode := cnodeId, slot := args.srcSlot }
      let dst : CSpaceAddr := { cnode := cnodeId, slot := args.dstSlot }
      let badge : Option SeLe4n.Badge :=
        if args.badge.val = 0 then none else some args.badge
      cspaceMint src dst args.rights badge
```

Analogous theorems for copy, move, and delete. All proofs are `by simp
[dispatchWithCap, hSyscall, hTarget, hDecode]` — they unfold the dispatch
function and substitute the hypotheses.

**File:** `SeLe4n/Kernel/API.lean`
**Acceptance:** All 4 theorems compile (zero sorry).

#### K-C.8 — Build and smoke verification

Run `lake build` and `./scripts/test_smoke.sh` to confirm:
- Zero compilation errors
- Zero `sorry` or `axiom` in production code
- All Tier 0–2 tests pass
- Existing trace output matches fixture (no dispatch-path changes affect
  trace scenarios since CSpace syscalls were not previously traced)

**Acceptance:** `test_smoke.sh` exits 0.

**Exit criteria:**
- `dispatchWithCap` accepts `SyscallDecodeResult` instead of `SyscallId`.
- All 4 CSpace syscalls fully dispatch to kernel operations via decoded args.
- No `.illegalState` stubs remain for CSpace syscalls.
- `dispatchSyscall` call site updated to pass full `decoded`.
- All 3 existing soundness theorems compile unchanged.
- 4 new delegation theorems proved (one per CSpace syscall).
- `lake build` passes; `test_smoke.sh` passes.
- Zero `sorry`/`axiom` in production proof surface.

**Files modified:**
- `SeLe4n/Kernel/API.lean` — Signature change, 4 CSpace stubs replaced,
  call site update, 4 delegation theorems added.

**Version target:** v0.16.2

---

### WS-K-D — Lifecycle and VSpace Syscall Dispatch

**Goal:** Wire `lifecycleRetype`, `vspaceMap`, `vspaceUnmap` through
`dispatchWithCap` using decoded message register arguments. Replace all 3
remaining `.illegalState` stubs with real dispatch paths that decode per-syscall
arguments from `SyscallDecodeResult.msgRegs` and delegate to the existing
kernel-level lifecycle and VSpace operations.

**Design rationale:**

The three remaining stubs in `dispatchWithCap` (API.lean:438–441) block the
lifecycle and VSpace subsystems from the register-sourced entry point. After
K-C, only 3 of 13 syscalls remain stubbed. This phase eliminates them all.

**Lifecycle retype design challenge:** `lifecycleRetypeObject` (Lifecycle/
Operations.lean:225–242) takes `authority : CSpaceAddr` and internally performs
`cspaceLookupSlot authority st` to resolve the authority capability. However,
in the register-sourced dispatch path, the capability has **already** been
resolved and validated by `syscallInvoke` (with `.retype` right). Re-resolving
via a CSpaceAddr would require information (`tcb.cspaceRoot`, the slot
reference) not available inside `dispatchWithCap`.

**Solution:** Introduce `lifecycleRetypeDirect` — a companion to
`lifecycleRetypeObject` that accepts an already-resolved capability instead of
a CSpaceAddr. It performs the same authority check via
`lifecycleRetypeAuthority` (which verifies `cap.target = .object target` and
`cap.hasRight .write`), the same lifecycle metadata consistency check, and the
same `storeObject` call. This avoids a double capability lookup and keeps the
dispatch layer clean.

**VSpace design:** `vspaceMapPage` and `vspaceUnmapPage` take ASID, vaddr,
paddr, and perms directly — no authority CSpaceAddr needed. The dispatch layer
decodes these from message registers and delegates directly. For user-space
entry, the bounds-checked variant `vspaceMapPageChecked` is used (rejects
`paddr ≥ 2^52`). A `PagePermissions.ofNat` helper decodes the raw permissions
word from the register into the structured `PagePermissions` type using a
bitfield layout (bit 0=read, 1=write, 2=execute, 3=user, 4=cacheable).

**Type tag design:** `objectOfTypeTag` maps a raw `Nat` type tag to a default
`KernelObject` constructor. The tag encoding follows `KernelObjectType` ordinal
order (0=tcb, 1=endpoint, 2=notification, 3=cnode, 4=vspaceRoot, 5=untyped).
Unrecognized tags produce `.invalidTypeTag`. The size hint from the third
message register is used only for untyped objects (as `regionSize`); other
types ignore it. All constructed objects use field defaults (zero ThreadId,
empty slots, idle state, etc.) — the retype operation only creates the identity;
subsequent operations configure the object.

**Subtasks:**

#### K-D.1 — `objectOfTypeTag` helper (Lifecycle/Operations.lean)

Define a total function mapping a raw type tag and size hint to a default
`KernelObject`:
```lean
def objectOfTypeTag (typeTag : Nat) (sizeHint : Nat)
    : Except KernelError KernelObject :=
  match typeTag with
  | 0 => .ok (.tcb {
      tid := ThreadId.ofNat 0
      priority := Priority.ofNat 0
      domain := DomainId.ofNat 0
      cspaceRoot := ObjId.ofNat 0
      vspaceRoot := ObjId.ofNat 0
      ipcBuffer := VAddr.ofNat 0
    })
  | 1 => .ok (.endpoint { sendQ := {}, receiveQ := {} })
  | 2 => .ok (.notification {
      state := .idle, waitingThreads := [], pendingBadge := none
    })
  | 3 => .ok (.cnode {
      depth := 0, guardWidth := 0, guardValue := 0,
      radixWidth := 0, slots := {}
    })
  | 4 => .ok (.vspaceRoot {
      asid := ASID.ofNat 0, mappings := {}
    })
  | 5 => .ok (.untyped {
      regionBase := PAddr.ofNat 0,
      regionSize := sizeHint,
      watermark := 0,
      children := [],
      isDevice := false
    })
  | _ => .error .invalidTypeTag
```

Design notes:
- Returns `Except KernelError KernelObject` — never panics, never partial.
- The size hint is meaningful only for untyped objects (sets `regionSize`).
  Other constructors use field defaults.
- Tag 0–5 correspond to `KernelObjectType` ordinal order. This is a fixed
  convention documented in the function's docstring; changing it requires a
  coordinated update to all user-space stubs.
- The default TCB uses zero-valued typed identifiers. A subsequent
  `setTcbFields` or similar configuration operation would set the real values.
  This matches seL4's pattern where `Untyped_Retype` creates an identity and
  `TCB_Configure` populates it.

Add a corresponding `objectOfTypeTag_type` lemma verifying that successful
results have the expected `KernelObjectType`:
```lean
theorem objectOfTypeTag_type (tag : Nat) (size : Nat) (obj : KernelObject)
    (hOk : objectOfTypeTag tag size = .ok obj) :
    (tag = 0 → obj.objectType = .tcb) ∧
    (tag = 1 → obj.objectType = .endpoint) ∧
    (tag = 2 → obj.objectType = .notification) ∧
    (tag = 3 → obj.objectType = .cnode) ∧
    (tag = 4 → obj.objectType = .vspaceRoot) ∧
    (tag = 5 → obj.objectType = .untyped)
```

Add a determinism theorem (`objectOfTypeTag_deterministic`, trivially `rfl`)
and an error-exclusivity theorem:
```lean
theorem objectOfTypeTag_error_iff (tag : Nat) (size : Nat) :
    (∃ e, objectOfTypeTag tag size = .error e) ↔ tag > 5
```

**File:** `SeLe4n/Kernel/Lifecycle/Operations.lean`
**Acceptance:** All three theorems proved (zero sorry); `lake build` passes.

#### K-D.2 — `PagePermissions.ofNat` helper (Model/Object/Structures.lean)

Define a total decoder mapping a raw `Nat` permissions word to a
`PagePermissions` structure using a bitfield layout:
```lean
def PagePermissions.ofNat (n : Nat) : PagePermissions :=
  { read      := n &&& 1 != 0
    write     := n &&& 2 != 0
    execute   := n &&& 4 != 0
    user      := n &&& 8 != 0
    cacheable := n &&& 16 != 0 }
```

Design notes:
- `ofNat` is total (no error return). Every `Nat` maps to a valid
  `PagePermissions` — W^X enforcement happens downstream in
  `vspaceMapPage` (which checks `perms.wxCompliant`). The decode layer
  does not validate policy; it only converts representation.
- Bit layout matches ARM64 PTE descriptor conventions:
  bit 0 = AP[1] (read), bit 1 = AP[2] (write), bit 2 = UXN (execute),
  bit 3 = user, bit 4 = AttrIndx (cacheable).
- The companion `PagePermissions.toNat` encoder is defined for round-trip
  proofs:
  ```lean
  def PagePermissions.toNat (p : PagePermissions) : Nat :=
    (if p.read then 1 else 0) |||
    (if p.write then 2 else 0) |||
    (if p.execute then 4 else 0) |||
    (if p.user then 8 else 0) |||
    (if p.cacheable then 16 else 0)
  ```

Add a round-trip theorem:
```lean
theorem PagePermissions.ofNat_toNat_roundtrip (p : PagePermissions) :
    PagePermissions.ofNat (PagePermissions.toNat p) = p
```

Add a determinism theorem (`PagePermissions.ofNat_deterministic`, trivially
`rfl`).

**File:** `SeLe4n/Model/Object/Structures.lean`
**Acceptance:** `ofNat`, `toNat`, round-trip, and determinism theorems compile
(zero sorry); `lake build` passes.

#### K-D.3 — `lifecycleRetypeDirect` helper (Lifecycle/Operations.lean)

Define a companion to `lifecycleRetypeObject` that accepts a pre-resolved
capability instead of a `CSpaceAddr`. This is the function called by the
register-sourced dispatch path, where `syscallInvoke` has already resolved
and rights-checked the capability.

```lean
/-- WS-K-D: Retype with a pre-resolved authority capability.
Companion to `lifecycleRetypeObject` for the register-sourced dispatch
path where the authority cap has already been resolved by `syscallInvoke`.

Deterministic branch contract:
1. Target object must exist (`objectNotFound` otherwise).
2. Lifecycle metadata must agree with object-store type (`illegalState`).
3. Authority cap must satisfy `lifecycleRetypeAuthority` — targets the
   object with `.write` right (`illegalAuthority` otherwise).
4. Object store is updated atomically on success via `storeObject`. -/
def lifecycleRetypeDirect
    (authCap : Capability) (target : SeLe4n.ObjId)
    (newObj : KernelObject) : Kernel Unit :=
  fun st =>
    match st.objects[target]? with
    | none => .error .objectNotFound
    | some currentObj =>
        if st.lifecycle.objectTypes[target]? = some currentObj.objectType then
          if lifecycleRetypeAuthority authCap target then
            storeObject target newObj st
          else
            .error .illegalAuthority
        else
          .error .illegalState
```

This is structurally identical to `lifecycleRetypeObject` minus the
`cspaceLookupSlot` step. The authority check (`lifecycleRetypeAuthority`)
verifies `cap.target = .object target ∧ cap.hasRight .write`, ensuring the
resolved capability actually authorizes the retype.

Add an equivalence theorem linking the two functions:
```lean
/-- When `cspaceLookupSlot authority st` resolves to `(cap, st)` (state
unchanged), `lifecycleRetypeDirect` with that cap equals
`lifecycleRetypeObject` with the authority address. -/
theorem lifecycleRetypeDirect_eq_lifecycleRetypeObject
    (authority : CSpaceAddr) (authCap : Capability)
    (target : SeLe4n.ObjId) (newObj : KernelObject) (st : SystemState)
    (hLookup : cspaceLookupSlot authority st = .ok (authCap, st)) :
    lifecycleRetypeDirect authCap target newObj st =
    lifecycleRetypeObject authority target newObj st
```

This theorem proves the dispatch path is semantically equivalent to the
`apiLifecycleRetype` path — they perform the same operation on the same
state, just with different cap resolution strategies.

Add determinism theorem (`lifecycleRetypeDirect_deterministic`, trivially
`rfl`) and error-decomposition theorems:
```lean
theorem lifecycleRetypeDirect_error_objectNotFound
    (cap : Capability) (target : SeLe4n.ObjId) (newObj : KernelObject)
    (st : SystemState)
    (hNone : st.objects[target]? = none) :
    lifecycleRetypeDirect cap target newObj st = .error .objectNotFound

theorem lifecycleRetypeDirect_error_illegalState
    (cap : Capability) (target : SeLe4n.ObjId) (newObj : KernelObject)
    (st : SystemState) (currentObj : KernelObject)
    (hSome : st.objects[target]? = some currentObj)
    (hMeta : st.lifecycle.objectTypes[target]? ≠ some currentObj.objectType) :
    lifecycleRetypeDirect cap target newObj st = .error .illegalState

theorem lifecycleRetypeDirect_error_illegalAuthority
    (cap : Capability) (target : SeLe4n.ObjId) (newObj : KernelObject)
    (st : SystemState) (currentObj : KernelObject)
    (hSome : st.objects[target]? = some currentObj)
    (hMeta : st.lifecycle.objectTypes[target]? = some currentObj.objectType)
    (hNoAuth : lifecycleRetypeAuthority cap target = false) :
    lifecycleRetypeDirect cap target newObj st = .error .illegalAuthority
```

**File:** `SeLe4n/Kernel/Lifecycle/Operations.lean`
**Acceptance:** Function and all theorems compile (zero sorry); `lake build`
passes.

#### K-D.4 — Wire `.lifecycleRetype` dispatch (API.lean)

Replace the `.lifecycleRetype` stub (currently `fun _ => .error .illegalState`)
with a full dispatch path:
```lean
| .lifecycleRetype =>
    match cap.target with
    | .object _ =>
        fun st => match decodeLifecycleRetypeArgs decoded with
        | .error e => .error e
        | .ok args =>
            match objectOfTypeTag args.newType args.size with
            | .error e => .error e
            | .ok newObj =>
                lifecycleRetypeDirect cap args.targetObj newObj st
    | _ => fun _ => .error .invalidCapability
```

The dispatch flow:
1. Cap target must be `.object _` (the cap targets the authority object).
2. Decode `LifecycleRetypeArgs` from message registers (target ObjId,
   type tag, size hint). Decode failure → error propagation.
3. Convert type tag + size to a `KernelObject` via `objectOfTypeTag`.
   Invalid tag → `.invalidTypeTag`.
4. Delegate to `lifecycleRetypeDirect` with the resolved cap, decoded
   target, and constructed new object.

Note: `lifecycleRetypeAuthority` inside `lifecycleRetypeDirect` checks that
`cap.target = .object args.targetObj` — the cap must target the specific
object being retyped. If the user passes a target ObjId that doesn't match
the invoked capability's target, the authority check fails with
`.illegalAuthority`. This prevents a user from retyping arbitrary objects
by invoking a capability targeting a different object.

**File:** `SeLe4n/Kernel/API.lean` (line ~438)
**Acceptance:** `lake build` passes; `.lifecycleRetype` no longer returns
`.illegalState`.

#### K-D.5 — Wire `.vspaceMap` dispatch (API.lean)

Replace the `.vspaceMap` stub with a full dispatch path:
```lean
| .vspaceMap =>
    match cap.target with
    | .object _ =>
        fun st => match decodeVSpaceMapArgs decoded with
        | .error e => .error e
        | .ok args =>
            Architecture.vspaceMapPageChecked args.asid args.vaddr args.paddr
              (PagePermissions.ofNat args.perms) st
    | _ => fun _ => .error .invalidCapability
```

Design notes:
- Uses `vspaceMapPageChecked` (not `vspaceMapPage`) because this is a
  user-space entry point. The checked variant rejects `paddr ≥ 2^52`,
  preventing user-space from mapping physical addresses outside the valid
  address space. This matches the production entry point classification in
  `VSpace.lean:57–62`.
- `PagePermissions.ofNat args.perms` converts the raw register value to
  structured permissions. W^X enforcement happens inside `vspaceMapPage`
  (which checks `perms.wxCompliant`), not at the decode boundary.
- The ASID from `args.asid` is used by `resolveAsidRoot` inside
  `vspaceMapPage` to locate the VSpace root. If the ASID is not bound,
  `vspaceMapPage` returns `.asidNotBound`.

**File:** `SeLe4n/Kernel/API.lean` (line ~440)
**Acceptance:** `lake build` passes; `.vspaceMap` no longer returns
`.illegalState`.

#### K-D.6 — Wire `.vspaceUnmap` dispatch (API.lean)

Replace the `.vspaceUnmap` stub with a full dispatch path:
```lean
| .vspaceUnmap =>
    match cap.target with
    | .object _ =>
        fun st => match decodeVSpaceUnmapArgs decoded with
        | .error e => .error e
        | .ok args =>
            Architecture.vspaceUnmapPage args.asid args.vaddr st
    | _ => fun _ => .error .invalidCapability
```

Design notes:
- `vspaceUnmapPage` needs only ASID and vaddr — no permissions or physical
  address needed for unmap.
- No bounds check needed (unlike map) — unmap operates on an existing
  mapping, and the ASID/vaddr are validated against the ASID table and
  mapping store.
- On `none` from `unmapPage` (no mapping exists), returns
  `.translationFault` — matching the deterministic error contract.

**File:** `SeLe4n/Kernel/API.lean` (line ~441)
**Acceptance:** `lake build` passes; `.vspaceUnmap` no longer returns
`.illegalState`. Zero `.illegalState` stubs remain in `dispatchWithCap`.

#### K-D.7 — Verify existing soundness theorems compile unchanged

After K-D.4–K-D.6, verify that all existing soundness theorems still compile
without modification:

1. **`dispatchSyscall_requires_right`** (API.lean:536): The proof calls
   `syscallInvoke_requires_right` with `dispatchWithCap decoded tid`.
   Since `syscallInvoke_requires_right` quantifies over any
   `op : Capability → Kernel α`, the proof composes regardless of
   `dispatchWithCap`'s internal changes.

2. **`syscallEntry_implies_capability_held`** (API.lean:572): Threads
   through `dispatchSyscall_requires_right`. No direct reference to
   `dispatchWithCap`.

3. **`syscallEntry_requires_valid_decode`** (API.lean:508): Does not
   reference `dispatchWithCap` at all.

4. **CSpace delegation theorems** (API.lean:627–684): These reference
   specific `decoded.syscallId` matches (`.cspaceMint`, etc.) and are
   unaffected by changes to the `.lifecycleRetype`/`.vspaceMap`/
   `.vspaceUnmap` arms.

**File:** `SeLe4n/Kernel/API.lean`
**Acceptance:** All existing theorems compile (zero sorry); no proof
modifications needed.

#### K-D.8 — Add lifecycle and VSpace delegation theorems (API.lean)

Add three delegation theorems proving each new dispatch path correctly
delegates to the corresponding kernel operation:

```lean
/-- WS-K-D: When lifecycleRetype dispatch succeeds, `lifecycleRetypeDirect`
is invoked with the resolved cap, decoded target, and constructed object. -/
theorem dispatchWithCap_lifecycleRetype_delegates
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (cap : Capability) (objId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.LifecycleRetypeArgs)
    (newObj : KernelObject)
    (hSyscall : decoded.syscallId = .lifecycleRetype)
    (hTarget : cap.target = .object objId)
    (hDecode : decodeLifecycleRetypeArgs decoded = .ok args)
    (hType : objectOfTypeTag args.newType args.size = .ok newObj) :
    dispatchWithCap decoded tid cap =
      lifecycleRetypeDirect cap args.targetObj newObj
```

```lean
/-- WS-K-D: When vspaceMap dispatch succeeds, `vspaceMapPageChecked` is
invoked with the decoded ASID, vaddr, paddr, and permissions. -/
theorem dispatchWithCap_vspaceMap_delegates
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (cap : Capability) (objId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.VSpaceMapArgs)
    (hSyscall : decoded.syscallId = .vspaceMap)
    (hTarget : cap.target = .object objId)
    (hDecode : decodeVSpaceMapArgs decoded = .ok args) :
    dispatchWithCap decoded tid cap =
      Architecture.vspaceMapPageChecked args.asid args.vaddr args.paddr
        (PagePermissions.ofNat args.perms)
```

```lean
/-- WS-K-D: When vspaceUnmap dispatch succeeds, `vspaceUnmapPage` is
invoked with the decoded ASID and vaddr. -/
theorem dispatchWithCap_vspaceUnmap_delegates
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (cap : Capability) (objId : SeLe4n.ObjId)
    (args : Architecture.SyscallArgDecode.VSpaceUnmapArgs)
    (hSyscall : decoded.syscallId = .vspaceUnmap)
    (hTarget : cap.target = .object objId)
    (hDecode : decodeVSpaceUnmapArgs decoded = .ok args) :
    dispatchWithCap decoded tid cap =
      Architecture.vspaceUnmapPage args.asid args.vaddr
```

All proofs are `by simp [dispatchWithCap, hSyscall, hTarget, hDecode, ...]`
— they unfold the dispatch function and substitute the hypotheses. The
lifecycle theorem additionally substitutes `hType` to resolve the
`objectOfTypeTag` match.

**File:** `SeLe4n/Kernel/API.lean`
**Acceptance:** All 3 theorems compile (zero sorry).

#### K-D.9 — Add Tier 3 invariant surface anchors

Add `#check` anchors to `tests/InvariantSurfaceSuite.lean` for all new
definitions and theorems:
- `objectOfTypeTag`
- `objectOfTypeTag_type`
- `objectOfTypeTag_error_iff`
- `PagePermissions.ofNat`
- `PagePermissions.toNat`
- `PagePermissions.ofNat_toNat_roundtrip`
- `lifecycleRetypeDirect`
- `lifecycleRetypeDirect_eq_lifecycleRetypeObject`
- `dispatchWithCap_lifecycleRetype_delegates`
- `dispatchWithCap_vspaceMap_delegates`
- `dispatchWithCap_vspaceUnmap_delegates`

**File:** `tests/InvariantSurfaceSuite.lean`
**Acceptance:** All `#check` anchors compile.

#### K-D.10 — Build and smoke verification

Run `lake build` and `./scripts/test_smoke.sh` to confirm:
- Zero compilation errors
- Zero `sorry` or `axiom` in production code
- All Tier 0–2 tests pass
- Existing trace output matches fixture (no dispatch-path changes affect
  trace scenarios since lifecycle/VSpace syscalls were not previously
  traced)

**Acceptance:** `test_smoke.sh` exits 0.

**Exit criteria:**
- `objectOfTypeTag` defined in `Lifecycle/Operations.lean` with type, error,
  and determinism theorems.
- `PagePermissions.ofNat` and `PagePermissions.toNat` defined in
  `Model/Object/Structures.lean` with round-trip theorem.
- `lifecycleRetypeDirect` defined in `Lifecycle/Operations.lean` with
  equivalence, error-decomposition, and determinism theorems.
- All 3 stubs replaced with full dispatch in `dispatchWithCap`.
- Zero `.illegalState` stubs remaining in `dispatchWithCap`.
- 3 delegation theorems proved (one per syscall).
- All existing soundness theorems compile unchanged.
- Tier 3 anchors added for all new definitions.
- `lake build` passes; `test_smoke.sh` passes.
- Zero `sorry`/`axiom` in production proof surface.

**Files modified:**
- `SeLe4n/Model/Object/Structures.lean` — Add `PagePermissions.ofNat`,
  `PagePermissions.toNat`, round-trip theorem.
- `SeLe4n/Kernel/Lifecycle/Operations.lean` — Add `objectOfTypeTag` with
  theorems, `lifecycleRetypeDirect` with equivalence and error theorems.
- `SeLe4n/Kernel/API.lean` — Replace 3 `.illegalState` stubs with full
  dispatch paths, add 3 delegation theorems.
- `tests/InvariantSurfaceSuite.lean` — Add Tier 3 anchors.

**Version target:** v0.16.3

---

### WS-K-E — Service Policy and IPC Message Population

**Goal:** Replace `(fun _ => true)` service policy stubs with
configuration-sourced predicates. Populate IPC message bodies from decoded
message registers. This phase closes the two remaining dispatch-layer gaps
identified in audit findings §2.3 (service policy stubs) and §2.4 (empty
IPC message bodies).

**Design rationale:**

After K-D, all 13 syscalls dispatch to real kernel operations. Two
quality-of-implementation gaps remain:

1. **Service policy stubs.** The `.serviceStart` and `.serviceStop` dispatch
   arms pass `(fun _ => true)` as the `ServicePolicy` argument. Any thread
   with a capability to the service object can start/stop it unconditionally.
   The fix introduces a `ServiceConfig` record in `SystemState` that carries
   configurable `allowStart`/`allowStop` predicates. The dispatch layer reads
   the policy from state, making the gate auditable and testable.

2. **Empty IPC message bodies.** The `.send`, `.call`, and `.reply` dispatch
   arms construct `IpcMessage` with `registers := #[]`, discarding the message
   register values that `decodeSyscallArgs` already captured into
   `decoded.msgRegs`. The fix introduces `extractMessageRegisters` to convert
   `Array RegValue` to `Array Nat` (matching `IpcMessage.registers : Array Nat`)
   and populate the message body.

**Key type observation:** `IpcMessage.registers` is `Array Nat`, not
`Array RegValue`. The `extractMessageRegisters` function must convert via
`RegValue.val` (the `.val` projection on the `RegValue` wrapper structure).
This conversion is a no-op in the abstract model (both carry `Nat` payloads)
but is type-correct and explicit.

**Inline vs. IPC buffer registers:** On ARM64, only 4 inline message registers
(x2–x5) are available at the register-decode level. The `MessageInfo.length`
field can encode up to 120, but the register-decode layer only captures the
inline subset. `extractMessageRegisters` extracts `min info.length msgRegs.size`
values, bounded above by `maxMessageRegisters`. The full 120-register IPC buffer
transport is a future-workstream concern (shared-memory IPC buffer reads).

**Subtasks:**

#### K-E.1 — ServiceConfig structure (Model/State.lean)

Define the service policy configuration record above the `SystemState`
structure:
```lean
/-- Configuration record holding policy predicates for service operations.
    The dispatch layer reads these from `SystemState.serviceConfig` to gate
    `serviceStart` and `serviceStop` transitions.
    `Inhabited` default is `(fun _ => true)` — all operations allowed. -/
structure ServiceConfig where
  allowStart : ServicePolicy
  allowStop  : ServicePolicy

instance : Inhabited ServiceConfig where
  default := { allowStart := fun _ => true, allowStop := fun _ => true }
```

Design notes:
- `ServicePolicy` is `ServiceGraphEntry → Bool` (defined in
  `Service/Operations.lean:40`). The `ServiceConfig` fields use this same
  type, maintaining consistency with `serviceStart`/`serviceStop` signatures.
- The `Inhabited` instance provides permissive defaults (`fun _ => true`),
  ensuring all existing `SystemState` construction sites (which use `default`)
  continue to work unchanged. This is the same backward-compatibility strategy
  used for `objectIndexSet` and `asidTable` (both default to `{}`).
- `ServiceConfig` does not derive `DecidableEq` or `Repr` because function
  fields (`ServicePolicy`) are not decidably comparable. The `Inhabited`
  instance is sufficient for the testing and default-construction use cases.

**File:** `SeLe4n/Model/State.lean` (before `SystemState` definition)
**Acceptance:** `lake build` passes; `ServiceConfig` has `Inhabited` instance.

#### K-E.2 — SystemState extension (Model/State.lean)

Add `serviceConfig : ServiceConfig := default` field to `SystemState`. The
default value ensures all existing construction sites compile unchanged —
`BootstrapBuilder.build`, `Inhabited SystemState`, and direct struct literals
in test files all omit the new field and get the permissive default.

```lean
structure SystemState where
  ...
  services : Std.HashMap ServiceId ServiceGraphEntry
  serviceConfig : ServiceConfig := default    -- NEW
  scheduler : SchedulerState
  ...
```

Place the field immediately after `services` for logical grouping — service
entries and service configuration belong together.

**File:** `SeLe4n/Model/State.lean` (line ~135)
**Acceptance:** `lake build` passes; all existing `SystemState` construction
sites compile unchanged.

#### K-E.3 — extractMessageRegisters helper (RegisterDecode.lean)

Define the message register extraction function that converts `Array RegValue`
to `Array Nat` (matching `IpcMessage.registers : Array Nat`) and bounds-limits
the result:
```lean
/-- Extract message register values for IPC message population.
    Converts `RegValue` wrappers to raw `Nat` values and limits the result
    to `min info.length (min maxMessageRegisters msgRegs.size)` entries.

    The length is bounded three ways:
    1. `info.length` — the sender's declared message length.
    2. `maxMessageRegisters` (120) — the seL4 protocol maximum.
    3. `msgRegs.size` — the platform's inline register count (4 on ARM64).

    Returns `Array Nat` to match `IpcMessage.registers : Array Nat`. -/
@[inline] def extractMessageRegisters (msgRegs : Array RegValue)
    (info : MessageInfo) : Array Nat :=
  let count := min info.length (min maxMessageRegisters msgRegs.size)
  (msgRegs.extract 0 count).map RegValue.val
```

Design notes:
- `Array.extract 0 count` takes the first `count` elements, or fewer if the
  array is shorter (extract is total and clamps silently).
- `.map RegValue.val` converts each `RegValue` to its underlying `Nat`.
- The function is pure and total — no `Except`, no state access.
- `@[inline]` matches the existing encode/decode helper convention.

**File:** `SeLe4n/Kernel/Architecture/RegisterDecode.lean` (after `encodeMsgRegs`)
**Acceptance:** Function compiles; `lake build` passes.

#### K-E.4 — extractMessageRegisters_length lemma (RegisterDecode.lean)

Prove that the extracted array's size is bounded by `maxMessageRegisters`:
```lean
/-- The extracted message register array has at most `maxMessageRegisters`
    entries. This guarantees `IpcMessage.bounded` for the registers component
    when the message is constructed from the extraction result. -/
theorem extractMessageRegisters_length (msgRegs : Array RegValue)
    (info : MessageInfo) :
    (extractMessageRegisters msgRegs info).size ≤ maxMessageRegisters
```

Proof strategy: unfold `extractMessageRegisters`, use `Array.size_map` and
`Array.size_extract` to reduce to `min info.length (min maxMessageRegisters
msgRegs.size) ≤ maxMessageRegisters`, which follows from `Nat.min_le_right`.

**File:** `SeLe4n/Kernel/Architecture/RegisterDecode.lean`
**Acceptance:** Theorem proved (zero sorry).

#### K-E.5 — extractMessageRegisters_bounded lemma (RegisterDecode.lean)

Prove that an `IpcMessage` constructed from `extractMessageRegisters` output
satisfies the IPC bounded predicate (registers ≤ 120, caps = 0 ≤ 3):
```lean
/-- An IpcMessage constructed from extracted registers with empty caps
    satisfies `IpcMessage.bounded`. -/
theorem extractMessageRegisters_ipc_bounded (msgRegs : Array RegValue)
    (info : MessageInfo) (badge : Option SeLe4n.Badge) :
    IpcMessage.bounded {
      registers := extractMessageRegisters msgRegs info,
      caps := #[],
      badge := badge }
```

This composes `extractMessageRegisters_length` with `IpcMessage.empty_bounded`
for the caps component.

**File:** `SeLe4n/Kernel/Architecture/RegisterDecode.lean`
**Acceptance:** Theorem proved (zero sorry).

#### K-E.6 — extractMessageRegisters_deterministic theorem (RegisterDecode.lean)

State the determinism theorem for `extractMessageRegisters`. Since the function
is pure, this is trivially `rfl`:
```lean
theorem extractMessageRegisters_deterministic (msgRegs : Array RegValue)
    (info : MessageInfo) :
    extractMessageRegisters msgRegs info =
    extractMessageRegisters msgRegs info := rfl
```

**File:** `SeLe4n/Kernel/Architecture/RegisterDecode.lean`
**Acceptance:** Theorem compiles (zero sorry).

#### K-E.7 — Update `.serviceStart` dispatch (API.lean)

Replace the `(fun _ => true)` policy stub with a state-sourced policy
read from `st.serviceConfig.allowStart`:
```lean
| .serviceStart =>
    match cap.target with
    | .object objId =>
        fun st => serviceStart (ServiceId.ofNat objId.toNat)
                    st.serviceConfig.allowStart st
    | _ => fun _ => .error .invalidCapability
```

The key change is replacing the inline `(fun _ => true)` lambda with
`st.serviceConfig.allowStart`. Since `serviceStart` takes `ServicePolicy`
(which is `ServiceGraphEntry → Bool`) as its second argument, and
`st.serviceConfig.allowStart` has exactly that type, the substitution is
type-correct. The `st` at the end is the `Kernel` state argument
(the `fun st =>` lambda feeds it to `serviceStart`).

**Design note:** The `st` in `st.serviceConfig.allowStart` and the `st` passed
to `serviceStart` are the **same** state — the dispatch reads the policy from
the current state, then passes the same state to the kernel operation. This is
important: the policy is evaluated against the current state, not a stale one.

**File:** `SeLe4n/Kernel/API.lean` (line ~473–477)
**Acceptance:** `lake build` passes; `.serviceStart` uses config policy.

#### K-E.8 — Update `.serviceStop` dispatch (API.lean)

Analogous replacement for `.serviceStop`:
```lean
| .serviceStop =>
    match cap.target with
    | .object objId =>
        fun st => serviceStop (ServiceId.ofNat objId.toNat)
                    st.serviceConfig.allowStop st
    | _ => fun _ => .error .invalidCapability
```

**File:** `SeLe4n/Kernel/API.lean` (line ~478–482)
**Acceptance:** `lake build` passes; `.serviceStop` uses config policy.

#### K-E.9 — Update `.send` IPC dispatch (API.lean)

Populate the IPC message body from decoded message registers:
```lean
| .send =>
    match cap.target with
    | .object epId =>
        let body := extractMessageRegisters decoded.msgRegs decoded.msgInfo
        endpointSendDual epId tid { registers := body, caps := #[], badge := cap.badge }
    | _ => fun _ => .error .invalidCapability
```

The `extractMessageRegisters` call converts `decoded.msgRegs : Array RegValue`
to `Array Nat` and caps the length. The `body` replaces the previous `#[]`.

**File:** `SeLe4n/Kernel/API.lean` (line ~375–379)
**Acceptance:** `lake build` passes; `.send` populates message body.

#### K-E.10 — Update `.call` IPC dispatch (API.lean)

Populate the IPC message body for `.call`:
```lean
| .call =>
    match cap.target with
    | .object epId =>
        let body := extractMessageRegisters decoded.msgRegs decoded.msgInfo
        endpointCall epId tid { registers := body, caps := #[], badge := cap.badge }
    | _ => fun _ => .error .invalidCapability
```

**File:** `SeLe4n/Kernel/API.lean` (line ~387–391)
**Acceptance:** `lake build` passes; `.call` populates message body.

#### K-E.11 — Update `.reply` IPC dispatch (API.lean)

Populate the IPC message body for `.reply`:
```lean
| .reply =>
    match cap.target with
    | .replyCap targetTid =>
        let body := extractMessageRegisters decoded.msgRegs decoded.msgInfo
        endpointReply tid targetTid { registers := body, caps := #[], badge := cap.badge }
    | _ => fun _ => .error .invalidCapability
```

**File:** `SeLe4n/Kernel/API.lean` (line ~392–396)
**Acceptance:** `lake build` passes; `.reply` populates message body.

#### K-E.12 — Service dispatch delegation theorems (API.lean)

Add two delegation theorems proving service dispatch correctly reads
policy from `SystemState.serviceConfig`:

```lean
/-- K-E: When serviceStart dispatch is invoked, the policy is sourced from
`st.serviceConfig.allowStart`. -/
theorem dispatchWithCap_serviceStart_uses_config
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (cap : Capability) (objId : SeLe4n.ObjId)
    (hSyscall : decoded.syscallId = .serviceStart)
    (hTarget : cap.target = .object objId) :
    dispatchWithCap decoded tid cap =
      fun st => serviceStart (ServiceId.ofNat objId.toNat)
                  st.serviceConfig.allowStart st

/-- K-E: When serviceStop dispatch is invoked, the policy is sourced from
`st.serviceConfig.allowStop`. -/
theorem dispatchWithCap_serviceStop_uses_config
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (cap : Capability) (objId : SeLe4n.ObjId)
    (hSyscall : decoded.syscallId = .serviceStop)
    (hTarget : cap.target = .object objId) :
    dispatchWithCap decoded tid cap =
      fun st => serviceStop (ServiceId.ofNat objId.toNat)
                  st.serviceConfig.allowStop st
```

All proofs are `by simp [dispatchWithCap, hSyscall, hTarget]`.

**File:** `SeLe4n/Kernel/API.lean`
**Acceptance:** Both theorems compile (zero sorry).

#### K-E.13 — IPC message population delegation theorems (API.lean)

Add three delegation theorems proving IPC dispatch populates message bodies:

```lean
/-- K-E: When send dispatch is invoked, the IPC message body is populated
from decoded message registers via `extractMessageRegisters`. -/
theorem dispatchWithCap_send_populates_msg
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (cap : Capability) (epId : SeLe4n.ObjId)
    (hSyscall : decoded.syscallId = .send)
    (hTarget : cap.target = .object epId) :
    dispatchWithCap decoded tid cap =
      let body := extractMessageRegisters decoded.msgRegs decoded.msgInfo
      endpointSendDual epId tid { registers := body, caps := #[], badge := cap.badge }
```

Analogous theorems for `.call` and `.reply` (`.reply` matches on
`.replyCap targetTid`).

All proofs are `by simp [dispatchWithCap, hSyscall, hTarget]`.

**File:** `SeLe4n/Kernel/API.lean`
**Acceptance:** All 3 theorems compile (zero sorry).

#### K-E.14 — Verify existing soundness theorems compile unchanged

After K-E.7–K-E.13, verify that all existing soundness theorems still compile
without modification:

1. **`dispatchSyscall_requires_right`**: The proof calls
   `syscallInvoke_requires_right` with `dispatchWithCap decoded tid`. Since
   `syscallInvoke_requires_right` quantifies over any `op : Capability →
   Kernel α`, the proof composes regardless of `dispatchWithCap`'s internal
   changes to service and IPC arms.

2. **`syscallEntry_implies_capability_held`**: Threads through
   `dispatchSyscall_requires_right`. No direct reference to `dispatchWithCap`.

3. **`syscallEntry_requires_valid_decode`**: Does not reference
   `dispatchWithCap` at all.

4. **CSpace and lifecycle/VSpace delegation theorems** (K-C, K-D): These
   reference specific `decoded.syscallId` matches (`.cspaceMint`, etc.) and
   are unaffected by changes to the `.serviceStart`/`.serviceStop`/IPC arms.

**File:** `SeLe4n/Kernel/API.lean`
**Acceptance:** All existing theorems compile (zero sorry); no proof
modifications needed.

#### K-E.15 — StateBuilder and fixture updates

Verify that `BootstrapBuilder.build` compiles unchanged. The new
`serviceConfig` field has a default value (`default`), so `build` — which
constructs `SystemState` with struct literal syntax omitting `serviceConfig` —
picks up the default automatically.

For test scenarios that need non-default policies (K-G), add a builder
combinator:
```lean
def withServiceConfig (builder : BootstrapBuilder) (config : ServiceConfig)
    : BootstrapBuilder :=
  { builder with serviceConfig := config }
```

This requires adding `serviceConfig : ServiceConfig := default` to
`BootstrapBuilder` and threading it through `build`.

**Files:**
- `SeLe4n/Testing/StateBuilder.lean` — Add `serviceConfig` field and combinator.
**Acceptance:** `lake build` passes; existing tests compile unchanged.

#### K-E.16 — Tier 3 invariant surface anchors

Add `#check` anchors to `tests/InvariantSurfaceSuite.lean` for all new
definitions and theorems:
- `ServiceConfig`
- `extractMessageRegisters`
- `extractMessageRegisters_length`
- `extractMessageRegisters_bounded` (the `_ipc_bounded` variant)
- `extractMessageRegisters_deterministic`
- `dispatchWithCap_serviceStart_uses_config`
- `dispatchWithCap_serviceStop_uses_config`
- `dispatchWithCap_send_populates_msg`
- `dispatchWithCap_call_populates_msg`
- `dispatchWithCap_reply_populates_msg`

**File:** `tests/InvariantSurfaceSuite.lean`
**Acceptance:** All `#check` anchors compile.

#### K-E.17 — Build and smoke verification

Run `lake build` and `./scripts/test_smoke.sh` to confirm:
- Zero compilation errors
- Zero `sorry` or `axiom` in production code
- All Tier 0–2 tests pass
- Trace fixture still matches (IPC trace scenarios will now show populated
  message bodies — fixture must be updated if trace output changes)

**Acceptance:** `test_smoke.sh` exits 0.

**Exit criteria:**
- `ServiceConfig` structure defined with `Inhabited` default in `Model/State.lean`.
- `SystemState` includes `serviceConfig : ServiceConfig := default` field.
- `extractMessageRegisters` converts `Array RegValue` → `Array Nat` with triple
  bound (`info.length`, `maxMessageRegisters`, `msgRegs.size`).
- `extractMessageRegisters_length` lemma: result size ≤ `maxMessageRegisters`.
- `extractMessageRegisters_ipc_bounded` lemma: constructed `IpcMessage` is bounded.
- `extractMessageRegisters_deterministic` theorem proved (trivially `rfl`).
- `.serviceStart`/`.serviceStop` dispatch reads policy from `st.serviceConfig`.
- `.send`/`.call`/`.reply` dispatch populates message body from decoded registers.
- No `(fun _ => true)` policy stubs remain in `dispatchWithCap`.
- No `registers := #[]` in IPC dispatch arms (replaced with extracted registers).
- 2 service delegation theorems proved.
- 3 IPC message population delegation theorems proved.
- All existing soundness theorems compile unchanged.
- `BootstrapBuilder` extended with `serviceConfig` field and `withServiceConfig`
  combinator.
- Tier 3 anchors added for all new definitions and theorems.
- `lake build` passes; `test_smoke.sh` passes.
- Zero `sorry`/`axiom` in production proof surface.

**Files modified:**
- `SeLe4n/Model/State.lean` — Add `ServiceConfig`, extend `SystemState`.
- `SeLe4n/Kernel/API.lean` — Replace service stubs, populate IPC messages,
  add 5 delegation theorems.
- `SeLe4n/Kernel/Architecture/RegisterDecode.lean` — Add
  `extractMessageRegisters` with length, bounded, and determinism theorems.
- `SeLe4n/Testing/StateBuilder.lean` — Add `serviceConfig` field and
  `withServiceConfig` combinator to `BootstrapBuilder`.
- `tests/InvariantSurfaceSuite.lean` — Add Tier 3 anchors.

**Version target:** v0.16.4

---

### WS-K-F — Proofs: Round-Trip, Preservation, and NI Integration

**Goal:** Prove round-trip correctness for all new decode paths, verify
preservation of the proof-layer invariant bundle across new dispatch paths,
complete remaining NI lifecycle proofs, and confirm full NI coverage.

WS-K-F is subdivided into six granular sub-phases. Each sub-phase is an
independently committable unit that builds on the previous phase and can be
validated in isolation via `lake build`.

---

#### K-F1 — Encode Functions for All 7 Argument Structures

**Scope:** Define canonical encode functions that invert the Layer 2 decode
functions. These are the encode-side of the round-trip contract.

**Tasks:**
1. Define `encodeCSpaceMintArgs : CSpaceMintArgs → Array RegValue`:
   maps `srcSlot`, `dstSlot`, `rights`, `badge` fields to a 4-element
   `RegValue` array via `.toNat` / `.val`.
2. Define `encodeCSpaceCopyArgs : CSpaceCopyArgs → Array RegValue`:
   maps `srcSlot`, `dstSlot` to a 2-element array.
3. Define `encodeCSpaceMoveArgs : CSpaceMoveArgs → Array RegValue`:
   maps `srcSlot`, `dstSlot` to a 2-element array.
4. Define `encodeCSpaceDeleteArgs : CSpaceDeleteArgs → Array RegValue`:
   maps `targetSlot` to a 1-element array.
5. Define `encodeLifecycleRetypeArgs : LifecycleRetypeArgs → Array RegValue`:
   maps `targetObj`, `newType`, `size` to a 3-element array.
6. Define `encodeVSpaceMapArgs : VSpaceMapArgs → Array RegValue`:
   maps `asid`, `vaddr`, `paddr`, `perms` to a 4-element array.
7. Define `encodeVSpaceUnmapArgs : VSpaceUnmapArgs → Array RegValue`:
   maps `asid`, `vaddr` to a 2-element array.

**Pattern:** Each encode function constructs `#[⟨field₁.toNat⟩, ⟨field₂.toNat⟩, ...]`
mirroring the decode function's `requireMsgReg` index order. The encode is pure,
deterministic, and requires no imports beyond `Model.State`.

**File modified:** `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean`

---

#### K-F2 — Round-Trip Proofs for All 7 Argument Structures

**Scope:** Prove that encoding then decoding each argument structure recovers
the original, anchoring the Layer 2 decode contract.

**Tasks:**
1. `decodeCSpaceMintArgs_roundtrip`: for any `args : CSpaceMintArgs`,
   `decodeCSpaceMintArgs ⟨encodeCSpaceMintArgs args, ...⟩ = .ok args`.
   Proof: unfold encode/decode, apply `Slot.ofNat_toNat`, `Badge.ofNat_toNat`,
   and `AccessRightSet` field identity.
2. `decodeCSpaceCopyArgs_roundtrip`: analogous, using `Slot.ofNat_toNat`.
3. `decodeCSpaceMoveArgs_roundtrip`: analogous, using `Slot.ofNat_toNat`.
4. `decodeCSpaceDeleteArgs_roundtrip`: analogous, single-field.
5. `decodeLifecycleRetypeArgs_roundtrip`: using `ObjId.ofNat_toNat`.
6. `decodeVSpaceMapArgs_roundtrip`: using `ASID.ofNat_toNat`, `VAddr.ofNat_toNat`,
   `PAddr.ofNat_toNat`.
7. `decodeVSpaceUnmapArgs_roundtrip`: using `ASID.ofNat_toNat`, `VAddr.ofNat_toNat`.
8. `decode_layer2_roundtrip_all`: composed conjunction theorem stating all 7
   round-trips hold simultaneously (parallel to `decode_components_roundtrip`
   in `RegisterDecode.lean`).

**Proof pattern:** Each theorem creates a `SyscallDecodeResult` stub with
`msgRegs := encodeXxxArgs args` and proves the decode returns `.ok args`.
The key lemma chain is: `requireMsgReg` unfolds to array indexing → the
`#[...]` literal has known size → `simp` resolves the index → `ofNat_toNat`
collapses the wrapper → structure eta gives `args`.

**File modified:** `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean`

---

#### K-F3 — Extraction Round-Trip Proof

**Scope:** Prove that encoding message register values into an array and
extracting them via `extractMessageRegisters` recovers the originals,
completing the Layer 1 extraction contract.

**Tasks:**
1. `extractMessageRegisters_roundtrip`: for an array `vals` and a
   `MessageInfo` with `length = vals.size` and `length ≤ maxMessageRegisters`,
   `extractMessageRegisters vals info = vals`.
   Proof: unfold `extractMessageRegisters`, show that `Array.extract` with
   `min(info.length, maxMessageRegisters)` = `vals.size` returns the full
   array, then `Array.map id` = identity.

**File modified:** `SeLe4n/Kernel/Architecture/RegisterDecode.lean`

---

#### K-F4 — Dispatch-Level Invariant Preservation

**Scope:** Prove that `dispatchWithCap` preserves `proofLayerInvariantBundle`
by composing per-operation preservation theorems.

**Tasks:**
1. Verify that each dispatch arm in `dispatchWithCap` (API.lean:372–493)
   delegates to an operation whose preservation theorem already exists:
   - CSpace mint/copy/move/delete: existing theorems in
     `Capability/Invariant/Preservation.lean`.
   - Lifecycle retype: existing theorem in `Lifecycle/Invariant.lean`.
   - VSpace map/unmap: existing theorem in `Architecture/VSpaceInvariant.lean`.
   - Service start/stop: existing theorems in `Service/Invariant/Policy.lean`.
   - IPC send/call/reply/recv: existing theorems in
     `IPC/Invariant/EndpointPreservation.lean`.
2. Add `dispatchWithCap_decode_pure` theorem: Layer 2 decode functions do not
   modify state (they operate on the `SyscallDecodeResult` value, not
   `SystemState`). Therefore, the only state-modifying operation is the
   delegated kernel call.
3. Add `dispatchWithCap_preserves_bundle` theorem: for each dispatch arm,
   if the pre-state satisfies `proofLayerInvariantBundle` and the delegated
   operation succeeds, the post-state satisfies `proofLayerInvariantBundle`.
   This is a match-on-syscall proof that invokes the appropriate per-operation
   preservation theorem in each branch.

**Files modified:**
- `SeLe4n/Kernel/API.lean` — `dispatchWithCap_decode_pure`,
  `dispatchWithCap_preserves_bundle`.

---

#### K-F5 — Complete Remaining NI Lifecycle Proofs

**Scope:** Write the two remaining deferred NI `lowEquivalent` proofs for
lifecycle operations, and update the stale deferred-proof comment.

**Tasks:**
1. `lifecycleRetypeObject_preserves_lowEquivalent`: retype at a non-observable
   target preserves low-equivalence. Proof delegates to
   `lifecycleRetypeObject_ok_as_storeObject` (decomposition lemma) then
   `storeObject_at_unobservable_preserves_lowEquivalent`.
2. `retypeFromUntyped_preserves_lowEquivalent`: retype-from-untyped at
   non-observable targets preserves low-equivalence. Proof decomposes into
   two `storeObject` calls (untyped update + child creation), each at a
   non-observable target, then composes via transitivity.
3. Update the stale deferred-proof comment at
   `InformationFlow/Invariant/Operations.lean:15–33` to reflect that all 5
   originally deferred proofs are now complete:
   - `cspaceDeleteSlot_preserves_lowEquivalent` — completed WS-H9
   - `cspaceCopy_preserves_lowEquivalent` — completed WS-H9
   - `cspaceMove_preserves_lowEquivalent` — completed WS-H9
   - `lifecycleRetypeObject_preserves_lowEquivalent` — completed K-F5
   - `retypeFromUntyped_preserves_lowEquivalent` — completed K-F5

**File modified:**
- `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean`

---

#### K-F6 — NI Coverage Verification

**Scope:** Confirm that all dispatch paths introduced in WS-K are covered by
existing `NonInterferenceStep` constructors. No new constructors needed.

**Tasks:**
1. Verify that the 33 existing `NonInterferenceStep` constructors
   (Composition.lean:34–241) cover every operation reachable from
   `dispatchWithCap`:
   - `.cspaceMint` (line 52) — covers `cspaceMint` dispatch arm.
   - `.cspaceCopy` (line 129) — covers `cspaceCopy` dispatch arm.
   - `.cspaceMove` (line 135) — covers `cspaceMove` dispatch arm.
   - `.cspaceDeleteSlot` (line 141) — covers `cspaceDelete` dispatch arm.
   - `.lifecycleRetype` (line 63) — covers `lifecycleRetype` dispatch arm.
   - `.vspaceMapPage` (line 113) — covers `vspaceMap` dispatch arm.
   - `.vspaceUnmapPage` (line 119) — covers `vspaceUnmap` dispatch arm.
   - `.serviceStart` (line 91) — covers `serviceStart` dispatch arm.
   - `.serviceStop` (line 96) — covers `serviceStop` dispatch arm.
   - `.endpointSendDual` (line 41) — covers IPC send dispatch arm.
   - `.endpointCallHigh` (line 157) — covers IPC call dispatch arm.
   - `.endpointReply` (line 146) — covers IPC reply dispatch arm.
   - `.endpointReceiveDualHigh` (line 152) — covers IPC recv dispatch arm.
   - `.syscallDecodeError` (line 225) — covers decode failure path.
   - `.syscallDispatchHigh` (line 237) — covers high-domain dispatch path.
2. Add `syscallEntry_NI_coverage` theorem: if `syscallEntry` succeeds from a
   high-domain thread, the transition is a `NonInterferenceStep`. If decode
   fails, state is unchanged and the `syscallDecodeError` constructor applies.
3. Verify `step_preserves_projection` (Composition.lean:245–505) handles all
   constructors — confirmed by exhaustive pattern match.

**Assessment:** No new `NonInterferenceStep` constructors are required. The
Layer 2 decode is pure (no state change) and argument extraction is pure.
Every dispatch arm delegates to a kernel operation already covered by an
existing constructor.

**Files modified:**
- `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean` — verification
  theorem (no structural changes to existing proofs).

---

**Combined exit criteria:**
- 7 encode functions defined (K-F1).
- 7 round-trip proofs + composed conjunction theorem (K-F2).
- Message register extraction round-trip proved (K-F3).
- `dispatchWithCap_preserves_bundle` theorem proved (K-F4).
- 2 lifecycle NI `lowEquivalent` proofs completed; stale comment updated (K-F5).
- NI coverage verification theorem; all 33 constructors confirmed (K-F6).
- Zero `sorry` / `axiom` in production proof surface.
- `lake build` passes; `test_full.sh` passes.

**All files modified (combined):**
- `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` — Encode functions,
  round-trip proofs (K-F1, K-F2).
- `SeLe4n/Kernel/Architecture/RegisterDecode.lean` — Extraction round-trip
  (K-F3).
- `SeLe4n/Kernel/API.lean` — Dispatch preservation theorem (K-F4).
- `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean` — Lifecycle NI
  proofs, stale comment update (K-F5).
- `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean` — NI coverage
  verification theorem (K-F6).

**Version target:** v0.16.5

---

### WS-K-G — Comprehensive Testing

**Goal:** Full test coverage for every new decode, dispatch, and error path.

**Tasks:**
1. **Negative-state tests** in `tests/NegativeStateSuite.lean`:
   - `cspaceMint_via_entry_insufficient_msgRegs`: decode fails when msgRegs
     too short.
   - `cspaceMint_via_entry_no_capability`: dispatch fails without mint right.
   - `cspaceCopy_via_entry_invalid_slot`: dispatch fails for nonexistent slot.
   - `cspaceMove_via_entry_invalid_slot`: analogous.
   - `cspaceDelete_via_entry_object_not_found`: dispatch fails for missing CNode.
   - `lifecycleRetype_via_entry_invalid_type`: decode fails for bad type tag.
   - `lifecycleRetype_via_entry_no_authority`: dispatch fails without retype right.
   - `vspaceMap_via_entry_asid_not_bound`: dispatch fails for unmapped ASID.
   - `vspaceMap_via_entry_wx_violation`: dispatch fails for W+X permissions.
   - `vspaceUnmap_via_entry_translation_fault`: dispatch fails for unmapped page.
   - `serviceStart_via_entry_policy_denied`: dispatch fails when policy denies.
   - `serviceStop_via_entry_policy_denied`: analogous.
   - `ipc_send_empty_msgRegs`: send succeeds with 0-length message.
   - `ipc_send_full_msgRegs`: send succeeds with maxMessageRegisters values.

2. **Trace tests** in `SeLe4n/Testing/MainTraceHarness.lean`:
   - Add trace scenarios for each newly-wired syscall:
     - CSpace mint through register-sourced entry.
     - CSpace copy through register-sourced entry.
     - Lifecycle retype through register-sourced entry.
     - VSpace map through register-sourced entry.
     - Service start with non-trivial policy.
     - IPC send with populated message body.

3. **Determinism tests**: verify that `decodeSyscallArgs` followed by
   per-syscall decode produces identical results across double invocation.

4. **Tier 3 invariant surface anchors**: add anchor theorems referencing:
   - All 7 new argument structures.
   - All 7 decode functions.
   - `extractMessageRegisters`.
   - `ServiceConfig`.
   - Delegation theorems.

5. Update `tests/fixtures/main_trace_smoke.expected` with new trace output.

6. Run `test_full.sh` to verify all tiers pass.

**Exit criteria:**
- ≥14 new negative-state tests covering all error paths.
- ≥6 new trace scenarios covering all newly-wired syscalls.
- Tier 3 anchors for all new definitions and theorems.
- `test_full.sh` passes with zero failures and zero warnings.
- `tests/fixtures/main_trace_smoke.expected` updated to match.

**Files modified:**
- `tests/NegativeStateSuite.lean` — New negative tests.
- `SeLe4n/Testing/MainTraceHarness.lean` — New trace scenarios.
- `tests/fixtures/main_trace_smoke.expected` — Updated expected output.
- `tests/InvariantSurfaceSuite.lean` — New Tier 3 anchors.

**Version target:** v0.16.6–v0.16.7

---

### WS-K-H — Documentation Sync and Workstream Closeout

**Goal:** Synchronize all documentation with the completed implementation.
Update GitBook chapters and claim evidence index.

**Tasks:**
1. Update `docs/WORKSTREAM_HISTORY.md`:
   - Add WS-K portfolio entry with status, version range, and phase summary.
2. Update `docs/spec/SELE4N_SPEC.md`:
   - Syscall dispatch section: document complete 13/13 dispatch.
   - Message register extraction: document register layout → typed args.
   - Service policy: document `ServiceConfig` mechanism.
3. Update `docs/DEVELOPMENT.md`:
   - Active workstreams section: add WS-K entry.
   - Next steps: update to reflect post-WS-K state.
4. Update `docs/CLAIM_EVIDENCE_INDEX.md`:
   - Add claims for WS-K-A through WS-K-G with test commands.
   - Update WS-J1 claims to note that WS-K extends them.
5. Update `docs/gitbook/` chapters:
   - `03-architecture-and-module-map.md` — Add `SyscallArgDecode.lean` to
     module map.
   - `04-project-design-deep-dive.md` — Document decode architecture
     (two-layer: raw registers → SyscallDecodeResult → per-syscall args).
   - `05-specification-and-roadmap.md` — Update roadmap milestones.
   - `12-proof-and-invariant-map.md` — Add round-trip and delegation theorems
     to the proof map.
6. Regenerate `docs/codebase_map.json`:
   ```bash
   python3 ./scripts/generate_codebase_map.py --pretty --output docs/codebase_map.json
   ```
7. Update `README.md` metrics via `report_current_state.py` if applicable.
8. Update this workstream plan status from "Planned" to "Completed" with
   version annotations on all checklist items.
9. Run `test_full.sh` one final time to verify documentation changes don't
   break Tier 0 hygiene (website link check).

**Exit criteria:**
- All documentation files listed above updated and consistent.
- `docs/codebase_map.json` regenerated.
- GitBook chapters mirror canonical sources.
- `test_full.sh` passes (including Tier 0 link check).
- Workstream plan status updated to "Completed".

**Files modified:**
- `docs/WORKSTREAM_HISTORY.md`
- `docs/spec/SELE4N_SPEC.md`
- `docs/DEVELOPMENT.md`
- `docs/CLAIM_EVIDENCE_INDEX.md`
- `docs/gitbook/03-architecture-and-module-map.md`
- `docs/gitbook/04-project-design-deep-dive.md`
- `docs/gitbook/05-specification-and-roadmap.md`
- `docs/gitbook/12-proof-and-invariant-map.md`
- `docs/codebase_map.json`
- `README.md`
- This file (status update).

**Version target:** v0.16.8

---

## 6. File impact map

### Core model layer
| File | Change | Phase |
|------|--------|-------|
| `SeLe4n/Model/Object/Types.lean` | Add `msgRegs` to `SyscallDecodeResult` | K-A |
| `SeLe4n/Model/State.lean` | Add `ServiceConfig`, extend `SystemState` | K-E |

### Architecture layer
| File | Change | Phase |
|------|--------|-------|
| `SeLe4n/Kernel/Architecture/RegisterDecode.lean` | Populate msgRegs, extraction helper + length/bounded/determinism lemmas | K-A, K-E |
| `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` | **NEW** — argument structures + decode fns | K-B |
| `SeLe4n/Model/Object/Structures.lean` | `PagePermissions.ofNat`, `toNat`, round-trip | K-D |

### Kernel API
| File | Change | Phase |
|------|--------|-------|
| `SeLe4n/Kernel/API.lean` | Full dispatch for all 13 syscalls | K-C, K-D, K-E |

### Kernel subsystems
| File | Change | Phase |
|------|--------|-------|
| `SeLe4n/Kernel/Lifecycle/Operations.lean` | `objectOfTypeTag`, `lifecycleRetypeDirect`, theorems | K-D |

### Information flow
| File | Change | Phase |
|------|--------|-------|
| `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean` | Complete deferred NI proofs | K-F |

### Testing
| File | Change | Phase |
|------|--------|-------|
| `tests/NegativeStateSuite.lean` | ≥14 new negative tests | K-G |
| `SeLe4n/Testing/MainTraceHarness.lean` | ≥6 new trace scenarios | K-G |
| `tests/fixtures/main_trace_smoke.expected` | Updated expected output | K-G |
| `tests/InvariantSurfaceSuite.lean` | New Tier 3 anchors | K-G |
| `SeLe4n/Testing/StateBuilder.lean` | Update defaults for new fields | K-A, K-E |

### Documentation
| File | Change | Phase |
|------|--------|-------|
| `docs/WORKSTREAM_HISTORY.md` | WS-K portfolio entry | K-H |
| `docs/spec/SELE4N_SPEC.md` | Syscall dispatch, MR extraction, service policy | K-H |
| `docs/DEVELOPMENT.md` | Active workstreams, next steps | K-H |
| `docs/CLAIM_EVIDENCE_INDEX.md` | WS-K claims | K-H |
| `docs/gitbook/03-architecture-and-module-map.md` | Module map update | K-H |
| `docs/gitbook/04-project-design-deep-dive.md` | Decode architecture | K-H |
| `docs/gitbook/05-specification-and-roadmap.md` | Roadmap update | K-H |
| `docs/gitbook/12-proof-and-invariant-map.md` | Proof map update | K-H |
| `docs/codebase_map.json` | Regenerated | K-H |
| `README.md` | Metrics sync | K-H |

---

## 7. Risk register and mitigations

| # | Risk | Likelihood | Impact | Mitigation |
|---|------|-----------|--------|------------|
| R1 | `SyscallDecodeResult` extension breaks many call sites | High | Medium | Phase K-A explicitly lists all call sites. The new field has a default value (`#[]`), allowing incremental migration. |
| R2 | `dispatchWithCap` signature change breaks soundness theorems | Medium | High | Change signature in K-C only after verifying theorem structure. Existing theorems quantify over `SyscallId`, not `SyscallDecodeResult`, so they should compose. |
| R3 | `SystemState` extension for `ServiceConfig` breaks fixture construction | Medium | Medium | `ServiceConfig` has `Inhabited` instance. Existing fixtures use default construction and are unaffected. |
| R4 | Deferred NI proofs (Operations.lean:15–33) prove harder than expected | Medium | High | These proofs follow the `storeObject_preserves_projection` pattern already used elsewhere. CDT operations compose with frame lemmas. If blocked, add targeted `sorry` with TPI-D annotation and track as sub-workstream. |
| R5 | `objectOfTypeTag` introduces non-determinism via unrecognized type tags | Low | Critical | Return `Except KernelError KernelObject` — unrecognized tags produce `.invalidTypeTag`. No default object construction. |
| R6 | Message register array length mismatch between platform layouts | Low | Medium | `decodeMsgRegs_length` lemma enforces `decoded.msgRegs.size = layout.msgRegs.size`. Per-syscall decode checks minimum count. |

---

## 8. Validation plan

### Per-phase validation
| Phase | Validation | Command |
|-------|-----------|---------|
| K-A | Build + smoke | `./scripts/test_smoke.sh` |
| K-B | Build + smoke | `./scripts/test_smoke.sh` |
| K-C | Build + smoke + soundness | `./scripts/test_smoke.sh` |
| K-D | Build + smoke + soundness | `./scripts/test_smoke.sh` |
| K-E | Build + smoke | `./scripts/test_smoke.sh` |
| K-F | Build + full (theorem changes) | `./scripts/test_full.sh` |
| K-G | Full test suite | `./scripts/test_full.sh` |
| K-H | Full + hygiene | `./scripts/test_full.sh` |

### Cross-phase validation
- **After K-D:** All 13 syscalls dispatch (zero `.illegalState` stubs).
  Verify with `grep -c 'illegalState' SeLe4n/Kernel/API.lean` → 0 in
  `dispatchWithCap`.
- **After K-E:** `grep '(fun _ => true)' SeLe4n/Kernel/API.lean` → 0.
- **After K-E:** `grep 'registers := #\[\]' SeLe4n/Kernel/API.lean` → 0.
- **After K-F:** `grep -c 'sorry' SeLe4n/**/*.lean` → 0.
- **After K-G:** `./scripts/test_full.sh` exits 0 with all tiers passing.
- **After K-H:** `./scripts/test_full.sh` exits 0 (includes Tier 0 link check).

---

## 9. Completion evidence checklist

- [x] K-A: `SyscallDecodeResult` includes `msgRegs : Array RegValue` (v0.16.0) ✓
- [x] K-A: `decodeSyscallArgs` populates `msgRegs` from layout (v0.16.0) ✓
- [x] K-A: `decodeMsgRegs_length` lemma proved (v0.16.0) ✓
- [x] K-B: All 7 argument structures defined (v0.16.1) ✓
- [x] K-B: All 7 decode functions total with `Except` returns (v0.16.1) ✓
- [x] K-B: Determinism and error-exclusivity theorems proved (v0.16.1) ✓
- [x] K-C.1: `dispatchWithCap` accepts `SyscallDecodeResult` (v0.16.2) ✓
- [x] K-C.2: `cspaceMint` dispatches through decode → operation (v0.16.2) ✓
- [x] K-C.3: `cspaceCopy` dispatches through decode → operation (v0.16.2) ✓
- [x] K-C.4: `cspaceMove` dispatches through decode → operation (v0.16.2) ✓
- [x] K-C.5: `cspaceDelete` dispatches through decode → operation (v0.16.2) ✓
- [x] K-C.6: Existing soundness theorems pass unchanged (v0.16.2) ✓
- [x] K-C.7: 4 CSpace delegation theorems proved (v0.16.2) ✓
- [x] K-C.8: `lake build` + `test_smoke.sh` pass (v0.16.2) ✓
- [x] K-D.1: `objectOfTypeTag` defined with type/error/determinism theorems (v0.16.3) ✓
- [x] K-D.2: `PagePermissions.ofNat`/`toNat` with round-trip theorem (v0.16.3) ✓
- [x] K-D.3: `lifecycleRetypeDirect` with equivalence/error theorems (v0.16.3) ✓
- [x] K-D.4: `lifecycleRetype` dispatches through decode → operation (v0.16.3) ✓
- [x] K-D.5: `vspaceMap` dispatches through decode → operation (v0.16.3) ✓
- [x] K-D.6: `vspaceUnmap` dispatches through decode → operation (v0.16.3) ✓
- [x] K-D.7: Existing soundness theorems compile unchanged (v0.16.3) ✓
- [x] K-D.8: 3 delegation theorems proved (lifecycle + VSpace) (v0.16.3) ✓
- [x] K-D.9: Tier 3 anchors for all new definitions (v0.16.3) ✓
- [x] K-D.10: Zero `.illegalState` stubs in `dispatchWithCap` (v0.16.3) ✓
- [x] K-E.1: `ServiceConfig` structure with `Inhabited` default (v0.16.4) ✓
- [x] K-E.2: `SystemState` extended with `serviceConfig` field (v0.16.4) ✓
- [x] K-E.3: `extractMessageRegisters` converts `Array RegValue` → `Array Nat` (v0.16.4) ✓
- [x] K-E.4: `extractMessageRegisters_length` lemma proved (v0.16.4) ✓
- [x] K-E.5: `extractMessageRegisters_ipc_bounded` lemma proved (v0.16.4) ✓
- [x] K-E.6: `extractMessageRegisters_deterministic` theorem proved (v0.16.4) ✓
- [x] K-E.7: `.serviceStart` dispatch uses `st.serviceConfig.allowStart` (v0.16.4) ✓
- [x] K-E.8: `.serviceStop` dispatch uses `st.serviceConfig.allowStop` (v0.16.4) ✓
- [x] K-E.9: `.send` IPC message populated from decoded registers (v0.16.4) ✓
- [x] K-E.10: `.call` IPC message populated from decoded registers (v0.16.4) ✓
- [x] K-E.11: `.reply` IPC message populated from decoded registers (v0.16.4) ✓
- [x] K-E.12: 2 service delegation theorems proved (v0.16.4) ✓
- [x] K-E.13: 3 IPC message population delegation theorems proved (v0.16.4) ✓
- [x] K-E.14: All existing soundness theorems compile unchanged (v0.16.4) ✓
- [x] K-E.15: `BootstrapBuilder` extended with `serviceConfig` (v0.16.4) ✓
- [x] K-E.16: Tier 3 anchors for all new definitions (v0.16.4) ✓
- [x] K-E.17: `lake build` + `test_smoke.sh` pass (v0.16.4) ✓
- [ ] K-F: Round-trip proofs for all 7 argument structures (v0.16.5)
- [ ] K-F: Message register extraction round-trip proved (v0.16.5)
- [ ] K-F: Deferred NI proofs completed (v0.16.5)
- [ ] K-F: Zero `sorry`/`axiom` in production proof surface (v0.16.5)
- [ ] K-G: ≥14 negative-state tests for new error paths (v0.16.6)
- [ ] K-G: ≥6 trace scenarios for newly-wired syscalls (v0.16.6)
- [ ] K-G: Tier 3 anchors for all new definitions (v0.16.7)
- [ ] K-G: `test_full.sh` passes with zero failures (v0.16.7)
- [ ] K-H: `docs/WORKSTREAM_HISTORY.md` updated (v0.16.8)
- [ ] K-H: `docs/spec/SELE4N_SPEC.md` updated (v0.16.8)
- [ ] K-H: GitBook chapters synchronized (v0.16.8)
- [ ] K-H: `docs/codebase_map.json` regenerated (v0.16.8)
- [ ] K-H: `test_full.sh` exits 0 including Tier 0 hygiene (v0.16.8)

---

## 10. Relationship to prior work

### Builds on
- **WS-J1** (v0.15.4–v0.15.10): Typed register wrappers, decode layer,
  syscall entry point, 13-case dispatch skeleton. WS-K completes the dispatch
  paths that WS-J1 deferred.
- **WS-F3/F4** (v0.12.2): CSpace CRUD NI proofs (partially deferred). WS-K-F
  completes the deferred proofs now that the dispatch path makes them
  exercisable.
- **WS-H13** (v0.14.7): Service backing object validation. WS-K-E builds on
  this by adding policy configuration.

### Supersedes
- **WS-J1-E deferred note** (API.lean:389): "Full MR-based argument extraction
  deferred to WS-J1-E" — WS-K replaces this deferral with implementation.
- **WS-F3 deferred proofs** (Operations.lean:15–33): Five NI proofs marked as
  deferred to WS-F4. WS-K-F completes them.

### Enables future work
- **Hardware platform binding**: With all 13 syscalls dispatching, the RPi5
  platform contract can exercise the full kernel surface.
- **Extra capability transfer**: IPC message `caps` field can be populated in
  a follow-up workstream once CSpace dispatch is live.
- **Boot sequence verification**: Requires lifecycle retype to be dispatchable
  for initial object creation.

---

## 11. Architectural integrity notes

### Deterministic semantics preservation
Every new function returns `Except KernelError T`. No `Option.get!`, no
`panic!`, no partial functions. All `match` expressions are exhaustive.
The project's deterministic-semantics invariant is maintained.

### Typed identifier discipline
All new argument structures use typed identifiers (`Slot`, `ObjId`, `ASID`,
`VAddr`, `PAddr`, `Badge`) — never raw `Nat`. Decode functions perform the
`Nat → Typed` conversion at the decode boundary.

### Proof surface completeness
WS-K-F is the proof-heavy phase. It targets:
- 7 round-trip proofs (one per argument structure)
- 1 message register extraction round-trip
- 5 deferred NI proofs from WS-F3
- 0 new `sorry`/`axiom` — all proofs are complete

### Module dependency preservation
The new `SyscallArgDecode.lean` depends only on `Model.State` (for types) and
`RegisterDecode.lean` (for `SyscallDecodeResult`). It does not import any
kernel subsystem module, maintaining the same dependency discipline as
`RegisterDecode.lean`.
