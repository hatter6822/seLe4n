# seLe4n Workstream Plan — Full Syscall Dispatch Completion (WS-K)

**Version target:** v0.16.0–v0.16.8
**Base version:** v0.15.10
**Status:** Planned
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
register array.

**Tasks:**
1. Add `msgRegs : Array RegValue` to `SyscallDecodeResult` in
   `Model/Object/Types.lean`.
2. Update `decodeSyscallArgs` in `RegisterDecode.lean` to read and store
   message register values after bounds validation:
   ```lean
   let msgRegVals ← layout.msgRegs.mapM fun r => do
     validateRegBound r regCount
     pure (readReg regs r)
   ```
3. Update all call sites that construct `SyscallDecodeResult` directly
   (tests, fixtures) to include the new `msgRegs` field.
4. Add `decodeMsgRegs_length` lemma proving `decoded.msgRegs.size =
   layout.msgRegs.size` when decode succeeds.
5. Add round-trip lemma for message register values: encoding then decoding
   the raw array preserves values.
6. Verify `lake build` passes with zero errors.

**Exit criteria:**
- `SyscallDecodeResult` includes `msgRegs` field.
- `decodeSyscallArgs` reads and stores message register values.
- Length invariant and round-trip lemma proved.
- `lake build` passes; `test_smoke.sh` passes.

**Files modified:**
- `SeLe4n/Model/Object/Types.lean` — Add `msgRegs` field to structure.
- `SeLe4n/Kernel/Architecture/RegisterDecode.lean` — Update decode function
  and add lemmas.
- `tests/*.lean` — Update any direct `SyscallDecodeResult` construction.
- `SeLe4n/Testing/MainTraceHarness.lean` — Update trace scenarios.

**Version target:** v0.16.0

---

### WS-K-B — Per-Syscall Argument Decode Layer

**Goal:** Define typed argument structures for each syscall family and total
decode functions that extract them from `SyscallDecodeResult.msgRegs`.

**Tasks:**
1. Define `CSpaceMintArgs`, `CSpaceCopyArgs`, `CSpaceMoveArgs`,
   `CSpaceDeleteArgs` structures in a new file
   `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean`.
2. Define `LifecycleRetypeArgs`, `VSpaceMapArgs`, `VSpaceUnmapArgs` in the
   same file.
3. Implement decode functions for each:
   - `decodeCSpaceMintArgs : SyscallDecodeResult → Except KernelError CSpaceMintArgs`
   - `decodeCSpaceCopyArgs : SyscallDecodeResult → Except KernelError CSpaceCopyArgs`
   - `decodeCSpaceMoveArgs : SyscallDecodeResult → Except KernelError CSpaceMoveArgs`
   - `decodeCSpaceDeleteArgs : SyscallDecodeResult → Except KernelError CSpaceDeleteArgs`
   - `decodeLifecycleRetypeArgs : SyscallDecodeResult → Except KernelError LifecycleRetypeArgs`
   - `decodeVSpaceMapArgs : SyscallDecodeResult → Except KernelError VSpaceMapArgs`
   - `decodeVSpaceUnmapArgs : SyscallDecodeResult → Except KernelError VSpaceUnmapArgs`
4. Each function checks `msgRegs.size` against minimum required register count
   and returns `invalidMessageInfo` if insufficient.
5. Add determinism theorem for each decode function (trivially `rfl`).
6. Add error-exclusivity theorems: decode fails iff register count insufficient.

**Exit criteria:**
- All 7 argument structures defined with `DecidableEq`, `Repr`.
- All 7 decode functions are total with explicit error returns.
- Determinism and error-exclusivity theorems proved.
- `lake build` passes; `test_smoke.sh` passes.

**Files created:**
- `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean`

**Files modified:**
- `SeLe4n/Kernel/API.lean` — Import new module.

**Version target:** v0.16.1

---

### WS-K-C — CSpace Syscall Dispatch

**Goal:** Wire `cspaceMint`, `cspaceCopy`, `cspaceMove`, `cspaceDelete`
through `dispatchWithCap` using decoded message register arguments.

**Tasks:**
1. Modify `dispatchWithCap` to accept `SyscallDecodeResult` instead of just
   `SyscallId`:
   ```lean
   private def dispatchWithCap (decoded : SyscallDecodeResult)
       (tid : SeLe4n.ThreadId) (cap : Capability) : Kernel Unit
   ```
2. Replace `cspaceMint` stub with:
   ```lean
   | .cspaceMint =>
       match cap.target with
       | .object cnodeId =>
           fun st => match decodeCSpaceMintArgs decoded with
           | .error e => .error e
           | .ok args =>
               let src : CSpaceAddr := { cnode := cnodeId, slot := args.srcSlot }
               let dst : CSpaceAddr := { cnode := cnodeId, slot := args.dstSlot }
               cspaceMint src dst args.rights args.badge st
       | _ => fun _ => .error .invalidCapability
   ```
3. Replace `cspaceCopy`, `cspaceMove`, `cspaceDelete` stubs with analogous
   patterns using their respective decode functions.
4. Update `dispatchSyscall` call site to pass full `decoded` to
   `dispatchWithCap`.
5. Verify all existing soundness theorems still hold (`dispatchSyscall_requires_right`,
   `syscallEntry_implies_capability_held`, `syscallEntry_requires_valid_decode`).
6. Add `dispatchWithCap_cspaceMint_delegates` theorem proving the dispatch path
   delegates to the kernel-level `cspaceMint` operation.

**Exit criteria:**
- All 4 CSpace syscalls fully dispatch to kernel operations.
- No `.illegalState` stubs remain for CSpace syscalls.
- Existing soundness theorems pass unchanged.
- New delegation theorem proved.
- `lake build` passes; `test_smoke.sh` passes.

**Files modified:**
- `SeLe4n/Kernel/API.lean` — Replace CSpace stubs, update `dispatchWithCap`
  signature.

**Version target:** v0.16.2

---

### WS-K-D — Lifecycle and VSpace Syscall Dispatch

**Goal:** Wire `lifecycleRetype`, `vspaceMap`, `vspaceUnmap` through
`dispatchWithCap` using decoded arguments.

**Tasks:**
1. Replace `lifecycleRetype` stub:
   ```lean
   | .lifecycleRetype =>
       fun st => match decodeLifecycleRetypeArgs decoded with
       | .error e => .error e
       | .ok args =>
           let authority : CSpaceAddr := { cnode := ..., slot := ... }
           lifecycleRetypeObject authority args.targetObj
             (objectOfTypeTag args.newType args.size) st
   ```
2. Define `objectOfTypeTag : Nat → Nat → KernelObject` helper that maps
   a type tag + size into a default `KernelObject`. Returns error for
   unrecognized tags. Place in `Lifecycle/Operations.lean`.
3. Replace `vspaceMap` stub:
   ```lean
   | .vspaceMap =>
       fun st => match decodeVSpaceMapArgs decoded with
       | .error e => .error e
       | .ok args =>
           Architecture.vspaceMapPage args.asid args.vaddr args.paddr
             (PagePermissions.ofNat args.perms) st
   ```
4. Replace `vspaceUnmap` stub:
   ```lean
   | .vspaceUnmap =>
       fun st => match decodeVSpaceUnmapArgs decoded with
       | .error e => .error e
       | .ok args =>
           Architecture.vspaceUnmapPage args.asid args.vaddr st
   ```
5. Add `PagePermissions.ofNat` helper if not already present.
6. Verify existing soundness theorems still hold.
7. Add delegation theorems for lifecycle and VSpace dispatch paths.

**Exit criteria:**
- All 3 stubs replaced with full dispatch.
- Zero `.illegalState` stubs remaining in `dispatchWithCap`.
- `objectOfTypeTag` defined and used.
- Delegation theorems proved.
- `lake build` passes; `test_smoke.sh` passes.

**Files modified:**
- `SeLe4n/Kernel/API.lean` — Replace lifecycle and VSpace stubs.
- `SeLe4n/Kernel/Lifecycle/Operations.lean` — Add `objectOfTypeTag`.
- `SeLe4n/Kernel/Architecture/VSpace.lean` — Add `PagePermissions.ofNat`
  if needed.

**Version target:** v0.16.3

---

### WS-K-E — Service Policy and IPC Message Population

**Goal:** Replace `(fun _ => true)` service policy stubs with
configuration-sourced predicates. Populate IPC message bodies from decoded
message registers.

**Tasks:**
1. Define `ServiceConfig` structure in `Model/State.lean`:
   ```lean
   structure ServiceConfig where
     allowStart : ServicePolicy
     allowStop  : ServicePolicy
     deriving Inhabited
   ```
   The `Inhabited` instance provides `(fun _ => true)` as default, preserving
   backward compatibility for existing tests.
2. Add `serviceConfig : ServiceConfig` field to `SystemState`.
3. Update `dispatchWithCap` for `.serviceStart`:
   ```lean
   | .serviceStart =>
       match cap.target with
       | .object objId =>
           fun st => serviceStart (ServiceId.ofNat objId.toNat)
                       st.serviceConfig.allowStart st
       | _ => fun _ => .error .invalidCapability
   ```
4. Update `.serviceStop` analogously with `st.serviceConfig.allowStop`.
5. Define `extractMessageRegisters`:
   ```lean
   def extractMessageRegisters (msgRegs : Array RegValue)
       (info : MessageInfo) : Array RegValue :=
     msgRegs.extract 0 (min info.length maxMessageRegisters)
   ```
6. Update IPC dispatch paths (send, call, reply) to populate message bodies:
   ```lean
   | .send =>
       match cap.target with
       | .object epId =>
           let body := extractMessageRegisters decoded.msgRegs decoded.msgInfo
           endpointSendDual epId tid
             { registers := body, caps := #[], badge := cap.badge }
   ```
7. Add `extractMessageRegisters_length` lemma: result length ≤
   `maxMessageRegisters`.
8. Add `extractMessageRegisters_deterministic` theorem.
9. Update all `SystemState` construction sites (default state, test fixtures)
   to include `serviceConfig` field.

**Exit criteria:**
- No `(fun _ => true)` policy stubs in `dispatchWithCap`.
- IPC messages carry register contents (not empty arrays).
- `ServiceConfig` in `SystemState` with `Inhabited` default.
- Length and determinism lemmas proved.
- `lake build` passes; `test_smoke.sh` passes.

**Files modified:**
- `SeLe4n/Model/State.lean` — Add `ServiceConfig`, extend `SystemState`.
- `SeLe4n/Kernel/API.lean` — Replace stubs, populate IPC messages.
- `SeLe4n/Kernel/Architecture/RegisterDecode.lean` — Add
  `extractMessageRegisters`.
- `tests/*.lean` — Update `SystemState` construction.
- `SeLe4n/Testing/StateBuilder.lean` — Update builder defaults.

**Version target:** v0.16.4

---

### WS-K-F — Proofs: Round-Trip, Preservation, and NI Integration

**Goal:** Prove round-trip correctness for all new decode paths, preservation
of the proof-layer invariant bundle across new dispatch paths, and extend NI
coverage.

**Tasks:**
1. **Round-trip proofs** in `SyscallArgDecode.lean`:
   - `decodeCSpaceMintArgs_roundtrip`: encoding CSpaceMintArgs into message
     registers then decoding recovers the original.
   - Analogous for all 7 argument structures.
   - Pattern: define `encodeCSpaceMintArgs : CSpaceMintArgs → Array RegValue`,
     then prove `decodeCSpaceMintArgs ∘ encodeCSpaceMintArgs = .ok`.

2. **Message register extraction round-trip** in `RegisterDecode.lean`:
   - `extractMessageRegisters_roundtrip`: for well-formed inputs, extracting
     from the array of encoded values recovers the originals.

3. **Invariant preservation** — verify that
   `proofLayerInvariantBundle` is preserved across new dispatch paths:
   - CSpace dispatch: composes with existing CSpace preservation theorems.
   - Lifecycle dispatch: composes with existing lifecycle preservation.
   - VSpace dispatch: composes with existing VSpace preservation.
   - Service config: policy change does not affect invariant (policy is
     read-only during dispatch).
   - IPC message population: does not affect state (message is an argument,
     not a state mutation).

4. **NI integration** — verify existing `NonInterferenceStep` constructors
   suffice:
   - `cspaceMint`, `cspaceCopy`, `cspaceMove`, `cspaceDeleteSlot`,
     `lifecycleRetype`, `vspaceMapPage`, `vspaceUnmapPage` constructors
     already exist (Composition.lean:52–144).
   - `serviceStart`, `serviceStop` constructors already exist (lines 91–105).
   - `syscallDispatchHigh` constructor covers the register-sourced entry path.
   - **Assessment:** No new NI constructors needed — existing 33 constructors
     cover all dispatch paths. The decode is pure (no state change) and the
     argument extraction is pure. The dispatch delegates to operations already
     covered.

5. **Deferred NI proof completion** — the operations module
   (`InformationFlow/Invariant/Operations.lean:15–33`) lists deferred proofs
   for `cspaceDeleteSlot`, `cspaceCopy`, `cspaceMove`,
   `lifecycleRevokeDeleteRetype`. Complete these using `storeObject`-level
   projection lemmas and CDT frame lemmas now that the dispatch path is live.

6. Add `dispatchWithCap_preserves_bundle` theorem or verify it follows from
   per-operation preservation.

**Exit criteria:**
- Round-trip proofs for all 7 argument structures.
- Message register extraction round-trip proved.
- Invariant preservation verified for all new dispatch paths.
- NI coverage confirmed (no gaps in `NonInterferenceStep` constructors).
- Deferred NI proofs for CSpace/lifecycle operations completed.
- Zero `sorry` / `axiom` in production proof surface.
- `lake build` passes; `test_full.sh` passes.

**Files modified:**
- `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` — Round-trip proofs.
- `SeLe4n/Kernel/Architecture/RegisterDecode.lean` — Extraction round-trip.
- `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean` — Complete
  deferred NI proofs.
- `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean` — Verify
  coverage (likely no changes needed).

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
| `SeLe4n/Kernel/Architecture/RegisterDecode.lean` | Populate msgRegs, extraction helper, lemmas | K-A, K-E |
| `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` | **NEW** — argument structures + decode fns | K-B |
| `SeLe4n/Kernel/Architecture/VSpace.lean` | `PagePermissions.ofNat` if needed | K-D |

### Kernel API
| File | Change | Phase |
|------|--------|-------|
| `SeLe4n/Kernel/API.lean` | Full dispatch for all 13 syscalls | K-C, K-D, K-E |

### Kernel subsystems
| File | Change | Phase |
|------|--------|-------|
| `SeLe4n/Kernel/Lifecycle/Operations.lean` | `objectOfTypeTag` helper | K-D |

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
| R5 | `objectOfTypeTag` introduces non-determinism via unrecognized type tags | Low | Critical | Return `Except KernelError KernelObject` — unrecognized tags produce `.invalidArgument`. No default object construction. |
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

- [ ] K-A: `SyscallDecodeResult` includes `msgRegs : Array RegValue` (v0.16.0)
- [ ] K-A: `decodeSyscallArgs` populates `msgRegs` from layout (v0.16.0)
- [ ] K-A: `decodeMsgRegs_length` lemma proved (v0.16.0)
- [ ] K-B: All 7 argument structures defined (v0.16.1)
- [ ] K-B: All 7 decode functions total with `Except` returns (v0.16.1)
- [ ] K-B: Determinism and error-exclusivity theorems proved (v0.16.1)
- [ ] K-C: `cspaceMint` dispatches through decode → operation (v0.16.2)
- [ ] K-C: `cspaceCopy` dispatches through decode → operation (v0.16.2)
- [ ] K-C: `cspaceMove` dispatches through decode → operation (v0.16.2)
- [ ] K-C: `cspaceDelete` dispatches through decode → operation (v0.16.2)
- [ ] K-C: Existing soundness theorems pass unchanged (v0.16.2)
- [ ] K-D: `lifecycleRetype` dispatches through decode → operation (v0.16.3)
- [ ] K-D: `vspaceMap` dispatches through decode → operation (v0.16.3)
- [ ] K-D: `vspaceUnmap` dispatches through decode → operation (v0.16.3)
- [ ] K-D: Zero `.illegalState` stubs in `dispatchWithCap` (v0.16.3)
- [ ] K-E: `ServiceConfig` in `SystemState` with `Inhabited` default (v0.16.4)
- [ ] K-E: Service dispatch uses `st.serviceConfig` (v0.16.4)
- [ ] K-E: IPC messages populated from decoded registers (v0.16.4)
- [ ] K-E: `extractMessageRegisters_length` lemma proved (v0.16.4)
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
