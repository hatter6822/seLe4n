# Project Design Deep Dive

This chapter explains the design decisions that shape seLe4n and distinguish it from both seL4 and other verification projects. Each decision is motivated by a concrete engineering trade-off.

## 1. Core design principles

### 1.1 Deterministic transition semantics

Every kernel operation is a pure function that returns an explicit result — either a success value or a typed error. There are no partial functions, no silent failures, no undefined behavior.

- **Every error path is a modeled path.** An invalid capability lookup returns `capNotFound`, not an unhandled `none`.
- **Proofs cover failure paths.** Error-case preservation theorems confirm that failed operations leave state unchanged.
- **Executable traces are complete.** `Main.lean` exercises both success and failure paths, and the Tier 2 fixture locks expected output.

In seL4, some error conditions are handled by C-level assertions or undefined behavior. seLe4n eliminates this gap — the Lean type-checker enforces totality.

### 1.2 Local-first theorem layering

For any transition `t`, the proof strategy follows a strict order:

1. Prove `t` preserves each local invariant component (e.g., `schedulerWellFormed`).
2. Prove the local facts compose into the subsystem bundle (e.g., `schedulerInvariantBundle`).
3. Prove the subsystem bundles compose into the cross-subsystem bundle (e.g., `kernelInvariant`).

Adding a new invariant component only requires re-proving the local-to-bundle step. When WS-H4 extended `capabilityInvariantBundle` from a 4-tuple to a 7-tuple, scheduler and IPC proofs were untouched.

### 1.3 Compositional invariant architecture

Monolithic invariants are brittle. seLe4n decomposes invariants into named components:

```
schedulerInvariantBundle =
  schedulerWellFormed ∧ currentThreadInActiveDomain ∧ timeSlicePositive

capabilityInvariantBundle =
  cspaceSlotUnique ∧ cspaceLookupSound ∧ cdtWellFormed
  ∧ cspaceSlotCountBounded ∧ cdtCompleteness ∧ cdtAcyclicity ∧ ...
```

Each component has a clear semantic meaning. Bundle composition is explicit and verified by Tier 3 anchor checks.

### 1.4 Executable evidence as a contract

`Main.lean` is not a demo — it is a regression surface. The trace harness constructs a realistic kernel state, exercises scheduler/capability/IPC/lifecycle/VSpace/service operations, and produces deterministic output. Tier 2 checks compare this output against `tests/fixtures/main_trace_smoke.expected`.

Every claimed semantic property has both a theorem (machine-checked) and a runtime witness (fixture-checked). If a refactor changes behavior, the fixture breaks before the PR lands.

### 1.5 Register decode boundary — type-safe syscall argument parsing

On real ARM64 hardware, syscall arguments arrive in general-purpose registers (x0–x7). The kernel must decode these raw untrusted values into typed kernel identifiers before any authority check can proceed. seLe4n models this boundary explicitly with `RegisterDecode.lean`:

- **Total decode functions** return `Except KernelError` — no partial functions at the syscall boundary.
- **Round-trip lemmas** prove that encoding then decoding recovers the original value for all three decode components: `decodeCapPtr_roundtrip`, `decodeSyscallId_roundtrip`, `decodeMsgInfo_roundtrip` (bitwise proof via `Nat.testBit` extensionality over seL4 message-info bit-field layout). The composite `decode_components_roundtrip` theorem proves all three round-trips hold simultaneously. The underlying `MessageInfo.encode_decode_roundtrip` proves the bit-field extraction at the type level.
- **Determinism theorem** proves decode of identical register states produces identical results.
- **Error exclusivity** theorems map each error variant to exactly one failure mode (`decodeSyscallId_error_iff`, `decodeMsgInfo_error_iff`).
- **Platform-configurable layout** via `SyscallRegisterLayout` — the ARM64 default maps x0=capPtr, x1=msgInfo, x2–x5=msgRegs, x7=syscallNum.

This closes the gap between machine registers and kernel transitions: nothing happens at the syscall boundary that isn't either proved or explicitly modeled as an error. The module is self-contained (no kernel subsystem imports), ensuring the decode layer cannot accidentally depend on kernel state it's supposed to validate.

### 1.6 Two-layer syscall argument decode (WS-K)

The syscall boundary uses a two-layer decode architecture that converts raw ARM64 register values into typed kernel arguments:

**Layer 1 — RegisterDecode.lean:** Converts the raw register file (x0–x7) into a flat `SyscallDecodeResult` containing `capAddr : CPtr`, `msgInfo : MessageInfo`, `syscallId : SyscallId`, and `msgRegs : Array RegValue`. This layer handles architecture-specific register layout via `SyscallRegisterLayout` and provides total decode with explicit `Except` errors. Round-trip, determinism, and error-exclusivity theorems are proved at this layer.

**Layer 2 — SyscallArgDecode.lean:** Converts the `msgRegs` array within `SyscallDecodeResult` into per-syscall typed argument structures. Seven structures cover the syscall families:

| Syscall family | Structure | Min regs | Fields |
|---|---|---|---|
| CSpace mint | `CSpaceMintArgs` | 4 | srcSlot, dstSlot, rights, badge |
| CSpace copy | `CSpaceCopyArgs` | 2 | srcSlot, dstSlot |
| CSpace move | `CSpaceMoveArgs` | 2 | srcSlot, dstSlot |
| CSpace delete | `CSpaceDeleteArgs` | 1 | targetSlot |
| Lifecycle retype | `LifecycleRetypeArgs` | 3 | targetObj, newType, size |
| VSpace map | `VSpaceMapArgs` | 4 | asid, vaddr, paddr, perms |
| VSpace unmap | `VSpaceUnmapArgs` | 2 | asid, vaddr |

A shared `requireMsgReg` helper provides safe indexing with `invalidMessageInfo` on insufficient registers. All decode functions are pure `Except KernelError T` — no state access, no side effects. Seven encode functions provide the inverse mapping for round-trip proofs (`decode_layer2_roundtrip_all`).

**Dispatch integration:** `dispatchWithCap` accepts a full `SyscallDecodeResult` and routes through the appropriate layer-2 decode function before delegating to the kernel operation. All 13 syscalls are fully wired — zero `.illegalState` stubs remain.

**Service policy:** `ServiceConfig` in `SystemState` holds policy predicates (`allowStart`, `allowStop`) for service start/stop operations, replacing the original permissive `(fun _ => true)` stubs with configuration-sourced, auditable predicates.

**IPC message population:** `extractMessageRegisters` converts `Array RegValue` → `Array Nat` with a triple bound (info.length, maxMessageRegisters, msgRegs.size). IPC send/call/reply dispatch arms populate message bodies from decoded registers instead of empty arrays.

### 1.7 IPC hot-path optimization (WS-L1)

IPC operations are the kernel's hottest paths. The WS-L audit (v0.16.8)
identified 4 redundant TCB lookups on critical IPC paths where a TCB was
fetched, used, and then fetched again in the next step.

**Pass-through TCB pattern:** `endpointQueuePopHead` was changed to return the
pre-dequeue TCB alongside the thread ID and updated state. Callers
(`endpointReceiveDual`, transport preservation theorems) receive the TCB
directly, eliminating a redundant `lookupTcb` on the hot path.

**`_fromTcb` variants:** `storeTcbIpcStateAndMessage_fromTcb` and
`storeTcbIpcState_fromTcb` accept an already-looked-up TCB and skip the
internal lookup. Equivalence theorems prove these produce identical results
to the lookup-based originals. `endpointReply`, `endpointReplyRecv`, and
`notificationWait` use these variants.

This is a zero-behavior-change refactor — all ~18 pattern-match sites across
6 invariant files were mechanically updated, with all proofs re-checked. The
optimization targets the same principle that seL4's hand-tuned C
implementation uses: avoid redundant kernel-object lookups on IPC fast paths.

### 1.8 Operations/Invariant split

Every kernel subsystem is split into two files:

| File | Contains |
|------|----------|
| `Operations.lean` | Executable transition functions (`chooseThread`, `cspaceMint`, `endpointSendDual`) |
| `Invariant.lean` | Preservation theorems and invariant definitions |

Transitions are pure state transformers that never depend on invariant proofs. Invariant proofs are external obligations, not runtime preconditions. This makes the executable model usable for testing and trace generation without proof baggage.

## 2. Data structure design: O(1) by default

seLe4n uses `Std.HashMap` and `Std.HashSet` for all kernel hot paths. This is a deliberate departure from seL4's list/array-based structures.

| Data structure | seL4 | seLe4n |
|----------------|------|--------|
| Object store | Array indexed by ID | `HashMap ObjId KernelObject` |
| CNode slots | Array indexed by slot | `HashMap Slot Capability` |
| VSpace mappings | Page table tree | `HashMap VAddr (PAddr × PagePermissions)` with W^X enforcement |
| Run queue | Linked list | `HashMap Priority (List ThreadId)` + `HashSet ThreadId` with dequeue-on-dispatch (WS-H12b) |
| CDT children | Linked list | `HashMap CdtNodeId (List CdtNodeId)` |

HashMap key uniqueness is structural (guaranteed by the data structure), so properties like `slotsUnique` become trivially true. This eliminated entire classes of proof obligations during the WS-G migration.

## 3. IPC design: intrusive dual-queue

seLe4n's IPC uses an intrusive dual-queue modeled after Linux's `hlist` pattern. Each endpoint maintains separate send and receive queues, and each TCB carries its own queue linkage:

- `queuePrev` — previous node in queue
- `queuePPrev` — pointer-to-pointer for O(1) removal (analogous to Linux `**pprev`)
- `queueNext` — next node in queue

The `queuePPrev` field enables O(1) mid-queue removal without scanning — critical for timeout handling and thread cancellation. The dual-queue (separate send/receive queues per endpoint) eliminates the direction-tagged single queue used by seL4, making queue invariants simpler.

WS-H5 formalized this with `intrusiveQueueWellFormed` and `tcbQueueLinkIntegrity`, with 13 preservation theorems covering all queue operations.

WS-L1 (v0.16.9) eliminated 4 redundant TCB lookups on IPC hot paths by returning the pre-dequeue TCB from `endpointQueuePopHead` and adding `_fromTcb` variants of store operations with equivalence theorems. This avoids O(log n) HashMap lookups on every endpoint receive, reply, and notification wait — zero new preservation lemmas needed.

## 4. Capability derivation tree: node-stable CDT

seL4's CDT uses mutable doubly-linked lists. seLe4n replaces this with a node-stable design:

- **Derivation edges** connect stable node IDs, not mutable slot pointers.
- **Bidirectional maps** (`cdtSlotNode`, `cdtNodeSlot`) link slots to nodes.
- **`cspaceMove`** updates slot-to-node ownership without rewriting CDT edges.
- **`childMap : HashMap CdtNodeId (List CdtNodeId)`** gives O(1) children lookup.
- **`descendantsOf`** runs in O(n+e) via DFS with `HashSet` visited tracking.

This eliminates dangling-pointer hazards and makes revocation semantics cleaner: `cspaceRevokeCdtStrict` reports the first descendant deletion failure with offending slot context.

## 5. Information flow: N-domain configurable flow policy

seL4 uses a binary high/low partition. seLe4n generalizes to a parameterized N-domain framework with two complementary systems:

- **Legacy `SecurityLabel`** — two-dimensional product label (confidentiality × integrity) with four fixed security classes, providing backward-compatible Bell-LaPadula/Biba semantics.
- **Generic `SecurityDomain`** — Nat-indexed domain identifier with pluggable `DomainFlowPolicy` supporting arbitrary domain counts and custom flow relations (linear order, flat lattice, or application-specific policies).

The legacy 2D system embeds into the generic N-domain system via `embedLegacyLabel` with a proven flow-preservation theorem. `computeObservableSet` precomputes visible objects using `HashSet ObjId`, and `projectStateFast` uses O(1) membership checks. The `projectStateFast_eq` theorem proves equivalence with the naive projection.

## 6. Milestone slicing strategy

seLe4n builds incrementally through milestone slices:

| Milestone | Focus | What hardens |
|-----------|-------|-------------|
| Bootstrap | Foundation types, monad, error taxonomy | Type discipline |
| M1 | Scheduler transitions + invariants | State machine semantics |
| M2 | Capability CSpace + CDT | Authority model |
| M3/M3.5 | IPC + scheduler coherence | Cross-subsystem handshake |
| M4-A/M4-B | Lifecycle retype | Object creation/mutation |
| M5 | Service orchestration | Component lifecycle |
| M6 | Architecture boundary | Platform abstraction |
| M7 | Audit remediation | Production hardening |

Each slice follows the same loop: implement transitions, prove invariants, add executable evidence, anchor in tests, synchronize docs. No slice redesigns the layers below it. When WS-G migrated all data structures to HashMap, each subsystem was migrated independently (G1–G9) with the rest of the kernel unchanged.

## 7. Platform abstraction: typeclass-based binding

The `PlatformBinding` typeclass decouples kernel semantics from hardware:

- `RuntimeBoundaryContract` — runtime invariants the platform guarantees
- `BootBoundaryContract` — initial state the bootloader provides
- `InterruptBoundaryContract` — interrupt delivery guarantees

The simulation platform (`Platform/Sim/`) provides permissive contracts for testing. The RPi5 platform (`Platform/RPi5/`) provides substantive hardware-specific contracts (WS-H15b: SP-preservation register stability, GIC-400 IRQ range validation, MMIO disjointness proof, empty-initial-state boot checks). Both platforms provide concrete `AdapterProofHooks` instantiations (WS-H15d) grounding the adapter preservation chain end-to-end. Kernel logic is identical in both — only platform contracts differ.

## 8. Syscall argument decode: register-sourced authority (WS-J1)

The current model passes syscall arguments as pre-typed Lean parameters directly
to `api*` wrappers. Real ARM64 hardware delivers syscall arguments in
general-purpose registers (x0–x7), and the kernel must decode these raw machine
words into typed references before any authority check can proceed.

WS-J1 addresses this modeling gap in 6 phases (J1-A through J1-F):

1. **Typed register wrappers** (WS-J1-A — **completed**): `RegName` and
   `RegValue` are now wrapper structures (`structure RegName where val : Nat` /
   `structure RegValue where val : Nat`) with full instance suites
   (`DecidableEq`, `Hashable`, `LawfulHashable`, `EquivBEq`, `LawfulBEq`,
   `Repr`, `ToString`, `ofNat`/`toNat`, roundtrip/injectivity proofs), matching
   the 15 existing typed identifiers. All 10 machine lemmas re-proved.
   Zero sorry/axiom. Zero behavior change.
2. **Register decode layer** (WS-J1-B — **completed**, v0.15.5): `RegisterDecode.lean`
   provides total, deterministic functions that convert raw register
   words into typed kernel references (`CPtr`, `MessageInfo`, `SyscallId`),
   with round-trip lemmas, determinism theorem, and error exclusivity proofs.
3. **Syscall entry point** (WS-J1-C — **completed**, v0.15.6): `syscallEntry` reads
   arguments from the current thread's register context and dispatches through
   the decode layer to `api*` wrappers via `SyscallGate`/`syscallInvoke`.
4. **Invariant/NI integration** (WS-J1-D — **completed**, v0.15.8):
   `registerDecodeConsistent` predicate, invariant preservation through
   `syscallEntry`, NI bridge theorems (`syscallDecodeError`, `syscallDispatchHigh`).
5. **Testing and trace evidence** (WS-J1-E — **completed**, v0.15.9): 18 negative
   decode tests, 5 register-decode trace scenarios, 2 operation-chain tests,
   13 Tier 3 invariant surface anchors.
6. **CdtNodeId cleanup** (WS-J1-F — **completed**, v0.15.10): Replaced
   `abbrev CdtNodeId := Nat` with `structure CdtNodeId where val : Nat`,
   added full instance suite (`DecidableEq`, `Hashable`, `LawfulHashable`,
   `EquivBEq`, `LawfulBEq`, `Repr`, `ToString`, `Inhabited`, `ofNat`/`toNat`),
   fixed downstream compilation, documentation synchronized. All 16 kernel
   identifiers are now typed wrappers. **WS-J1 portfolio fully completed.**

```
User space → hardware trap → RegisterDecode.decodeSyscallArgs → syscallEntry
    → SyscallGate → api* wrapper → internal kernel operation
```

The existing `api*` functions remain as the internal kernel API. `syscallEntry`
models the user-space boundary where untrusted register values become trusted
kernel references — exactly where real-world confusion attacks occur.

**WS-K extension (completed, v0.16.0–v0.16.8):** The decode architecture uses a
two-layer design. **Layer 1 completed (K-A, v0.16.0):**
`RegisterDecode.decodeSyscallArgs` now extracts raw message register values
(x2–x5 on ARM64) into `SyscallDecodeResult.msgRegs` in a single
validate-and-read pass via `Array.mapM`. The `decodeMsgRegs_length` theorem
proves the output array size equals the layout's message register count. Layer 2
(completed, K-B v0.16.1): `SyscallArgDecode.lean` converts raw `msgRegs` values
into per-syscall typed argument structures (e.g., `CSpaceMintArgs`, `VSpaceMapArgs`)
via a shared `requireMsgReg` bounds-checked helper, with 7 determinism and 7
error-exclusivity theorems, enabling full dispatch for all 13 syscalls. **Layer 3
(completed, K-C v0.16.2):** `dispatchWithCap` now accepts `SyscallDecodeResult`
(not just `SyscallId`), enabling CSpace dispatch arms to decode per-syscall
arguments from `msgRegs`. All 4 CSpace syscalls (`cspaceMint`, `cspaceCopy`,
`cspaceMove`, `cspaceDelete`) are fully wired through dispatch with 4 delegation
theorems proved. **Layer 4 (completed, K-D v0.16.3):** Lifecycle and VSpace
syscall dispatch — all 3 remaining `.illegalState` stubs replaced with full
dispatch logic. `objectOfTypeTag` maps raw type tags to default `KernelObject`
constructors (dedicated `invalidTypeTag` error variant for unrecognized tags);
`lifecycleRetypeDirect` accepts pre-resolved capabilities (avoiding
double lookup); `PagePermissions.ofNat`/`toNat` provides bitfield codec with
round-trip proof. 3 delegation theorems proved (`lifecycleRetype`, `vspaceMap`,
`vspaceUnmap`). All 13 syscalls now fully dispatch through `dispatchWithCap`.
**Layer 5 (completed, K-E v0.16.4):** Service policy and IPC message population.
`ServiceConfig` in `SystemState` replaces `(fun _ => true)` stubs — service
start/stop dispatch reads configurable policy predicates from
`st.serviceConfig.allowStart`/`allowStop`. `extractMessageRegisters` converts
decoded `Array RegValue` to `Array Nat` (matching `IpcMessage.registers` type)
with triple bound (`info.length`, `maxMessageRegisters`, `msgRegs.size`); `.send`,
`.call`, `.reply` dispatch arms now populate message bodies instead of empty arrays.
5 delegation theorems proved; `extractMessageRegisters_length` and
`extractMessageRegisters_ipc_bounded` lemmas ensure IPC message boundedness.
**Layer 6 (completed, K-F v0.16.5):** Round-trip proofs, preservation composition,
and NI integration. 7 encode functions + 7 round-trip theorems close the layer-2
decode contract. `extractMessageRegisters_roundtrip` closes the layer-1 extraction
gap. `dispatchWithCap_layer2_decode_pure` proves decode depends only on `msgRegs`.
`retypeFromUntyped_preserves_lowEquivalent` completes the last deferred NI proof.
**Layer 7 (completed, K-G v0.16.7):** Lifecycle NI proof completion.
`lifecycleRevokeDeleteRetype_preserves_lowEquivalent` completes the deferred
composed lifecycle NI proof. `NonInterferenceStep` extended to 34 constructors.
`syscallNI_coverage_witness` confirms all 34 NI constructors are exhaustive. See
[`AUDIT_v0.15.10_SYSCALL_COMPLETION_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.15.10_SYSCALL_COMPLETION_WORKSTREAM_PLAN.md).

## 9. Testing: obligation-based coverage

seLe4n defines coverage as **obligation coverage**: every transition, error path, and invariant component must have both a theorem and a fixture witness.

| Tier | Gate | What it catches |
|------|------|----------------|
| 0 | Hygiene | Forbidden markers (`sorry`/`axiom`), import leaks, fixture isolation |
| 1 | Build | Type errors, proof failures, theorem compilation |
| 2 | Trace + Negative | Semantic regressions, missing error handling |
| 3 | Surface anchors | Missing theorems, dropped definitions, stale docs |

Tier 3 is the key innovation: it checks that named theorems and definitions still exist after refactors. If you rename `chooseThread_preserves_schedulerInvariantBundle`, Tier 3 fails.

## 10. Related chapters

- [Architecture & Module Map](03-architecture-and-module-map.md) — module responsibilities and dependency flow
- [Kernel Performance Optimization](08-kernel-performance-optimization.md) — WS-G technical breakdown
- [Proof and Invariant Map](12-proof-and-invariant-map.md) — theorem inventory and naming conventions
- [Specification & Roadmap](05-specification-and-roadmap.md) — milestone history and contracts
