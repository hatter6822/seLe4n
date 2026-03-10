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

### 1.5 Operations/Invariant split

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

## 8. Testing: obligation-based coverage

seLe4n defines coverage as **obligation coverage**: every transition, error path, and invariant component must have both a theorem and a fixture witness.

| Tier | Gate | What it catches |
|------|------|----------------|
| 0 | Hygiene | Forbidden markers (`sorry`/`axiom`), import leaks, fixture isolation |
| 1 | Build | Type errors, proof failures, theorem compilation |
| 2 | Trace + Negative | Semantic regressions, missing error handling |
| 3 | Surface anchors | Missing theorems, dropped definitions, stale docs |

Tier 3 is the key innovation: it checks that named theorems and definitions still exist after refactors. If you rename `chooseThread_preserves_schedulerInvariantBundle`, Tier 3 fails.

## 9. Related chapters

- [Architecture & Module Map](03-architecture-and-module-map.md) — module responsibilities and dependency flow
- [Kernel Performance Optimization](08-kernel-performance-optimization.md) — WS-G technical breakdown
- [Proof and Invariant Map](12-proof-and-invariant-map.md) — theorem inventory and naming conventions
- [Specification & Roadmap](05-specification-and-roadmap.md) — milestone history and contracts
