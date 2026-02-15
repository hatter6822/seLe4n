# Codebase Reference (Developer-Facing)

This chapter is a practical map of the current Lean codebase so developers can reason about where
semantics live, where proofs live, and how to evolve modules without breaking milestone contracts.

## 1. Repository-level structure

- `SeLe4n.lean`
  - package export root; re-exports the public model + kernel API surface.
- `Main.lean`
  - executable scenario integration trace used in Tier 2 smoke checks.
- `SeLe4n/`
  - foundational model, transition, and proof modules.

## 2. Foundation layer

### `SeLe4n/Prelude.lean`

Purpose:

- defines core ID aliases (`ObjId`, `ThreadId`, `CPtr`, etc.),
- defines `KernelM`, a small state+error monad for executable transitions.

Why it matters:

- all kernel operations and proof statements ultimately rely on these type aliases and monadic
  conventions.

Design notes:

- aliases remain architecture-neutral (`Nat`) intentionally to keep early slices focused on
  semantic correctness over representation detail.

### `SeLe4n/Machine.lean`

Purpose:

- defines abstract machine state (`RegisterFile`, `MachineState`),
- provides pure primitive update/read helpers (`readReg`, `writeReg`, `readMem`, `writeMem`, etc.).

Why it matters:

- allows transitions to carry machine context while keeping proof effort concentrated on kernel
  object semantics.

## 3. Object/state modeling layer

### `SeLe4n/Model/Object.lean`

Primary contents:

- capability rights + capability target model,
- TCB model with M3.5 IPC-visible thread state (`ready`, `blockedOnSend`, `blockedOnReceive`),
- endpoint model (`state`, queue, optional waiting receiver),
- CNode structure and slot operations (`lookup`, `insert`, `remove`, local revoke helper),
- `KernelObject` sum type (`tcb`, `endpoint`, `cnode`).

Reasoning value:

- central place where object semantics are typed and constrained before transition code applies
  updates.

### `SeLe4n/Model/State.lean`

Primary contents:

- `KernelError`, `SchedulerState`, `SystemState`, `SlotRef`.
- global object lookup/store transitions (`lookupObject`, `storeObject`, `setCurrentThread`).
- typed CSpace helpers (`lookupCNode`, `lookupSlotCap`, `ownsSlot`, `ownedSlots`) + local lemmas.

Reasoning value:

- provides reusable typed access patterns; reduces repeated object-store pattern matching in kernel
  transitions and theorem scripts.

## 4. Scheduler layer (M1)

### `SeLe4n/Kernel/Scheduler/Invariant.lean`

Core invariants:

1. `runQueueUnique`
2. `currentThreadValid`
3. `queueCurrentConsistent`
4. composed alias bundle `schedulerInvariantBundle`

Design intent:

- strict queue/current consistency policy today (current must appear in runnable list).
- aliases are used so milestone naming can evolve without breaking theorem call sites.

### `SeLe4n/Kernel/Scheduler/Operations.lean`

Primary transitions:

- `chooseThread`
- `schedule`
- `handleYield`

Proof style:

- case-split over runnable queue and object lookup shape,
- preserve each invariant component,
- compose component proofs into bundle-level preservation entrypoints.

## 5. Capability layer (M2)

### `SeLe4n/Kernel/Capability/Operations.lean`

Primary semantics:

- slot lookup/insert (`cspaceLookupSlot`, `cspaceInsertSlot`),
- minting with rights attenuation (`cspaceMint`, `rightsSubset`, `mintDerivedCap`),
- lifecycle transitions (`cspaceDeleteSlot`, `cspaceRevoke`).

Authority modeling:

- attenuation + local revoke semantics intentionally scoped to current slice constraints.

### `SeLe4n/Kernel/Capability/Invariant.lean`

Core invariant components:

1. `cspaceSlotUnique`
2. `cspaceLookupSound`
3. `cspaceAttenuationRule`
4. `lifecycleAuthorityMonotonicity`

Composition surfaces:

- `capabilityInvariantBundle`
- `m3IpcSeedInvariantBundle`
- `m35IpcSchedulerInvariantBundle`

Cross-layer role:

- composes scheduler + capability + IPC invariants while preserving milestone-wise theorem naming
  conventions.

## 6. IPC layer (M3/M3.5)

### `SeLe4n/Kernel/IPC/Invariant.lean`

Primary transitions:

- `endpointSend`
- `endpointAwaitReceive`
- `endpointReceive`

Core invariant surfaces:

- endpoint-local validity (`endpointQueueWellFormed`, `endpointObjectValid`, `endpointInvariant`),
- system-level IPC validity (`ipcInvariant`),
- scheduler coherence predicates for M3.5 handshake contract:
  - `runnableThreadIpcReady`,
  - `blockedOnSendNotRunnable`,
  - `blockedOnReceiveNotRunnable`,
  - composed `ipcSchedulerContractPredicates`.

Proof organization:

- local helper lemmas for `storeObject` effects,
- transition-specific preservation theorems,
- bundle-level preservation theorems reusing local components.

## 7. API and executable integration

### `SeLe4n/Kernel/API.lean`

Purpose:

- compatibility barrel re-exporting kernel surfaces for client imports.

### `Main.lean`

Purpose:

- constructs bootstrap object graph,
- executes scheduler/capability/IPC scenario chain,
- emits trace lines validated by Tier 2 fixture checks.

## 8. How to reason about changes safely

When editing a module, apply this map:

1. identify which milestone contract the file owns,
2. identify which composed bundle references that contract,
3. add/adjust local helper lemmas near transition changes,
4. preserve theorem-entrypoint naming shape,
5. update docs + fixture/test anchors in same commit range.

## 9. Typical developer navigation patterns

- **Need to add a new transition?**
  - start in `Model/Object` or `Model/State` for data model updates,
  - implement transition in the relevant kernel subsystem,
  - add invariant component + preservation theorem,
  - update composed bundle if needed.

- **Need to understand an existing proof failure?**
  - inspect transition-local helper lemmas first,
  - then invariant component theorem,
  - then composed bundle theorem that imports those components.

- **Need to adjust executable scenario behavior?**
  - update `Main.lean`,
  - run Tier 2 trace check,
  - update fixture lines intentionally and document rationale.
