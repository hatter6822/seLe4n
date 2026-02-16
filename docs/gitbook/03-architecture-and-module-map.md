# Architecture and Module Map

## 1. Layered model structure

seLe4n uses a layered architecture so semantic changes can be reviewed and proved incrementally.

1. **Foundations (`Prelude`, `Machine`)**
   - core type aliases and error/state monad shape,
   - abstract machine state helpers used by kernel transitions.

2. **Typed object/state model (`Model/Object`, `Model/State`)**
   - kernel object universe and lifecycle-relevant object fields,
   - global object store, scheduler state, typed lookup/store helpers,
   - shared error taxonomy (`KernelError`, including explicit illegal-state/authority lifecycle branches).

3. **Kernel transition subsystems (`Kernel/Scheduler`, `Kernel/Capability`, `Kernel/IPC`, `Kernel/Lifecycle`, `Kernel/Service`)**
   - executable transition definitions,
   - local invariants and transition-preservation theorem entrypoints.

4. **Cross-subsystem composition (`Kernel/Capability/Invariant` + IPC links)**
   - milestone bundles and composed preservation theorem surfaces.

5. **Executable integration (`Main.lean`)**
   - scenario trace demonstrating composed behavior under current milestone stage.

## 2. Module responsibilities by file

### Foundations

- `SeLe4n/Prelude.lean`
  - object/thread IDs and kernel monad contract used globally.
- `SeLe4n/Machine.lean`
  - machine registers, memory abstraction, and pure update/read helpers.

### Model

- `SeLe4n/Model/Object.lean`
  - capability rights/targets,
  - TCB structure + IPC state,
  - endpoint protocol fields,
  - CNode slot store and local revoke helper,
  - `KernelObject` discriminated union.

- `SeLe4n/Model/State.lean`
  - `SystemState` (machine + object store + scheduler + IRQ handlers),
  - `lookupObject` / `storeObject` / `setCurrentThread`,
  - typed CSpace lookup/ownership helpers and supporting lemmas.

### Scheduler subsystem

- `SeLe4n/Kernel/Scheduler/Invariant.lean`
  - M1 component invariants and scheduler bundle alias.
- `SeLe4n/Kernel/Scheduler/Operations.lean`
  - scheduling transitions + preservation theorem families.

### Capability subsystem

- `SeLe4n/Kernel/Capability/Operations.lean`
  - CSpace transitions (`lookup`, `insert`, `mint`, `delete`, `revoke`).
- `SeLe4n/Kernel/Capability/Invariant.lean`
  - capability invariants + composed milestone bundles + IPC/scheduler composition links.

### IPC subsystem

- `SeLe4n/Kernel/IPC/Invariant.lean`
  - endpoint transitions (`send`, `awaitReceive`, `receive`),
  - endpoint + IPC invariants,
  - scheduler-coherence contract predicates,
  - preservation theorem entrypoints.

### Lifecycle subsystem

- `SeLe4n/Kernel/Lifecycle/Operations.lean`
  - deterministic lifecycle retype transition (`lifecycleRetypeObject`),
  - explicit illegal-state / illegal-authority error branching and local theorem entrypoints.
- `SeLe4n/Kernel/Lifecycle/Invariant.lean`
  - step-3 lifecycle invariant components and bundle layering,
  - explicit split between identity/aliasing and capability-reference constraints.

### Service subsystem

- `SeLe4n/Kernel/Service/Operations.lean`
  - deterministic orchestration transitions (`serviceStart`, `serviceStop`, `serviceRestart`),
  - explicit `policyDenied`, `dependencyViolation`, and `illegalState` branches,
  - staged-order theorem surface for restart composition.

### API + executable

- `SeLe4n/Kernel/API.lean`
  - compatibility barrel import surface for clients.
- `Main.lean`
  - concrete scenario execution and trace output validated by fixture checks.

## 3. Dependency flow

Conceptual dependency direction:

`Prelude/Machine` → `Model` → `Scheduler/Capability/IPC transitions` → `Invariant composition` → `Main trace`

This direction should be preserved to prevent proof cycles and maintain module readability.

## 4. Cross-cutting architectural rules

1. transition behavior must be deterministic and explicit,
2. invariant components should be named and localized,
3. bundle composition should remain additive,
4. theorem naming should remain discoverable,
5. docs and fixtures should evolve with semantics in the same change set.
