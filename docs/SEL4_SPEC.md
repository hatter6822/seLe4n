# seL4-in-Lean Bootstrap Specification

## 1. Purpose and intent

This specification defines the **bootstrap milestone** for a Lean 4 formalization of the seL4
microkernel. The goal is to establish a small, executable, and provable core model that can be
extended toward richer semantics and stronger correctness guarantees.

The bootstrap milestone optimizes for:

- a coherent abstract state machine,
- deterministic transition semantics,
- and at least one machine-checked invariant preservation proof.

## 2. Definitions

- **Bootstrap milestone**: the initial repository state that provides a working semantic core, not
  full kernel fidelity.
- **Executable semantics**: Lean definitions that can be evaluated (e.g., through `#eval` or a
  runnable `Main.lean`) without introducing axioms.
- **Kernel transition**: a state transformer in `KernelM` that maps an input `SystemState` to either
  `(result, SystemState)` or `KernelError`.
- **Invariant**: a predicate over `SystemState` that must be preserved by designated transitions.

## 3. Scope

### 3.1 In scope

The following are required in this milestone:

1. ~~Core type aliases for kernel identifiers.~~
2. ~~Abstract machine state (`RegisterFile`, `MachineState`).~~
3. ~~Kernel object universe (`TCB`, `Endpoint`, `CNode`, capabilities).~~
4. Global system state (`SystemState`) with object store and scheduler fields.
5. Basic kernel monad (`KernelM`) and error type (`KernelError`).
6. Initial scheduler transitions (`chooseThread`, `schedule`, `handleYield`).
7. A proof that at least one scheduler transition preserves a base invariant.

### 3.2 Out of scope

The following are explicitly deferred to later milestones:

- architecture-specific MMU/page-table behavior,
- full capability derivation tree constraints,
- interrupt-controller hardware detail,
- refinement to C implementation artifacts,
- compatibility proofs with Isabelle/HOL seL4 developments.

These deferred items are now tracked as named follow-on milestones in §7.

## 3.3 Bootstrap milestone status review

Code review against current sources confirms that **items 1–3 are implemented** and align with the
bootstrap intent:

- **Item 1 (identifier aliases)**: `SeLe4n.Prelude` defines the core ID/value aliases used across
  the model (`ObjId`, `ThreadId`, `DomainId`, `Priority`, `Irq`, `CPtr`, `Slot`, `Badge`, `ASID`,
  `VAddr`, `PAddr`).
- **Item 2 (abstract machine state)**: `SeLe4n.Machine` defines `RegisterFile` and `MachineState`
  as pure data structures, with inhabited defaults and basic read/write helpers for registers and
  memory.
- **Item 3 (object universe)**: `SeLe4n.Model.Object` defines capabilities, capability targets,
  `TCB`, `Endpoint`, `CNode`, and the `KernelObject` sum type.

Items **4–7 remain open** in this checklist for milestone-tracking purposes, even where partial
infrastructure exists in the codebase. They should only be crossed out once the full acceptance
intent (including end-to-end validation/proof expectations) is met.

## 4. Architecture and module responsibilities

### 4.1 Type layer (`SeLe4n.Prelude`)

Defines primitive identifier aliases and reusable monadic/error infrastructure used by transition
functions.

### 4.2 Machine layer (`SeLe4n.Machine`)

Represents abstract register and memory state as pure data and provides a stable target for future
trap/context-switch semantics.

### 4.3 Object/state layer (`SeLe4n.Model.Object`, `SeLe4n.Model.State`)

Defines kernel objects and global state:

- `Capability` (typed target, rights + optional badge),
- payload types (`TCB`, `Endpoint` with queue state, `CNode` with slots),
- `KernelObject` sum type,
- `SystemState` including machine state, object heap, scheduler metadata, and IRQ handlers.

### 4.4 Kernel API/proof layer (`SeLe4n.Kernel.API`)

Defines:

- scheduler-focused invariants (`schedulerWellFormed`),
- composed kernel invariant (`kernelInvariant`),
- scheduling transitions,
- at least one preservation theorem (e.g., `schedule_preserves_wellFormed`).

## 5. Functional requirements

The implementation **shall** satisfy all requirements below:

1. **Buildability**: `lake build` succeeds from a clean checkout.
2. **Executability**: at least one transition path can be executed from `Main.lean`.
3. **Determinism**: transition definitions in scope are total and deterministic.
4. **Extensibility**: module boundaries permit adding semantics without cross-cutting refactors.
5. **Proof entry point**: at least one transition-preservation theorem is present and checked by Lean.

## 6. Acceptance criteria

A repository revision satisfies the bootstrap milestone when all checks below hold:

1. Source builds with the pinned toolchain and current `lakefile.toml`.
2. `Main.lean` demonstrates a concrete transition execution path.
3. Scheduler invariant predicates are defined and referenced by at least one theorem.
4. No `axiom` is introduced to bypass missing proofs in bootstrap invariants.
5. Public module organization under `SeLe4n/` remains coherent by layer (Prelude, Machine, Model,
   Kernel).

## 7. Verification roadmap (post-bootstrap)

Planned progression after bootstrap is split into explicit milestones so deferred scope can be
implemented incrementally and validated with concrete exit criteria.

### Milestone A — Invariant strengthening

- Add runnable queue uniqueness and no-duplicate constraints.
- Strengthen `current`-thread validity beyond list membership (e.g., object existence + TCB type).
- Add object-reference well-formedness predicates over capability targets.
- Exit criteria:
  - strengthened invariant bundle replaces current `kernelInvariant`,
  - preservation proofs for `chooseThread` and `schedule` are present.

### Milestone B — IPC semantics

- Model endpoint send/receive state transitions.
- Define blocking/unblocking behavior and queue updates.
- Prove basic send/receive correspondence and queue safety properties.
- Exit criteria:
  - executable IPC transition examples,
  - at least one preservation theorem involving endpoint queues.

### Milestone C — CSpace and capability safety

- Add capability lookup/update/delete operations over `CNode` structures.
- Specify capability transfer/retyping constraints (bootstrap-safe approximation first).
- Prove non-escalation properties for rights-preserving operations.
- Exit criteria:
  - API-level CSpace operations exposed,
  - capability safety theorem family added.

### Milestone D — Architecture + interrupt model

- Introduce abstract architecture layer for address translation and ASID semantics.
- Model IRQ delivery/ack transitions and scheduler interaction.
- Keep architecture details abstract enough for proof reuse before platform specialization.
- Exit criteria:
  - interrupt path executable in model,
  - proofs connecting IRQ transitions to scheduler invariants.

### Milestone E — Refinement + external alignment

- Define refinement relation from concrete machine operations to abstract kernel steps.
- Add trace/step correspondence lemmas for selected transitions.
- Align major abstractions with Isabelle/HOL seL4 concepts to reduce semantic drift.
- Exit criteria:
  - documented refinement statement with machine-checked lemmas,
  - compatibility notes mapping key terms to Isabelle/HOL artifacts.

### Milestone F — Proof architecture and maintainability

- Reorganize theorem libraries by subsystem (`Scheduler`, `IPC`, `CSpace`, `Machine`).
- Introduce reusable proof helpers and normal forms to reduce tactic duplication.
- Add CI checks to ensure theorem build remains lightweight.
- Exit criteria:
  - subsystem-oriented module tree established,
  - proof build targets documented and stable.

### Out-of-scope tracking map

Deferred item → planned milestone mapping:

- MMU/page-table behavior → **Milestone D**,
- capability derivation tree constraints → **Milestone C**,
- interrupt-controller detail → **Milestone D**,
- C artifact refinement → **Milestone E**,
- Isabelle/HOL compatibility proofs → **Milestone E**.

## 8. Non-functional requirements

- Keep model updates deterministic and total.
- Avoid `axiom` unless explicitly justified in documentation.
- Maintain fast local feedback (`lake build` should remain lightweight).
- Prefer clear naming and small compositional definitions over dense monolithic encodings.

## 9. Deliverables for this repository revision

- Lean toolchain pin (`lean-toolchain`).
- Lake package configuration (`lakefile.toml`).
- Multi-module scaffold under `SeLe4n/`.
- Executable demonstration in `Main.lean`.
- Documentation under `docs/`, including this specification.

## 10. Change control

Any future revision that changes scope, acceptance criteria, or invariant obligations should update
this document in the same commit as the corresponding code/proof changes.
