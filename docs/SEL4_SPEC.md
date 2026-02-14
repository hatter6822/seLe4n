# seL4-in-Lean Bootstrap Specification

## 1. Purpose and intent

This document defines the **bootstrap milestone** for a Lean 4 formalization of the seL4
microkernel, and records the current implementation status against that milestone.

The bootstrap milestone is intentionally narrow: establish a small abstract state machine that is
executable, deterministic, and amenable to proof-driven extension.

Primary bootstrap outcomes:

- coherent abstract state and object model,
- deterministic transition semantics for basic scheduling,
- machine-checked invariant preservation proof(s),
- a clear handoff plan into post-bootstrap milestones.

## 2. Definitions

- **Bootstrap milestone**: the initial repository state that provides a working semantic core, not
  full kernel fidelity.
- **Executable semantics**: Lean definitions that can be evaluated via `lake exe sele4n` or `#eval`
  without introducing axioms.
- **Kernel transition**: a `Kernel` computation from `SystemState` to either `(result,
  SystemState)` or `KernelError`.
- **Invariant**: a predicate over `SystemState` that designated transitions should preserve.
- **Milestone status**:
  - **Done**: implemented in code and typechecked,
  - **Partial**: present but weaker than target intent,
  - **Deferred**: intentionally excluded from bootstrap scope.

## 3. Scope and status

### 3.1 In-scope bootstrap milestones

Status is based on the repository state at the time of this spec revision.

1. ~~Core type aliases for kernel identifiers.~~ (**Done**)
2. ~~Abstract machine state (`RegisterFile`, `MachineState`).~~ (**Done**)
3. ~~Kernel object universe (`TCB`, `Endpoint`, `CNode`, capabilities).~~ (**Done**)
4. ~~Global system state (`SystemState`) with object store and scheduler fields.~~ (**Done**)
5. ~~Basic kernel monad (`KernelM`) and error type (`KernelError`).~~ (**Done**)
6. ~~Initial scheduler transitions (`chooseThread`, `schedule`, `handleYield`).~~ (**Done**)
7. ~~A proof that at least one scheduler transition preserves a base invariant.~~ (**Done**; includes end-to-end preservation for `schedule` and its `handleYield` entrypoint.)

### 3.2 Out-of-scope milestone catalog (explicitly deferred)

These are tracked to prevent accidental scope creep during bootstrap.

#### A. Virtual memory and architecture semantics

- architecture-specific MMU/page-table structures,
- ASID pool behavior and TLB interaction,
- user/kernel address-space switching rules,
- architecture-dependent trap/exception entry details.

#### B. Capability-system depth

- full capability derivation tree constraints,
- revoke/delete cascading behavior,
- mint/mutate semantics with authority attenuation proofs,
- CSpace lookup failure taxonomy matching production seL4.

#### C. IPC and synchronization completeness

- endpoint send/receive operational semantics with blocking behavior,
- notification objects and signal/wait interactions,
- reply-cap lifecycle and call/reply protocol correctness.

#### D. Memory management and object lifecycle

- untyped memory model and retype invariants,
- object allocation/deallocation proofs,
- alignment and size class constraints.

#### E. Interrupt/temporal fidelity

- interrupt-controller hardware detail,
- timer interrupt delivery and preemption model,
- deterministic interleaving model for asynchronous events.

#### F. Refinement and ecosystem compatibility

- refinement to C implementation artifacts,
- compatibility proofs with Isabelle/HOL seL4 developments,
- proof-producing translation or correspondence infrastructure.

## 4. Architecture and module responsibilities

### 4.1 Type and monad layer (`SeLe4n.Prelude`)

Defines:

- primitive identifier aliases (`ObjId`, `ThreadId`, `DomainId`, `Priority`, `Irq`, etc.),
- the bootstrap state/error monad (`KernelM`) with `Monad` instance.

### 4.2 Machine layer (`SeLe4n.Machine`)

Defines:

- abstract register and memory vocabulary (`RegName`, `RegValue`, `Memory`),
- machine state records (`RegisterFile`, `MachineState`),
- utility operations (`readReg`, `writeReg`, `readMem`, `writeMem`, `setPC`, `tick`).

### 4.3 Object and global state layer (`SeLe4n.Model.Object`, `SeLe4n.Model.State`)

Defines:

- capability-target/addressing model and rights,
- kernel object payloads (`TCB`, `Endpoint`, `CNode`),
- object universe sum type (`KernelObject`),
- global state (`SystemState`) and scheduler state,
- bootstrap kernel error channel (`KernelError`),
- utility state operations (`lookupObject`, `setCurrentThread`).

### 4.4 Kernel API and invariant layer (`SeLe4n.Kernel.API`)

Defines:

- scheduler base invariant (`schedulerWellFormed`),
- composed invariant entrypoint (`kernelInvariant`),
- scheduler transitions (`chooseThread`, `schedule`, `handleYield`),
- a current preservation theorem (`setCurrentThread_preserves_wellFormed`).

## 5. Functional requirements (normative)

The implementation **shall** satisfy all items below for bootstrap completion:

1. **Buildability**: `lake build` succeeds from a clean checkout.
2. **Executability**: at least one transition path executes from `Main.lean`.
3. **Determinism**: in-scope transitions are total, pure, and deterministic.
4. **Extensibility**: module boundaries permit adding semantics without broad refactors.
5. **Proof entry point**: at least one transition-preservation theorem is machine checked.
6. **No axiomatic bypass**: no `axiom` used to mask missing bootstrap proofs.

## 6. Acceptance criteria and evidence mapping

A revision satisfies bootstrap when **all** acceptance checks pass:

1. Builds with pinned toolchain and `lakefile.toml` configuration.
2. `Main.lean` demonstrates concrete state transition execution.
3. Scheduler invariants are defined and linked to theorem(s).
4. No `axiom` introduced for invariant obligations.
5. Layered module organization under `SeLe4n/` remains coherent.

Evidence should be maintained as:

- executable demonstration path in code (`Main.lean`),
- theorem artifacts in `SeLe4n/Kernel/API.lean`,
- CI/build command output (local and/or CI workflow).

## 7. Detailed roadmap after bootstrap

### 7.1 Near-term (Milestone M1)

- strengthen scheduler invariants:
  - runnable queue uniqueness,
  - current-thread validity against object heap,
  - optional non-empty runnable/current consistency;
- prove `schedule` preserves strengthened invariant bundle.

### 7.2 Capability and CSpace (Milestone M2)

- introduce typed CSpace tree semantics,
- add lookup/mint/revoke/delete operations,
- prove basic capability safety properties (authority monotonicity, reachability constraints).

### 7.3 IPC semantics (Milestone M3)

- endpoint send/receive state machine,
- queue discipline invariants and progress properties,
- call/reply correspondence and reply-cap validity lemmas.

### 7.4 Memory/object management (Milestone M4)

- untyped memory/retype lifecycle,
- object creation/deletion safety,
- disjointness, alignment, and aliasing invariants.

### 7.5 Refinement and correspondence (Milestone M5+)

- relation between abstract machine operations and kernel transitions,
- staged refinement toward executable low-level model,
- initial correspondence strategy with Isabelle/HOL artifacts.

## 8. Non-functional requirements

- preserve deterministic, total model updates,
- keep proof scripts maintainable and compositional,
- avoid introducing `axiom` except with explicit documented rationale,
- keep local build/test feedback fast (`lake build` baseline),
- prefer clear naming and modular namespaces.

## 9. Deliverables for this repository revision

- toolchain pin (`lean-toolchain`),
- Lake configuration (`lakefile.toml`),
- layered Lean modules under `SeLe4n/`,
- executable bootstrap path in `Main.lean`,
- specification and development documentation under `docs/`.

## 10. Change control and milestone hygiene

Any revision changing scope, acceptance criteria, or invariant obligations must update this spec in
that same commit.

Milestone markup policy:

- only strike through milestones that are fully implemented and validated,
- if implementation regresses or is shown incomplete, remove strike-through immediately,
- prefer marking nuanced states as **Partial** over optimistic completion.
