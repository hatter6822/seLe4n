# seL4-in-Lean Bootstrap Specification

## 1. Project intent

This repository initializes a formalization effort for the seL4 microkernel in Lean 4. The
initial scaffold focuses on a coherent *abstract state machine* with executable semantics and
foundational invariants, rather than full kernel behavior.

## 2. Scope of this bootstrap phase

### In scope

- Core type aliases for kernel identifiers.
- Abstract machine state (`RegisterFile`, `MachineState`).
- Kernel object universe (`TCB`, `Endpoint`, `CNode`, capabilities).
- Global system state (`SystemState`) with object store + scheduler.
- Basic kernel monad (`KernelM`) and error type (`KernelError`).
- Initial scheduler transition (`schedule`) with proof of a basic invariant.

### Out of scope (future phases)

- Architecture-specific MMU/page table semantics.
- Full capability derivation tree constraints.
- Interrupt controller details.
- Binary correctness/refinement to C implementation.
- End-to-end proof compatibility with existing Isabelle/HOL artifacts.

## 3. High-level architecture

## 3.1 Type layer (`SeLe4.Prelude`)

Defines primitive identifiers and a state/error monad used to make transition functions executable
inside Lean.

## 3.2 Machine layer (`SeLe4.Machine`)

Represents abstract register and memory state as pure data. This supports future integration of
trap handling and context switches.

## 3.3 Object and state layer (`SeLe4.Model.Object`, `SeLe4.Model.State`)

Defines kernel objects and global state:

- `Capability` with rights + optional badge.
- `TCB`, `Endpoint`, `CNode` object payloads.
- `KernelObject` sum type.
- `SystemState` with machine state, object heap, scheduler, IRQ handlers.

## 3.4 Kernel API layer (`SeLe4.Kernel.API`)

Defines:

- `schedulerWellFormed` invariant.
- `kernelInvariant` bundle (currently minimal).
- Scheduling transitions (`chooseThread`, `schedule`, `handleYield`).
- Proof `schedule_preserves_wellFormed`.

## 4. Functional requirements

1. **Buildability**: `lake build` must pass from clean checkout.
2. **Executability**: at least one transition path should run from `Main.lean`.
3. **Extensibility**: module structure must support incremental semantic enrichment.
4. **Proof entry point**: at least one state transition preservation theorem must be present.

## 5. Verification roadmap

1. Expand invariant set:
   - runnable queue uniqueness,
   - current thread validity,
   - object-reference well-formedness.
2. Add IPC semantics with send/receive matching proofs.
3. Add CSpace operations and capability safety theorems.
4. Introduce refinement relation from concrete machine operations to abstract kernel steps.
5. Add theorem grouping by subsystem with `namespace`-scoped proof libraries.

## 6. Non-functional requirements

- Keep all model updates deterministic and total.
- Avoid introducing `axiom` unless explicitly justified.
- Preserve fast feedback: build should remain quick on developer hardware.

## 7. Deliverables in this repository revision

- Lean toolchain pin (`lean-toolchain`).
- Lake package config (`lakefile.toml`).
- Multi-module library scaffold under `SeLe4/`.
- Executable demo in `Main.lean`.
- Development and specification docs under `docs/`.
