# seL4-in-Lean Specification and Milestone Plan

## 1. Purpose and intent

This document captures the current specification baseline for seLe4n after bootstrap completion
and defines the immediate plan for Milestone M1.

The project now targets a disciplined progression from an executable abstract kernel model to a
proof-oriented scheduler and capability semantics stack.

Primary outcomes for this revision:

- codify that bootstrap requirements are complete,
- establish explicit M1 acceptance criteria,
- tighten change-control expectations for upcoming milestones.

## 2. Definitions

- **Bootstrap milestone**: the initial semantic core with executable transitions and at least one
  machine-checked invariant-preservation proof.
- **M1 (Scheduler Integrity)**: the next milestone focused on strengthening scheduler invariants
  and proving preservation across core scheduling transitions.
- **Executable semantics**: Lean definitions evaluable via `lake exe sele4n` or `#eval` without
  axiomatic escape hatches.
- **Kernel transition**: a `Kernel` computation from `SystemState` to either `(result,
  SystemState)` or `KernelError`.
- **Invariant bundle**: a compositional predicate over `SystemState` made from smaller,
  independently provable properties.

## 3. Scope and status

### 3.1 Bootstrap milestones (complete)

1. ✅ Core type aliases for kernel identifiers.
2. ✅ Abstract machine state (`RegisterFile`, `MachineState`).
3. ✅ Kernel object universe (`TCB`, `Endpoint`, `CNode`, capabilities).
4. ✅ Global system state (`SystemState`) with object store and scheduler fields.
5. ✅ Basic kernel monad (`KernelM`) and error type (`KernelError`).
6. ✅ Initial scheduler transitions (`chooseThread`, `schedule`, `handleYield`).
7. ✅ Preservation theorem entrypoint for scheduler well-formedness.

### 3.2 Milestone M1 scope (in progress)

The repository shall next implement and prove:

1. Runnable queue uniqueness.
2. Current-thread object validity (if current is set, it refers to a TCB object).
3. Queue/current consistency (policy-driven; choose and document strict or relaxed form).
4. Preservation of the strengthened invariant bundle for:
   - `chooseThread`,
   - `schedule`,
   - `handleYield`.

### 3.3 Deferred (explicitly out-of-scope for M1)

- virtual memory and architecture-specific MMU semantics,
- full capability derivation tree and revoke/delete cascade behavior,
- full IPC/reply-cap lifecycle correctness,
- untyped memory allocation and retype proofs,
- Isabelle/HOL correspondence and refinement-to-C obligations.

## 4. Architecture and module responsibilities

### 4.1 Core layers

- `SeLe4n.Prelude`: identifiers and base kernel monad infrastructure.
- `SeLe4n.Machine`: machine state/register/memory abstractions.
- `SeLe4n.Model.Object`: kernel object and capability model.
- `SeLe4n.Model.State`: global state, scheduler state, and utility accessors.
- `SeLe4n.Kernel.API`: transition semantics and invariant theorems.

### 4.2 Documentation layers

- `docs/SEL4_SPEC.md`: normative scope and acceptance requirements.
- `docs/DEVELOPMENT.md`: implementation workflow and review checks.

## 5. Normative requirements

The project shall preserve the following through M1:

1. `lake build` succeeds from a clean checkout.
2. `Main.lean` continues to demonstrate executable scheduler behavior.
3. No `axiom` is introduced to bypass missing proofs.
4. Every new scheduler invariant has:
   - a clear definition,
   - at least one proof use-site,
   - placement in the composed invariant entrypoint.
5. Milestone changes that affect scope or acceptance criteria update this document in the same
   commit.

## 6. Acceptance criteria and evidence mapping

M1 is complete when all checks below are satisfied:

1. Strengthened scheduler invariants are present in `SeLe4n.Kernel.API`.
2. Theorems show preservation for `chooseThread`, `schedule`, and `handleYield`.
3. `lake build` passes with no axiomatic bypass introduced.
4. `Main.lean` still runs a concrete transition path from an explicit bootstrap state.
5. Documentation (`SEL4_SPEC.md` + `DEVELOPMENT.md`) reflects implemented behavior.

Evidence sources:

- theorem statements/proofs in `SeLe4n/Kernel/API.lean`,
- executable path in `Main.lean`,
- build output from local checks.

## 7. Roadmap

### 7.1 M1 (current): scheduler integrity

- compose scheduler invariant bundle,
- prove preservation across core scheduling transitions,
- add small helper lemmas to keep proof scripts modular.

### 7.2 M2: capability and CSpace semantics

- typed CSpace tree model,
- lookup/mint/revoke/delete operations,
- authority monotonicity and reachability constraints.

### 7.3 M3: IPC semantics

- endpoint send/receive transitions,
- queue discipline invariants,
- call/reply correspondence lemmas.

### 7.4 M4: memory/object lifecycle

- untyped memory + retype operations,
- object creation/deletion safety,
- alignment/disjointness constraints.

### 7.5 M5+: refinement and correspondence

- abstract-to-lower-level refinement relation,
- staged correspondence strategy toward external seL4 artifacts.

## 8. Change control

- Keep milestone status conservative; only mark complete when code and proofs validate.
- Any regression in completed criteria must be reflected immediately in this spec.
- Avoid speculative requirement text that lacks code-path ownership.
