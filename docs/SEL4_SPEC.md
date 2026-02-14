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

The immediate next step is to complete a **Scheduler Invariant Bundle v1** with explicit policy and
proof coverage. The repository shall implement and prove:

1. ✅ Runnable queue uniqueness (no duplicate TIDs in `runQueue`).
2. ⏳ Current-thread object validity (if `currentThread = some tid`, object lookup resolves to a
   `TCB`).
3. ⏳ Queue/current consistency under an explicitly chosen policy:
   - **strict policy**: current thread must be in `runQueue`, or
   - **relaxed policy**: current thread may be absent while blocked/idle.
4. Preservation of the composed scheduler invariant bundle for:
   - `chooseThread`,
   - `schedule`,
   - `handleYield`.

### 3.3 M1 implementation boundary (normative)

Within this step, changes should stay inside scheduler semantics and proofs. The following are in
scope:

- adding helper predicates/lemmas needed to define and prove scheduler invariants,
- minor state-accessor refactors required for theorem clarity,
- executable examples in `Main.lean` that exercise affected transitions.

The following are out-of-scope for this step even if they appear adjacent:

- introducing new kernel object classes,
- extending capability operations beyond what scheduler proofs consume,
- architecture-specific behavior (timer interrupts, MMU details, etc.).

### 3.4 Deferred (explicitly out-of-scope for M1)

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

The next step (M1 Scheduler Invariant Bundle v1) is complete when all checks below are satisfied.
Current proof debt after landing step 1: complete items (2) and (3), then discharge composed preservation for all three transitions:

### 6.1 Functional and proof acceptance criteria

1. A single composed scheduler invariant entrypoint exists in `SeLe4n.Kernel.API` and includes at
   least:
   - runnable queue uniqueness,
   - current-thread object validity,
   - queue/current consistency with the documented policy.
2. Each component invariant has at least one dedicated preservation lemma or helper theorem.
3. Theorems show preservation of the composed invariant for:
   - `chooseThread`,
   - `schedule`,
   - `handleYield`.
4. The policy choice (strict vs. relaxed) is stated in comments/doc text close to the invariant
   definition and reflected in theorem statements.

### 6.2 Build and executability acceptance criteria

5. `lake build` passes with no new `axiom` introduced to bypass missing proofs.
6. `lake exe sele4n` (or equivalent `#eval` path used by `Main.lean`) still demonstrates at least
   one concrete scheduler transition from an explicit state.

### 6.3 Documentation acceptance criteria

7. `docs/SEL4_SPEC.md` and `docs/DEVELOPMENT.md` both describe:
   - current invariant bundle scope,
   - remaining proof gaps (if any),
   - next intended increment.

Evidence sources:

- theorem statements/proofs in `SeLe4n/Kernel/API.lean`,
- executable path in `Main.lean`,
- build/execution output from local checks.

### 6.4 Definition of done for this step

This step should be marked complete only when all acceptance criteria pass in one commit range,
and no open TODOs remain for the three targeted transitions.

## 7. Roadmap

### 7.1 M1 (current): scheduler integrity

Incremental plan:

1. Lock invariant policy (strict vs. relaxed queue/current consistency).
2. Encode component predicates and compose the bundle entrypoint.
3. Prove preservation for `chooseThread`.
4. Prove preservation for `schedule`.
5. Prove preservation for `handleYield`.
6. Consolidate helper lemmas and remove redundant proof scaffolding.
7. Update docs to record what is complete and what remains.

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
