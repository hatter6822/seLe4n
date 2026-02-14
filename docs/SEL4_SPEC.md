# seL4-in-Lean Specification and Milestone Plan

## 1. Purpose and intent

This document captures the current specification baseline for seLe4n after bootstrap completion,
records closure evidence for M1, and defines the immediate plan for Milestone M2.

The project now targets a disciplined progression from an executable abstract kernel model to a
proof-oriented scheduler and capability semantics stack.

Primary outcomes for this revision:

- codify that bootstrap requirements are complete,
- record that M1 Scheduler Invariant Bundle v1 is complete with verification evidence,
- establish explicit acceptance criteria for the next implementation step (M2 foundation),
- tighten change-control expectations for upcoming milestones.

## 2. Definitions

- **Bootstrap milestone**: the initial semantic core with executable transitions and at least one
  machine-checked invariant-preservation proof.
- **M1 (Scheduler Integrity)**: completed milestone that strengthened scheduler invariants and
  proved preservation across core scheduling transitions.
- **M2 (Capability & CSpace Semantics)**: active milestone for typed CSpace operations and
  authority-safety properties.
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

### 3.2 Milestone M1 scope (complete)

M1 **Scheduler Invariant Bundle v1** is complete. Implemented and proven artifacts:

1. ✅ Runnable queue uniqueness (no duplicate TIDs in `runQueue`).
2. ✅ Current-thread object validity (if `currentThread = some tid`, object lookup resolves to a
   `TCB`).
3. ✅ Queue/current consistency under explicit strict policy.
4. ✅ Preservation of the composed scheduler invariant bundle for:
   - `chooseThread`,
   - `schedule`,
   - `handleYield`.

### 3.3 Immediate next step scope: M2 foundation slice (active)

The immediate next step is to deliver a narrow **M2 Foundation Slice: typed CSpace lookup and
mint model** that is proof-ready and does not destabilize completed scheduler results.

In-scope for this slice:

1. ~~Introduce minimal CSpace transition API surface in `SeLe4n.Kernel.API` (or a sibling kernel
   module) for:~~
   ~~- slot lookup,~~
   ~~- cap insertion/update,~~
   ~~- mint-like derivation with rights attenuation.~~
2. ~~Add state/model helpers needed to represent slot-level capability ownership without adding
   architecture-specific detail.~~
3. ~~Define a first capability-safety invariant bundle for this slice (e.g., slot uniqueness,
   lookup soundness, attenuation monotonicity).~~
4. ~~Prove preservation for at least one write transition and one read transition in the new API.~~
5. Keep `Main.lean` executable path functional; if changed, include a concrete demonstration of at
   least one CSpace operation.

Out-of-scope for this slice:

- full revoke/delete cascade semantics,
- endpoint IPC/reply-cap lifecycle,
- untyped retype/allocation semantics,
- correspondence/refinement obligations to external artifacts.

### 3.4 M2 foundation implementation boundary (normative)

Within this step, changes should stay inside CSpace/capability semantics and proofs. The following
are in scope:

- adding helper predicates/lemmas needed to define and prove capability invariants,
- minor state-accessor refactors required for theorem clarity,
- executable examples in `Main.lean` that exercise affected transitions.

The following are out-of-scope for this step even if they appear adjacent:

- introducing new architecture-specific object classes,
- extending capability operations beyond the M2 foundation slice,
- architecture-specific behavior (timer interrupts, MMU details, etc.).

### 3.5 Deferred (explicitly out-of-scope for M2 foundation slice)

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

The project shall preserve the following through M2 foundation:

1. `lake build` succeeds from a clean checkout.
2. `Main.lean` continues to demonstrate executable transition behavior.
3. No `axiom` is introduced to bypass missing proofs.
4. Every new capability invariant has:
   - a clear definition,
   - at least one proof use-site,
   - placement in the composed invariant entrypoint.
5. Milestone changes that affect scope or acceptance criteria update this document in the same
   commit.

## 6. Acceptance criteria and evidence mapping

The next step is **M2 Foundation Slice: typed CSpace lookup and mint model**. This step is
complete when all checks below are satisfied.

### 6.1 M2 functional and proof acceptance criteria

1. A composed capability invariant bundle entrypoint exists and includes at least:
   - slot-level uniqueness/no-alias property for the modeled structure,
   - lookup soundness (resolved slot points to the modeled capability),
   - rights attenuation monotonicity for mint/derive-style operations.
2. Each invariant component has at least one dedicated preservation lemma or helper theorem.
3. Theorems show preservation of the composed capability invariant for at least:
   - one read transition (`lookup`-style),
   - one write transition (`insert`/`mint`-style).
4. The attenuation policy is stated in code comments/doc text near definitions and reflected in
   theorem statements.

### 6.2 Build and executability acceptance criteria

5. `lake build` passes with no new `axiom` introduced to bypass missing proofs.
6. `lake exe sele4n` (or equivalent `#eval` path used by `Main.lean`) demonstrates at least one
   concrete transition (scheduler and/or capability path) from an explicit state.

### 6.3 Documentation acceptance criteria

7. `docs/SEL4_SPEC.md` and `docs/DEVELOPMENT.md` both describe:
   - current M2 foundation scope,
   - remaining proof gaps (if any),
   - next intended increment.

Evidence sources:

- theorem statements/proofs in `SeLe4n/Kernel/API.lean` (or adjacent kernel semantics module),
- executable path in `Main.lean`,
- build/execution output from local checks.

### 6.4 Definition of done for this step

This step should be marked complete only when all acceptance criteria pass in one commit range,
and no open TODOs remain for the transitions introduced in this slice.

### 6.5 Progress snapshot (current repository state)

- M2 Foundation **Step 1 API surface** is implemented in `SeLe4n.Kernel.API` with `cspaceLookupSlot`,
  `cspaceInsertSlot`, `mintDerivedCap`, and `cspaceMint`, including read/write preservation and
  attenuation theorems.
- M2 Foundation **Step 2 state/model helpers** are implemented in `SeLe4n.Model.State` (`SlotRef`,
  ownership-oriented lookup/accessor helpers) and connected to kernel lookup/insert lemmas.
- M2 Foundation **Step 3 invariant bundle** is now implemented in `SeLe4n.Kernel.API` as
  `capabilityInvariantBundle` with explicit components (`cspaceSlotUnique`, `cspaceLookupSound`,
  `cspaceAttenuationRule`) and dedicated helper lemmas/theorem entrypoints.
- M2 Foundation **Step 4 preservation proofs** are now established for one read transition (`cspaceLookupSlot_preserves_capabilityInvariantBundle`) and one write transition (`cspaceMint_preserves_capabilityInvariantBundle`) in `SeLe4n.Kernel.API`.
- Remaining M2 work focuses on broader capability lifecycle transitions (revoke/delete) and
  strengthening authority properties across those new operations.


## 7. Audit closure report (Bootstrap + M1)

The repository has been audited against completed milestone claims.

### 7.1 Bootstrap verification summary

- Core identifiers, machine state, object universe, and global state are implemented in
  `Prelude`, `Machine`, `Model.Object`, and `Model.State` modules.
- `KernelM`, `KernelError`, and executable scheduling transitions are present and buildable.

### 7.2 M1 verification summary

- Invariant components (`runQueueUnique`, `currentThreadValid`, `queueCurrentConsistent`) and
  composed entrypoint (`schedulerInvariantBundle`) are implemented.
- Preservation theorems exist for `chooseThread`, `schedule`, and `handleYield` over bundle
  components and composed bundle.
- Strict queue/current policy is documented in-code at invariant definition.
- Repository search shows no `axiom`, `sorry`, or unresolved `TODO` markers in Lean code.

### 7.3 Audit evidence commands

- `lake build`
- `lake exe sele4n`
- `rg -n "axiom|TODO|sorry"`

## 8. Roadmap

### 8.1 M1 (completed): scheduler integrity

Incremental plan:

1. ✅ Lock invariant policy (strict vs. relaxed queue/current consistency).
2. ✅ Encode component predicates and compose the bundle entrypoint.
3. ✅ Prove preservation for `chooseThread`.
4. ✅ Prove preservation for `schedule`.
5. ✅ Prove preservation for `handleYield`.
6. ✅ Consolidate helper lemmas and remove redundant proof scaffolding.
7. ✅ Update docs to record what is complete and what remains.

### 8.2 M2 (current): capability and CSpace semantics

- ✅ Step 1 complete: typed CSpace lookup/insert/mint API with explicit rights attenuation policy and core theorems.
- ✅ ~~Step 2 complete: state/model helpers for slot-level capability ownership without architecture-specific details.~~
- ✅ Step 3 complete: first capability invariant bundle is defined/proven (slot uniqueness, lookup soundness, attenuation monotonicity).
- 🔄 Next: add revoke/delete transitions and extend authority constraints across lifecycle operations.
- 🔄 Later: authority monotonicity and reachability constraints across extended operations.

### 8.3 M3: IPC semantics

- endpoint send/receive transitions,
- queue discipline invariants,
- call/reply correspondence lemmas.

### 8.4 M4: memory/object lifecycle

- untyped memory + retype operations,
- object creation/deletion safety,
- alignment/disjointness constraints.

### 8.5 M5+: refinement and correspondence

- abstract-to-lower-level refinement relation,
- staged correspondence strategy toward external seL4 artifacts.

## 9. Change control

- Keep milestone status conservative; only mark complete when code and proofs validate.
- Any regression in completed criteria must be reflected immediately in this spec.
- Avoid speculative requirement text that lacks code-path ownership.
