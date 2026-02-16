# Codebase Reference (Deep Developer Map)

This chapter is a practical map of the current Lean codebase so developers can reason about where
semantics live, where proofs live, how runtime traces are produced, and how to evolve modules
without breaking milestone contracts.

---

## 1. Repository-level structure

- `SeLe4n.lean`
  - package export root; re-exports the public model + kernel API surface.
- `Main.lean`
  - executable scenario integration trace used in Tier 2 smoke checks.
- `SeLe4n/`
  - foundational model, transition, and proof modules.
- `scripts/`
  - tiered test entrypoints (`test_fast`, `test_smoke`, `test_full`, `test_nightly`) and shared
    logging/check helpers (`test_lib.sh`).

Design intent:

- Keep the import boundary stable at `SeLe4n.lean` so external users can import one root while
  internal modules continue to evolve.
- Keep executable evidence (`Main.lean`) independent from theorem files so scenario growth does not
  force theorem namespace churn.

---

## 2. Foundation layer

### `SeLe4n/Prelude.lean`

Purpose:

- defines core ID aliases (`ObjId`, `ThreadId`, `CPtr`, `Slot`, etc.),
- defines `KernelM`, a small state+error monad for executable transitions.

Why this design matters:

- all kernel operations and proof statements ultimately rely on these type aliases and monadic
  conventions,
- aliases remain architecture-neutral (`Nat`) intentionally to keep early slices focused on
  semantic correctness over representation detail,
- `KernelM` stays intentionally minimal (`σ → Except ε (α × σ)`) so transition proofs can unfold
  directly without heavy monad-transformer infrastructure.

### `SeLe4n/Machine.lean`

Purpose:

- defines abstract machine state (`RegisterFile`, `MachineState`),
- provides pure primitive update/read helpers (`readReg`, `writeReg`, `readMem`, `writeMem`, etc.).

Why this design matters:

- transitions can carry machine context while proof effort stays concentrated on kernel object
  semantics,
- machine details are available to future milestones without forcing immediate architecture lock-in.

---

## 3. Object and global-state modeling layer

### `SeLe4n/Model/Object.lean`

Primary contents:

- capability rights + capability target model (`AccessRight`, `CapTarget`, `Capability`),
- M3.5 IPC-visible thread status (`ThreadIpcState`),
- endpoint model (`EndpointState`, queue, optional waiting receiver),
- CNode structure + operations (`lookup`, `insert`, `remove`, `revokeTargetLocal`),
- global `KernelObject` sum type and `KernelObjectType` discriminator.

Key design choices:

1. **Capability target is explicit (`object` or `cnodeSlot`)**
   - preserves room for richer CSpace stories without changing capability shape later.
2. **CNode represented as slot list**
   - favors proof readability and deterministic update semantics over optimized lookup structure.
3. **`revokeTargetLocal` explicitly scoped**
   - only revokes sibling slots in one CNode while preserving source slot authority;
   - full graph-based revocation is deferred intentionally and documented in comments.

### `SeLe4n/Model/State.lean`

Primary contents:

- `KernelError` (including `illegalState`/`illegalAuthority` lifecycle errors), `SchedulerState`, `SystemState`, `SlotRef`,
- global lookup/store transitions (`lookupObject`, `storeObject`, `setCurrentThread`),
- typed CSpace helpers (`lookupCNode`, `lookupSlotCap`, `ownsSlot`, `ownedSlots`),
- small support lemmas that simplify subsystem-level invariants.

Key design choices:

1. **Object store as function map (`ObjId → Option KernelObject`)**
   - replacement updates are simple and theorem-friendly.
2. **`SlotRef` as first-class typed address**
   - avoids ad-hoc `(obj,slot)` tuple handling across capability and invariant code.
3. **Ownership relation local to CNode identity**
   - enough to state authority monotonicity constraints in current milestones.

---

## 4. Scheduler layer (M1 contract)

### `SeLe4n/Kernel/Scheduler/Invariant.lean`

Core invariants:

1. `runQueueUnique`
2. `currentThreadValid`
3. `queueCurrentConsistent`
4. composed aliases (`schedulerWellFormed`, `schedulerInvariantBundle`)

Preservation entrypoints:

- scheduler operations preserve the component predicates and bundle-level aliases.

### `SeLe4n/Kernel/Scheduler/Operations.lean`

Primary transitions:

- `chooseThread`
- `schedule`
- `handleYield`

Operational semantics snapshot:

- `chooseThread` returns head of runnable queue or `none`, without state mutation,
- `schedule` sets `current` to first runnable TCB if object is valid TCB; otherwise clears
  `current` to prevent invalid selection,
- `handleYield` currently aliases `schedule` to keep syscall surface stable while implementation
  remains narrow.

Proof style:

- strong use of case analysis over runnable queue shape and object lookup result,
- small helper lemmas (`chooseThread_returns_runnable_or_none`,
  `setCurrentThread_*_preserves_*`) reduce repetition in bundle theorem proofs.

---

## 5. Capability + CSpace layer (M2 contract)

### `SeLe4n/Kernel/Capability/Operations.lean`

Primary semantics:

- slot access/update (`cspaceLookupSlot`, `cspaceInsertSlot`),
- minting with attenuation (`rightsSubset`, `mintDerivedCap`, `cspaceMint`),
- lifecycle/authority operations (`cspaceDeleteSlot`, `cspaceRevoke`).

Design details that matter:

1. **Attenuation as explicit list-subset rule**
   - requested rights must be subset of source rights.
2. **Mint does not silently widen authority**
   - failure path is explicit via `invalidCapability`.
3. **Revoke is local by design**
   - aligns with the current CNode-local revoke helper in object model.

### `SeLe4n/Kernel/Lifecycle/Operations.lean`

Primary semantics:

- lifecycle retype authority predicate (`lifecycleRetypeAuthority`),
- deterministic retype transition (`lifecycleRetypeObject`),
- explicit branch theorems for illegal-state and illegal-authority outcomes.

Design details that matter:

1. **Metadata coherence gate before mutation**
   - retype fails with `illegalState` when object-store type and lifecycle metadata diverge.
2. **Authority is explicit and narrow**
   - retype authority requires direct-object target and `write` rights; violations return
     `illegalAuthority`.
3. **Successful path reuses `storeObject`**
   - object store and lifecycle object-type metadata are updated atomically.

### `SeLe4n/Kernel/Service/Operations.lean`

Primary semantics:

- orchestration transitions (`serviceStart`, `serviceStop`, `serviceRestart`),
- explicit failure outcomes (`policyDenied`, `dependencyViolation`, `illegalState`),
- staged-order theorem witness (`serviceRestart_ok_implies_staged_steps`).

Design details that matter:

1. **Transition checks are ordered and explicit**
   - lookup/state/policy/dependency gates occur in deterministic sequence.
2. **Policy is separated from mutation**
   - transitions receive predicate parameters and only mutate after policy approval.
3. **Restart is composition-first**
   - restart semantics are encoded as stop-then-start and proven as staged execution.

### `SeLe4n/Kernel/Service/Invariant.lean`

Primary semantics:

- reusable policy components (`policyBackingObjectTyped`, `policyOwnerAuthorityRefRecorded`,
  `policyOwnerAuthoritySlotPresent`),
- service policy bundle entrypoint (`servicePolicySurfaceInvariant`),
- bridge theorem (`servicePolicySurfaceInvariant_of_lifecycleInvariant`) for deriving policy
  obligations from lifecycle contracts plus backing-object existence assumptions.

Design details that matter:

1. **Policy and mutation are separated by construction**
   - service policy predicates are pure state predicates and do not mutate kernel state.
2. **Bridge shape is compositional**
   - bridge lemmas are local and reusable so policy obligations can be discharged without copying
     transition proofs.
3. **Failure branch intent is explicit**
   - `serviceStart_policyDenied_separates_check_from_mutation` and
     `serviceStop_policyDenied_separates_check_from_mutation` keep denial outcomes tied to check-only
     semantics.

### `SeLe4n/Kernel/Lifecycle/Invariant.lean`

Primary semantics:

- identity/aliasing lifecycle invariants (`lifecycleIdentityAliasingInvariant`),
- capability-reference lifecycle invariants (`lifecycleCapabilityReferenceInvariant`),
- composed lifecycle invariant bundle (`lifecycleInvariantBundle`),
- M4-B stale-reference hardening surfaces (`lifecycleStaleReferenceExclusionInvariant`,
  `lifecycleIdentityStaleReferenceInvariant`).

Design details that matter:

1. **Invariant layering is explicit**
   - identity/aliasing constraints are defined and reviewed independently from capability-reference constraints.
2. **Naming is milestone-oriented**
   - definitions are narrow and named so later preservation theorems can compose cleanly.
3. **Metadata-to-bundle bridge is explicit**
   - `lifecycleInvariantBundle_of_metadata_consistent` connects model-level consistency assumptions to the lifecycle bundle surface.
4. **WS-B stale-reference hardening is explicit**
   - theorems lift stale-reference components from lifecycle bundle assumptions and preserve them across `lifecycleRetypeObject`.

### `SeLe4n/Kernel/Capability/Invariant.lean`

Core components:

1. `cspaceSlotUnique`
2. `cspaceLookupSound`
3. `cspaceAttenuationRule`
4. `lifecycleAuthorityMonotonicity`

Composition surfaces:

- `capabilityInvariantBundle`
- `lifecycleCapabilityStaleAuthorityInvariant`
- `m3IpcSeedInvariantBundle`
- `m35IpcSchedulerInvariantBundle`

Cross-layer role:

- capability theorems are composed with scheduler and IPC predicates to preserve milestone
  continuity while proof surfaces grow.

---

## 6. IPC layer (M3 + M3.5 contract)

### `SeLe4n/Kernel/IPC/Invariant.lean`

Primary transitions:

- `endpointSend`
- `endpointAwaitReceive`
- `endpointReceive`

Core invariant surfaces:

- endpoint-local validity (`endpointQueueWellFormed`, `endpointObjectValid`, `endpointInvariant`),
- system-level IPC validity (`ipcInvariant`),
- M3.5 scheduler coherence contract:
  - `runnableThreadIpcReady`,
  - `blockedOnSendNotRunnable`,
  - `blockedOnReceiveNotRunnable`,
  - `ipcSchedulerContractPredicates`.

Handshake behavior modeled today:

- waiting receiver path (`endpointAwaitReceive`) marks thread blocked on receive and records
  waiting receiver in endpoint,
- send path can satisfy waiting receiver directly (handoff-like behavior),
- queued senders are still supported and drained by `endpointReceive`.

Proof organization:

- local helper lemmas for store/update effects,
- transition-specific preservation theorems,
- composed theorem entrypoints over IPC + scheduler + capability surfaces.

---

## 7. Executable evidence and trace contract

### `Main.lean`

`main` builds a deterministic scenario in this order:

1. scheduler step (`schedule`),
2. root capability lookup,
3. lifecycle retype unauthorized + illegal-state + success branches,
4. mint + sibling mint,
5. composed revoke/delete/retype alias-guard failure and success path,
6. post-revoke/post-delete lookup checks,
7. waiting-receiver handshake send,
8. queued senders + receives,
9. expected error on extra receive.

Why this matters:

- each stage emits trace lines consumed by Tier 2 fixture checks,
- executable traces provide semantic evidence beyond “build succeeds”.

### `tests/fixtures/main_trace_smoke.expected`

- stores stable semantic fragments expected in executable output,
- intentionally fragment-based (not full exact output snapshot) so harmless formatting shifts do not
  destabilize the gate.

### `scripts/test_tier2_trace.sh`

- runs `lake exe sele4n`,
- checks each non-empty fixture line appears in output,
- emits diagnostics and optional trace artifacts for CI debugging.

---

## 8. Test framework logging and color prefixes

The shared `scripts/test_lib.sh` logging layer now supports color-coded prefixes:

- category prefixes (`[META]`, `[TRACE]`, `[HYGIENE]`, `[BUILD]`, `[INVARIANT]`) are colorized,
- status prefixes in messages (`RUN`, `PASS`, `FAIL`) are colorized,
- color output is automatically disabled when stdout is not a TTY or `NO_COLOR` is set.

This gives local developers faster scanability while preserving CI-safe plain output behavior.

---

## 9. Safe change workflow by module

When editing a module, follow this decision path:

1. identify which milestone contract the file owns,
2. identify composed bundles that include that contract,
3. adjust local helper lemmas nearest the transition,
4. keep theorem entrypoint naming stable where practical,
5. update docs and fixture anchors in the same commit range.

---

## 10. Debug playbooks

### A) Proof breakage after transition changes

1. Re-run `lake build` and note first failing theorem.
2. Inspect transition-local helper lemmas before editing bundle theorem scripts.
3. Re-establish component theorem first, then bundle theorem.

### B) Trace fixture mismatch

1. Run Tier 2 script to collect missing lines.
2. Decide if change is bug or intentional semantics shift.
3. If intentional, update fixture and document rationale in docs/PR.

### C) Capability authority surprise

1. Check minted rights against source cap (`rightsSubset` path).
2. Check local revoke behavior (same-CNode sibling target removal only).
3. Verify ownership assumptions in `SystemState.ownsSlot`-based invariants.

This map should be your primary orientation reference before touching theorem-heavy files.
