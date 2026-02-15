# seLe4n Specification and Milestone Plan

## 1. Purpose

This document is the normative planning baseline for the seLe4n Lean model.

It has five jobs:

1. Capture what is implemented and trusted today.
2. Define the exact **current delivery slice** and why it matters.
3. Define the exact **next delivery slice** so implementation does not stall after current-slice closure.
4. Declare what is out of scope so review stays focused.
5. Provide acceptance gates that can be validated locally.

The project is currently in a **post-M3-seed / mid-M3.5** stage: M1 scheduler invariants, M2
capability semantics, and M3 endpoint send/receive seed semantics are complete and executable, while M3.5 step 7 remains open.

Testing baseline status: Tier 0 hygiene checks, Tier 1 build checks, and Tier 2 fixture-backed
executable smoke checks are implemented under `scripts/test_*.sh` and enforced in pull-request CI.

---

## 2. Milestone glossary and stage markers

- **Bootstrap (complete)**: executable model skeleton (state, objects, kernel monad, transition style).
- **M1 (complete)**: scheduler integrity bundle and preservation.
- **M2 (complete)**: typed CSpace operations and capability lifecycle invariants.
- **M3 (complete)**: endpoint send/receive seed semantics with first IPC invariant bundle.
- **M3.5 (current slice, in progress)**: typed IPC handshake + scheduler interaction contract.
- **M4 (next slice, planned)**: object lifecycle/retype safety with capability-object coupling invariants.

---

## 3. Current status (implemented and expected stable)

### 3.1 Bootstrap (complete)

Implemented baseline:

1. Core identifiers and `Kernel` monad flow.
2. Machine model (`RegisterFile`, `MachineState`).
3. Object universe (`TCB`, `Endpoint`, `CNode`, `Capability`).
4. Global `SystemState` with object store and scheduler state.
5. Executable transitions with explicit error handling.

### 3.2 M1 Scheduler Integrity Bundle v1 (complete)

Implemented and theorem-backed:

1. `runQueueUnique`.
2. `currentThreadValid`.
3. `queueCurrentConsistent`.
4. Composed `schedulerInvariantBundle` preservation for `chooseThread`, `schedule`, `handleYield`.

### 3.3 M2 Capability & CSpace Semantics (complete)

Implemented and theorem-backed:

1. Addressing model: `SlotRef` and `CSpaceAddr`.
2. Read/write transitions: `cspaceLookupSlot`, `cspaceInsertSlot`, `cspaceMint`.
3. Lifecycle transitions: `cspaceDeleteSlot`, `cspaceRevoke`.
4. Authority policy support: `capAttenuates`, rights subset/attenuation lemmas.
5. Bundle: slot uniqueness, lookup soundness, attenuation rule, lifecycle authority monotonicity.
6. Preservation entrypoints for lookup/insert/mint/delete/revoke.

### 3.4 M3 IPC seed (complete)

Implemented and theorem-backed:

1. Endpoint model state (`EndpointState` + queue field on endpoint objects).
2. IPC transitions: `endpointSend`, `endpointReceive`.
3. Explicit mismatch/error branches and empty-queue receive failure path.
4. IPC invariants:
   - `endpointQueueWellFormed`,
   - `endpointObjectValid`,
   - `endpointInvariant`,
   - `ipcInvariant`,
   - composed `m3IpcSeedInvariantBundle`.
5. Preservation entrypoints for both endpoint transitions over IPC, scheduler, capability, and
   composed M3 seed bundle invariants.

---

## 4. Current slice definition: M3.5 IPC handshake + scheduler interaction

### 4.1 Slice objective

Move from queue-only endpoint seed semantics toward a typed handshake model that introduces the
first blocking/wakeup contract between IPC transitions and scheduler-visible thread state, while
keeping M1/M2/M3 guarantees intact.

### 4.2 Why this slice is now

M3 established endpoint-local safety. The highest-value next step is to connect endpoint behavior
to scheduling consequences in a narrow and provable way. This creates a clean bridge to richer IPC
protocol semantics without a large proof reset.

### 4.3 Required target outcomes for M3.5 closure

A change set claiming M3.5 completion must satisfy all outcomes below.

1. **Endpoint protocol state refinement**
   - represent waiting direction(s) explicitly (at least one waiting sender or waiting receiver form),
   - maintain deterministic and architecture-neutral representation.

2. **Typed blocking/wakeup transition surface**
   - include at least one send path that can block or mark waiting state,
   - include at least one receive path that can wake or deliver against waiting counterpart state,
   - preserve explicit `KernelError` paths for illegal object/state combinations.

3. **Scheduler interaction contract**
   - define predicate(s) connecting runnable queue membership and IPC-blocked thread state,
   - preserve or intentionally update those predicates in endpoint transitions.

4. **Invariant bundle extension**
   - add at least two invariant components covering:
     - endpoint protocol-state coherence,
     - thread blocked/runnable coherence,
   - integrate those invariants into a composed bundle layered on `m3IpcSeedInvariantBundle`.

5. **Preservation theorem entrypoints**
   - provide machine-checked preservation theorem entrypoints for each new/changed endpoint transition,
   - demonstrate compositional compatibility with existing scheduler and capability bundles.

6. **Executable evidence path**
   - extend `Main.lean` with at least one waiting-to-delivery (or waiting-to-ready) scenario,
   - preserve prior scheduler/CSpace/M3-seed behavior as executable prefix.

### 4.4 M3.5 acceptance criteria (all required)

1. `./scripts/test_fast.sh` succeeds.
2. `./scripts/test_smoke.sh` succeeds (including Tier 2 fixture checks).
3. `lake build` succeeds.
4. `lake exe sele4n` succeeds and exhibits IPC behavior beyond queue-only seed semantics.
5. Hygiene scan is clean:
   - `rg -n "axiom|sorry|TODO" SeLe4n Main.lean`.
6. New endpoint/scheduler interaction invariants exist and are included in the active IPC bundle.
7. New/updated endpoint transitions have machine-checked preservation theorem entrypoints.
8. `README.md`, `docs/SEL4_SPEC.md`, and `docs/DEVELOPMENT.md` are internally stage-consistent.

### 4.5 M3.5 implementation sequence progress

- ✅ **Step 1 complete (state-model refinement)**
  - endpoint model now includes explicit waiting-counterpart identity for deterministic handshake setup (`waitingReceiver`),
  - TCB model now carries explicit IPC blocking status (`ready`, `blockedOnSend endpoint`, `blockedOnReceive endpoint`) to keep scheduler-facing ownership clear,
  - endpoint well-formedness now captures ownership coupling between endpoint mode and waiting-receiver identity (non-receive states require `none`, receive requires `some`).
- ✅ **Step 2 complete (transition updates)**
  - added explicit receiver-wait registration transition (`endpointAwaitReceive`) for idle endpoints,
  - `endpointSend` now has an explicit receive-handshake success path (`receive` + waiting receiver) and explicit state-mismatch error branches for illegal endpoint shapes,
  - `endpointReceive` now keeps explicit success/error splits over queue + waiting-receiver combinations,
  - send/receive preservation theorem entrypoints remain machine-checked after transition-surface updates.
- ✅ **Step 3 complete (scheduler contract predicates)**
  - added explicit scheduler/IPC coherence predicates for the active slice (`runnableThreadIpcReady`, `blockedOnSendNotRunnable`, `blockedOnReceiveNotRunnable`),
  - composed the targeted trio under `ipcSchedulerContractPredicates` with intentionally narrow (non-over-generalized) scope,
  - added machine-checked preservation entrypoints for send/await-receive/receive under the new scheduler-contract predicate set.
- ✅ **Step 4 complete (invariant bundle composition)**
  - added named IPC+scheduler coherence components (`ipcSchedulerRunnableReadyComponent`, `ipcSchedulerBlockedSendComponent`, `ipcSchedulerBlockedReceiveComponent`) and aggregated them under `ipcSchedulerCoherenceComponent`,
  - introduced composed `m35IpcSchedulerInvariantBundle` layered directly over `m3IpcSeedInvariantBundle`,
  - added machine-checked preservation entrypoints for send/await-receive/receive over the new composed M3.5 bundle.
- ✅ **Step 5 complete (helper lemmas)**
  - added local endpoint-store lookup helpers near transitions (`tcb_lookup_of_endpoint_store`, `runnable_membership_of_endpoint_store`, `not_runnable_membership_of_endpoint_store`),
  - send/await-receive/receive scheduler-contract preservation proofs now discharge concrete lookup/runnable obligations via these small local lemmas rather than repeated ad hoc case splits.
- ✅ **Step 6 complete (preservation-theorem hardening)**
  - endpoint transitions now expose local-first preservation theorems for scheduler-contract components (`<transition>_preserves_runnableThreadIpcReady`, `<transition>_preserves_blockedOnSendNotRunnable`, `<transition>_preserves_blockedOnReceiveNotRunnable`),
  - composed scheduler-contract and M3.5 bundle preservation theorems are layered second and continue to compile machine-checked.
- ⏳ **Remaining M3.5 steps**
  - executable-demonstration extension (step 7) remains in progress.

---

### 4.6 Explicit non-goals for M3.5

Out of scope for this slice:

- Reply-cap transfer protocol completeness.
- Priority donation and full scheduling policy reasoning.
- Architecture/MMU/ASID details.
- Retype/object-creation semantics (deferred to M4).
- Full refinement correspondence to C-level seL4 implementation.

---

## 5. Next slice definition (planned): M4 object lifecycle / retype safety

### 5.1 M4 objective

Introduce typed object lifecycle semantics (creation/retype-class operations) and prove that
capability/object ownership relationships remain coherent under lifecycle changes.

### 5.2 Why M4 follows M3.5

After M3.5, endpoint/scheduler coupling gains a minimal protocol skeleton. The next structural
safety risk is object lifecycle evolution; addressing it early prevents capability reasoning from
splitting away from object-state reasoning.

### 5.3 Planned M4 target outcomes

1. **Retype/lifecycle transition surface**
   - define executable transitions for at least one object lifecycle operation,
   - keep operation typing explicit and failure branches deterministic.

2. **Lifecycle coherence invariants**
   - object identity/aliasing constraints,
   - capability references remain valid and authority-consistent across lifecycle updates.

3. **Composed bundle integration**
   - compose M4 lifecycle invariants with existing scheduler/capability/IPC bundles,
   - retain separable theorem surfaces for maintainable proof updates.

4. **Preservation theorem entrypoints**
   - theorem entrypoints for lifecycle transitions,
   - at least one compositional theorem touching both capability and lifecycle layers.

5. **Executable scenario evidence**
   - `Main.lean` demonstration of lifecycle operation with stable expected trace semantics,
   - fixture updates in `tests/fixtures/main_trace_smoke.expected` only when behavior change is intentional.

### 5.4 M4 provisional acceptance criteria (planning baseline)

1. Current required gates continue to pass (`test_fast`, `test_smoke`, `lake build`, `lake exe`).
2. Lifecycle transitions compile with explicit success/error branches.
3. Lifecycle invariants are named and integrated into composed invariant bundle structure.
4. Preservation theorem entrypoints compile without `axiom`/`sorry` additions.
5. Documentation is updated to reflect M4 scope and post-M4 next-slice plan.

### 5.5 Explicit non-goals for M4 (initial pass)

- Full allocator/heap policy modeling.
- Architecture-specific memory management internals.
- End-to-end refinement proof to C implementation.
- Full policy framework redesign.

---

## 6. Change-control policy

When milestone scope, transition APIs, or invariant composition changes:

1. Update docs in the same commit range as code.
2. Keep milestone status markers accurate (`complete`, `in progress`, `planned`).
3. If scope is deferred, record reason and destination milestone.
4. Do not claim milestone completion without executable + theorem evidence.
5. Keep `README.md`, `docs/SEL4_SPEC.md`, and `docs/DEVELOPMENT.md` synchronized.

---

## 7. Milestone closure evidence checklist

Include this checklist in PR descriptions:

- [ ] New/updated transition definitions for claimed slice exist.
- [ ] Invariant components are named, documented, and bundled.
- [ ] Preservation theorem entrypoints compile.
- [ ] `lake build` executed successfully.
- [ ] `lake exe sele4n` executed successfully.
- [ ] Hygiene scan (`axiom|sorry|TODO`) executed and clean.
- [ ] Docs updated to match implementation and next slice.
- [ ] Explicit statement of remaining proof debt (if any).

---

## 8. Roadmap horizon (after M4)

1. **M5 refinement bridge (incremental)**
   - staged correspondence obligations between abstract Lean transitions and lower-level semantics.
2. **M6 policy/protocol deepening**
   - richer IPC/reply-capability protocol and stronger scheduler-policy obligations.
3. **M7 assurance hardening**
   - expanded integration checks and stronger compositional coverage across milestone bundles.

The roadmap remains incremental so proof breakage and review complexity stay local and tractable.
