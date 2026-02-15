# seLe4n Specification and Milestone Plan

## 1. Purpose

This document is the normative planning baseline for the seLe4n Lean model.

It has four jobs:

1. Capture what is implemented and trusted today.
2. Define the exact **next delivery slice** and why it matters.
3. Declare what is out of scope so review stays focused.
4. Provide acceptance gates that can be validated locally.

The project is currently in a **post-M3-seed** stage: M1 scheduler invariants, M2 capability
semantics, and M3 endpoint send/receive seed semantics are complete and executable.

Testing framework baseline status: Tier 0 hygiene checks, Tier 1 build checks, and Tier 2 fixture-backed executable smoke checks are implemented under `scripts/test_*.sh`; pull-request CI now enforces `./scripts/test_fast.sh` and `./scripts/test_smoke.sh`.

---

## 2. Milestone glossary

- **Bootstrap**: executable model skeleton (state, objects, kernel monad, transition style).
- **M1 (Scheduler Integrity Bundle v1)**: queue/current-thread invariants + preservation.
- **M2 (Capability & CSpace Semantics)**: typed slot operations, mint attenuation, lifecycle effects.
- **M3 (IPC seed)**: minimal endpoint send/receive semantics + first IPC invariants.
- **M3.5 (next slice: IPC handshake + scheduler interaction)**: introduce blocking/wakeup-facing
  endpoint behavior while preserving existing theorem bundles.

---

## 3. Current status (implemented and expected to remain stable)

### 3.1 Bootstrap (complete)

The codebase provides:

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
6. Local store/lookup helper lemmas colocated near endpoint transitions to keep proof scripts
   compositional and readable.

---

## 4. Next slice definition: M3.5 IPC handshake + scheduler interaction

### 4.1 Slice objective

Move from queue-only endpoint seed semantics toward a typed handshake model that introduces the
first blocking/wakeup contract between IPC transitions and scheduler-visible thread state, while
keeping all M1/M2/M3 guarantees intact.

### 4.2 Why this slice is next

M3 seed established endpoint-local safety. The highest-leverage next step is to connect endpoint
state transitions to scheduling consequences in a narrow and provable way. This enables later
reply-cap and protocol refinements without forcing a full redesign.

### 4.3 Required target outcomes

A change set claiming M3.5 completion must satisfy all outcomes below.

1. **Endpoint protocol state refinement (new)**
   - Extend endpoint state to represent at least one waiting receiver / waiting sender direction
     explicitly (not just queue content).
   - Keep representation architecture-neutral and deterministic.

2. **Typed blocking/wakeup transition surface (new)**
   - Add at least one send path that can place a sender into a blocked/waiting state.
   - Add at least one receive path that can unblock or hand off work to a waiting counterpart.
   - Preserve explicit `KernelError` branches for invalid object/state combinations.

3. **Scheduler interaction contract (new)**
   - Define a minimal scheduler-facing predicate relating runnable queue membership and blocked IPC
     state for touched threads.
   - Ensure endpoint transitions preserve or intentionally update this contract.

4. **Invariant bundle extension (new)**
   - Add at least two invariant components that cover:
     - endpoint protocol-state coherence,
     - thread blocking/runnable coherence for IPC-touched threads.
   - Integrate them into a clearly named bundle layered on top of existing M3 seed invariant
     structure.

5. **Preservation theorem entrypoints (new)**
   - Provide machine-checked preservation theorems for each new/changed endpoint transition.
   - Show compositional preservation with existing scheduler and capability bundles.

6. **Executable evidence path (new)**
   - Extend `Main.lean` trace to demonstrate at least one blocking-to-delivery or waiting-to-ready
     IPC story.
   - Preserve existing scheduler + CSpace + M3-seed behaviors as a prefix of the demo path.

### 4.4 Explicit non-goals for M3.5

Out of scope for this slice:

- Reply-cap transfer protocol completeness.
- Priority donation and full scheduling policy reasoning.
- Architecture/MMU/ASID details.
- Retype/object-creation semantics (tracked for later milestone).
- Full refinement correspondence to C-level seL4 implementation.

---

## 5. Acceptance criteria for M3.5

All criteria are required:

1. `./scripts/test_fast.sh` succeeds.
2. `./scripts/test_smoke.sh` succeeds (including Tier 2 fixture-backed trace checks).
3. `lake build` succeeds.
4. `lake exe sele4n` succeeds and shows IPC behavior beyond the seed queue-only story.
5. Hygiene scan is clean:
   - `rg -n "axiom|sorry|TODO" SeLe4n Main.lean`.
6. New endpoint/scheduler interaction invariants exist and are included in the active IPC bundle.
7. New/updated endpoint transitions have machine-checked preservation theorem entrypoints.
8. `docs/SEL4_SPEC.md`, `docs/DEVELOPMENT.md`, and `README.md` reflect the same stage and next
   slice scope.

---

## 6. Change-control policy

When milestone scope, transition APIs, or invariant composition changes:

1. Update documentation in the same commit range as code.
2. Keep milestone status markers accurate (`complete`, `in progress`, `planned`).
3. If scope is deferred, record the reason and the destination milestone.
4. Do not claim milestone completion without executable + theorem evidence.

---

## 7. Milestone closure evidence checklist

Include this checklist in PR descriptions:

- [ ] New/updated transition definitions for the claimed slice exist.
- [ ] Invariant components are named, documented, and bundled.
- [ ] Preservation theorem entrypoints compile.
- [ ] `lake build` executed successfully.
- [ ] `lake exe sele4n` executed successfully.
- [ ] Hygiene scan (`axiom|sorry|TODO`) executed and clean.
- [ ] Docs updated to match implementation and next slice.
- [ ] Explicit statement of remaining proof debt (if any).

---

## 8. Roadmap after M3.5 (planning horizon)

1. **M4 Object lifecycle/retype safety**
   - typed object creation/retype model,
   - ownership/aliasing constraints,
   - capability/object lifecycle interaction invariants.
2. **M5 Refinement bridge (incremental)**
   - progressive correspondence obligations between abstract Lean transitions and lower-level
     semantics.
3. **M6 Policy and protocol deepening**
   - richer IPC/reply capability protocol and stronger scheduler-policy obligations.

This roadmap is intentionally incremental so proof breakage stays local and reviewable.
