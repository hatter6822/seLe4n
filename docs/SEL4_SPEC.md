# seLe4n Specification and Milestone Plan

## 1. Purpose

This document defines the current normative specification baseline for seLe4n and the immediate
next delivery target.

It serves three roles:

1. Record **what is already complete** in the Lean codebase.
2. Define **what the next slice must deliver**.
3. Provide **acceptance criteria** that can be validated with local commands.

---

## 2. Milestone glossary

- **Bootstrap**: executable core model and initial invariant-preservation theorem pipeline.
- **M1 (Scheduler Integrity Bundle v1)**: scheduler-focused invariant components + preservation.
- **M2 (Capability & CSpace Semantics)**: typed CSpace operations, attenuation, lifecycle effects.
- **M3 (IPC seed)**: first endpoint transition model and IPC safety invariants.

---

## 3. Current status (implemented)

### 3.1 Bootstrap (complete)

The repository includes:

1. Core object/thread/slot identifiers and kernel monad structure.
2. Abstract machine model (`RegisterFile`, `MachineState`).
3. Kernel object universe (`TCB`, `Endpoint`, `CNode`, `Capability`).
4. Global `SystemState` with object store and scheduler state.
5. Executable kernel transitions and error handling path.

### 3.2 M1 Scheduler Integrity Bundle v1 (complete)

The following invariants are modeled and used in preservation entrypoints:

1. `runQueueUnique`: runnable queue has no duplicate TIDs.
2. `currentThreadValid`: current thread resolves to a TCB.
3. `queueCurrentConsistent`: current thread must be in runnable queue under strict policy.
4. `schedulerInvariantBundle` composed entrypoint and preservation alignment.

### 3.3 M2 Capability & CSpace Semantics (complete)

Implemented M2 scope includes:

1. Typed CSpace address model (`SlotRef` / `CSpaceAddr`).
2. Read/write transitions:
   - `cspaceLookupSlot`,
   - `cspaceInsertSlot`,
   - `cspaceMint`.
3. Lifecycle transitions:
   - `cspaceDeleteSlot`,
   - `cspaceRevoke`.
4. Authority policy components:
   - rights attenuation (`capAttenuates`),
   - lifecycle authority reduction statements.
5. Composed capability invariant entrypoint:
   - slot uniqueness,
   - lookup soundness,
   - attenuation rule,
   - lifecycle authority monotonicity.
6. Preservation theorem entrypoints for lookup/insert/mint/delete/revoke progression.
7. Executable trace in `Main.lean` showing scheduler + capability lifecycle behavior.

### 3.4 M3 IPC seed (in progress)

Implemented pieces already landed for the active slice:

1. Minimal explicit endpoint model state (`EndpointState` + queue on `Endpoint`).
2. Typed endpoint transition entrypoints:
   - `endpointSend`,
   - `endpointReceive`.
3. Explicit IPC error branches for mismatched endpoint/object states and empty-send-queue cases.
4. IPC seed invariants and preservation theorem entrypoints:
   - `endpointQueueWellFormed`,
   - `endpointObjectValid`,
   - `endpointInvariant`,
   - `ipcInvariant`,
   - `endpointSend_preserves_ipcInvariant`,
   - `endpointReceive_preserves_ipcInvariant`.

---

## 4. Next slice: M3 IPC seed (target outcomes)

### 4.1 Objective

Land a narrow, typed IPC model centered on endpoint send/receive transitions and prove first-order
safety invariants, while keeping M1/M2 theorems and executable path stable.

### 4.2 Required outcomes

For this slice to be considered complete, all of the following must be true.
Status is tracked per outcome.

1. **Endpoint transition API exists** *(complete)*
   - Add typed endpoint transition entrypoints (minimum one send path and one receive path).
   - Transitions must use existing `Kernel` style and explicit error handling.

2. **State modeling remains minimal but explicit** *(complete)*
   - Any new state needed for IPC queues or pending messages is represented in model structures
     with clear ownership and access discipline.
   - Avoid architecture-specific payload details in this slice.

3. **First IPC invariant bundle component is introduced** *(complete)*
   - At minimum, define one queue well-formedness condition and one endpoint/object validity
     condition.
   - Bundle naming should align with existing invariant terminology and theorem style.

4. **Preservation proof coverage lands for new transitions** *(complete)*
   - At least one send transition preservation theorem.
   - At least one receive transition preservation theorem.
   - New proof entrypoints should be composable with existing M1/M2 bundles.

5. **Executable trace includes IPC behavior** *(open)*
   - Extend or add executable demonstration to show endpoint transition flow.
   - Existing scheduler + CSpace demo should remain available or equivalent coverage provided.

### 4.3 Explicit out-of-scope for this slice

- Full blocking/wakeup scheduler semantics.
- Reply-cap semantics and complete endpoint protocol states.
- Architecture/MMU/ASID-specific details.
- Global refinement relation to C implementation.

---

## 5. Acceptance criteria for M3 IPC seed

A change set claiming M3 slice completion must satisfy all criteria below:

1. `lake build` succeeds.
2. `lake exe sele4n` succeeds and demonstrates IPC-related behavior.
3. No new unresolved proof escapes in core Lean sources:
   - `rg -n "axiom|sorry|TODO" SeLe4n Main.lean`.
4. New IPC transitions have machine-checked preservation theorem entrypoints.
5. `docs/SEL4_SPEC.md` and `docs/DEVELOPMENT.md` reflect delivered API and proof status.

---

## 6. Change-control and documentation policy

When milestone scope changes, update docs first (or in the same commit range) with:

1. New/changed transition names.
2. New invariant components and bundle composition.
3. New preservation theorem entrypoints.
4. Remaining proof debt explicitly called out as deferred.

Claims of milestone completion must include evidence in code, proofs, and executable behavior.

---

## 7. Evidence checklist for milestone closure

Use this checklist in PR descriptions:

- [ ] Transition definitions for the claimed slice exist.
- [ ] Invariant components for the slice are defined and bundled.
- [ ] Preservation theorem entrypoints compile.
- [ ] Executable path demonstrates slice behavior.
- [ ] `lake build` output is clean.
- [ ] Hygiene scan (`axiom|sorry|TODO`) is clean for core Lean sources.
- [ ] Docs updated to match implementation stage and next-slice plan.

---

## 8. Medium-term roadmap (post-M3)

Planned sequence after M3 seed stabilization:

1. **M3 expansion**: blocking semantics, endpoint state refinements, reply-cap scaffolding.
2. **M4 Object lifecycle/retype safety**: typed object creation/retyping invariants.
3. **M5+ Refinement/correspondence track**: progressively connect abstract model obligations to
   lower-level semantics.

This roadmap is intentionally staged to keep proof breakage localized and reviewable.
