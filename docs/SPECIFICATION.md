# seL4-in-Lean Specification and Boilerplate Plan

## Mission

Build a mechanically checked Lean model of seL4 with a layered refinement story:

1. **Abstract functional model** of kernel state transitions
2. **Executable specification** of syscall behavior
3. **Security and safety invariants** preserved by transitions
4. **Refinement interface** for connecting to lower-level implementations

---

## Scope and Non-Goals (initial phase)

### In scope

- Core object model (threads, endpoints, CNodes, capabilities)
- Deterministic syscall transition relation
- Invariant framework for capability safety and IPC consistency
- Initial theorem skeletons to drive proof decomposition

### Out of scope (phase 1)

- Full binary compatibility with existing seL4 C implementation
- Machine-level memory model and hardware interrupts
- Verified compiler integration

---

## Repository Architecture

```text
SeL4/
  Model/
    Types.lean          -- primitive IDs, capabilities, syscall syntax
    KernelState.lean    -- abstract kernel object/state representation
    Syscall.lean        -- syscall result type and status channel
  Execution/
    Step.lean           -- executable small-step syscall semantics
  Spec/
    Objects.lean        -- object graph/well-formedness invariants
    Capabilities.lean   -- capability validity/safety invariants
    IPC.lean            -- endpoint queue consistency invariants
  Refinement/
    Simulation.lean     -- aggregate invariants + preservation theorem shell
  Proofs/
    InvariantLemmas.lean -- starter theorem over empty state
```

---

## Formal Model Requirements

### 1) Object Universe

- Thread IDs, endpoint IDs, notification IDs, CNode IDs are abstract naturals.
- Capability slots are indexed by naturals.
- Capabilities include null, thread, endpoint-with-rights, notification, and CNode forms.

### 2) Kernel State

The top-level state must include:

- current thread pointer
- runnable queue
- thread table (`ThreadId → Option TCB`)
- endpoint table (`EndpointId → Option EndpointState`)
- cspace table (`CNodeId → Option CNodeState`)

### 3) Syscall Surface

The initial syscall algebra supports:

- send
- recv
- yield
- mintCap

Each syscall returns either:

- successful state (`ok`)
- blocked state (`blocked`)
- error condition (`invalidCapability`, `invalidEndpoint`)

### 4) Invariant Stack

`KernelInvariant` is defined as conjunction of:

- `ObjectsWellFormed`
- `CapabilitySafe`
- `IPCQueuesConsistent`

All future proofs should use this layered invariant to avoid monolithic theorem statements.

---

## Proof Engineering Strategy

### Phase A: Structural invariants

- prove easy constructor lemmas
- derive read-only framing lemmas for unaffected substructures

### Phase B: Syscall-by-syscall preservation

- one theorem per syscall constructor
- combine via dispatch theorem (`step_preserves_invariant`)

### Phase C: Refinement adapters

- define relation between abstract state and concrete state record
- prove forward simulation for each syscall

### Phase D: Security and authority

- non-interference style lemmas over capability graph reachability
- integrity properties for CSpace updates (mint/move/revoke)

---

## Milestone Backlog

1. Expand object model with notifications and reply objects.
2. Replace placeholder `step` semantics with realistic queue transfer behavior.
3. Add scheduler model (priority queues, budget accounting, time slicing).
4. Introduce memory capability regions and untyped retype semantics.
5. Mechanize Hoare-style API layer for compositional syscall proof scripts.
6. Connect abstract model with executable test traces.

---

## Definition of Done (for each feature)

A change is complete only if it adds:

1. Data structure updates in `SeL4/Model/*` (if needed)
2. Transition semantics updates in `SeL4/Execution/Step.lean`
3. Invariant updates in `SeL4/Spec/*`
4. Preservation/update theorem adjustments in `SeL4/Refinement/*`
5. At least one proof lemma in `SeL4/Proofs/*`
6. Documentation update in this file if the model boundary changed

---

## Development Workflow

1. Write/adjust state and syntax definitions.
2. Encode transition semantics.
3. State invariants narrowly, then aggregate.
4. Prove local lemmas before global theorem closure.
5. Keep theorem statements stable; evolve proof internals incrementally.

---

## Risks and Mitigations

- **Risk**: Overly concrete early model hampers refinement.
  - **Mitigation**: Keep IDs abstract and tables functional (`Option` maps).
- **Risk**: Proof brittleness from giant simplification steps.
  - **Mitigation**: build named helper lemmas and local simp sets.
- **Risk**: Scope explosion.
  - **Mitigation**: preserve milestone boundaries and enforce phase gates.

---

## Immediate Next Tasks

- Implement real send/recv queue state transitions.
- Add ownership/authority relation to capabilities.
- Extend `invariant_of_empty_state` with more reusable helper lemmas.
- Add trace-level properties (`step*`) for multi-syscall executions.
