# Microkernel and seL4 Primer

This chapter provides background on microkernel design and seL4 — the kernel whose architecture seLe4n models and extends. Readers already familiar with seL4 can skip to [section 4](#4-where-sele4n-departs-from-sel4).

## 1. What is a microkernel?

A microkernel keeps only minimal mechanisms in kernel mode:

- **Thread management** — creating, scheduling, and destroying threads of execution.
- **Address-space management** — virtual memory mapping and protection.
- **IPC** — inter-process communication primitives for message passing.
- **Capability-based access control** — unforgeable tokens that mediate all resource access.

Everything else — drivers, filesystems, networking, user services — runs in user space as isolated components that communicate through IPC.

### Why microkernels matter for security

1. **Smaller trusted computing base.** Fewer lines of privileged code means fewer places for bugs that compromise the whole system. seL4's kernel is ~10,000 lines of C; a monolithic kernel like Linux is millions.
2. **Fault isolation.** A crashed driver or service can be restarted without bringing down the system. The kernel enforces memory isolation between all components.
3. **Principle of least privilege.** Each component receives only the capabilities it needs. A compromised network driver cannot access the filesystem unless explicitly granted that authority.
4. **Formal verification feasibility.** A small kernel is tractable to verify. seL4 demonstrated this; seLe4n extends it with Lean 4's dependent type system.

### Trade-offs

- **IPC overhead.** Operations that would be function calls inside a monolithic kernel become cross-address-space messages. Careful design (like seLe4n's O(1) dual-queue) mitigates this.
- **System composition complexity.** Boot order, service dependencies, and capability distribution require explicit management (seLe4n's service orchestration layer addresses this).
- **Verification effort.** Proving correctness properties is labor-intensive, though Lean 4's tactic language and type inference help significantly compared to Isabelle/HOL.

## 2. What is seL4?

seL4 is a high-assurance microkernel originally developed at NICTA (now Data61/CSIRO). It is the first operating-system kernel with a complete, machine-checked functional correctness proof.

### Key seL4 concepts

| Concept | Description |
|---------|-------------|
| **Capabilities** | Unforgeable references to kernel objects. All system calls require a capability. Capabilities carry access rights (read, write, grant) and can be copied, minted (with reduced rights), or revoked. |
| **CSpace** | A per-thread capability space organized as a tree of CNode objects. Each CNode has a fixed number of slots, each holding one capability. Capability lookups traverse CNodes using guard/radix bit extraction. |
| **CDT** | The capability derivation tree tracks parent-child relationships between capabilities. Revoking a capability also revokes all its descendants. |
| **Endpoints** | IPC channels. A thread sends to or receives from an endpoint. If no partner is ready, the thread blocks. seL4 uses a single queue per endpoint with direction tags. |
| **Notifications** | Lightweight signaling objects. A notification carries a word-sized badge that is bitwise-ORed on signal and consumed atomically on wait. |
| **Untyped memory** | All physical memory starts as untyped objects. The `Retype` operation carves typed kernel objects (TCBs, CNodes, endpoints, page tables) from untyped regions. This gives the kernel no hidden allocator — all memory management is explicit and capability-controlled. |
| **VSpace** | Virtual address space management. Page tables are explicit kernel objects that user-space components map, unmap, and manage through capabilities. |
| **Scheduling** | Priority-based round-robin with optional MCS (mixed-criticality) extensions for temporal isolation. |

### seL4's verification approach

seL4 uses a three-layer refinement:

1. **Abstract specification** (Isabelle/HOL) — high-level functional model.
2. **Executable specification** (Haskell) — deterministic implementation model.
3. **C implementation** — the actual kernel code.

Proofs show that each layer refines the one above: the C code behaves exactly as the abstract spec says. This is approximately 200,000 lines of Isabelle/HOL proof for ~10,000 lines of C.

## 3. Why seLe4n models seL4 semantics

seLe4n does not replicate seL4's proof corpus. Instead, it takes a fundamentally different approach:

- **The kernel IS the specification.** In seLe4n, executable Lean 4 functions ARE the formal model. There is no separate abstract spec to refine against — the Lean code compiles to both a proof artifact and a runnable program.
- **Incremental formalization.** Key semantic surfaces (scheduler, capabilities, IPC, lifecycle) are formalized one milestone at a time, with each layer hardening before the next is built.
- **Co-located proofs.** Theorems live next to the code they prove, not in a separate proof corpus. The Operations/Invariant split keeps them organized without separating them from the code.

### What seLe4n preserves from seL4

- Capability-based access control as the sole authority mechanism.
- Explicit untyped memory management via retype operations.
- Endpoint-based IPC with blocking semantics.
- Architecture-neutral kernel logic with platform-specific bindings.
- The principle that all kernel state transitions are deterministic and total.

## 4. Where seLe4n departs from seL4

| Area | seL4 | seLe4n | Rationale |
|------|------|--------|-----------|
| **Proof language** | Isabelle/HOL (post-hoc refinement) | Lean 4 (co-located, same-language) | Eliminates spec-implementation gap |
| **IPC queues** | Single linked list per endpoint | Intrusive dual-queue with `queuePPrev` | O(1) mid-queue removal |
| **Information flow** | Binary high/low partition | N-domain two-dimensional labels | Richer security policies |
| **CDT** | Mutable doubly-linked list | Node-stable with HashMap `childMap` | Eliminates dangling pointers |
| **Scheduler** | Priority round-robin | Priority-bucketed + EDF with domain partitioning | O(1) operations, temporal isolation |
| **Service management** | Not in kernel | Service orchestration layer | Dependency graphs, partial-failure |
| **Data structures** | Arrays and linked lists | `Std.HashMap`/`Std.HashSet` throughout | O(1) hot paths |
| **Error handling** | Some paths use assertions | All paths return typed errors | Complete modeled error coverage |

## 5. Key terminology

| Term | Meaning in seLe4n |
|------|-------------------|
| **Transition** | A pure function from `SystemState` to `SystemState` (possibly with a result). |
| **Invariant** | A predicate over `SystemState` that must hold before and after every transition. |
| **Preservation theorem** | A proof that a specific transition preserves a specific invariant. |
| **Bundle** | A conjunction of related invariants (e.g., `schedulerInvariantBundle`). |
| **Tier** | A validation level in the testing hierarchy (Tier 0 = hygiene, Tier 3 = surface anchors). |
| **Workstream** | A scoped unit of audit remediation or feature work (e.g., WS-G4 = run queue restructure). |

## 6. Further reading

- [Project Overview](01-project-overview.md) — what seLe4n implements today
- [Project Design Deep Dive](04-project-design-deep-dive.md) — design rationale in depth
- [Architecture & Module Map](03-architecture-and-module-map.md) — module responsibilities
- seL4 reference semantics: [`docs/spec/SEL4_SPEC.md`](../spec/SEL4_SPEC.md)
