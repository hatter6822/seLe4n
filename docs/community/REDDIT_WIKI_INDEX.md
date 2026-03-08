# r/seLe4n Wiki Index

Welcome to the official wiki for **r/seLe4n**, the community hub for the seLe4n microkernel project — a production-oriented, formally verified microkernel written in Lean 4.

- **Website:** [seLe4n.org](https://seLe4n.org)
- **Repository:** [github.com/hatter6822/seLe4n](https://github.com/hatter6822/seLe4n)

---

## Table of Contents

1. [What is seLe4n?](#1-what-is-selen)
2. [Why seLe4n Exists](#2-why-selen-exists)
3. [How seLe4n Differs from seL4](#3-how-selen-differs-from-sel4)
4. [Architecture Overview](#4-architecture-overview)
5. [The Capability System](#5-the-capability-system)
6. [IPC and the Dual-Queue Innovation](#6-ipc-and-the-dual-queue-innovation)
7. [Scheduler Design](#7-scheduler-design)
8. [Information Flow and Security](#8-information-flow-and-security)
9. [Service Orchestration](#9-service-orchestration)
10. [Memory Management and Lifecycle](#10-memory-management-and-lifecycle)
11. [Virtual Memory (VSpace)](#11-virtual-memory-vspace)
12. [Platform Abstraction and Hardware Targets](#12-platform-abstraction-and-hardware-targets)
13. [The Proof System](#13-the-proof-system)
14. [Performance Engineering](#14-performance-engineering)
15. [Project Status and Accomplishments](#15-project-status-and-accomplishments)
16. [Roadmap and Future Direction](#16-roadmap-and-future-direction)
17. [Getting Started as a Contributor](#17-getting-started-as-a-contributor)
18. [Glossary](#18-glossary)
19. [Frequently Asked Questions](#19-frequently-asked-questions)

---

## 1. What is seLe4n?

**seLe4n** is a microkernel whose every state transition is an executable pure function written in [Lean 4](https://lean-lang.org/), with every invariant machine-checked by the Lean type-checker. There are **zero `sorry` statements and zero axioms** across the entire production proof surface — meaning no proof obligation is deferred or assumed; every claim is fully verified.

The project started as a formalization of the [seL4](https://sel4.systems/) microkernel's semantics but has evolved into a novel kernel that preserves seL4's capability-based security model while introducing substantial architectural improvements in IPC, scheduling, information-flow enforcement, and service management.

### At a Glance (v0.13.5)

| Metric | Value |
|--------|-------|
| Production Lean code | 28,713 lines across 40 modules |
| Test code | 2,063 lines across 3 test suites |
| Proved declarations | 840 (theorems and lemmas) |
| Sorry/axiom count | 0 |
| Build jobs | 84 |
| First hardware target | Raspberry Pi 5 (ARM64, BCM2712) |

### Why Lean 4?

Lean 4 is both a theorem prover and a general-purpose functional programming language. This dual nature is central to seLe4n's design: the kernel specification *is* the implementation. There is no separate model that must be shown to correspond to executable code — the pure functions that define kernel transitions are themselves the specification, and the Lean type-checker verifies that all stated invariants hold over those functions. This eliminates an entire class of refinement-correctness concerns that traditional verification approaches must address.

---

## 2. Why seLe4n Exists

Microkernels minimize the trusted computing base (TCB) by placing only essential services — scheduling, IPC, memory management, and capability enforcement — in the kernel, with everything else running in user-space. seL4 proved that a microkernel could be formally verified, but its verification stack (Isabelle/HOL, ~200,000 lines of proof) is separate from its C implementation, requiring a multi-layer refinement argument to connect the abstract specification to the executable binary.

seLe4n asks: **what if the kernel specification and the kernel implementation were the same artifact?**

By writing the kernel as pure Lean 4 functions and co-locating proofs with the transitions they verify, seLe4n achieves:

- **No refinement gap:** The executable function *is* the specification. Proofs operate directly on the code that runs.
- **Compositional verification:** Each subsystem (scheduler, IPC, capabilities) has self-contained invariant bundles that compose into a unified kernel invariant.
- **Deterministic semantics:** Every transition returns an explicit `Except KernelError Result` — no hidden non-determinism, no undefined behavior, no silent error swallowing.
- **Executable evidence:** The kernel can be compiled and run as a trace harness, producing fixture-validated output that serves as empirical evidence alongside the formal proofs.

---

## 3. How seLe4n Differs from seL4

seLe4n is not a port of seL4. It is a ground-up reimplementation that uses seL4's capability-based security model as a starting point and then departs significantly in architecture and verification approach.

| Area | seL4 | seLe4n |
|------|------|--------|
| **Language** | C (kernel) + Isabelle/HOL (proofs) | Lean 4 (both kernel and proofs) |
| **Proof methodology** | Post-hoc 3-layer refinement (abstract spec → executable spec → C) | Co-located proofs on executable pure functions |
| **IPC queuing** | Single linked list per endpoint | Dual-queue with intrusive backlinks for O(1) removal |
| **Information flow** | Binary high/low partition | N-domain two-dimensional labels (confidentiality + integrity) |
| **Service management** | Not in kernel | First-class service orchestration with dependency graphs |
| **Capability derivation (CDT)** | Mutable doubly-linked list | Node-stable tree with HashMap-indexed children |
| **Scheduling** | Priority-based round-robin | Priority + EDF tie-breaking with domain-aware partitioning |
| **Data structures** | Arrays and linked lists | Hash maps and hash sets throughout (O(1) hot paths) |
| **Error handling** | Some C assertions; silent error swallowing in revocation | Typed errors on every path; strict first-failure reporting |
| **Hardware abstraction** | C-level HAL | `PlatformBinding` typeclass with three formalized boundary contracts |
| **IPC fast path** | Heavily hand-optimized in C | O(1) by design — no fast-path/slow-path split needed |

---

## 4. Architecture Overview

seLe4n is organized as a layered stack of pure-functional modules. Each layer depends only on layers below it, and each subsystem enforces a strict separation between **operations** (executable transitions) and **invariants** (machine-checked proofs).

```
┌─────────────────────────────────────┐
│          Kernel API                 │  ← Unified public interface
├──────┬──────┬──────┬───────┬────────┤
│Sched │ Cap  │ IPC  │ Life  │Service │  ← Subsystem transitions
│      │      │      │ cycle │        │
├──────┴──────┴──────┴───────┴────────┤
│    Information Flow Enforcement     │  ← Security label checking
├─────────────────────────────────────┤
│  Architecture (VSpace, Adapters)    │  ← Platform-neutral HW boundary
├─────────────────────────────────────┤
│    Model (Object, State, CDT)       │  ← Core data structures
├─────────────────────────────────────┤
│  Foundations (Prelude, Machine)     │  ← Typed IDs, monad, registers
├─────────────────────────────────────┤
│  Platform (Contract, Sim, RPi5)    │  ← Hardware binding typeclass
└─────────────────────────────────────┘
```

### Key Design Principles

- **Deterministic semantics:** Every transition returns `Except KernelError Result`. No hidden state, no non-deterministic branches, no undefined behavior.
- **Local-first theorem layering:** Each subsystem proves its own invariants independently. These compose into a unified `apiInvariantBundle` without requiring cross-subsystem reasoning at the proof level.
- **Executable evidence:** The kernel compiles to an executable trace harness. Running `lake exe sele4n` produces output validated against stable fixture files, providing empirical evidence alongside formal proofs.
- **Typed identifiers everywhere:** `ThreadId`, `ObjId`, `CPtr`, `Slot`, `DomainId`, `ASID`, etc. are all distinct wrapper types — not raw `Nat` aliases. This prevents an entire class of "wrong ID passed to wrong function" bugs at compile time.

### The Kernel Monad (`KernelM`)

All kernel operations run inside `KernelM`, a monad that threads `SystemState` through pure functions and supports early return via `Except KernelError`. There is no mutable state, no IO — just pure functional transformations of an immutable state value.

---

## 5. The Capability System

seLe4n inherits seL4's capability-based access control model but reimplements it with significant structural improvements.

### What Are Capabilities?

A **capability** is an unforgeable token that grants a specific set of access rights to a specific kernel object. Every operation in the kernel requires the caller to present a valid capability — there are no ambient authorities. This is the foundation of the principle of least privilege.

```
Capability = {
  target : CapTarget      -- what object this grants access to
  rights : [AccessRight]  -- read, write, grant, grantReply
  badge  : Option Badge   -- optional IPC identification badge
}
```

**CapTarget variants:**
- `object id` — direct reference to a kernel object
- `cnodeSlot (cnode, slot)` — indirect reference to a capability slot
- `replyCap senderTcb` — one-shot reply capability for IPC call semantics

### CNodes and CSpace

Capabilities are stored in **CNodes** (capability nodes), which form a tree structure called the **CSpace** (capability space). Each thread has a CSpace root, and capability addresses are resolved through a guard/radix path-resolution mechanism similar to seL4.

**seLe4n improvement:** CNode slots are backed by `HashMap Slot Capability` instead of arrays, giving O(1) amortized lookup, insertion, and deletion regardless of CNode size.

### Capability Derivation Tree (CDT)

When a capability is minted (derived from a parent), the derivation relationship is tracked in the **CDT** — a tree structure that enables efficient revocation. Revoking a capability automatically revokes all its descendants.

**seLe4n improvement:** The CDT uses a node-stable representation with a `childMap` HashMap index, enabling:
- O(1) children lookup (vs. linked-list traversal in seL4)
- O(n+e) descendant enumeration for revocation
- Bidirectional slot↔node mappings for fast cross-referencing

### Core Capability Operations

| Operation | Description |
|-----------|-------------|
| `cspaceLookupSlot` | O(1) HashMap lookup to find a capability in a CNode |
| `cspaceResolvePath` | Guard/radix path resolution through CSpace tree |
| `cspaceMint` | Derive a new capability with attenuated rights (`derived.rights ⊆ parent.rights`) |
| `cspaceCopy` | Copy a capability to a new slot |
| `cspaceMove` | Transfer a capability between slots |
| `cspaceDeleteSlot` | Remove a capability and cascade revocation via CDT |
| `cspaceInsertSlot` | Insert a capability (rejects occupied slots — no silent overwrite) |

---

## 6. IPC and the Dual-Queue Innovation

Inter-process communication (IPC) is the heart of any microkernel. In a system where all services run in user-space, every cross-service interaction requires an IPC round-trip through the kernel. IPC performance and correctness are therefore critical.

### The Problem with Traditional Endpoint Queues

seL4 uses a single linked list per endpoint to track waiting threads. When a sender arrives and no receiver is waiting (or vice versa), the thread is appended to the queue. Removing a thread from the middle of the queue — for example, when a timeout fires — requires O(n) traversal.

### seLe4n's Dual-Queue Design

seLe4n introduces **intrusive dual-queue endpoints**: each endpoint maintains two separate queues (one for senders, one for receivers) implemented using intrusive linked-list linkage stored directly in the TCB (Thread Control Block).

Each TCB carries three queue-link fields:
- `queuePrev` — pointer to the previous thread in the queue
- `queuePPrev` — a **backpointer** to the pointer that points to this thread (inspired by Linux's `hlist_node` with `**pprev`)
- `queueNext` — pointer to the next thread in the queue

The `queuePPrev` backpointer is the key innovation: it allows **O(1) arbitrary removal** from anywhere in the queue without traversal. When a thread needs to be dequeued (e.g., due to timeout or cancellation), the kernel updates the backpointer in constant time.

### IPC States

Threads track their IPC blocking state explicitly:
- **ready** — runnable, not blocked
- **blockedOnSend** — waiting in an endpoint's send queue
- **blockedOnReceive** — waiting in an endpoint's receive queue
- **blockedOnCall** — combined send+receive (transitions to blockedOnReply after the send completes)
- **blockedOnReply** — waiting for a reply, with a validated reply-target to prevent confused-deputy attacks
- **blockedOnNotification** — waiting for a notification signal

### Message Passing

IPC messages are staged in the sender's TCB during the send phase and transferred to the receiver upon rendezvous. This avoids shared-buffer races and keeps the message lifecycle fully deterministic.

### Formal Guarantees

The IPC subsystem has 13 preservation theorems proving that the intrusive dual-queue structural invariant (`intrusiveQueueWellFormed`, `dualQueueSystemInvariant`, `tcbQueueLinkIntegrity`) is maintained across all IPC transitions.

---

## 7. Scheduler Design

seLe4n implements a priority-based scheduler with Earliest Deadline First (EDF) tie-breaking and domain-aware partitioning — going well beyond seL4's priority round-robin.

### Three-Level Candidate Selection

When choosing the next thread to run, the scheduler applies three criteria in strict order:

1. **Priority** — Higher numeric priority strictly wins.
2. **EDF tie-breaking** — Among threads at equal priority, the one with the lowest nonzero deadline wins. This enables sporadic server scheduling for real-time workloads.
3. **FIFO stability** — At equal priority and equal deadline, the incumbent thread is retained (no preemption), providing scheduling stability.

The comparison predicate `isBetterCandidate` is proven to be irreflexive, asymmetric, and transitive — guaranteeing a total order.

### Priority-Bucketed RunQueue

The run queue is organized as priority buckets backed by `HashMap Priority (List ThreadId)`. A cached `maxPriority` field tracks the highest active priority, allowing the scheduler to jump directly to the relevant bucket on most scheduling decisions — O(1) amortized instead of scanning the entire thread list.

### Scheduling Domains

seLe4n supports **domain-based scheduling** for temporal isolation and mixed-criticality systems:

- A **domain schedule table** defines a round-robin sequence of domains, each with an allocated time budget.
- Only threads belonging to the **active domain** are eligible to run during that domain's time window.
- When the domain's time expires, the scheduler switches to the next domain in the schedule.

This provides temporal partitioning — a critical feature for safety-critical and real-time systems where different criticality levels must not interfere with each other's timing guarantees.

### Formal Properties

The scheduler subsystem includes proven invariants for:
- `timeSlicePositive` — every runnable thread has a positive time slice remaining
- EDF candidate optimality — the selected thread is provably the best candidate
- Bidirectional consistency between the flat thread list and priority-bucket representation

---

## 8. Information Flow and Security

seLe4n implements a comprehensive information-flow enforcement framework that goes far beyond seL4's binary high/low partition.

### N-Domain Security Labels

Instead of dividing the system into just "high" and "low" security domains, seLe4n uses **parameterized two-dimensional security labels** with independent confidentiality and integrity components. Each kernel entity (thread, endpoint, CNode, service) can be assigned its own label, enabling fine-grained multi-domain security policies.

A flow predicate `securityFlowsTo : Label → Label → Bool` determines whether information may flow from one label to another. This supports lattice-based information-flow control.

### Two-Layer Enforcement

Security enforcement operates at two levels:

**Layer 1 — Policy-checked operations** (explicit information-flow gates):
These operations check the security policy before allowing cross-domain interaction:
- `endpointSendDualChecked` — verifies sender→endpoint flow before IPC send
- `endpointReceiveDualChecked` — verifies endpoint→receiver flow before IPC receive
- `cspaceMintChecked` — verifies source→destination flow for capability derivation
- `cspaceCopyChecked` / `cspaceMoveChecked` — flow checks on capability transfer
- `notificationSignalChecked` — verifies flow for notification signals
- `serviceRestartChecked` — verifies orchestrator→service flow

When a flow is denied, the operation returns `.flowDenied` without modifying state — no partial effects, no side channels.

**Layer 2 — Capability-based operations** (authority through possession):
Operations like `cspaceLookupSlot`, `vspaceMapPage`, and basic `notificationSignal` rely on the capability system itself as the access-control mechanism. Possessing the capability *is* the authorization.

### Non-Interference Proofs

The information-flow subsystem contains **72+ non-interference theorems** covering more than 80% of kernel operations. The `NonInterferenceStep` inductive type has 31 constructors, one for each kernel transition that must preserve non-interference. These proofs guarantee that an observer at one security level cannot distinguish between two system executions that differ only in state invisible to that observer.

---

## 9. Service Orchestration

This is a feature entirely novel to seLe4n — seL4 has no in-kernel service management.

### Why In-Kernel Service Orchestration?

In a microkernel architecture, system services (file systems, network stacks, device drivers) run as user-space processes. Managing their lifecycle — starting, stopping, restarting, and tracking dependencies — is traditionally left to an ad-hoc user-space service manager. seLe4n elevates this to a kernel-level concern with formal guarantees.

### Service Graph

Each service is represented as a `ServiceGraphEntry` containing:
- **Identity** — service ID, backing kernel object, owner thread
- **Status** — a deterministic state machine: `stopped → running → failed → isolated`
- **Dependencies** — a list of services this service depends on
- **Isolation edges** — services this one is explicitly isolated from (for non-interference)

### Acyclic Dependency Enforcement

Before registering a new dependency edge, the kernel performs a **DFS-based reachability check** (`serviceHasPathTo`) using a `HashSet` for visited tracking. If adding the edge would create a cycle, the operation is rejected. This prevents circular dependency deadlocks at the kernel level.

The cycle detection runs in O(n+e) time (where n = services, e = dependency edges), having been optimized from an earlier O(n²) implementation.

### Deterministic Partial-Failure Semantics

Service restart follows strict semantics:
- **Stop phase** — transition running→stopped. If stop fails, the service stays in its current state and the restart aborts.
- **Start phase** — transition stopped→running, checking that all dependencies are satisfied. If start fails, the service remains stopped (no inconsistent intermediate state).

This means a restart is never "half done" — the system is always in a well-defined state.

---

## 10. Memory Management and Lifecycle

### Untyped Memory Model

seLe4n implements seL4's untyped memory concept: all physical memory starts as **untyped regions** that are carved into typed kernel objects through a **retype** operation.

Each `UntypedObject` tracks:
- `regionBase` / `regionSize` — the contiguous physical memory region it manages
- `watermark` — a monotonic free pointer (only moves forward, never backward)
- `children` — objects allocated from this region

The watermark-based allocation prevents double-allocation and enforces proper object sizing. Device untyped regions (e.g., memory-mapped I/O) cannot back kernel objects, preventing security-critical kernel data from living in device memory.

### Lifecycle Operations

| Operation | Description |
|-----------|-------------|
| `retypeFromUntyped` | Carve a new typed object from an untyped region |
| `objectDelete` | Delete a kernel object and reclaim its resources |
| `objectRetype` | Transform an object from one type to another |

### Safety Guards

seLe4n includes lifecycle safety guards not present in seL4:

- **ChildId collision detection** — before creating a new object, the kernel checks that the proposed child ID does not collide with existing objects, preventing silent aliasing.
- **TCB scheduler cleanup** — when retyping away from a TCB, the thread is automatically removed from the scheduler run queue, preventing dangling references.
- **CNode CDT detach** — when retyping away from a CNode, all CDT slot references are detached to prevent orphaned derivation edges.

These guards are proven to maintain the lifecycle invariant bundle across all transitions.

---

## 11. Virtual Memory (VSpace)

### Architecture-Neutral Design

seLe4n models virtual memory through a `VSpaceRoot` abstraction that is independent of any specific hardware page-table format. Virtual-to-physical mappings are stored as `HashMap VAddr PAddr`, giving O(1) lookup.

A `VSpaceBackend` typeclass defines the interface between the abstract VSpace model and platform-specific page-table implementations. The simulation platform provides a `hashMapVSpaceBackend` instance; the Raspberry Pi 5 platform will provide an ARM64 page-table backend.

### ASID Management

Address Space Identifiers (ASIDs) are managed through an `asidTable : HashMap ASID ObjId` that maps ASIDs to their VSpace root objects. This enables O(1) ASID resolution, critical for context-switch performance.

### Operations

| Operation | Description |
|-----------|-------------|
| `vspaceMapPage` | Map a virtual address to a physical address |
| `vspaceUnmapPage` | Remove a virtual-to-physical mapping |
| `vspaceLookup` | Translate a virtual address to physical |
| `resolveAsidRoot` | O(1) HashMap lookup to find VSpace root by ASID |

---

## 12. Platform Abstraction and Hardware Targets

### The PlatformBinding Typeclass

seLe4n uses a Lean 4 typeclass called `PlatformBinding` to abstract over hardware-specific details. Any platform that wants to run seLe4n must provide an instance of this typeclass, which bundles:

- **Platform name** — for diagnostics and tracing
- **MachineConfig** — architectural constants (register width, page size, ASID limits, physical memory map)
- **RuntimeBoundaryContract** — decidable predicates for runtime constraints:
  - `timerMonotonic` — the timer only moves forward
  - `registerContextStable` — register updates produce stable context
  - `memoryAccessAllowed` — access respects the platform memory layout
- **BootBoundaryContract** — boot-time consistency guarantees
- **InterruptBoundaryContract** — IRQ support and handler mapping

All runtime boundary predicates have `Decidable` instances, meaning they can be checked at runtime as well as reasoned about in proofs.

### Raspberry Pi 5 (BCM2712) — First Hardware Target

The RPi5 platform binding is in the "stubs complete, ready for implementation" stage:

- **Memory map:** 4,032 MiB RAM, 32 MiB GPU/VideoCore, ~24.3 MiB low peripherals
- **Architecture:** ARM Cortex-A76, 64-bit registers, 48-bit virtual addresses, 44-bit physical addresses, 4 KiB pages, 16-bit ASIDs
- **Interrupt controller:** GIC-400 with 192 SPIs; timer PPI IDs configured for non-secure physical (30) and virtual (27) timers
- **Boot contract:** Exception level (EL1/EL2), MMU identity-map flag, DTB location, kernel entry point, initial stack pointer

### Simulation Platform

For development and testing, a simulation platform provides permissive contracts that allow the kernel to be exercised without real hardware. The executable trace harness (`lake exe sele4n`) runs against this simulation platform.

### Architecture Adapter Layer

Between the abstract kernel operations and the platform binding sits an **adapter layer** that enforces boundary contracts at runtime:
- `adapterAdvanceTimer` — increments timer only if monotonicity holds
- `adapterWriteRegister` — updates register only if context stability holds
- `adapterReadMemory` — reads memory only if access is allowed

If a contract is violated, the adapter returns an error rather than proceeding — defense in depth against platform misbehavior.

---

## 13. The Proof System

### The Invariant/Operations Split

Every kernel subsystem maintains a strict separation:
- **`Operations.lean`** — executable pure functions that transform `SystemState`
- **`Invariant.lean`** — machine-checked theorems proving that the operations preserve stated invariants

This separation serves multiple purposes: it keeps the executable code readable without interleaved proofs, it enables independent proof development, and it makes the invariant surface auditable without needing to understand implementation details.

### Invariant Bundles

Each subsystem defines an invariant bundle — a structure collecting all properties that the subsystem must maintain:

| Bundle | Key Properties |
|--------|---------------|
| `SchedulerInvariantBundle` | Runnable consistency, priority monotonicity, time-slice positivity |
| `CapabilityInvariantBundle` | 7-tuple including slot-count bounds, CDT completeness, CDT acyclicity |
| `IpcInvariantBundle` | Endpoint state consistency, dual-queue well-formedness, link integrity |
| `LifecycleInvariantBundle` | Object type stability, CDT graph integrity, watermark monotonicity |
| `ServiceInvariantBundle` | State machine validity, cycle-freedom, dependency satisfaction |
| `InformationFlowInvariantBundle` | Label consistency, non-interference preservation |

These compose into a unified `apiInvariantBundle` (via `proofLayerInvariantBundle`) that captures the full kernel invariant.

### Zero Sorry, Zero Axiom

The production proof surface contains no `sorry` (deferred proof obligation) and no `axiom` (unverified assumption). Every theorem is fully checked by Lean's type-checker. This is mechanically verified by the Tier 0 hygiene check, which scans for forbidden markers on every build.

Any exception to this rule (e.g., in experimental or testing code) must carry a `TPI-D*` annotation for explicit tracking.

### Proof Scale

With 840 proved declarations across 28,713 lines of production code, seLe4n achieves approximately **1 proved declaration per 34 lines of code** — a high proof density for a kernel of this complexity.

---

## 14. Performance Engineering

seLe4n underwent a comprehensive kernel performance audit that identified 14 findings across 6 subsystems. All 14 have been resolved through systematic migration to O(1) hash-based data structures.

### Before and After

| Subsystem | Before | After |
|-----------|--------|-------|
| Object store | Linear list scan O(n) | `HashMap ObjId KernelObject` O(1) |
| ASID table | Linear scan O(n) | `HashMap ASID ObjId` O(1) |
| Run queue | Full list scan O(n) | Priority-bucketed with cached max O(1) |
| CNode slots | Linear slot array O(m) | `HashMap Slot Capability` O(1) |
| VSpace mappings | Linear mapping list O(m) | `HashMap VAddr PAddr` O(1) |
| IPC queues | Linear dequeue O(n) | Intrusive dual-queue O(1) |
| Service graph | BFS with list visited O(n²) | DFS with HashSet O(n+e) |
| CDT children | Linked-list traversal O(k) | `childMap` HashMap O(1) |
| Info-flow projection | Repeated linear scan O(n) | Precomputed `HashSet ObjId` O(1) |

### Design Philosophy

Rather than implementing separate fast-paths and slow-paths (as seL4 does for IPC), seLe4n makes the **default path fast by construction**. When every data structure supports O(1) operations, there is no need for hand-optimized special cases — the common case and the worst case have the same algorithmic complexity.

---

## 15. Project Status and Accomplishments

### Core Kernel (Complete)

- **Full capability system** with CSpace path resolution, mint/copy/move/delete, rights attenuation, and CDT-based revocation with strict error reporting.
- **Intrusive dual-queue IPC** with O(1) arbitrary removal, 5 blocking states, staged message passing, reply-target scoping for confused-deputy prevention, and notification signaling.
- **Priority + EDF scheduler** with domain partitioning, priority-bucketed run queue, time-slice preemption, and proven candidate optimality.
- **Untyped memory model** with watermark-based allocation, device-region rejection, and collision detection guards.
- **Virtual memory abstraction** with `VSpaceBackend` typeclass, O(1) ASID resolution, and platform-neutral page mapping.
- **Service orchestration** with dependency graphs, O(n+e) cycle detection, deterministic start/stop/restart semantics, and isolation edges.

### Formal Verification (Substantial)

- **840 proved declarations** with zero sorry/axiom across the production surface.
- **72+ non-interference theorems** covering >80% of kernel operations.
- **13 IPC structural invariant preservation** theorems with dual-queue well-formedness.
- **25+ capability invariant preservation** theorems with a meaningful 7-tuple bundle (slot-count bounds, CDT completeness, CDT acyclicity).
- **8+ scheduler invariant theorems** with EDF bridge and bidirectional consistency.
- **27+ lifecycle safety theorems** with childId guards and TCB cleanup proofs.

### Security Hardening (Production-Ready)

- Policy-checked wrappers (`*Checked` operations) enforce information-flow security at 8 policy-gated operations.
- Thread-state updates fail with `objectNotFound` for missing TCBs (prevents ghost queue entries).
- Sentinel ID 0 rejected at IPC boundaries.
- Reply-target scoping prevents confused-deputy attacks on IPC call paths.
- Strict revocation error reporting (vs. seL4's silent swallowing).
- Lifecycle guards prevent childId collision, self-overwrite, and dangling references.

### Infrastructure (Mature)

- **4-tier test suite** with automated CI: hygiene → build → trace → invariant surface anchors.
- **Fixture-backed executable evidence** — trace harness output validated against stable expected files.
- **Documentation synchronization** — automated checking that README, spec, development guide, and GitBook all reflect current state.
- **Website link protection** — manifest-based verification that no linked repository paths are broken.

---

## 16. Roadmap and Future Direction

### Near-Term: Model Refinement

The next phase focuses on improving model fidelity and proof quality:

- **Badge bitmask modeling** — Representing notification badges as proper bitmasks rather than abstract values, matching real hardware behavior.
- **Per-thread register contexts** — Extending the register model to support full per-thread register save/restore.
- **Multi-level CSpace** — Supporting CSpace trees deeper than one level for more flexible capability address spaces.
- **Invariant quality refinement** — Reclassifying tautological invariants, adding adapter proof hooks, and strengthening remaining proof surface gaps.

### Medium-Term: Hardware Binding (Raspberry Pi 5)

The project follows a structured progression toward real hardware:

| Stage | Description | Status |
|-------|-------------|--------|
| **H0** | Architecture-neutral kernel semantics and proofs | Complete |
| **H1** | Architecture-boundary interfaces and adapter layer | Complete |
| **H2** | Audit-driven proof deepening | Active |
| **H3** | Platform binding — map abstract model to RPi5 hardware | Prep complete |
| **H4** | Evidence convergence — connect proofs to platform assumptions | Planned |

The RPi5 platform stubs are already in place with BCM2712 memory maps, GIC-400 interrupt controller constants, and ARM Cortex-A76 configuration. The next step is implementing the actual platform binding that connects the abstract `PlatformBinding` typeclass to real hardware operations.

### Long-Term Vision

- **Executable kernel on real hardware** — Running seLe4n on a Raspberry Pi 5 with verified boot, interrupt handling, and user-space process isolation.
- **Complete non-interference coverage** — Extending the 80%+ information-flow proofs to cover 100% of kernel transitions.
- **Mixed-criticality real-time support** — Leveraging domain partitioning and EDF scheduling for safety-critical systems (automotive, aerospace, medical).
- **Multi-core support** — Extending the single-core model to verified multi-core operation with inter-processor interrupt (IPI) handling.
- **User-space ecosystem** — Building verified user-space services (drivers, file systems, network stacks) that compose with the kernel's formal guarantees.

---

## 17. Getting Started as a Contributor

### Quick Start

```bash
# Clone the repository
git clone https://github.com/hatter6822/seLe4n.git
cd seLe4n

# Set up the Lean 4 environment and build
./scripts/setup_lean_env.sh --build

# Run the executable trace harness
lake exe sele4n

# Run the smoke tests (recommended before any PR)
./scripts/test_smoke.sh
```

### Key Resources

| Resource | Description |
|----------|-------------|
| [seLe4n.org](https://seLe4n.org) | Project website |
| [Repository](https://github.com/hatter6822/seLe4n) | Source code, issues, PRs |
| `docs/DEVELOPMENT.md` | Day-to-day contributor workflow |
| `docs/spec/SELE4N_SPEC.md` | Normative project specification |
| `docs/TESTING_FRAMEWORK_PLAN.md` | Testing tier details |
| `CONTRIBUTING.md` | 5-minute contributor onboarding |

### Validation Tiers

| Tier | Command | What It Checks | When to Run |
|------|---------|----------------|-------------|
| 0+1 | `./scripts/test_fast.sh` | Hygiene + build | Every change |
| 0-2 | `./scripts/test_smoke.sh` | + trace + negative-state | Before any PR |
| 0-3 | `./scripts/test_full.sh` | + invariant surface anchors | Theorem/invariant changes |
| 0-4 | `NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh` | + determinism checks | Nightly/CI |

### Contribution Guidelines

- Keep scope to one coherent change per PR.
- All kernel transitions must be deterministic — explicit success/failure, no hidden non-determinism.
- Pair any invariant/theorem changes with implementation changes in the same PR.
- Update documentation (README, spec, dev guide) alongside behavioral changes.
- Run at least `test_smoke.sh` before submitting.

---

## 18. Glossary

| Term | Definition |
|------|-----------|
| **Capability** | An unforgeable token granting specific access rights to a kernel object |
| **CNode** | A kernel object that stores capabilities in indexed slots |
| **CSpace** | The tree of CNodes forming a thread's capability address space |
| **CDT** | Capability Derivation Tree — tracks parent/child relationships between capabilities for revocation |
| **TCB** | Thread Control Block — the kernel object representing a thread |
| **Endpoint** | An IPC rendezvous point where senders and receivers meet |
| **Notification** | A lightweight signaling mechanism using badge bitmasks |
| **Untyped** | A region of physical memory not yet carved into typed kernel objects |
| **Retype** | The operation of creating a typed kernel object from untyped memory |
| **VSpace** | Virtual address space — the mapping from virtual to physical addresses |
| **ASID** | Address Space Identifier — uniquely identifies a VSpace for hardware TLB |
| **RunQueue** | The scheduler's priority-bucketed data structure of runnable threads |
| **EDF** | Earliest Deadline First — a real-time scheduling algorithm used for tie-breaking |
| **Domain** | A scheduling domain for temporal partitioning in mixed-criticality systems |
| **KernelM** | The kernel monad — threads SystemState through pure functions with error handling |
| **Invariant Bundle** | A structure collecting all proven properties a subsystem must maintain |
| **Non-interference** | A security property: observers at one level cannot distinguish executions differing only in invisible state |
| **Platform Binding** | A typeclass instance connecting the abstract kernel model to specific hardware |
| **Intrusive Queue** | A linked list where link pointers are stored inside the elements themselves (in the TCB) |
| **`queuePPrev`** | A backpointer (pointer-to-pointer) enabling O(1) arbitrary removal from intrusive queues |
| **Badge** | An IPC identification value attached to capabilities, transferred during IPC |

---

## 19. Frequently Asked Questions

### Is seLe4n a fork of seL4?

No. seLe4n is a ground-up reimplementation in Lean 4. It uses seL4's capability-based security model as inspiration but does not share any code with the seL4 C implementation or the seL4 Isabelle/HOL proofs. The architecture has diverged significantly, with novel features like dual-queue IPC, N-domain information flow, and service orchestration.

### Can I run seLe4n on real hardware today?

Not yet. The kernel currently runs as an executable trace harness on a simulation platform. The Raspberry Pi 5 hardware binding stubs are in place, but the actual platform implementation connecting the abstract model to ARM64 hardware is the next major milestone.

### What does "zero sorry, zero axiom" mean?

In Lean 4, `sorry` is a keyword that allows you to skip a proof ("I'll prove this later"), and `axiom` declares an unproven assumption. seLe4n has neither in its production proof surface — every stated property is fully machine-checked. This is mechanically verified on every build.

### How does the proof approach differ from seL4?

seL4 uses a three-layer refinement approach: an abstract specification in Isabelle/HOL, an executable specification in Haskell, and a C implementation, with proofs connecting each layer. seLe4n collapses this into a single layer — the Lean 4 pure functions *are* both the specification and the implementation, with proofs operating directly on the executable code.

### What is Lean 4?

[Lean 4](https://lean-lang.org/) is a functional programming language and interactive theorem prover developed at Microsoft Research (now maintained by the Lean FRO). It combines a dependently-typed lambda calculus (for proofs) with a practical programming language (for executable code), making it uniquely suited for projects like seLe4n where the specification and implementation must be the same artifact.

### How can I contribute?

Start with the [Contributing Guide](https://github.com/hatter6822/seLe4n/blob/main/CONTRIBUTING.md) and `docs/DEVELOPMENT.md`. Pick a focused area, make a small change, run `test_smoke.sh`, and open a PR. The project welcomes contributions to kernel implementation, proof engineering, testing, documentation, and platform binding.

### What makes this different from other verified kernels?

Most verified kernels (seL4, CertiKOS, Komodo) use separate languages for implementation and verification. seLe4n uses a single language (Lean 4) for both, eliminating the refinement gap. Additionally, seLe4n introduces architectural innovations (dual-queue IPC, service orchestration, N-domain information flow) that go beyond replicating existing kernels.

### Is this production-ready?

The kernel architecture, proof surface, and security hardening are production-grade. What remains is the hardware binding (connecting the abstract model to real ARM64 hardware on the Raspberry Pi 5) and completing the remaining model fidelity improvements. The project is actively working toward these goals.

---

*This wiki is maintained by the r/seLe4n community. For corrections or additions, open an issue or PR on the [repository](https://github.com/hatter6822/seLe4n).*

*Last updated: March 2026 (v0.13.5)*
