# seL4 Microkernel Specification Summary

This document provides a detailed summary of the seL4 microkernel specification. seL4
(Secure Embedded L4) is a third-generation, high-assurance, capability-based microkernel
in the L4 family. It is the world's first operating-system kernel with a machine-checked
proof of functional correctness.

---

## Table of Contents

1. [Design Philosophy](#1-design-philosophy)
2. [Kernel Objects](#2-kernel-objects)
3. [Capability System](#3-capability-system)
4. [System Call Interface](#4-system-call-interface)
5. [IPC Mechanisms](#5-ipc-mechanisms)
6. [Memory Management](#6-memory-management)
7. [Virtual Memory](#7-virtual-memory)
8. [Thread Management](#8-thread-management)
9. [Scheduling](#9-scheduling)
10. [Fault Handling](#10-fault-handling)
11. [Interrupt Handling](#11-interrupt-handling)
12. [Virtualization Support](#12-virtualization-support)
13. [MCS Extensions](#13-mcs-extensions)
14. [Formal Verification](#14-formal-verification)
15. [Architecture Support](#15-architecture-support)

---

## 1. Design Philosophy

seL4 keeps only the minimal mechanisms required in kernel mode:

- **Thread management** and scheduling.
- **IPC primitives** for synchronous message passing and asynchronous signalling.
- **Capability-based access control** mediating all authority in the system.
- **Virtual memory primitives** providing hardware-level address-space management.

- comprehensive-audit findings:
  [`docs/audits/AUDIT_v0.9.32.md`](./audits/AUDIT_v0.9.32.md)
- comprehensive-audit workstream execution plan:
  [`docs/audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md`](./audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md)

---

## 2. Kernel Objects

seL4 manages a fixed set of first-class kernel object types. Each object implements a
particular abstraction and supports one or more invocable methods. Access to every object
is mediated exclusively by capabilities.

### 2.1 Platform-Independent Objects

- **M4-A:** complete (lifecycle/retype foundations)
- **M4-B:** complete (lifecycle-capability composition hardening)
- M4-B (complete) baseline is retained for historical compatibility checks
- **M5:** complete (service graph + policy surfaces + proof package)
- **M6:** complete (architecture-boundary assumptions/adapters/invariant hooks)
- **M7:** complete (audit remediation WS-A1..WS-A8)
- **Current active slice:** comprehensive-audit v0.9.32 WS-C execution kickoff (Phase P0/P1 transition; execution now beginning on WS-C workstreams).

---

## 3. Capability System

### 3.1 Fundamentals

All access to kernel services is mediated by **capabilities**. A capability is an
unforgeable token that references a kernel object and encodes specific access rights.
This implements a take-grant access control model: no operation can be performed without
holding a capability with sufficient rights.

### 3.2 CSpace Structure

A thread's **Capability Space (CSpace)** is a directed graph of CNode objects rooted at
the thread's CSpace root capability. A capability address is the concatenation of indices
along the CNode path from the root to the target slot.

Each CNode has a configurable **guard** -- a fixed bit prefix checked during address
resolution. Guards enable sparse and efficient capability address spaces. Address
resolution proceeds as follows:

1. Strip the guard bits from the front of the address and verify they match.
2. Use the next *radix* bits as the index into the CNode's slot array.
3. If the slot contains another CNode capability and there are remaining address bits,
   recurse into that CNode.
4. If no bits remain, the current slot is the target.

### 3.3 Access Rights

seL4 defines four orthogonal access rights whose interpretation depends on the object type:

| Right | Endpoint | Frame | Notification |
|---|---|---|---|
| **Read** | Receive messages | Read data | Wait for signal |
| **Write** | Send messages | Write data | Signal |
| **Grant** | Transfer capabilities via IPC | -- | -- |
| **GrantReply** | Transfer reply capability via IPC | -- | -- |

Rights can be reduced but never elevated when deriving new capabilities.

### 3.4 Capability Operations (CNode Methods)

| Method | Description |
|---|---|
| `seL4_CNode_Mint` | Copy a capability with a new badge and/or reduced rights. |
| `seL4_CNode_Copy` | Copy a capability to a new slot with a rights mask. |
| `seL4_CNode_Move` | Move a capability between slots (source becomes empty). |
| `seL4_CNode_Mutate` | Move a capability while modifying its CNode guard. |
| `seL4_CNode_Delete` | Remove a capability from a slot. Destroys the object if it was the last capability to it. |
| `seL4_CNode_Revoke` | Recursively delete all capabilities derived from the specified capability. |
| `seL4_CNode_Rotate` | Atomically swap/rotate capabilities between two slots. |
| `seL4_CNode_SaveCaller` | (Non-MCS only) Save the implicit reply capability into a regular CSlot. |
| `seL4_CNode_CancelBadgedSends` | Cancel all outstanding sends using a specific badge on an endpoint. |

### 3.5 Capability Derivation Tree (CDT)

The kernel maintains a **Capability Derivation Tree (CDT)** tracking parent-child
relationships between capabilities. Relationships are established by:

- `seL4_Untyped_Retype` -- newly created capabilities become children of the untyped
  capability.
- `seL4_CNode_Mint` / `seL4_CNode_Copy` -- the new capability becomes a child of the
  source.

`seL4_CNode_Revoke` traverses the CDT to remove all descendants. This mechanism is
central to safe memory reclamation and authority revocation.

### 3.6 Badges

Endpoint and Notification capabilities support **badging**: an unbadged capability can be
minted with a non-zero badge value (one machine word; on 32-bit platforms, the low 28 bits
are usable). When a message is sent through a badged endpoint, the receiver sees the
sender's badge, enabling sender identification. A badged capability is treated as an
"original badged capability" in the CDT.

---

## 4) Active slice specification: comprehensive-audit WS-C portfolio

seL4 has a minimal system call interface. Logically, the kernel provides only three
fundamental operations: **Send**, **Receive**, and **Yield**. All other calls are
combinations or variants of these.

### 4.1 Standard (Non-MCS) System Calls

| System Call | Description |
|---|---|
| `seL4_Send(dest, msgInfo)` | Blocking send on an endpoint. Blocks until a receiver arrives. |
| `seL4_NBSend(dest, msgInfo)` | Non-blocking send. If no receiver is waiting, the message is silently dropped. |
| `seL4_Call(dest, msgInfo)` | Atomic send + receive. Generates a one-off reply capability for the receiver. Blocks until a reply is received. |
| `seL4_Recv(src, sender)` | Blocking receive on an endpoint or notification. Returns the sender's badge. |
| `seL4_NBRecv(src, sender)` | Non-blocking receive. Returns immediately if no message is pending. |
| `seL4_Reply(msgInfo)` | Send a reply via the implicit reply capability stored in the TCB. Cannot block. |
| `seL4_ReplyRecv(src, msgInfo, sender)` | Atomic reply + receive (combined for efficiency). |
| `seL4_Yield()` | Donate the remaining timeslice to another thread of the same priority. |

- **WS-C1:** IPC handshake correctness (critical; completed for notification badge accumulation and waiter ipcState wiring)
- **WS-C2:** Scheduler semantic fidelity (high; completed)
- **WS-C3:** Proof-surface de-tautologization (critical; kickoff starting)
- **WS-C4:** Test validity hardening (high; kickoff starting)
- **WS-C5:** Information-flow assurance (critical; Phase P2 target)
- **WS-C6:** CI and supply-chain hardening (medium; Phase P3 target)
- **WS-C7:** Model structure and maintainability (medium; Phase P3 target)
- **WS-C8:** Documentation and GitBook consolidation (high; in progress)

- `seL4_Signal(dest)` -- equivalent to `seL4_Send` on a Notification capability.
- `seL4_Wait(src, sender)` -- equivalent to `seL4_Recv` on a Notification.
- `seL4_Poll(src, sender)` -- non-blocking variant of `seL4_Wait`.

- **P0:** WS-C8 baseline reset + active-plan publication (in progress)
- **P1:** WS-C3 + fixture-repair WS-C4 (WS-C1 + WS-C2 completed)
- **P2:** WS-C5 + remaining WS-C4 assurance expansion
- **P3:** WS-C6 + WS-C7 sustainment hardening

### 4.4 Acceptance expectations for WS-C work

| System Call | Description |
|---|---|
| `seL4_Recv(src, sender, reply)` | Takes an explicit Reply object to store the generated reply capability. |
| `seL4_ReplyRecv(src, msgInfo, sender, reply)` | Reply + receive with explicit Reply object. |
| `seL4_NBSendRecv(dest, msgInfo, src, sender, reply)` | Non-blocking send on one capability + blocking receive on another (single syscall). |
| `seL4_NBSendWait(dest, msgInfo, src, sender)` | Non-blocking send + wait (no reply object). |
| `seL4_Wait(src, sender)` | Receive without reply object (used when no reply is expected). |
| `seL4_NBWait(src, sender)` | Non-blocking variant of `seL4_Wait`. |

`seL4_Reply` is removed as a standalone syscall in MCS; replies are always performed
through explicit Reply objects.

Authoritative detail for per-workstream goals, dependencies, and evidence gates:
[`docs/audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md`](./audits/AUDIT_v0.9.32_WORKSTREAM_PLAN.md).

Security assumptions and trust boundaries for active and historical slices are documented in [`docs/THREAT_MODEL.md`](./THREAT_MODEL.md).

---

## 5. IPC Mechanisms

### 5.1 Synchronous IPC (Endpoints)

IPC in seL4 is synchronous and zero-copy where possible. Messages are transferred directly
between sender and receiver through **Endpoint** objects acting as rendezvous points:

- If no receiver is waiting, the sender blocks (or the message is silently dropped for
  `seL4_NBSend`).
- If no sender is waiting, the receiver blocks.
- The kernel never buffers IPC data internally.

### 5.2 IPC Message Format

Each message consists of:

**Message Info Tag (`seL4_MessageInfo_t`)** -- a single machine word containing:

| Field | Description |
|---|---|
| `label` | User-defined; not interpreted by kernel; passed unmodified (used for operation codes). |
| `length` | Number of data words to transfer (max `seL4_MsgMaxLength`). |
| `extraCaps` | Number of capabilities to transfer. |
| `capsUnwrapped` | Bitmask indicating which capabilities were unwrapped (receive side only). |

**Message Registers (MRs):** Data payload. Small messages fit in hardware registers
(`seL4_FastMessageRegisters`, typically 4); overflow spills into the thread's IPC buffer
in memory.

**Capability Transfer:** Capabilities to send are placed in the `caps` array of the
sender's IPC buffer. The receiver specifies a destination slot via `receiveCNode`,
`receiveIndex`, and `receiveDepth` fields in its IPC buffer. Requires `Grant` or
`GrantReply` right on the endpoint capability.

**Capability Unwrapping:** If a transferred capability refers to the same endpoint through
which the message is sent, the kernel "unwraps" it: the badge is placed in the receiver's
`caps_or_badges` array, and the corresponding bit is set in `capsUnwrapped`.

### 5.3 IPC Fastpath

A heavily optimized kernel code path handles common-case IPC. The fastpath activates when:

- The message fits in `seL4_FastMessageRegisters` hardware registers (typically 4 words).
- No capability transfer is requested.
- Both sender and receiver have valid address spaces.
- No higher-priority thread is runnable.

The fastpath applies to `seL4_Call` and `seL4_ReplyRecv`. Benchmark performance:

| Platform | IPC Call Round-Trip |
|---|---|
| ARM Cortex-A57 @ 1.9 GHz | ~735 cycles |
| Intel Skylake i7 @ 3.4 GHz | ~1,489 cycles (without Spectre/Meltdown mitigations) |

### 5.4 Notifications (Asynchronous Signalling)

Notification objects are **not** message-passing channels. They are arrays of binary
semaphores with three states: Idle, Active, and Waiting.

- `seL4_Signal` -- bitwise-ORs the badge of the signalling capability into the
  notification word. If a thread is waiting, it is woken.
- `seL4_Wait` -- blocks until the notification word is non-zero, then atomically reads
  and clears it.
- `seL4_Poll` -- non-blocking variant of Wait.

A notification can be **bound** to a thread (1:1 relationship). A thread blocked on an
endpoint receive will also be woken by signals from its bound notification. This is the
primary mechanism for hardware interrupt delivery.

### 5.5 Call/Reply Protocol

`seL4_Call` combines a send with a receive and generates a **one-off reply capability**:

- **Non-MCS:** stored internally in the receiver's TCB. Can be saved to a CSlot via
  `seL4_CNode_SaveCaller`.
- **MCS:** stored in an explicit Reply object passed to `seL4_Recv` / `seL4_ReplyRecv`.

Invoking the reply capability is guaranteed not to block (the caller is already waiting).
Once used, the reply capability is consumed.

---

## 6. Memory Management

### 6.1 Zero-Heap Kernel Design

seL4 does **not** dynamically allocate memory for kernel objects. The kernel has no heap.
At boot, all free physical memory is handed to the root task as **Untyped Memory**
capabilities. All kernel objects must be explicitly created from untyped memory via
`seL4_Untyped_Retype`.

This design eliminates an entire class of kernel vulnerabilities (heap overflows, use-after-free)
and makes memory consumption fully deterministic and user-controlled.

### 6.2 Untyped Memory and Retyping

`seL4_Untyped_Retype` creates kernel objects from untyped memory:

```
seL4_Untyped_Retype(
    service,       // capability to the untyped memory
    type,          // object type (e.g., seL4_TCBObject, seL4_EndpointObject)
    size_bits,     // size parameter (for variable-size objects only)
    root,          // CNode root for destination capabilities
    node_index,    // CNode index
    node_depth,    // CNode depth
    node_offset,   // starting slot offset in destination CNode
    num_objects    // number of objects to create
)
```

**Fixed-size objects:** TCB, Endpoint, Notification, Reply -- `size_bits` is ignored.

**Variable-size objects:** Untyped, CNode (CapTable), SchedContext -- `size_bits`
specifies the log2 size.

### 6.3 Watermark-Based Allocation

Each untyped region maintains a single **watermark**. Addresses before the watermark are
allocated; addresses after are free. On each retype:

1. The watermark advances to the alignment boundary required by the new object.
2. The watermark then advances past the object's extent.

Alignment gaps are wasted and cannot be reclaimed until all children are revoked. Best
practice: allocate largest objects first to minimize waste.

### 6.4 Memory Reclamation

To reclaim memory from an untyped region:

1. Call `seL4_CNode_Revoke` on the untyped capability. This destroys all capabilities
   derived from it (all objects created from it).
2. The watermark resets. The memory is zeroed on the first subsequent retype.

The CDT enforces safe memory reuse: all capabilities derived from an untyped region must
be removed before that region can be reallocated.

### 6.5 Device Memory

Untyped capabilities with `device = true` represent memory-mapped I/O regions or
non-RAM areas. Device memory:

- Cannot be written by the kernel.
- Is not zeroed on retype.
- Is retyped into device frames for mapping into user VSpaces.

---

## 7. Virtual Memory

### 7.1 VSpace Structure

The kernel provides hardware-level virtual memory primitives but **no virtual memory
management policy**. User-level code must explicitly create and install all paging
structures.

The root paging structure type is architecture-dependent:

| Architecture | Top-Level Object | Paging Levels |
|---|---|---|
| x86_64 | PML4 | PML4 → PDPT → PageDirectory → PageTable → Frame |
| IA-32 | PageDirectory | PageDirectory → PageTable → Frame |
| AArch32 | PageDirectory | PageDirectory → PageTable → Frame |
| AArch64 | VSpace | VSpace → PageTable → PageTable → PageTable → Frame |
| RISC-V | PageTable | PageTable (at all levels) → Frame |

### 7.2 Page Mapping

Pages are mapped with architecture-specific invocations:

```
seL4_<Arch>_Page_Map(page, vspace, vaddr, rights, vm_attributes)
```

- `rights` -- Read, Write permissions (silently downgraded if the capability lacks them).
- `vm_attributes` -- caching policy (e.g., cacheable, uncacheable, write-through).
- If required intermediate structures are missing, the call fails with
  `seL4_FailedLookup`, and `seL4_MappingFailedLookupLevel()` indicates how many bits
  could not be resolved.
- Each frame capability tracks exactly one mapping. To map a frame at multiple virtual
  addresses, the capability must be copied.

Pages can be unmapped via `Unmap` invocations on the frame or any intermediate paging
structure, or by deleting the last capability to the relevant structure.

### 7.3 ASID Management

Each VSpace must be assigned an ASID before use:

1. Create an ASID Pool from ASID Control + a 4 KiB untyped (each pool holds 1,024 slots).
2. `seL4_ASIDPool_Assign(pool, vspace)` assigns an ASID to the VSpace.

---

## 8. Thread Management

### 8.1 TCB Configuration

Each thread is represented by a TCB. A newly created TCB is initially suspended (inactive).

| Method | Description |
|---|---|
| `seL4_TCB_Configure` | Batch configuration: sets IPC buffer frame and address, CSpace root, VSpace root. |
| `seL4_TCB_SetSpace` | Sets fault endpoint, CSpace root, and VSpace root. |
| `seL4_TCB_SetIPCBuffer` | Sets the IPC buffer address and backing frame capability. |
| `seL4_TCB_SetPriority` | Sets thread priority (0--255). Caller cannot set a priority exceeding its own MCP. |
| `seL4_TCB_SetMCPriority` | Sets Maximum Controlled Priority (the highest priority this thread can assign to others). |
| `seL4_TCB_SetSchedParams` | (MCS) Sets priority, MCP, scheduling context, and fault endpoint. |
| `seL4_TCB_SetTimeoutEndpoint` | (MCS) Sets the timeout fault handler endpoint. |
| `seL4_TCB_ReadRegisters` | Read a suspended thread's register state. |
| `seL4_TCB_WriteRegisters` | Set a thread's registers (instruction pointer, stack pointer, etc.). Optionally resumes the thread. |
| `seL4_TCB_CopyRegisters` | Copy register state between threads. |
| `seL4_TCB_Resume` | Make a thread runnable (eligible for scheduling). |
| `seL4_TCB_Suspend` | Deactivate a thread (preserves state but removes from scheduler). |
| `seL4_TCB_BindNotification` | Bind a notification object to the thread (1:1). |
| `seL4_TCB_UnbindNotification` | Unbind the notification. |
| `seL4_TCB_SetAffinity` | (SMP) Set the CPU affinity of the thread. |

### 8.2 Thread Lifecycle

1. Create a TCB via `seL4_Untyped_Retype`.
2. Configure address spaces and IPC buffer via `seL4_TCB_Configure` / `seL4_TCB_SetSpace`.
3. Set initial registers (instruction pointer, stack pointer) via `seL4_TCB_WriteRegisters`.
4. Start execution via `seL4_TCB_Resume` (or the `resume_target` flag in `WriteRegisters`).
5. Pause with `seL4_TCB_Suspend`; inspect with `seL4_TCB_ReadRegisters`.
6. Destroy by deleting the last capability to the TCB.

---

## 9. Scheduling

### 9.1 Default (Non-MCS) Scheduling

seL4 uses a **preemptive, tickless, priority-based round-robin scheduler** with 256
priority levels (0--255, where 255 is the highest).

- The scheduler always selects the highest-priority runnable thread.
- Same-priority threads are scheduled round-robin.
- `seL4_Yield` donates the remaining timeslice to another thread at the same priority.
- Each TCB has:
  - **Priority** -- the effective scheduling priority.
  - **Maximum Controlled Priority (MCP)** -- upper bound on priorities this thread can
    set on other threads.

### 9.2 Domain Scheduler (Non-MCS)

For timing-channel mitigation, the non-MCS kernel provides a **domain scheduler**:

- Threads are assigned to **domains** via `seL4_DomainSet_Set`.
- Only threads in the currently active domain are scheduled.
- Cross-domain IPC is delayed until a domain switch.
- The domain schedule is statically configured at compile time as a cyclic schedule.
- A domain-specific idle thread runs when no threads are runnable in the active domain.

### 9.3 MCS Scheduling

The MCS extensions introduce **capability-based control over CPU time** through
Scheduling Context objects. See [Section 13](#13-mcs-extensions) for details.

---

## 10. Fault Handling

### 10.1 Mechanism

When a thread faults, the kernel blocks it and delivers a **fault message** over the
thread's registered fault endpoint. The kernel acts as the IPC sender; a fault handler
thread acts as the receiver. The handler corrects the fault condition and replies to
resume the faulting thread.

Fault endpoints are regular seL4 Endpoint objects. The kernel's capability to the
endpoint can be badged to distinguish faults from different threads, allowing a single
handler to serve multiple threads.

### 10.2 Fault Types

| Fault Type | Trigger | Availability |
|---|---|---|
| **Capability Fault** | Invalid capability access (lookup failure). | All configurations |
| **VM Fault** | Page fault or invalid memory access. | All configurations |
| **Unknown Syscall** | Unrecognized syscall number. | All configurations |
| **Debug Fault** | Breakpoint, watchpoint, or single-step event. | All configurations |
| **Timeout Fault** | Thread exhausts its scheduling context budget. | MCS only |

Each fault type has its own IPC message format with type-specific information (e.g., the
faulting address and access type for VM faults, the invalid capability address for
capability faults).

### 10.3 Fault Endpoint Configuration

- **Non-MCS:** The fault endpoint capability must reside in the faulting thread's own CSpace.
  Set via `seL4_TCB_SetSpace` or `seL4_TCB_Configure`.
- **MCS:** The fault endpoint capability must reside in the CSpace of the thread calling
  `seL4_TCB_Configure`. Timeout endpoints are set separately via
  `seL4_TCB_SetTimeoutEndpoint`.

### 10.4 Resuming Faulting Threads

Two options:

1. `seL4_Reply` (or `seL4_ReplyRecv`) with `label = 0` in the message info.
2. `seL4_TCB_Resume` on the faulting thread's TCB.

If the fault condition is not corrected, resuming the thread will re-trigger the fault.

---

## 11. Interrupt Handling

### 11.1 Model

Hardware interrupts are delivered to user-level device drivers via Notification objects.

**Setup:**

1. Obtain an IRQHandler capability via `seL4_IRQControl_Get(irqControl, irq, root, index, depth)`.
2. Bind a Notification to the handler via `seL4_IRQHandler_SetNotification(irqHandler, notification)`.
3. Acknowledge the interrupt to initialize state: `seL4_IRQHandler_Ack(irqHandler)`.

**Delivery:**

1. When a hardware interrupt fires, the kernel signals the bound Notification by
   bitwise-ORing the notification capability's badge into the notification word.
2. The driver thread receives the signal via `seL4_Wait` on the Notification.
3. Multiple interrupts can share a single Notification using distinct badge bits; the
   driver disambiguates via the badge bitmask.

**Acknowledgement:**

After processing, the driver calls `seL4_IRQHandler_Ack` to unmask the interrupt. The
kernel will not deliver further interrupts from that source until acknowledged.

### 11.2 Architecture-Specific Variants

- **x86:** `seL4_IRQControl_GetIOAPIC` (IOAPIC interrupts), `seL4_IRQControl_GetMSI`
  (MSI interrupts).
- **ARM:** `seL4_IRQControl_Get` with platform-specific IRQ numbers. SGI support via
  `ARMIRQIssueSGISignal`.
- **RISC-V:** Uses PLIC claim/complete mechanism.

### 11.3 Device Drivers and DMA

Device drivers run as normal user-level processes in their own address spaces. DMA safety
requires an IOMMU/SystemMMU. Without one, DMA-capable device drivers must be trusted.

On x86 with IOMMU support, IOPageTable and IODevice kernel objects enable
capability-mediated DMA isolation.

---

## 12. Virtualization Support

seL4 runs as a **hypervisor** on supported platforms:

- **ARM:** The kernel runs in hyp mode; virtual machine monitors (VMMs) run in supervisor
  mode.
- **x86:** The kernel runs in Ring-0 root mode; VMMs run in Ring-3 root mode using VT-x.

**VCPU** kernel objects represent virtual CPUs. The VMM (a user-level component) handles
virtualization events, traps, and device emulation. The kernel forwards guest traps and
faults to the VMM for processing.

---

## 13. MCS Extensions

The MCS (Mixed-Criticality Systems) extensions represent a fundamental enhancement to
seL4's temporal resource management. They treat CPU time as a capability-controlled
resource, paralleling how capabilities control spatial resources (memory, endpoints).

### 13.1 Scheduling Contexts

A **Scheduling Context (SchedContext)** represents CPU time as a (budget, period) pair:

- `budget == period` -- acts as a simple timeslice (round-robin behavior).
- `budget < period` -- creates a periodic thread with a guaranteed bandwidth fraction.

Temporal isolation is enforced via a **sporadic server** algorithm: during any window of
length `period`, the consumed CPU time cannot exceed `budget`.

### 13.2 Replenishments and Refills

Budget is tracked in chunks called **replenishments** (refills). Each refill has an amount
and a timestamp from which it can be consumed.

- Default: 2 refill slots per scheduling context.
- `extra_refills` parameter allows more (finer-grained preemption tracking but increased
  scheduling overhead).
- If all refill slots are consumed, remaining budget is forfeited until the next period.

### 13.3 Passive Servers

A server with no bound scheduling context is **passive**:

- On `seL4_Call`, the caller's scheduling context is **donated** to the passive server.
- On `seL4_ReplyRecv`, the scheduling context is returned to the caller.
- This allows shared servers to run on client time budgets, providing temporal isolation
  for shared resources.

### 13.4 Timeout Faults

When a thread exhausts its scheduling context budget, a **timeout fault** can be raised
if a handler is registered via `seL4_TCB_SetTimeoutEndpoint`. The fault message includes
the scheduling context identifier and consumed time.

### 13.5 SchedContext Operations

| Method | Description |
|---|---|
| `seL4_SchedControl_Configure` | Set budget, period, extra_refills, and badge on a scheduling context. |
| `seL4_SchedControl_ConfigureFlag` | Configure with additional flags (e.g., constant-bandwidth mode). |
| `seL4_SchedContext_Bind` | Bind a TCB or Notification to the scheduling context. |
| `seL4_SchedContext_Unbind` | Unbind all objects (renders bound thread passive). |
| `seL4_SchedContext_UnbindObject` | Unbind a specific object (TCB or Notification). |
| `seL4_SchedContext_Consumed` | Return consumed time since last fault/YieldTo/Consumed call. |
| `seL4_SchedContext_YieldTo` | Place the target thread at the head of its priority queue; return consumed time. |

### 13.6 Key Differences from Non-MCS Kernel

| Aspect | Non-MCS | MCS |
|---|---|---|
| Time representation | Fixed timeslice per TCB | SchedContext objects (budget/period) |
| Reply capability storage | Internal TCB slot | Explicit Reply objects |
| Temporal isolation | Domain scheduler (static, compile-time) | Sporadic server (dynamic, capability-controlled) |
| `seL4_Reply` syscall | Standalone syscall | Removed; reply via Reply objects |
| `seL4_CNode_SaveCaller` | Required to save reply caps | Not needed |
| Passive servers | Not supported | Supported |
| Timeout faults | Not supported | Supported |
| Domain scheduler | Present | Removed |

---

## 14. Formal Verification

### 14.1 Verification Chain

seL4's verification is structured as a refinement proof chain in **Isabelle/HOL**:

```
Abstract Specification (Isabelle/HOL)
        │
        │  Functional Correctness Refinement
        ▼
Executable Specification (Haskell prototype)
        │
        │  Refinement
        ▼
C Implementation (~10K SLOC)
        │
        │  Binary Verification (automated)
        ▼
Machine Code (binary)
```

The refinement proofs establish that each lower layer faithfully implements the layer
above, so all safety properties proved at the abstract level transfer to the binary.

### 14.2 Verified Properties

| Property | Description |
|---|---|
| **Functional Correctness** | The C code behaves precisely as the abstract specification. Implies absence of buffer overflows, null pointer dereferences, memory leaks, arithmetic exceptions, use of uninitialized variables, deadlocks, and livelocks. |
| **Integrity (Access Control)** | No application can modify data without holding a capability with appropriate authority. |
| **Confidentiality (Information Flow)** | No application can learn information from another without explicit authorization. Proved as information-flow noninterference between security domains. |
| **Availability** | No application can prevent resource access by other applications with proper authority. |
| **Binary Correctness** | The compiled machine code correctly implements the C semantics. Removes the compiler from the trusted computing base. |
| **Worst-Case Execution Time** | Sound WCET analysis of the binary (ARMv7). |

### 14.3 Verified Configurations

Not all configurations carry all proofs. The most comprehensive verification exists for:

| Architecture | FC to C | FC to Binary | Integrity | Confidentiality | WCET |
|---|---|---|---|---|---|
| ARMv7 (32-bit) | Yes | Yes | Yes | Yes | Yes |
| RISC-V 64-bit | Yes | Yes | Yes | Yes | -- |
| AArch64 | Yes | -- | -- | -- | -- |
| x86_64 | Yes | -- | -- | -- | -- |

### 14.4 Proof Scale and Track Record

- The proof comprises approximately **500,000 lines of Isabelle/HOL proof script** -- one
  of the largest machine-checked proofs ever produced.
- **Zero functional correctness defects** have been found in verified code since the
  initial proof completed in 2009 (over 15 years).
- The proof was completed by a team of ~12 researchers over approximately 5 years.
- Awards: 2019 ACM SIGOPS Hall of Fame Award; 2023 ACM Software System Award.

### 14.5 Proof Assumptions

The proof covers the kernel **after** it has been loaded into memory and brought to a
consistent initial state. The following are assumed correct and manually reviewed:

- Boot code (~1,200 lines of C).
- Handwritten assembly (~600 lines).
- TLB and cache management code.
- Hardware correctness (including absence of unmanaged DMA without IOMMU).
- Timing channels are **not** covered by the confidentiality proof.

---

## 15. Architecture Support

### 15.1 Supported Architectures

| Architecture | Word Size | Multicore | Hypervisor |
|---|---|---|---|
| ARMv7 (AArch32) | 32-bit | Yes | Yes |
| ARMv8 (AArch64) | 64-bit | Yes | Yes |
| x86 (IA-32) | 32-bit | No | No |
| x86_64 | 64-bit | Yes | Yes (VT-x) |
| RISC-V (RV32) | 32-bit | Yes | -- |
| RISC-V (RV64) | 64-bit | Yes | -- |

Multicore support uses a big-lock SMP approach, appropriate for tightly-coupled cores
sharing an L2 cache.

### 15.2 Kernel Size

| Architecture | C SLOC | Binary Size (approx.) |
|---|---|---|
| RISC-V 64-bit | ~10,000 | ~66 KiB |
| AArch32 | ~12,100 | -- |
| AArch64 (with hypervisor) | ~12,600 | ~162 KiB |
| x86_64 | ~16,000 | -- |

### 15.3 Selected Hardware Platforms

- **ARM:** i.MX6/8 series, Raspberry Pi 3B/4B, NVIDIA TK1/TX1/TX2, Xilinx Zynq,
  BeagleBone, Odroid, ROCKPro64, Ultra96v2.
- **RISC-V:** SiFive HiFive Unleashed, Microchip PolarFire, Pine64 Star64.
- **x86:** Generic PC99 platform.

### 15.4 Deployment History

seL4 and its L4 predecessors have been deployed in:

- Autonomous helicopters.
- Classified military and defense systems.
- CubeSats in space.
- OKL4 (earlier L4 variant from NICTA) deployed in 2+ billion mobile devices.
- Apple's Secure Enclave coprocessor (A7 and later) runs sepOS, based on L4-embedded
  from NICTA.

---

## References

- [seL4 Reference Manual](https://sel4.systems/Info/Docs/seL4-manual-latest.pdf)
- [seL4 Whitepaper](https://sel4.systems/About/seL4-whitepaper.pdf)
- [seL4 API Documentation](https://docs.sel4.systems/projects/sel4/api-doc.html)
- [seL4 Tutorials](https://docs.sel4.systems/Tutorials/)
- [seL4 Verification](https://sel4.systems/Verification/)
- [seL4 Verified Configurations](https://docs.sel4.systems/projects/sel4/verified-configurations.html)
- [Klein et al., "seL4: Formal Verification of an OS Kernel" (SOSP 2009)](https://www.sigops.org/s/conferences/sosp/2009/papers/klein-sosp09.pdf)
- [seL4 on Wikipedia](https://en.wikipedia.org/wiki/SeL4)
