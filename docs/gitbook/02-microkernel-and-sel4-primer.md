# Microkernel and seL4 Primer

## What is a microkernel?

A microkernel keeps only minimal core mechanisms in kernel mode, typically:

- address-space and thread management,
- scheduling,
- IPC primitives,
- capability-based authority mediation.

Most services (drivers, filesystems, networking stacks) run in user space as isolated components.

### Why microkernels are compelling

1. **Smaller trusted core**: fewer lines in privileged code reduce attack and bug surface.
2. **Fault containment**: a failed service can often be restarted without crashing entire system.
3. **Policy/mechanism separation**: kernel provides mechanisms, user-space components define policy.
4. **Security posture**: strong compartmentalization supports least privilege and high assurance.

### Trade-offs

- IPC and context-switch costs can be higher than monolithic kernels if not carefully designed.
- System composition is operationally complex (service graph, capability distribution, startup order).
- Verification and maintenance require disciplined interfaces and tooling.

## What is seL4?

seL4 is a high-assurance microkernel developed with machine-checked verification goals as a first
class design constraint. It is known for combining strong isolation with formal assurance claims.

Core seL4 characteristics relevant to seLe4n:

- capability-based access control,
- explicit object management and retype operations,
- endpoint-based IPC,
- scheduler and thread-state discipline,
- architecture-specific realizations grounded in architecture-neutral reasoning layers.

## Why seLe4n models seL4 semantics

seLe4n does not attempt to instantly replicate the full seL4 proof corpus. Instead, it incrementally
formalizes key semantic surfaces (scheduler, capabilities, IPC, lifecycle) so contributors can:

- understand the interactions in executable form,
- prove safety properties at each step,
- and avoid all-or-nothing proof resets.
