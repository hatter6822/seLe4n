# seLe4n Handbook

This GitBook is the long-form documentation for seLe4n.

## Project stage snapshot

- **Current slice:** M7 audit remediation workstreams (WS-A1 through WS-A8) as the immediate execution focus.
- **Most recently completed slice:** M6 architecture-binding interfaces and hardware-facing assumption hardening (WS-M6-A through WS-M6-E complete).
- **First real hardware architecture focus:** Raspberry Pi 5 (post-remediation binding trajectory).

Use [`docs/SEL4_SPEC.md`](../SEL4_SPEC.md) as the canonical milestone/acceptance reference.

## Recommended navigation

### 1) Orientation

1. [Project Overview](01-project-overview.md)
2. [Microkernel and seL4 Primer](02-microkernel-and-sel4-primer.md)
3. [Architecture & Module Map](03-architecture-and-module-map.md)
4. [Project Design Deep Dive](04-project-design-deep-dive.md)

### 2) Active planning and execution

5. [Specification & Roadmap](05-specification-and-roadmap.md)
6. [M6 Execution Plan and Workstreams](18-m6-execution-plan-and-workstreams.md)
7. [Development Workflow](06-development-workflow.md)
8. [Testing & CI](07-testing-and-ci.md)
9. [Codebase Reference](11-codebase-reference.md)
10. [Proof and Invariant Map](12-proof-and-invariant-map.md)
11. [End-to-End Audit and Quality Gates](19-end-to-end-audit-and-quality-gates.md)
12. [Repository Audit Remediation Workstreams](20-repository-audit-remediation-workstreams.md)

### 3) Slice history and long-horizon path

13. [M5 Closeout Snapshot](09-m5-closeout-snapshot.md)
14. [Completed Slice: M4-A](08-completed-slice-m4a.md)
15. [Completed Slice: M4-B](16-completed-slice-m4b.md)
16. [M4-B Execution Playbook](14-m4b-execution-playbook.md)
17. [Future Slices and Delivery Plan](13-future-slices-and-delivery-plan.md)
18. [M5 Development Blueprint](15-m5-development-blueprint.md)
19. [Project Usage and Value](17-project-usage-value.md)
20. [Path to Real Hardware (Raspberry Pi 5 First)](10-path-to-real-hardware-mobile-first.md)

## Anti-duplication guidance

To keep this handbook maintainable:

- put normative scope and acceptance criteria in `docs/SEL4_SPEC.md`,
- keep current-slice chapters focused on active execution details,
- keep completed-slice chapters as concise historical references,
- use cross-links when reusing definitions,
- and keep Raspberry Pi 5 planning details synchronized between roadmap and hardware chapters.
