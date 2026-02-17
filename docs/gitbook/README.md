# seLe4n Handbook

This GitBook is the long-form documentation for seLe4n.

## Project stage snapshot

- **Current slice:** M7 audit remediation workstreams (WS-A1 through WS-A8) with outcome-driven closure gates.
- **Most recently completed slice:** M6 architecture-binding interfaces and hardware-facing assumption hardening (WS-M6-A through WS-M6-E complete).
- **Planned next slice:** post-M7 hardware-oriented development path (Raspberry Pi 5 first) with architecture-specific adapter and evidence expansion.

Use [`docs/SEL4_SPEC.md`](../SEL4_SPEC.md) as the canonical milestone/acceptance reference.

## Recommended navigation

### 1) Orientation

1. [Project Overview](01-project-overview.md)
2. [Microkernel and seL4 Primer](02-microkernel-and-sel4-primer.md)
3. [Architecture & Module Map](03-architecture-and-module-map.md)
4. [Project Design Deep Dive](04-project-design-deep-dive.md)

### 2) Active planning and execution

5. [Specification & Roadmap](05-specification-and-roadmap.md)
6. [M7 Current Slice Outcomes and Workstreams](21-m7-current-slice-outcomes-and-workstreams.md)
7. [Repository Audit Remediation Workstreams](20-repository-audit-remediation-workstreams.md)
8. [Development Workflow](06-development-workflow.md)
9. [Testing & CI](07-testing-and-ci.md)
10. [Codebase Reference](11-codebase-reference.md)
11. [Proof and Invariant Map](12-proof-and-invariant-map.md)
12. [End-to-End Audit and Quality Gates](19-end-to-end-audit-and-quality-gates.md)

### 3) Transition and long-horizon path

13. [Next Slice Development Path (Post-M7)](22-next-slice-development-path.md)
14. [Path to Real Hardware (Raspberry Pi 5 First)](10-path-to-real-hardware-mobile-first.md)
15. [Project Usage and Value](17-project-usage-value.md)

### 4) Slice history archive

16. [M6 Execution Plan and Workstreams](18-m6-execution-plan-and-workstreams.md)
17. [M5 Closeout Snapshot](09-m5-closeout-snapshot.md)
18. [Completed Slice: M4-A](08-completed-slice-m4a.md)
19. [Completed Slice: M4-B](16-completed-slice-m4b.md)
20. [M4-B Execution Playbook](14-m4b-execution-playbook.md)
21. [Future Slices and Delivery Plan](13-future-slices-and-delivery-plan.md)
22. [M5 Development Blueprint](15-m5-development-blueprint.md)

## Anti-duplication guidance

To keep this handbook maintainable:

- put normative scope and acceptance criteria in `docs/SEL4_SPEC.md`,
- keep active-slice chapters focused on current execution details and closure evidence,
- keep completed-slice chapters as concise historical references,
- use cross-links when reusing definitions,
- and keep Raspberry Pi 5 planning details synchronized between roadmap, next-slice, and hardware chapters.
