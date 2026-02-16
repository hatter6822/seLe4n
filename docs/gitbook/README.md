# seLe4n Handbook

This GitBook is the long-form documentation for seLe4n.

## Project stage snapshot

- **Current slice:** M5 service-graph + policy surfaces (active; WS-M5-A/B/C/D/E complete, WS-M5-F in progress).
- **Most recently completed slice:** M4-B lifecycle-capability composition hardening.

Use [`docs/SEL4_SPEC.md`](../SEL4_SPEC.md) as the canonical milestone/acceptance reference.

## Recommended navigation

### 1) Orientation

1. [Project Overview](01-project-overview.md)
2. [Microkernel and seL4 Primer](02-microkernel-and-sel4-primer.md)
3. [Architecture & Module Map](03-architecture-and-module-map.md)
4. [Project Design Deep Dive](04-project-design-deep-dive.md)

### 2) Current slice execution

5. [Current Slice: M5](09-current-slice-m5.md)
6. [Specification & Roadmap](05-specification-and-roadmap.md)
7. [Development Workflow](06-development-workflow.md)
8. [Testing & CI](07-testing-and-ci.md)
9. [Codebase Reference](11-codebase-reference.md)
10. [Proof and Invariant Map](12-proof-and-invariant-map.md)

### 3) Slice history and forward planning

11. [Completed Slice: M4-A](08-completed-slice-m4a.md)
12. [Completed Slice: M4-B](16-completed-slice-m4b.md)
13. [M4-B Execution Playbook](14-m4b-execution-playbook.md)
14. [Future Slices and Delivery Plan](13-future-slices-and-delivery-plan.md)
15. [M5 Development Blueprint](15-m5-development-blueprint.md)
16. [Project Usage and Value](17-project-usage-value.md)
17. [Path to Real Hardware (Mobile-First)](10-path-to-real-hardware-mobile-first.md)

## Anti-duplication guidance

To keep this handbook maintainable:

- put normative scope and acceptance criteria in `docs/SEL4_SPEC.md`,
- keep current-slice chapters focused on active execution details,
- keep completed-slice chapters as concise historical references,
- prefer links to foundational chapters instead of restating shared definitions.
