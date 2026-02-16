# seLe4n Handbook

This GitBook is the long-form documentation for seLe4n.

## Project stage snapshot

- **Completed:** M4-B lifecycle-capability composition hardening.
- **Next:** M5 service-graph + policy surfaces.

Use [`docs/SEL4_SPEC.md`](../SEL4_SPEC.md) as the canonical milestone/acceptance reference.

## Recommended navigation

### 1) Orientation

1. [Project Overview](01-project-overview.md)
2. [Microkernel and seL4 Primer](02-microkernel-and-sel4-primer.md)
3. [Architecture & Module Map](03-architecture-and-module-map.md)
4. [Project Design Deep Dive](04-project-design-deep-dive.md)

### 2) Active engineering workflow

5. [Specification & Roadmap](05-specification-and-roadmap.md)
6. [Development Workflow](06-development-workflow.md)
7. [Testing & CI](07-testing-and-ci.md)
8. [Codebase Reference](11-codebase-reference.md)
9. [Proof and Invariant Map](12-proof-and-invariant-map.md)

### 3) Slice history and forward planning

10. [Completed Slice: M4-A](08-current-slice-m4a.md)
11. [Completed Slice: M4-B](09-next-slice-m4b.md)
12. [M4-B Execution Playbook](14-m4b-execution-playbook.md)
13. [Future Slices and Delivery Plan](13-future-slices-and-delivery-plan.md)
14. [M5 Blueprint and Project Usage Value](15-m5-blueprint-and-project-usage.md)
15. [Path to Real Hardware (Mobile-First)](10-path-to-real-hardware-mobile-first.md)

## Anti-duplication guidance

To keep this handbook maintainable:

- put normative scope and acceptance criteria in `docs/SEL4_SPEC.md`,
- keep chapter-level details focused on implementation context,
- prefer links to foundational chapters instead of restating shared definitions.
