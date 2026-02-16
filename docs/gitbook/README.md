# seLe4n Handbook

seLe4n is a Lean 4 formalization effort to build an executable, machine-checked model of core
[seL4](https://sel4.systems) microkernel semantics.

This handbook is the long-form documentation set for:

- project motivation and design rationale,
- milestone planning and delivery slices,
- proof + implementation workflow,
- testing/CI policy,
- and the roadmap toward running verified components on real hardware (mobile-first).

## Why this handbook exists

Repository-level docs are intentionally concise. The GitBook layer expands the "why" and "how" so
contributors can understand current contracts and next-slice execution paths.

## Current stage

- Recently completed slice: **M4-B lifecycle-capability composition hardening**.
- Next slice target: **M5 service-graph + policy surfaces**.

## Suggested reading order

1. [Project Overview](01-project-overview.md)
2. [Microkernel and seL4 Primer](02-microkernel-and-sel4-primer.md)
3. [Architecture & Module Map](03-architecture-and-module-map.md)
4. [Project Design Deep Dive](04-project-design-deep-dive.md)
5. [Specification & Roadmap](05-specification-and-roadmap.md)
6. [Development Workflow](06-development-workflow.md)
7. [Testing & CI](07-testing-and-ci.md)
8. [Completed Slice: M4-A](08-current-slice-m4a.md)
9. [Current Slice: M4-B](09-next-slice-m4b.md)
10. [Path to Real Hardware (Mobile-First)](10-path-to-real-hardware-mobile-first.md)
11. [Codebase Reference](11-codebase-reference.md)
12. [Proof and Invariant Map](12-proof-and-invariant-map.md)
13. [Future Slices and Delivery Plan](13-future-slices-and-delivery-plan.md)
14. [M4-B Execution Playbook](14-m4b-execution-playbook.md)
15. [M5 Blueprint and Project Usage Value](15-m5-blueprint-and-project-usage.md)

For normative acceptance criteria, treat `docs/SEL4_SPEC.md` as canonical.

## What changed in this edition

- Expanded roadmap chapters to include explicit M5 target outcomes and workstreams.
- Expanded M4-B closeout material to provide concrete handoff guidance.
- Added a dedicated chapter on developer/team usage modes and technical project value.
