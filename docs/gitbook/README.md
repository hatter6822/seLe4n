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

The repository docs (`README.md`, spec, development guide, testing plan) are intentionally concise.
This GitBook layer provides deeper explanations so contributors can understand **why** the project
is shaped this way, not only **what** commands to run.

## Current stage

- Active slice: **M4-A lifecycle/retype foundations**.
- Next slice: **M4-B lifecycle-capability composition hardening**.

## Suggested reading order

1. [Project Overview](01-project-overview.md)
2. [Microkernel and seL4 Primer](02-microkernel-and-sel4-primer.md)
3. [Architecture & Module Map](03-architecture-and-module-map.md)
4. [Project Design Deep Dive](04-project-design-deep-dive.md)
5. [Specification & Roadmap](05-specification-and-roadmap.md)
6. [Development Workflow](06-development-workflow.md)
7. [Testing & CI](07-testing-and-ci.md)
8. [Current Slice: M4-A](08-current-slice-m4a.md)
9. [Next Slice: M4-B](09-next-slice-m4b.md)
10. [Path to Real Hardware (Mobile-First)](10-path-to-real-hardware-mobile-first.md)
11. [Codebase Reference](11-codebase-reference.md)
12. [Proof and Invariant Map](12-proof-and-invariant-map.md)

For normative acceptance criteria, treat `docs/SEL4_SPEC.md` as canonical.
