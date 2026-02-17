# WS-B1 ADR: VSpace + Bounded Memory Model Foundation

GitBook mirror of [`docs/VSPACE_MEMORY_MODEL_ADR.md`](../VSPACE_MEMORY_MODEL_ADR.md).

## Status

Accepted — 2026-02-17

## Decision summary

- Introduce first-class `VSpaceRoot` modeled kernel objects.
- Provide deterministic `map/unmap/lookup` transition surface with explicit errors.
- Publish VSpace invariant bundle surface for ASID-root uniqueness and non-overlap.
- Keep hierarchical page-table specifics abstract in this slice.
- Use a bounded ASID-discovery window (`vspaceDiscoveryWindow`) until finite-map indexing lands.

## Why this matters

This closes the audit criticism that VSpace was only a placeholder and creates a stable
foundation for deeper CSpace/IPC/information-flow and hardware-bound workstreams.
