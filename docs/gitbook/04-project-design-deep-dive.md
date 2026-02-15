# Project Design Deep Dive

## Core design principles

### 1) Deterministic transition semantics

Every operation should expose clear success/error branching. Illegal object-state combinations must
fail explicitly rather than being hidden behind partial definitions.

### 2) Local-first theorem layering

For a transition `t`, prove local invariant component preservation first, then prove composed-bundle
preservation from those local facts. This keeps proof maintenance manageable across milestones.

### 3) Compositional invariant architecture

Avoid mega-invariants that become brittle. Instead:

- define meaningful components,
- name them clearly,
- compose them into milestone bundles,
- and preserve the bundle surface for downstream users/tests.

### 4) Executable evidence as a contract

`Main.lean` is not demo-only: it is part of the regression surface. Tier 2 fixture checks protect
semantic breadcrumbs in executable traces so docs/claims stay grounded.

## Why milestone slicing works here

Milestone slicing (M1→M4) reduces risk by avoiding simultaneous redesign of:

- object model,
- transition APIs,
- invariant architecture,
- theorem strategy,
- executable scenarios,
- and testing gates.

The slice approach allows each layer to harden before broader composition.

## Design pressure at M4

M4 is where object lifecycle semantics become central. This is a high-leverage layer because it
connects capability references with the evolving object store. Done well, it sets up later stages
for stronger stale-reference and authority proofs.
