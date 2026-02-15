# Project Overview

## 1. Motivation

seLe4n aims to make high-assurance kernel reasoning more usable for developers by combining three
properties in one workflow:

1. executable transition semantics,
2. machine-checked invariant preservation,
3. milestone-scoped change management.

Many projects optimize for only one or two of these at a time. seLe4n intentionally treats all
three as first-class engineering constraints.

## 2. Why this project exists now

The practical gap addressed by seLe4n:

- formal methods can be hard to iterate on in day-to-day engineering,
- executable prototypes can drift from proof claims,
- subsystem interactions (scheduler/capability/IPC/lifecycle) are often documented inconsistently.

seLe4n closes this gap by making transition/proof/executable/docs/test gates move together.

## 3. What is already implemented

Closed milestone surface today:

- Bootstrap: model skeleton,
- M1: scheduler invariants and preservation,
- M2: capability/CSpace semantics and authority invariants,
- M3: endpoint IPC seed semantics,
- M3.5: typed waiting handshake + scheduler coherence contract.

Current active milestone:

- M4-A lifecycle/retype foundations.

Planned immediate follow-on:

- M4-B lifecycle-capability hardening.

## 4. Project design in one page

- transitions are executable and explicit,
- errors are first-class (`KernelError`) outcomes,
- invariants are named components before bundle composition,
- theorem entrypoints are transition-oriented and searchable,
- integration evidence is executable (`Main.lean`) and fixture-guarded.

## 5. How contributors should think about the codebase

When touching any subsystem:

1. identify state-model assumptions in `Model/*`,
2. update transition semantics in subsystem module,
3. add/refine local invariant components,
4. prove local preservation first,
5. prove composed preservation next,
6. update executable trace and fixtures if semantic output changed,
7. synchronize docs in canonical + GitBook layers.

## 6. Long-horizon objective

seLe4n is not only a proof exercise; it is a staged path toward deployment-relevant reasoning,
including mobile-first hardware considerations. The roadmap chapter details how to bridge from
architecture-neutral model semantics to architecture binding and prototype integration constraints.
