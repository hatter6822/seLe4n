# Claim vs Evidence Index

Canonical source: [`docs/CLAIM_EVIDENCE_INDEX.md`](../CLAIM_EVIDENCE_INDEX.md).

seLe4n ties every substantive public claim to a command that checks it and an
artefact that carries it. If a claim is not in that index, it is not a claim
the project stands behind — and the index says as much about what is *not*
claimed as about what is.

## 1. Proof surface

Zero `sorry` and zero `axiom` in the production proof surface, proofs that are
not vacuous one-liners, transitions that are executable pure functions with
explicit success or failure, and a deterministic model pinned by a golden
trace. Checked by Tier 0 hygiene, `check_module_axioms.py`,
`check_proof_depth.py` and the Tier 2 determinism suite.

## 2. Kernel invariants

`ipcInvariantFull` — twenty conjuncts — is machine-checked end to end: no
theorem in its preservation family assumes a conjunct on its own post-state,
and the bundle carries across a whole syscall dispatch under inhabited
pre-state quiescence packs. Capability derivation is acyclic and complete;
twelve cross-subsystem predicates hold; slot and waiter uniqueness are
structural rather than state predicates.

## 3. Fault handling

A fault is delivered, never returned. No execution path returns a thread to its
faulting instruction without handler action, delivery is total with a
fail-closed suspend on every refusal, the live entry is the flow-checked arm,
and a kernel-origin exception is never delivered to a user handler.

## 4. SMP

Per-core scheduler state and scheduling, cross-core IPC preserving the IPC
bundle, CBS replenish-queue migration on every cross-core hand-off, a verified
TLB shootdown protocol with bounded wait, per-core non-interference with
enumerated covert channels, and audited declassification with causal
provenance. The WS-SM theorem total is measured rather than hand-summed.

## 5. Data structures and performance

The object store is a verified Robin Hood hash table with proven O(1) lookup —
a theorem, not a benchmark — and the CNode radix tree gets the same treatment.

## 6. Hardware and build

The HAL compiles and generates code for `aarch64-unknown-none` in both
profiles, with the three assembly sources verified to have assembled and clippy
denied on the cross target. Broadcast TLB maintenance is confined and gated. No
third-party code is linked into the runtime kernel binary.

## 7. Process

Version sites agree, deferrals are registered with owners, plan numbering is
consistent, no identifier encodes a workstream code, a gate that cannot run
reports NOT RUN rather than PASS, and website-linked paths still exist — each
enforced by a named script rather than by review.

## 8. What is **not** claimed

That the kernel boots on hardware; that per-object fine locks are deployed;
unconditional SMP starvation-freedom; that live WCRT matches the fine-lock
bound; that Tier 4 acceptance gates have passed; that a fault message past
`MR3` reaches a handler on hardware.

*(That the deployed RwLock is the one the Lean FIFO spec describes left this
list at v0.34.50: `STATIC_RW_LOCK_POOL` is `[QueuedRwLock; 4]` and
`queuedRwLock_refines_rwLockSpec` covers it. It is now a claim, in §4 of the
canonical index, with evidence.)*

Each is registered debt with a named owner, not an oversight. The canonical
index carries the owner for each.

## Proof claim qualification

Not every theorem carries the same assurance, and a coverage claim must say
which kind it means. The canonical index names six categories — substantive
preservation, error-case preservation, compositional preservation, structural
invariant, end-to-end chain, and non-interference — with the assurance level
each carries. Quoting a theorem count without the distinction hides it.

## Update policy

When a claim changes: update the canonical root source first, update this
mirror in the same PR, refresh the index row, and run at least
`./scripts/test_smoke.sh`. A claim that loses its evidence command loses its
row; a claim the tree no longer supports moves to §8 with an owner rather than
being quietly deleted.
