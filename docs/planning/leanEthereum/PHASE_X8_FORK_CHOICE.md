# Phase X8: Fork Choice (LMD GHOST)

**Version**: v0.8.0
**Status**: PLANNED
**Sub-tasks**: 20 atomic units
**Dependencies**: X6 (State Transition), X5 (Containers)
**Estimated Lean LoC**: ~850
**Files created**: 7 new files

## 1. Objective

Formalize the fork choice algorithm — LMD GHOST (Latest Message Driven Greedy
Heaviest Observed SubTree). This is the local decision rule each validator uses
to select the canonical chain head.

## 2. Source Layout

```
LeanEth/Consensus/ForkChoice/
├── Store.lean                     Store structure, initialization, error type
├── LMDGHOST.lean                  Head selection: weight computation + tree walk
├── AttestationProcessing.lean     Attestation validation + integration
├── Pruning.lean                   Stale data removal
└── Proofs/
    ├── HeadValidity.lean          Head descends from finalized
    ├── Consistency.lean           Store consistency preservation
    └── Convergence.lean           Convergence under honest majority
```

## 3. Sub-task Breakdown

### Group A: Store Structure (X8-A1 through X8-A4)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X8-A1 | **Define `Store` structure.** Fields: `time`, `config`, `head`, `safeTarget`, `latestJustified`, `latestFinalized`, `blocks : HashMap Bytes32 Block`, `states : HashMap Bytes32 State`, `validatorId`, `attestationSignatures`, `latestNewAggregatedPayloads`, `latestKnownAggregatedPayloads`. Two-tier attestation pool (new → known on tick). | `ForkChoice/Store.lean` | ~40 | X5 |
| X8-A2 | **Define `Store.fromAnchor`.** Initialize from anchor state + block. Validate `stateRoot = hashTreeRoot state`. Set head, safeTarget, justified, finalized to anchor. | `ForkChoice/Store.lean` | ~25 | X8-A1 |
| X8-A3 | **Define `storeConsistent` predicate.** All referenced blocks exist; parent chain is valid; justified/finalized roots exist in store. | `ForkChoice/Store.lean` | ~20 | X8-A1 |
| X8-A4 | **Define `ForkChoiceError` type.** `blockNotFound`, `stateNotFound`, `invalidAttestation`, `stateRootMismatch`, `futureAttestation`, `duplicateBlock`. | `ForkChoice/Store.lean` | ~10 | — |

### Group B: LMD GHOST Algorithm (X8-B1 through X8-B3)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X8-B1 | **Define `isDescendant` with termination.** Walk parent chain from child to ancestor. Fuel = store.blocks.size. Prove `isDescendant_refl`, `isDescendant_trans`. | `ForkChoice/LMDGHOST.lean` | ~30 | X8-A1 |
| X8-B2 | **Define weight computation.** `computeWeights : Store → HashMap Bytes32 Nat` — for each validator's latest attestation, walk from `att.head.root` backward, incrementing weight at each ancestor. O(validators × chain depth). | `ForkChoice/LMDGHOST.lean` | ~35 | X8-B1 |
| X8-B3 | **Define LMD GHOST head selection.** `lmdGhost : Store → Bytes32` — from `latestJustified.root`, at each fork choose child with max (weight, tiebreak by root hash). Terminate at leaf. | `ForkChoice/LMDGHOST.lean` | ~35 | X8-B2 |

### Group C: Store Operations (X8-C1 through X8-C5)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X8-C1 | **Define `validateAttestation`.** Checks: blocks exist, topology valid (source ≤ target ≤ head), checkpoint slots match block slots, not future. | `ForkChoice/AttestationProcessing.lean` | ~35 | X8-A1 |
| X8-C2 | **Define `onBlock`.** Add block + state, verify signatures, apply STF, propagate checkpoint advances, update head. Skip duplicates. | `ForkChoice/Store.lean` | ~45 | X8-B3, X8-C1 |
| X8-C3 | **Define `onAttestation`.** Validate, verify XMSS signature, store in attestation pool. | `ForkChoice/AttestationProcessing.lean` | ~30 | X8-C1 |
| X8-C4 | **Define `onTick`.** Advance time, migrate new→known attestation pool, re-run head selection. | `ForkChoice/Store.lean` | ~20 | X8-B3 |
| X8-C5 | **Define attestation pruning.** Remove entries with `target.slot ≤ finalized.slot`. Prune states for non-finalized blocks. | `ForkChoice/Pruning.lean` | ~25 | X8-A1 |

### Group D: Proofs (X8-D1 through X8-D5)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X8-D1 | **Prove head descends from finalized.** `lmdGhost_descendant_of_finalized`. GHOST starts from justified; justified descends from finalized. | `Proofs/HeadValidity.lean` | ~35 | X8-B3, X8-A3 |
| X8-D2 | **Prove store consistency preservation.** `onBlock_preserves_consistency`, `onAttestation_preserves_consistency`, `onTick_preserves_consistency`, `prune_preserves_consistency`. | `Proofs/Consistency.lean` | ~40 | X8-C2 through X8-C5 |
| X8-D3 | **Prove convergence.** `lmdGhost_convergence : sameAttestations → sameHead`. GHOST is deterministic given same inputs. | `Proofs/Convergence.lean` | ~35 | X8-B3 |
| X8-D4 | **Fork choice test suite.** 5 scenarios: simple chain, fork with equal weight, attestation reorg, justification shift, pruning safety. | `tests/ForkChoiceSuite.lean` | ~40 | All X8-* |
| X8-D5 | **Create re-export hub.** `LeanEth/Consensus/ForkChoice.lean`. | `Consensus/ForkChoice.lean` | ~5 | All X8-* |

## 4. Exit Criteria

- [ ] LMD GHOST matches Python reference
- [ ] Head descends from finalized (proved)
- [ ] Store consistency preserved (proved)
- [ ] Convergence under honest majority (proved)
- [ ] Fork choice test suite passes (5 scenarios)
- [ ] Zero sorry in fork choice modules
