# Phase X8: Fork Choice (LMD GHOST)

**Version**: v0.8.0
**Status**: PLANNED
**Sub-tasks**: 14 atomic units
**Dependencies**: X6 (State Transition), X5 (Containers)
**Estimated Lean LoC**: ~700
**Files created**: 6 new files

## 1. Objective

Formalize the fork choice algorithm — LMD GHOST (Latest Message Driven Greedy
Heaviest Observed SubTree). This is the local decision rule each validator uses
to select the canonical chain head. The Store structure maintains the validator's
view of the block tree, attestation pool, and justified/finalized checkpoints.

## 2. Reference

`src/lean_spec/subspecs/forkchoice/store.py` (~53 KB)

## 3. Source Layout

```
LeanEth/Consensus/ForkChoice/
├── Store.lean                     Store structure, initialization
├── LMDGHOST.lean                  Head selection algorithm
├── AttestationProcessing.lean     Attestation validation + integration
├── Pruning.lean                   Stale data removal
└── Proofs/
    ├── HeadValidity.lean          Head descends from finalized
    ├── Consistency.lean           Store consistency preservation
    └── Convergence.lean           Convergence under honest majority
```

## 4. Sub-task Breakdown

### Group A: Store Structure (X8-A1 through X8-A3)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X8-A1 | **Define `Store` structure.** `structure Store where time : Uint64; config : Config; head : Bytes32; safeTarget : Bytes32; latestJustified : Checkpoint; latestFinalized : Checkpoint; blocks : HashMap Bytes32 Block; states : HashMap Bytes32 State; validatorId : Option ValidatorIndex; attestationSignatures : HashMap AttestationData (List AttestationSignatureEntry)`. `structure AttestationSignatureEntry where validatorId : ValidatorIndex; signature : Signature`. | `ForkChoice/Store.lean` | ~35 | X5 |
| X8-A2 | **Define `Store.fromAnchor`.** `fromAnchor : State → Block → Option ValidatorIndex → Except ForkChoiceError Store`. Validates `anchor_block.stateRoot = hashTreeRoot state`. Computes `anchorRoot = hashTreeRoot anchor_block`. Initializes head, safeTarget, justified, finalized to anchor. | `ForkChoice/Store.lean` | ~25 | X8-A1 |
| X8-A3 | **Define `storeConsistent` predicate.** `def storeConsistent (store : Store) : Prop := (store.blocks.contains store.head) ∧ (store.blocks.contains store.latestJustified.root) ∧ (store.blocks.contains store.latestFinalized.root) ∧ (∀ root ∈ store.blocks.keys, root ≠ ZERO_HASH → store.blocks.contains (store.blocks[root]!.parentRoot) ∨ root = anchorRoot)`. All referenced blocks exist. | `ForkChoice/Store.lean` | ~20 | X8-A1 |

### Group B: Core Operations (X8-B1 through X8-B5)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X8-B1 | **Define LMD GHOST head selection.** `lmdGhost : Store → Bytes32`. Starting from `store.latestJustified.root`, at each fork choose the child with the highest attestation weight. Weight = count of validators whose latest attestation points to a descendant of the candidate. Terminate at leaf (no children). Use `isDescendant : HashMap Bytes32 Block → Bytes32 → Bytes32 → Bool` helper (walk parent chain with fuel). | `ForkChoice/LMDGHOST.lean` | ~50 | X8-A1 |
| X8-B2 | **Define attestation validation.** `validateAttestation : Store → Attestation → Except ForkChoiceError Unit`. Checks: (1) source, target, head blocks exist in store. (2) `source.slot < target.slot`. (3) Head is at least as recent as source and target (slot ordering). (4) Checkpoint slots match block slots. (5) Vote is not for a future slot (relative to store.time). | `ForkChoice/AttestationProcessing.lean` | ~35 | X8-A1 |
| X8-B3 | **Define store update operations.** `onBlock : Store → SignedBlock → State → Except ForkChoiceError Store` — add block + post-state, update justified/finalized if the new state has higher checkpoints. `onAttestation : Store → Attestation → Except ForkChoiceError Store` — validate + store attestation. `onTick : Store → Uint64 → Store` — advance time. After each update, re-run `lmdGhost` to update head. | `ForkChoice/Store.lean` | ~50 | X8-B1, X8-B2 |
| X8-B4 | **Define stale attestation pruning.** `pruneStaleAttestationData : Store → Store`. Remove attestation entries targeting slots ≤ `store.latestFinalized.slot`. This keeps the attestation pool bounded. Also prune `states` for blocks not on the finalized chain. | `ForkChoice/Pruning.lean` | ~25 | X8-A1 |
| X8-B5 | **Define `isDescendant` with proof of termination.** `isDescendant : HashMap Bytes32 Block → Bytes32 → Bytes32 → Bool`. Walk from child to ancestor via `parentRoot` links. Terminate when: (a) found ancestor → true, (b) reached genesis/missing block → false. Use fuel parameter (max depth = store.blocks.size) for termination. Prove `isDescendant_refl`, `isDescendant_trans`. | `ForkChoice/LMDGHOST.lean` | ~30 | X8-A1 |

### Group C: Proofs (X8-C1 through X8-C4)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X8-C1 | **Prove head descends from finalized.** `lmdGhost_descendant_of_finalized : storeConsistent store → isDescendant store.blocks (lmdGhost store) store.latestFinalized.root = true`. Proof: GHOST starts from justified root; justified root descends from finalized (by consensus invariant); GHOST only moves to children → result descends from justified → descends from finalized. | `ForkChoice/Proofs/HeadValidity.lean` | ~35 | X8-B1, X8-A3 |
| X8-C2 | **Prove store consistency preservation.** `onBlock_preserves_consistency`, `onAttestation_preserves_consistency`, `onTick_preserves_consistency`, `pruneStaleAttestationData_preserves_consistency`. Adding blocks only adds entries; removing stale data only removes entries for finalized slots. | `ForkChoice/Proofs/Consistency.lean` | ~40 | X8-B3, X8-B4 |
| X8-C3 | **Prove convergence under honest majority.** `lmdGhost_convergence : honestSupermajority validators → sameAttestationView store₁ store₂ → storeConsistent store₁ → storeConsistent store₂ → lmdGhost store₁ = lmdGhost store₂`. With the same attestations, all honest nodes select the same head. Proof: GHOST is deterministic given the same block tree and attestation weights. | `ForkChoice/Proofs/Convergence.lean` | ~40 | X8-B1 |
| X8-C4 | **Fork choice test suite.** Scenarios: (1) simple chain (no forks) — head is latest block. (2) Single fork with equal weight — tie-breaking by root hash. (3) Attestation-driven reorg — new attestations shift weight. (4) Justification advancement — GHOST root shifts. (5) Pruning doesn't affect live attestations. | `tests/ForkChoiceSuite.lean` | ~40 | All X8-* |

### Group D: Integration (X8-D1 through X8-D2)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X8-D1 | **Define `ForkChoiceError` type.** `inductive ForkChoiceError | blockNotFound (root : Bytes32) | stateNotFound (root : Bytes32) | invalidAttestation (reason : String) | stateRootMismatch | futurAttestation (attSlot storeSlot : Slot) | duplicateBlock`. | `ForkChoice/Store.lean` | ~10 | — |
| X8-D2 | **Create re-export hub.** `LeanEth/Consensus/ForkChoice.lean` importing all submodules. | `Consensus/ForkChoice.lean` | ~5 | All X8-* |

## 5. Exit Criteria

- [ ] LMD GHOST head selection matches Python reference
- [ ] Head always descends from finalized (proved)
- [ ] Store consistency preserved across all operations (proved)
- [ ] Convergence under honest majority (proved)
- [ ] Fork choice test suite passes (5 scenarios)
- [ ] Zero sorry in fork choice modules
