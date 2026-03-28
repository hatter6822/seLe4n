# Phase X5: Consensus Containers

**Version**: v0.5.0
**Status**: PLANNED
**Sub-tasks**: 26 atomic units
**Dependencies**: X2 (SSZ Merkleization), X4 (XMSS — for signature types)
**Estimated Lean LoC**: ~950
**Files created**: 12 new files

## 1. Objective

Formalize all consensus-layer data structures: Slot (with 3SF-mini justifiable
distance predicates), Checkpoint, Validator, AttestationData, AggregatedAttestation,
Block, BlockHeader, SignedBlock, and the full State container. Every type gets
SSZ serialization and `hashTreeRoot` automatically via the X1/X2 infrastructure.

## 2. Reference Files

| Python File | Lean Target |
|-------------|-------------|
| `src/lean_spec/subspecs/containers/slot.py` | `Consensus/Containers/Slot.lean` |
| `src/lean_spec/subspecs/containers/checkpoint.py` | `Consensus/Containers/Checkpoint.lean` |
| `src/lean_spec/subspecs/containers/validator.py` | `Consensus/Containers/Validator.lean` |
| `src/lean_spec/subspecs/containers/config.py` | `Consensus/Containers/Config.lean` |
| `src/lean_spec/subspecs/containers/attestation/` | `Consensus/Containers/Attestation/*.lean` |
| `src/lean_spec/subspecs/containers/block/` | `Consensus/Containers/Block/*.lean` |
| `src/lean_spec/subspecs/containers/state/` | `Consensus/Containers/State/*.lean` |

## 3. Sub-task Breakdown

### Group A: Primitive Containers (X5-A1 through X5-A6)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X5-A1 | **Define `Slot` type with arithmetic.** `structure Slot where val : Uint64`. Derive instances. Arithmetic: `add`, `sub`, `lt`, `le`. Sentinel: `Slot.zero`. SSZ delegates to Uint64. | `Consensus/Containers/Slot.lean` | ~30 | X1, X2 |
| X5-A2 | **Define `isqrt` and 3SF-mini justifiable distance predicates.** `isqrt : Nat → Nat` (integer square root). `isJustifiableAfter : Slot → Slot → Bool` — delta `d = target - finalized`: (a) `d ≤ 5` (immediate window), OR (b) `isqrt(d)^2 = d` (perfect square), OR (c) `isqrt(4*d+1)^2 = 4*d+1 ∧ isqrt(4*d+1) % 2 = 1` (pronic number = n(n+1)). `justifiedIndexAfter : Slot → Slot → Option Nat`. | `Consensus/Containers/Slot.lean` | ~35 | X5-A1 |
| X5-A3 | **Prove Slot and isqrt properties.** (1) `isqrt_correct : isqrt n * isqrt n ≤ n ∧ (isqrt n + 1)^2 > n`. (2) `isJustifiableAfter_window : d ≤ 5 → true`. (3) `isJustifiableAfter_one : always true for d=1`. (4) `slot_lt_trans`, `slot_lt_irrefl`, `slot_le_antisymm`. (5) `perfect_square_is_justifiable : isqrt(d)^2 = d → isJustifiableAfter`. (6) `pronic_is_justifiable : d = n*(n+1) → isJustifiableAfter`. | `Consensus/Containers/Slot.lean` | ~45 | X5-A2 |
| X5-A4 | **Define `Checkpoint`.** `structure Checkpoint where root : Bytes32; slot : Slot`. SSZ, `isZero`. | `Consensus/Containers/Checkpoint.lean` | ~15 | X5-A1 |
| X5-A5 | **Define `ValidatorIndex` and `Validator`.** `ValidatorIndex` (Uint64 wrapper). `isProposerFor` (round-robin: slot % numValidators). `Validator` with attestation/proposal pubkeys. `Validators := SSZList Validator 4096`. | `Consensus/Containers/Validator.lean` | ~40 | X1, X4-A3 |
| X5-A6 | **Define `Config` and `ConsensusError`.** Chain constants (HISTORICAL_ROOTS_LIMIT, VALIDATOR_REGISTRY_LIMIT, SECONDS_PER_SLOT, etc). Error type with 12+ variants. | `Consensus/Containers/Config.lean` | ~40 | X1 |

### Group B: Attestation Types (X5-B1 through X5-B3)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X5-B1 | **Define attestation data structures.** `AttestationData` (slot, head, target, source checkpoints). `Attestation`, `AggregationBits := BaseBitlist 4096`, `AggregatedAttestation`, `AggregatedAttestations := SSZList AggregatedAttestation 4096`. | `Consensus/Containers/Attestation/Types.lean` | ~40 | X5-A1, X5-A4 |
| X5-B2 | **Define attestation aggregation.** `aggregateByData : List Attestation → List AggregatedAttestation` — group by `AttestationData`, merge `aggregationBits` via bitwise OR. | `Consensus/Containers/Attestation/Aggregation.lean` | ~30 | X5-B1 |
| X5-B3 | **Prove aggregation correctness.** `aggregateByData_preserves_votes` (no vote lost). `aggregateByData_no_spurious` (no vote invented). | `Consensus/Containers/Attestation/Proofs.lean` | ~30 | X5-B2 |

### Group C: Block Types (X5-C1 through X5-C4)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X5-C1 | **Define block structures.** `BlockBody`, `BlockHeader`, `Block`. SSZ serialization for all. | `Consensus/Containers/Block/Types.lean` | ~35 | X5-B1 |
| X5-C2 | **Define signed block and signature verification.** `AttestationSignatures`, `BlockSignatures`, `SignedBlock`. `verifySignatures` — verify proposer + attestation XMSS signatures. | `Consensus/Containers/Block/Signatures.lean` | ~45 | X5-C1, X4-F1 |
| X5-C3 | **Prove block header integrity.** `blockHeader_of_block` extraction. `blockHeader_bodyRoot_correct`. | `Consensus/Containers/Block/Proofs.lean` | ~20 | X5-C1 |
| X5-C4 | **Prove signature verification soundness.** `verifySignatures_implies_valid_proposer`. `verifySignatures_implies_valid_attestations`. | `Consensus/Containers/Block/Proofs.lean` | ~25 | X5-C2 |

### Group D: State Container (X5-D1 through X5-D6)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X5-D1 | **Define state support types.** `HistoricalBlockHashes`, `JustificationRoots`, `JustifiedSlots`, `JustificationValidators`. | `Consensus/Containers/State/Types.lean` | ~15 | X1 |
| X5-D2 | **Define `JustifiedSlots` operations.** `isSlotJustified` (relative indexing from finalized), `withJustified`, `extendToSlot`, `shiftWindow`. | `Consensus/Containers/State/Types.lean` | ~40 | X5-D1, X5-A1 |
| X5-D3 | **Prove JustifiedSlots correctness.** `extend_preserves_existing`, `withJustified_get`, `shiftWindow_correctness`, `extendToSlot_length_ge`. | `Consensus/Containers/State/Proofs.lean` | ~35 | X5-D2 |
| X5-D4 | **Define `State` container.** Full state: config, slot, header, justified/finalized checkpoints, history, justifiedSlots, validators, justification tracking. SSZ serialization. | `Consensus/Containers/State/State.lean` | ~25 | X5-D1, X5-A4, X5-A5 |
| X5-D5 | **Define `generateGenesis`.** `generateGenesis : Uint64 → Validators → State`. Prove: `genesis_slot_zero`, `genesis_justified_eq_finalized`, `genesis_history_empty`, `genesis_validators_preserved`. | `Consensus/Containers/State/Genesis.lean` | ~35 | X5-D4 |
| X5-D6 | **State well-formedness predicates.** `stateWellFormed : State → Prop` combining slot/history/validator bounds. Prove `genesis_well_formed`. | `Consensus/Containers/State/Proofs.lean` | ~25 | X5-D4, X5-D5 |

### Group E: Integration Tests (X5-E1 through X5-E2)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X5-E1 | **Container SSZ roundtrip test suite.** `hashTreeRoot` for every type vs Python reference. SSZ roundtrip for State, Block, Attestation. | `tests/ContainerSuite.lean` | ~40 | All X5-* |
| X5-E2 | **Genesis generation test.** Verify genesis matches Python output. Compare `hashTreeRoot(genesisState)` against reference. | `tests/ContainerSuite.lean` | ~20 | X5-D5 |

## 4. Exit Criteria

- [ ] All consensus containers compile with SSZ serialization
- [ ] `hashTreeRoot` matches Python reference for all types
- [ ] Genesis generation proved correct (4 properties)
- [ ] JustifiedSlots operations proved sound (4 properties)
- [ ] Attestation aggregation proved correct (no lost/invented votes)
- [ ] Block header chain integrity proved
- [ ] Signature verification soundness proved
- [ ] State well-formedness predicate with genesis proof
- [ ] Container SSZ roundtrip tests pass
- [ ] Zero sorry in all container modules
