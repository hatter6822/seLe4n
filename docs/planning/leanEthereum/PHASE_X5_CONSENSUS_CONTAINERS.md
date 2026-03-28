# Phase X5: Consensus Containers

**Version**: v0.5.0
**Status**: PLANNED
**Sub-tasks**: 20 atomic units
**Dependencies**: X2 (SSZ Merkleization), X4 (XMSS — for signature types)
**Estimated Lean LoC**: ~800
**Files created**: 12 new files

## 1. Objective

Formalize all consensus-layer data structures: Slot (with 3SF-mini justifiable
distance predicates), Checkpoint, Validator, AttestationData, AggregatedAttestation,
Block, BlockHeader, SignedBlock, and the full State container. Every type gets
SSZ serialization and `hashTreeRoot` automatically via the X1/X2 infrastructure.

This phase is critical because the State container and its supporting types are
the data that the state transition function (X6) operates on.

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
| `src/lean_spec/subspecs/chain/config.py` | `Consensus/Containers/Config.lean` |

## 3. Sub-task Breakdown

### Group A: Primitive Containers (X5-A1 through X5-A5)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X5-A1 | **Define `Slot` type with arithmetic.** `structure Slot where val : Uint64` deriving `DecidableEq, Repr, Ord, BEq, Hashable`. Add `SSZSerializable` (delegates to Uint64). Add arithmetic: `add : Slot → Uint64 → Slot`, `sub : Slot → Slot → Uint64`, `lt`, `le`, `gt`, `ge`. Add sentinel: `Slot.zero := Slot.mk (Uint64.ofNat 0)`. | `Consensus/Containers/Slot.lean` | ~30 | X1, X2 |
| X5-A2 | **Define 3SF-mini justifiable distance predicates.** `IMMEDIATE_JUSTIFICATION_WINDOW : Nat := 5`. `justifiedIndexAfter : Slot → Slot → Option Nat` — returns `none` if target ≤ finalized (implicitly justified), otherwise `some (target.val - finalized.val - 1)`. `isJustifiableAfter : Slot → Slot → Bool` — 3SF-mini rule: delta `d = target - finalized` is justifiable if: (a) `d ≤ 5`, OR (b) `d` is a perfect square (`isqrt(d)² = d`), OR (c) `d` is a pronic number (`4·d+1` is an odd perfect square). Define `isqrt : Nat → Nat` (integer square root). | `Consensus/Containers/Slot.lean` | ~40 | X5-A1 |
| X5-A3 | **Prove Slot predicates.** (1) `justifiedIndexAfter_some_implies_gt : justifiedIndexAfter t f = some i → t > f`. (2) `isJustifiableAfter_window : t.val - f.val ≤ 5 → isJustifiableAfter t f = true`. (3) `isJustifiableAfter_one : isJustifiableAfter (f + 1) f = true` (distance 1 is always justifiable). (4) `isqrt_correct : isqrt n * isqrt n ≤ n ∧ (isqrt n + 1) * (isqrt n + 1) > n`. (5) `slot_lt_trans`, `slot_lt_irrefl`, `slot_le_antisymm`. | `Consensus/Containers/Slot.lean` | ~40 | X5-A2 |
| X5-A4 | **Define `Checkpoint`.** `structure Checkpoint where root : Bytes32; slot : Slot` deriving `SSZSerializable, DecidableEq, Repr, BEq, Hashable`. SSZ: two fixed-size fields → Container is fixed-size. Define `Checkpoint.isZero : Checkpoint → Bool := root == ZERO_HASH`. | `Consensus/Containers/Checkpoint.lean` | ~15 | X5-A1 |
| X5-A5 | **Define `ValidatorIndex` and `Validator`.** `structure ValidatorIndex where val : Uint64` deriving `DecidableEq, Repr, Ord, BEq, Hashable`. Add `isProposerFor : ValidatorIndex → Slot → Uint64 → Bool := vi.val.toNat % numValidators.toNat == vi.val.toNat`. Add `isValid : ValidatorIndex → Uint64 → Bool := vi.val < numValidators`. Add `computeSubnetId : ValidatorIndex → Uint64 → SubnetId`. `structure Validator where attestationPubkey : Bytes52; proposalPubkey : Bytes52; index : ValidatorIndex` deriving SSZSerializable. `abbrev Validators := SSZList Validator 4096`. | `Consensus/Containers/Validator.lean` | ~40 | X1, X4-A3 |

### Group B: Configuration (X5-B1 through X5-B2)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X5-B1 | **Define `Config` container and chain constants.** `structure Config where genesisTime : Uint64` deriving SSZSerializable. Constants: `HISTORICAL_ROOTS_LIMIT : Nat := 262144`, `VALIDATOR_REGISTRY_LIMIT : Nat := 4096`, `SECONDS_PER_SLOT : Nat := 4`, `INTERVALS_PER_SLOT : Nat := 5`, `MILLISECONDS_PER_SLOT : Nat := 4000`, `MILLISECONDS_PER_INTERVAL : Nat := 800`, `JUSTIFICATION_LOOKBACK_SLOTS : Nat := 3`, `ATTESTATION_COMMITTEE_COUNT : Nat := 1`. | `Consensus/Containers/Config.lean` | ~25 | X1 |
| X5-B2 | **Define consensus error type.** `inductive ConsensusError | slotMismatch (expected actual : Slot) | parentMismatch (expected actual : Bytes32) | invalidProposer (index : ValidatorIndex) (slot : Slot) | stateRootMismatch (expected actual : Bytes32) | attestationFilterFailed (reason : String) | supermajorityNotReached (votes needed : Nat) | finalizationFailed | invalidSignature | buildBlockFailed (msg : String) | slotRegression (current target : Slot) | validatorNotFound (index : ValidatorIndex) | historyLimitExceeded`. | `Consensus/Containers/Config.lean` | ~20 | — |

### Group C: Attestation Types (X5-C1 through X5-C3)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X5-C1 | **Define attestation data structures.** `structure AttestationData where slot : Slot; head : Checkpoint; target : Checkpoint; source : Checkpoint` deriving `SSZSerializable, DecidableEq, BEq, Hashable`. `def dataRootBytes : AttestationData → Bytes32 := hashTreeRoot`. `structure Attestation where validatorId : ValidatorIndex; data : AttestationData`. `abbrev AggregationBits := BaseBitlist 4096`. `structure AggregatedAttestation where aggregationBits : AggregationBits; data : AttestationData` deriving SSZSerializable. `abbrev AggregatedAttestations := SSZList AggregatedAttestation 4096`. | `Consensus/Containers/Attestation/Types.lean` | ~40 | X5-A1, X5-A4, X5-A5 |
| X5-C2 | **Define attestation aggregation function.** `aggregateByData : List Attestation → List AggregatedAttestation` — group attestations sharing identical `AttestationData`, merge `aggregationBits` via bitwise OR. Implementation: fold over attestation list, accumulate into a HashMap keyed by `AttestationData`, merge bits on collision. | `Consensus/Containers/Attestation/Aggregation.lean` | ~30 | X5-C1 |
| X5-C3 | **Prove aggregation correctness.** (1) `aggregateByData_preserves_votes : ∀ att ∈ atts, ∃ agg ∈ aggregateByData atts, agg.aggregationBits.get att.validatorId.val.toNat = some true`. (2) `aggregateByData_no_spurious : ∀ agg ∈ aggregateByData atts, ∀ i, agg.aggregationBits.get i = some true → ∃ att ∈ atts, att.validatorId.val.toNat = i ∧ att.data = agg.data`. No vote is lost, no vote is invented. | `Consensus/Containers/Attestation/Proofs.lean` | ~30 | X5-C2 |

### Group D: Block Types (X5-D1 through X5-D3)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X5-D1 | **Define block structures.** `structure BlockBody where attestations : AggregatedAttestations` deriving SSZSerializable. `structure BlockHeader where slot : Slot; proposerIndex : ValidatorIndex; parentRoot : Bytes32; stateRoot : Bytes32; bodyRoot : Bytes32` deriving SSZSerializable, DecidableEq, BEq. `structure Block where slot : Slot; proposerIndex : ValidatorIndex; parentRoot : Bytes32; stateRoot : Bytes32; body : BlockBody` deriving SSZSerializable. | `Consensus/Containers/Block/Types.lean` | ~35 | X5-C1 |
| X5-D2 | **Define signed block and signature verification.** `structure AttestationSignatures := SSZList Signature ATTESTATION_SIG_LIMIT`. `structure BlockSignatures where attestationSignatures : AttestationSignatures; proposerSignature : Signature` deriving SSZSerializable. `structure SignedBlock where block : Block; signature : BlockSignatures`. `verifySignatures : SignedBlock → State → GeneralizedXmssScheme → Bool` — verify proposer signature over `hashTreeRoot block` and each attestation signature by participating validators (checking aggregationBits). | `Consensus/Containers/Block/Signatures.lean` | ~45 | X5-D1, X4-D4 |
| X5-D3 | **Prove block header chain integrity.** `blockHeader_of_block : Block → BlockHeader` extracts header from block (slot, proposerIndex, parentRoot, stateRoot, bodyRoot = hashTreeRoot body). Prove `blockHeader_bodyRoot_correct : (blockHeader_of_block b).bodyRoot = hashTreeRoot b.body`. | `Consensus/Containers/Block/Proofs.lean` | ~20 | X5-D1 |

### Group E: State Container (X5-E1 through X5-E5)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X5-E1 | **Define state support types.** `abbrev HistoricalBlockHashes := SSZList Bytes32 262144`. `abbrev JustificationRoots := SSZList Bytes32 262144`. `abbrev JustifiedSlots := BaseBitlist 262144`. `abbrev JustificationValidators := BaseBitlist (262144 * 4096)`. | `Consensus/Containers/State/Types.lean` | ~15 | X1 |
| X5-E2 | **Define `JustifiedSlots` operations.** `isSlotJustified : JustifiedSlots → Slot → Slot → Bool` — returns true if target slot is justified (either finalized or marked in bitfield at correct index). `withJustified : JustifiedSlots → Slot → Slot → Bool → JustifiedSlots` — set justification status for a target slot. `extendToSlot : JustifiedSlots → Slot → Slot → JustifiedSlots` — grow bitfield to accommodate a new slot (false-fill gaps). `shiftWindow : JustifiedSlots → Nat → JustifiedSlots` — drop first N bits after finalization advances. | `Consensus/Containers/State/Types.lean` | ~40 | X5-E1, X5-A1 |
| X5-E3 | **Prove JustifiedSlots operation correctness.** (1) `extend_preserves_existing : isSlotJustified js f s = true → isSlotJustified (extendToSlot js f s') f s = true` (extension doesn't lose data). (2) `withJustified_get : isSlotJustified (withJustified js f s v) f s = v`. (3) `shiftWindow_correctness : ∀ i ≥ n, (shiftWindow js n).get (i - n) = js.get i`. (4) `extendToSlot_length_ge : (extendToSlot js f s).length ≥ js.length`. | `Consensus/Containers/State/Proofs.lean` | ~35 | X5-E2 |
| X5-E4 | **Define `State` container.** `structure State where config : Config; slot : Slot; latestBlockHeader : BlockHeader; latestJustified : Checkpoint; latestFinalized : Checkpoint; historicalBlockHashes : HistoricalBlockHashes; justifiedSlots : JustifiedSlots; validators : Validators; justificationsRoots : JustificationRoots; justificationsValidators : JustificationValidators` deriving SSZSerializable. | `Consensus/Containers/State/State.lean` | ~25 | X5-E1, X5-A4, X5-A5, X5-D1 |
| X5-E5 | **Define `generateGenesis`.** `generateGenesis : Uint64 → Validators → State` — creates genesis state: slot=0, empty history, zero-hash justified/finalized checkpoints, empty justification tracking. Prove: `genesis_slot_zero`, `genesis_justified_eq_finalized`, `genesis_history_empty`, `genesis_validators_preserved : (generateGenesis t vs).validators = vs`. | `Consensus/Containers/State/Genesis.lean` | ~35 | X5-E4 |

### Group F: Integration Test (X5-F1 through X5-F2)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X5-F1 | **Container SSZ roundtrip test suite.** Test `hashTreeRoot` for every container type against Python reference values. Test SSZ serialize/deserialize roundtrip for State, Block, Attestation. | `tests/ContainerSuite.lean` | ~40 | All X5-* |
| X5-F2 | **Genesis generation test.** Verify genesis state matches Python `State.generate_genesis()` output for same inputs. Compare `hashTreeRoot(genesisState)` against reference. | `tests/ContainerSuite.lean` | ~20 | X5-E5 |

## 4. Exit Criteria

- [ ] All consensus containers compile with SSZ serialization
- [ ] `hashTreeRoot` matches Python reference for all types
- [ ] Genesis generation proved correct (4 properties)
- [ ] JustifiedSlots operations proved sound (4 properties)
- [ ] Attestation aggregation proved correct (no lost/invented votes)
- [ ] Block header chain integrity proved
- [ ] Container SSZ roundtrip tests pass
- [ ] Zero sorry in all container modules
