# Phase X6: State Transition — Core Operations

**Version**: v0.6.0
**Status**: PLANNED
**Sub-tasks**: 18 atomic units
**Dependencies**: X5 (Consensus Containers), X2 (SSZ for hashTreeRoot)
**Estimated Lean LoC**: ~1,100
**Files created**: 7 new files

## 1. Objective

Formalize the heart of the consensus layer: the state transition function.
Every block applied to the beacon state flows through `stateTransition`, which
composes `processSlots`, `processBlockHeader`, and `processAttestations`.

This is the most algorithmically complex phase. The attestation processing
logic implements 3SF-mini justification/finalization — including supermajority
voting, continuous justification chain detection, and finalization advancement
with historical tracking and bitfield pruning. Following seLe4n's pattern,
transitions go in `StateTransition/*.lean` and proofs go in Phase X7.

## 2. Reference

The primary reference is `src/lean_spec/subspecs/containers/state/state.py`,
methods: `process_slots`, `process_block_header`, `process_attestations`,
`process_block`, `state_transition`, `build_block`.

## 3. Source Layout

```
LeanEth/Consensus/StateTransition/
├── ProcessSlots.lean              Slot-by-slot state advancement
├── ProcessBlockHeader.lean        Block header validation + history tracking
├── ProcessAttestations/
│   ├── Filter.lean                Attestation filtering (validity checks)
│   ├── Voting.lean                Supermajority voting + justification
│   ├── Finalization.lean          Finalization advancement + pruning
│   └── Compose.lean              Full processAttestations composition
├── StateTransition.lean           Top-level state_transition function
└── BuildBlock.lean                Block production (greedy aggregation)
```

## 4. Sub-task Breakdown

### Group A: Slot Processing (X6-A1 through X6-A3)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X6-A1 | **Define `processSlots`.** `processSlots : State → Slot → Except ConsensusError State` — advance state one slot at a time from `state.slot` to `targetSlot - 1`. At each slot: (a) if `latestBlockHeader.stateRoot = ZERO_HASH`, set it to `hashTreeRoot state` (cache state root into empty header). (b) Increment slot by 1. Uses functional update (`{ state with slot := ... }`). Return error if `targetSlot < state.slot` (regression). | `ProcessSlots.lean` | ~35 | X5 |
| X6-A2 | **Prove `processSlots` basic properties.** (1) `processSlots_target_slot : processSlots s t = .ok s' → s'.slot = t`. (2) `processSlots_monotone : processSlots s t = .ok s' → s.slot ≤ s'.slot`. (3) `processSlots_preserves_validators : (·.validators)`. (4) `processSlots_preserves_config : (·.config)`. (5) `processSlots_preserves_finalized : (·.latestFinalized)`. (6) `processSlots_preserves_justified : (·.latestJustified)`. | `ProcessSlots.lean` | ~40 | X6-A1 |
| X6-A3 | **Prove processSlots rejects regression.** `processSlots_rejects_past : targetSlot < s.slot → processSlots s targetSlot = .error (slotRegression s.slot targetSlot)`. Also prove `processSlots_noop : s.slot = targetSlot → processSlots s targetSlot = .ok s` (no-op when already at target). | `ProcessSlots.lean` | ~20 | X6-A1 |

### Group B: Block Header Processing (X6-B1 through X6-B4)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X6-B1 | **Define `processBlockHeader` — validation.** `processBlockHeader : State → Block → Except ConsensusError State`. First section: validation checks. (1) `block.slot = state.slot` (slot match). (2) `block.slot > state.latestBlockHeader.slot` (monotonic progress). (3) `block.proposerIndex.isProposerFor block.slot state.validators.length` (valid proposer). (4) `block.parentRoot = hashTreeRoot state.latestBlockHeader` (parent chain). Return specific `ConsensusError` variant for each failure. | `ProcessBlockHeader.lean` | ~35 | X5 |
| X6-B2 | **Define `processBlockHeader` — genesis special case.** If the parent header is genesis (slot = 0): mark parent checkpoint as both justified and finalized. Set `latestJustified` and `latestFinalized` to `Checkpoint { root := block.parentRoot, slot := Slot.zero }`. This bootstraps the justification/finalization chain from genesis. | `ProcessBlockHeader.lean` | ~20 | X6-B1 |
| X6-B3 | **Define `processBlockHeader` — history and state update.** After validation: (a) append `block.parentRoot` to `historicalBlockHashes`. (b) For any gap between parent slot and current slot, append `ZERO_HASH` entries. (c) Extend `justifiedSlots` bitfield to accommodate block slot via `extendToSlot`. (d) Update `latestBlockHeader` to new `BlockHeader { slot, proposerIndex, parentRoot, stateRoot := ZERO_HASH, bodyRoot := hashTreeRoot block.body }` (stateRoot filled later). | `ProcessBlockHeader.lean` | ~40 | X6-B1 |
| X6-B4 | **Prove `processBlockHeader` properties.** (1) `rejects_wrong_slot : block.slot ≠ s.slot → error`. (2) `rejects_wrong_proposer`. (3) `rejects_wrong_parent`. (4) `preserves_validators`. (5) `extends_history : s'.historicalBlockHashes.length ≥ s.historicalBlockHashes.length`. (6) `preserves_config`. (7) `header_slot_matches : s'.latestBlockHeader.slot = block.slot`. | `ProcessBlockHeader.lean` | ~40 | X6-B1, X6-B3 |

### Group C: Attestation Processing — The Complex Core (X6-C1 through X6-C6)

This is the most intricate part of the consensus specification. The Python
implementation is ~150 lines of dense logic. We decompose it into three
focused sub-modules.

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X6-C1 | **Define attestation filter.** `filterAttestations : State → List AggregatedAttestation → List AggregatedAttestation`. For each attestation, apply ALL filter checks: (1) `att.data.source` is justified in current state (`justifiedSlots.isSlotJustified`). (2) `att.data.target` is NOT already justified. (3) `att.data.source.root ≠ ZERO_HASH`. (4) `att.data.target.root ≠ ZERO_HASH`. (5) Source and target roots exist in `historicalBlockHashes` at correct indices. (6) `att.data.target.slot > att.data.source.slot` (forward time). (7) `att.data.target.slot.isJustifiableAfter state.latestFinalized.slot` (3SF-mini distance rule). Return only attestations passing ALL checks. | `ProcessAttestations/Filter.lean` | ~60 | X5 |
| X6-C2 | **Prove filter soundness.** (1) `filter_subset : filterAttestations s atts ⊆ atts`. (2) `filter_source_justified : ∀ att ∈ filterAttestations s atts, isSlotJustified s.justifiedSlots s.latestFinalized.slot att.data.source.slot = true`. (3) `filter_target_not_justified`. (4) `filter_forward_time : ∀ att ∈ filtered, att.data.target.slot > att.data.source.slot`. (5) `filter_justifiable : ∀ att ∈ filtered, isJustifiableAfter att.data.target.slot s.latestFinalized.slot`. | `ProcessAttestations/Filter.lean` | ~35 | X6-C1 |
| X6-C3 | **Define supermajority voting.** `structure JustificationTracker where roots : Array Bytes32; validatorBits : Array (Array Bool)` — maps tracked block roots to per-validator vote bitfields. `applyVotes : JustificationTracker → List AggregatedAttestation → JustificationTracker` — for each filtered attestation targeting a tracked root, OR the attestation's `aggregationBits` into the tracker's validator bits for that root. `checkSupermajority : JustificationTracker → Nat → List (Bytes32 × Slot)` — for each tracked root, if `3 * votesFor(root) ≥ 2 * totalValidators`, add to justified list. | `ProcessAttestations/Voting.lean` | ~60 | X6-C1 |
| X6-C4 | **Define finalization advancement.** `advanceFinalization : State → List (Bytes32 × Slot) → State` — given newly justified checkpoints, check if finalization can advance. Condition: a checkpoint `cp` can be finalized if there exists a continuous chain of justifiable slots from `latestFinalized.slot` to `cp.slot` where each intermediate slot is justified. If finalization advances: (a) update `latestFinalized`. (b) Prune `justificationsRoots` entries for slots ≤ new finalized. (c) Shift `justifiedSlots` window via `shiftWindow`. (d) Rebase `justificationsValidators` bitfield. | `ProcessAttestations/Finalization.lean` | ~60 | X6-C3, X5-A2 |
| X6-C5 | **Compose full `processAttestations`.** `processAttestations : State → AggregatedAttestations → State`. Steps: (1) Reconstruct `JustificationTracker` from current state's `justificationsRoots` and `justificationsValidators`. (2) Filter attestations via X6-C1. (3) Apply votes via X6-C3. (4) Check supermajority and collect newly justified. (5) Update `justifiedSlots` for newly justified. (6) Advance finalization via X6-C4. (7) Convert tracker back to SSZ format (sorted roots + flattened validator bits). (8) Update `latestJustified` to highest justified checkpoint. | `ProcessAttestations/Compose.lean` | ~50 | X6-C1, X6-C3, X6-C4 |
| X6-C6 | **Prove processAttestations preserves field invariants.** (1) `preserves_slot`, (2) `preserves_validators`, (3) `preserves_config`, (4) `finalization_monotone : s'.latestFinalized.slot ≥ s.latestFinalized.slot`, (5) `justification_monotone : s'.latestJustified.slot ≥ s.latestJustified.slot`. These are the foundational properties needed by the safety proofs in X7. | `ProcessAttestations/Compose.lean` | ~40 | X6-C5 |

### Group D: Top-Level Composition (X6-D1 through X6-D3)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X6-D1 | **Define `processBlock`.** `processBlock : State → Block → Except ConsensusError State := fun s b => do let s' ← processBlockHeader s b; pure (processAttestations s' b.body.attestations)`. Simple sequential composition. | `StateTransition.lean` | ~10 | X6-B1, X6-C5 |
| X6-D2 | **Define `stateTransition`.** `stateTransition : State → Block → Bool → Except ConsensusError State := fun s b validateSigs => do let s₁ ← processSlots s b.slot; let s₂ ← processBlock s₁ b; if b.stateRoot = hashTreeRoot s₂ then .ok s₂ else .error (stateRootMismatch b.stateRoot (hashTreeRoot s₂))`. The `validateSigs` parameter is for test mode (signature validation deferred to SignedBlock level). | `StateTransition.lean` | ~15 | X6-D1, X6-A1 |
| X6-D3 | **Define `buildBlock` (block production).** `buildBlock : State → List Attestation → Validators → GeneralizedXmssScheme → ValidatorIndex → Except ConsensusError (Block × State × List AggregatedAttestation × List AggregatedSignatureProof)`. Steps: (1) Find attestations matching current justified checkpoint. (2) Aggregate by data. (3) Greedily select proofs maximizing new validator coverage. (4) Iterate: apply state transition, check if justification stabilized. (5) Compute state root. (6) Assemble Block with correct stateRoot. | `BuildBlock.lean` | ~60 | X6-D2, X5-C2, X4-E1 |

### Group E: Test Suite (X6-E1 through X6-E2)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X6-E1 | **State transition test vectors.** Create `tests/StateTransitionSuite.lean`: genesis → first block (no attestations), multi-block chain, attestation processing with supermajority trigger, finalization trigger. Compare state roots against Python reference for each transition. | `tests/StateTransitionSuite.lean` | ~50 | All X6-* |
| X6-E2 | **Negative state tests.** Test all error paths: invalid slot → error, wrong proposer → error, bad parent root → error, bad state root → error, slot regression → error. Verify correct error variant returned. | `tests/StateTransitionSuite.lean` | ~30 | X6-D2 |

## 5. Key Technical Detail: Attestation Processing Flow

```
processAttestations(state, attestations)
    │
    ├── 1. Reconstruct JustificationTracker from state
    │       roots = state.justificationsRoots
    │       bits  = state.justificationsValidators (flattened)
    │
    ├── 2. Filter attestations (X6-C1)
    │       ├── source justified? ──→ reject if no
    │       ├── target not justified? ──→ reject if already justified
    │       ├── roots non-zero? ──→ reject if zero
    │       ├── roots in history? ──→ reject if missing
    │       ├── forward time? ──→ reject if target ≤ source
    │       └── justifiable distance? ──→ reject if not 3SF-mini valid
    │
    ├── 3. Apply votes to tracker (X6-C3)
    │       For each valid attestation:
    │         tracker[target.root] |= attestation.aggregationBits
    │
    ├── 4. Check supermajority
    │       For each tracked root:
    │         if 3 * popcount(bits) ≥ 2 * totalValidators:
    │           mark as newly justified
    │           remove from tracker
    │
    ├── 5. Update justifiedSlots
    │       For each newly justified checkpoint:
    │         justifiedSlots.withJustified(finalized, target, true)
    │
    ├── 6. Advance finalization (X6-C4)
    │       Find longest continuous justification chain
    │       from latestFinalized to any newly justified:
    │         if all intermediate slots are justifiable AND justified:
    │           finalize the target
    │           prune history before new finalized
    │           shift justifiedSlots window
    │
    └── 7. Serialize tracker back to SSZ format
            Sort roots, flatten validator bits
```

## 6. Exit Criteria

- [ ] Full pipeline: processSlots → processBlockHeader → processAttestations → stateTransition
- [ ] All validation checks match Python reference behavior
- [ ] processSlots: 8 properties proved (target slot, monotone, 6 preservation)
- [ ] processBlockHeader: 7 properties proved
- [ ] processAttestations: filter soundness (5 props), field preservation (5 props)
- [ ] State transition test suite passes with fixture match
- [ ] Negative state tests cover all error paths
- [ ] Zero sorry in state transition modules
