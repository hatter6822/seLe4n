# Phase X6: State Transition — Core Operations

**Version**: v0.6.0
**Status**: PLANNED
**Sub-tasks**: 38 atomic units
**Dependencies**: X5 (Consensus Containers), X2 (SSZ for hashTreeRoot)
**Estimated Lean LoC**: ~1,600
**Files created**: 10 new files

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
├── ProcessSlots.lean                Slot-by-slot state advancement
├── ProcessBlockHeader.lean          Block header validation + history tracking
├── ProcessAttestations/
│   ├── Tracker.lean                 JustificationTracker reconstruction + serialization
│   ├── Filter.lean                  Per-attestation validity filtering (7 checks)
│   ├── Voting.lean                  Vote recording + supermajority detection
│   ├── Finalization.lean            Continuous chain detection + finalization advancement
│   ├── Pruning.lean                 Post-finalization state cleanup + rebasing
│   └── Compose.lean                 Full processAttestations orchestration
├── StateTransition.lean             Top-level state_transition function
├── BuildBlock.lean                  Block production (greedy aggregation)
└── Proofs/                          (Phase X7 — listed here for layout reference)
```

## 4. Sub-task Breakdown

### Group A: Slot Processing (X6-A1 through X6-A4)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X6-A1 | **Define `processSlots` core loop.** `processSlots : State → Slot → Except ConsensusError State` — advance state one slot at a time from `state.slot` to `targetSlot - 1`. At each slot: (a) if `latestBlockHeader.stateRoot = ZERO_HASH`, set it to `hashTreeRoot state` (cache state root into the empty header — this only happens on the **first** empty slot after a block). (b) Increment `state.slot` by 1. Return error `slotRegression` if `targetSlot < state.slot`. Implementation: tail-recursive helper `processSlots.loop` with fuel = `targetSlot - state.slot` for well-founded recursion, or structural recursion on the slot gap. | `ProcessSlots.lean` | ~35 | X5 |
| X6-A2 | **Define `processSlots` state root caching logic.** Separate helper: `cacheStateRootIfEmpty : State → State`. If `state.latestBlockHeader.stateRoot = ZERO_HASH` then compute `hashTreeRoot state` and update the header; otherwise return state unchanged. This is called once per slot iteration. Prove `cacheStateRootIfEmpty_idempotent : cacheStateRootIfEmpty (cacheStateRootIfEmpty s) = cacheStateRootIfEmpty s`. Prove `cacheStateRootIfEmpty_preserves_slot : (cacheStateRootIfEmpty s).slot = s.slot`. | `ProcessSlots.lean` | ~25 | X6-A1 |
| X6-A3 | **Prove `processSlots` basic properties.** (1) `processSlots_target_slot : processSlots s t = .ok s' → s'.slot = t`. (2) `processSlots_monotone : processSlots s t = .ok s' → s.slot ≤ s'.slot`. (3) `processSlots_preserves_validators`. (4) `processSlots_preserves_config`. (5) `processSlots_preserves_finalized`. (6) `processSlots_preserves_justified`. (7) `processSlots_preserves_history : s'.historicalBlockHashes = s.historicalBlockHashes`. (8) `processSlots_preserves_justifiedSlots : s'.justifiedSlots = s.justifiedSlots`. | `ProcessSlots.lean` | ~50 | X6-A1 |
| X6-A4 | **Prove processSlots edge cases.** (1) `processSlots_rejects_past : targetSlot < s.slot → processSlots s targetSlot = .error (slotRegression ...)`. (2) `processSlots_noop : s.slot = targetSlot → processSlots s targetSlot = .ok s`. (3) `processSlots_single_step : processSlots s (s.slot + 1) = .ok (cacheStateRootIfEmpty s with slot := s.slot + 1)`. (4) `processSlots_composition : processSlots s t₁ = .ok s₁ → processSlots s₁ t₂ = .ok s₂ → processSlots s t₂ = .ok s₂` (processing in stages gives same result). | `ProcessSlots.lean` | ~40 | X6-A1, X6-A2 |

### Group B: Block Header Processing (X6-B1 through X6-B6)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X6-B1 | **Define `processBlockHeader` — validation checks.** `processBlockHeader : State → Block → Except ConsensusError State`. Validation section (return specific error on failure): (1) `block.slot = state.slot` → `slotMismatch` error. (2) `block.slot > state.latestBlockHeader.slot` → `slotRegression` error (monotonic progress). (3) `block.proposerIndex.val.toNat % state.validators.length = block.proposerIndex.val.toNat` — round-robin proposer selection: the proposer index must satisfy `slot % numValidators = proposerIndex` → `invalidProposer` error. (4) `block.parentRoot = hashTreeRoot state.latestBlockHeader` → `parentMismatch` error. All checks are sequential; first failure short-circuits via `Except`. | `ProcessBlockHeader.lean` | ~40 | X5 |
| X6-B2 | **Define `processBlockHeader` — genesis parent detection.** If the parent header has `slot = 0` (genesis parent), bootstrap the justification/finalization chain: set `latestJustified := Checkpoint { root := block.parentRoot, slot := Slot.zero }` and `latestFinalized := Checkpoint { root := block.parentRoot, slot := Slot.zero }`. This is the trust anchor — genesis cannot receive attestation votes, so both checkpoints are force-set. Prove `genesis_parent_detection_correct : state.latestBlockHeader.slot = Slot.zero → isGenesisParent state = true`. | `ProcessBlockHeader.lean` | ~25 | X6-B1 |
| X6-B3 | **Define `processBlockHeader` — historical hash tracking.** After validation: (a) compute gap `numEmptySlots := block.slot.val - parentHeader.slot.val - 1`. (b) Append to `historicalBlockHashes`: first `block.parentRoot`, then `numEmptySlots` copies of `ZERO_HASH` (representing empty slots between parent and current block). This maintains a slot-indexed history where `historicalBlockHashes[slot]` gives the block root at that slot (or ZERO_HASH if no block). Prove `history_length_after : s'.historicalBlockHashes.length = s.historicalBlockHashes.length + 1 + numEmptySlots`. | `ProcessBlockHeader.lean` | ~30 | X6-B1 |
| X6-B4 | **Define `processBlockHeader` — justified slots extension.** Extend the `justifiedSlots` bitfield to accommodate the new block's slot via `extendToSlot state.justifiedSlots state.latestFinalized.slot (block.slot - 1)`. All new positions are initialized to `false` (unjustified). This ensures the bitfield is wide enough to track justification status for all slots up to the current block. | `ProcessBlockHeader.lean` | ~15 | X6-B1, X5-E2 |
| X6-B5 | **Define `processBlockHeader` — new header assembly.** Create the new `BlockHeader`: `{ slot := block.slot, proposerIndex := block.proposerIndex, parentRoot := block.parentRoot, stateRoot := ZERO_HASH, bodyRoot := hashTreeRoot block.body }`. The `stateRoot` is set to `ZERO_HASH` and will be filled in during the next `processSlots` call (state root caching). Update `state.latestBlockHeader` to this new header. | `ProcessBlockHeader.lean` | ~15 | X6-B1, X6-B3, X6-B4 |
| X6-B6 | **Prove `processBlockHeader` properties.** (1) `rejects_wrong_slot : block.slot ≠ s.slot → processBlockHeader s b = .error (slotMismatch ...)`. (2) `rejects_wrong_proposer`. (3) `rejects_wrong_parent`. (4) `preserves_validators`. (5) `preserves_config`. (6) `extends_history : s'.historicalBlockHashes.length ≥ s.historicalBlockHashes.length`. (7) `header_slot_matches : s'.latestBlockHeader.slot = block.slot`. (8) `header_stateRoot_zero : s'.latestBlockHeader.stateRoot = ZERO_HASH`. (9) `genesis_parent_sets_justified : isGenesisParent s → s'.latestJustified.slot = Slot.zero`. | `ProcessBlockHeader.lean` | ~50 | X6-B1 through X6-B5 |

### Group C: Attestation Processing — The Complex Core (X6-C1 through X6-C16)

This is the most intricate part of the consensus specification. The Python
implementation is ~150 lines of dense logic involving bitfield manipulation,
supermajority arithmetic, continuous chain detection, and finalization with
state rebasing. We decompose it into **six focused sub-modules** with 16
atomic sub-tasks.

#### Sub-group C.1: Justification Tracker (X6-C1 through X6-C3)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X6-C1 | **Define `JustificationTracker` structure.** `structure JustificationTracker where roots : Array Bytes32; votes : Array (Array Bool); numValidators : Nat; h_votes_len : votes.size = roots.size; h_votes_width : ∀ i (h : i < votes.size), (votes.get ⟨i, h⟩).size = numValidators`. This is the in-memory working representation of the justification vote tally. Each `roots[i]` is a tracked block root with `votes[i]` being a per-validator boolean array indicating who has voted for it. Define `empty : Nat → JustificationTracker` (no tracked roots, N validators). | `ProcessAttestations/Tracker.lean` | ~30 | X5 |
| X6-C2 | **Define tracker reconstruction from SSZ state.** `reconstructTracker : State → JustificationTracker`. Unpack the flattened SSZ layout: `state.justificationsRoots` is a list of tracked block roots; `state.justificationsValidators` is a flat bitlist where bits `[i*N .. (i+1)*N)` represent per-validator votes for root `i` (where `N = state.validators.length`). Iterate: for each root at index `i`, extract the corresponding `N`-bit slice from the flat bitlist into `votes[i]`. Prove `reconstructTracker_roots : (reconstructTracker s).roots = s.justificationsRoots.toArray`. | `ProcessAttestations/Tracker.lean` | ~35 | X6-C1 |
| X6-C3 | **Define tracker serialization back to SSZ.** `serializeTracker : JustificationTracker → (SSZList Bytes32 LIMIT × BaseBitlist LIMIT)`. Sort roots lexicographically (deterministic ordering). Flatten votes: concatenate `votes[sortedIndex[0]] ++ votes[sortedIndex[1]] ++ ...` into a single `BaseBitlist`. Prove `serializeTracker_roundtrip : serializeTracker (reconstructTracker s) = (s.justificationsRoots, s.justificationsValidators)` (up to sorting — roots may be reordered but vote data is consistent). | `ProcessAttestations/Tracker.lean` | ~30 | X6-C1, X6-C2 |

#### Sub-group C.2: Attestation Filtering (X6-C4 through X6-C7)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X6-C4 | **Define individual filter predicates.** Seven named boolean predicates, each testing one condition. (1) `sourceJustified : State → AggregatedAttestation → Bool` — `justifiedSlots.isSlotJustified finalizedSlot att.data.source.slot`. (2) `targetNotYetJustified : State → AggregatedAttestation → Bool` — `¬ justifiedSlots.isSlotJustified finalizedSlot att.data.target.slot`. (3) `sourceRootNonzero` — `att.data.source.root ≠ ZERO_HASH`. (4) `targetRootNonzero` — `att.data.target.root ≠ ZERO_HASH`. (5) `rootsOnChain : State → AggregatedAttestation → Bool` — source root matches `historicalBlockHashes[source.slot]` AND target root matches `historicalBlockHashes[target.slot]`. (6) `forwardTime` — `att.data.target.slot > att.data.source.slot`. (7) `justifiableDistance : State → AggregatedAttestation → Bool` — `isJustifiableAfter att.data.target.slot state.latestFinalized.slot`. Each predicate is a single-purpose function with a descriptive name for proof decomposition. | `ProcessAttestations/Filter.lean` | ~50 | X5 |
| X6-C5 | **Define composite filter.** `attestationValid : State → AggregatedAttestation → Bool := fun s att => sourceJustified s att ∧ targetNotYetJustified s att ∧ sourceRootNonzero att ∧ targetRootNonzero att ∧ rootsOnChain s att ∧ forwardTime att ∧ justifiableDistance s att`. Then: `filterAttestations : State → List AggregatedAttestation → List AggregatedAttestation := fun s atts => atts.filter (attestationValid s)`. This is a simple composition — each individual predicate is already defined and can be reasoned about independently. | `ProcessAttestations/Filter.lean` | ~15 | X6-C4 |
| X6-C6 | **Prove filter soundness — per-predicate guarantees.** For each of the 7 predicates, prove a post-condition theorem. (1) `filter_source_justified : ∀ att ∈ filterAttestations s atts, sourceJustified s att = true`. (2) `filter_target_not_justified`. (3-4) `filter_roots_nonzero`. (5) `filter_roots_on_chain`. (6) `filter_forward_time`. (7) `filter_justifiable_distance`. Proof strategy: all follow directly from `List.filter_mem` — membership in the filtered list implies the predicate holds. | `ProcessAttestations/Filter.lean` | ~30 | X6-C5 |
| X6-C7 | **Prove filter structural properties.** (1) `filter_subset : filterAttestations s atts ⊆ atts` (no attestations invented). (2) `filter_preserves_data : ∀ att ∈ filterAttestations s atts, att ∈ atts` (filtered attestations are unmodified). (3) `filter_idempotent : filterAttestations s (filterAttestations s atts) = filterAttestations s atts`. (4) `filter_monotone : atts₁ ⊆ atts₂ → filterAttestations s atts₁ ⊆ filterAttestations s atts₂`. | `ProcessAttestations/Filter.lean` | ~25 | X6-C5 |

#### Sub-group C.3: Vote Recording & Supermajority (X6-C8 through X6-C10)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X6-C8 | **Define vote recording.** `recordVote : JustificationTracker → Bytes32 → ValidatorIndex → JustificationTracker`. If `root` is already tracked: set `votes[rootIndex][validatorIndex] := true`. If `root` is new: add new entry with all-false votes, then set the validator's bit. `applyAttestationVotes : JustificationTracker → AggregatedAttestation → JustificationTracker` — for each validator index `i` where `att.aggregationBits.get i = true`, call `recordVote tracker att.data.target.root i`. `applyAllVotes : JustificationTracker → List AggregatedAttestation → JustificationTracker` — fold `applyAttestationVotes` over all filtered attestations. | `ProcessAttestations/Voting.lean` | ~45 | X6-C1 |
| X6-C9 | **Define supermajority detection.** `voteCount : JustificationTracker → Bytes32 → Nat` — count `true` values in the vote array for the given root. `isSupermajority : Nat → Nat → Bool := fun votes total => 3 * votes ≥ 2 * total` (the ≥2/3 threshold). `detectNewlyJustified : JustificationTracker → List (Bytes32 × Slot) → (List (Bytes32 × Slot) × JustificationTracker)` — for each tracked root, check if supermajority is achieved; if so, add `(root, slot)` to the newly-justified list and **remove** the root from the tracker (no longer needs individual vote tracking). The `Slot` for each root is looked up from `historicalBlockHashes`. | `ProcessAttestations/Voting.lean` | ~40 | X6-C8 |
| X6-C10 | **Prove voting properties.** (1) `recordVote_monotone : votes after ≥ votes before for all validators`. (2) `recordVote_specific : (recordVote t r vi).getVote r vi = true`. (3) `recordVote_preserves_others : vi ≠ vj → (recordVote t r vi).getVote r vj = t.getVote r vj`. (4) `applyAllVotes_monotone : vote counts only increase`. (5) `supermajority_threshold_correct : isSupermajority v n = true ↔ 3 * v ≥ 2 * n`. (6) `detectNewlyJustified_sound : (root, slot) ∈ newlyJustified → isSupermajority (voteCount tracker root) tracker.numValidators = true`. | `ProcessAttestations/Voting.lean` | ~40 | X6-C8, X6-C9 |

#### Sub-group C.4: Finalization Advancement (X6-C11 through X6-C13)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X6-C11 | **Define continuous justification chain detection.** `hasContinuousChain : JustifiedSlots → Slot → Slot → Slot → Bool` — check whether there are **no unjustified justifiable slots** between `source.slot` and `target.slot` relative to `finalizedSlot`. Implementation: iterate over all slots `s` in `(source.slot, target.slot)` (exclusive); for each `s`, if `isJustifiableAfter s finalizedSlot = true` AND `isSlotJustified justifiedSlots finalizedSlot s = false`, return `false` (chain is broken). If no such gap found, return `true`. This is the critical 3SF-mini finalization condition: finalization requires ALL intermediate justifiable slots to be justified. Prove `hasContinuousChain_empty : source.slot + 1 = target.slot → hasContinuousChain js f source.slot target.slot = true` (adjacent slots always have continuous chain). | `ProcessAttestations/Finalization.lean` | ~40 | X5-A2 |
| X6-C12 | **Define `advanceFinalization`.** `advanceFinalization : State → List (Bytes32 × Slot) → State`. For each newly justified checkpoint `(root, slot)`, check whether finalization can advance: the source checkpoint is the attestation's `source` (already justified), and we need a continuous chain from the current `latestFinalized` to `source`. If `hasContinuousChain justifiedSlots latestFinalized.slot source.slot target.slot = true`: (a) set `latestFinalized := source` (the source becomes the new finalization point). (b) Record the new finalized slot. Multiple justifications in a single block can cascade — process in slot order (ascending) so each finalization advancement can enable the next. The highest finalizable source wins. | `ProcessAttestations/Finalization.lean` | ~45 | X6-C11 |
| X6-C13 | **Prove finalization properties.** (1) `advanceFinalization_monotone : s'.latestFinalized.slot ≥ s.latestFinalized.slot`. (2) `advanceFinalization_requires_chain : s'.latestFinalized.slot > s.latestFinalized.slot → ∃ chain, hasContinuousChain ... = true`. (3) `advanceFinalization_preserves_validators`. (4) `advanceFinalization_preserves_slot`. (5) `advanceFinalization_preserves_config`. (6) `advanceFinalization_finalized_was_justified : s'.latestFinalized.slot > s.latestFinalized.slot → isSlotJustified s.justifiedSlots s.latestFinalized.slot s'.latestFinalized.slot = true`. | `ProcessAttestations/Finalization.lean` | ~40 | X6-C12 |

#### Sub-group C.5: Post-Finalization Cleanup (X6-C14 through X6-C15)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X6-C14 | **Define post-finalization state rebasing.** `rebaseAfterFinalization : State → Slot → State`. When finalization advances from `oldFinalized` to `newFinalized`: (a) compute `delta := newFinalized.val - oldFinalized.val`. (b) Shift `justifiedSlots` window by `delta` via `shiftWindow delta` — this drops the first `delta` bits since those slots are now at or before the finalized point and no longer need individual tracking. (c) Prune `justificationsRoots`: remove all roots whose corresponding slot `≤ newFinalized.slot`. (d) Prune corresponding entries from `justificationsValidators` (the flat bitlist). (e) Update `latestJustified` to the max of (current latestJustified, the newly finalized checkpoint) — finalized implies justified. | `ProcessAttestations/Pruning.lean` | ~40 | X5-E2 |
| X6-C15 | **Prove rebasing correctness.** (1) `rebase_preserves_future_justified : ∀ slot > newFinalized, isSlotJustified before = isSlotJustified after` (justification data for future slots is preserved). (2) `rebase_removes_old_roots : ∀ root ∈ prunedTracker.roots, rootSlot root > newFinalized.slot`. (3) `rebase_shifts_justified : (rebaseAfterFinalization s f).justifiedSlots.length = s.justifiedSlots.length - delta` (clamped at 0). (4) `rebase_preserves_validators`, `rebase_preserves_slot`, `rebase_preserves_config`. | `ProcessAttestations/Pruning.lean` | ~30 | X6-C14 |

#### Sub-group C.6: Full Composition (X6-C16)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X6-C16 | **Compose full `processAttestations`.** `processAttestations : State → AggregatedAttestations → State`. Orchestration in 8 steps: (1) Reconstruct `JustificationTracker` from SSZ state via `reconstructTracker`. (2) Filter attestations via `filterAttestations`. (3) Apply votes via `applyAllVotes`. (4) Detect newly justified checkpoints via `detectNewlyJustified`. (5) Update `justifiedSlots` for each newly justified: `withJustified finalizedSlot targetSlot true`. (6) Advance finalization via `advanceFinalization`. (7) If finalization advanced, rebase state via `rebaseAfterFinalization`. (8) Serialize tracker back to SSZ via `serializeTracker`. Update `latestJustified` to highest justified checkpoint. Return new state with all updates applied. Prove: `processAttestations_preserves_slot`, `processAttestations_preserves_validators`, `processAttestations_preserves_config`. | `ProcessAttestations/Compose.lean` | ~60 | X6-C2 through X6-C15 |

### Group D: Top-Level Composition (X6-D1 through X6-D3)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X6-D1 | **Define `processBlock`.** `processBlock : State → Block → Except ConsensusError State := fun s b => do let s' ← processBlockHeader s b; pure (processAttestations s' b.body.attestations)`. Simple sequential composition of header processing and attestation processing. The header processing can fail (validation); attestation processing is total (always returns a state — invalid attestations are silently filtered). | `StateTransition.lean` | ~10 | X6-B1, X6-C16 |
| X6-D2 | **Define `stateTransition`.** `stateTransition : State → Block → Bool → Except ConsensusError State := fun s b validateSigs => do let s₁ ← processSlots s b.slot; let s₂ ← processBlock s₁ b; if b.stateRoot = hashTreeRoot s₂ then .ok s₂ else .error (stateRootMismatch b.stateRoot (hashTreeRoot s₂))`. The `validateSigs` parameter exists for test mode — when `true`, signature validation is performed at the `SignedBlock` level (outside this function). State root verification ensures the block producer correctly predicted the post-state. | `StateTransition.lean` | ~20 | X6-D1, X6-A1 |
| X6-D3 | **Prove stateTransition composition properties.** (1) `stateTransition_slot_correct : stateTransition s b _ = .ok s' → s'.slot = b.slot`. (2) `stateTransition_preserves_validators`. (3) `stateTransition_preserves_config`. (4) `stateTransition_finalization_monotone : s'.latestFinalized.slot ≥ s.latestFinalized.slot`. (5) `stateTransition_justification_monotone : s'.latestJustified.slot ≥ s.latestJustified.slot`. These compose directly from the per-operation properties proved in Groups A-C. | `StateTransition.lean` | ~30 | X6-D2 |

### Group E: Block Production (X6-E1 through X6-E5)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X6-E1 | **Define attestation selection for block building.** `selectAttestations : State → Dict AttestationData (Set AggregatedSignatureProof) → Set Bytes32 → Checkpoint → List (AttestationData × Set AggregatedSignatureProof)`. Filter `aggregatedPayloads` by: (a) `att.data.head.root ∈ knownBlockRoots`, (b) `att.data.source = currentJustified`, (c) not already processed. Sort by `target.slot` ascending (process earlier targets first to enable cascading justification). | `BuildBlock.lean` | ~30 | X5, X6-C5 |
| X6-E2 | **Define greedy proof selection.** `greedySelectProofs : Set AggregatedSignatureProof → Set ValidatorIndex → List (AggregatedSignatureProof × AggregatedAttestation)`. For each attestation data with matching proofs: sort proofs by descending count of NEW participants (validators not yet covered). Greedily select proofs that add at least one new validator. Track `coveredValidators` set. For each selected proof, construct the corresponding `AggregatedAttestation` with merged `aggregationBits`. This maximizes validator coverage per block. | `BuildBlock.lean` | ~35 | X6-E1, X4-E1 |
| X6-E3 | **Define fixed-point justification loop.** `buildBlockLoop : State → ... → Nat → (Block × State × ...)`. The core loop that iterates until justification stabilizes: (1) Assemble candidate `Block` with current attestations. (2) Apply `processSlots(slot).processBlock(candidateBlock)` to get `postState`. (3) If `postState.latestJustified ≠ currentJustified`: justification advanced, so update `currentJustified` and loop again (new attestations may now pass filter with updated justified checkpoint). (4) If `postState.latestJustified = currentJustified`: convergence — exit loop. Use `Nat` fuel parameter for termination (max iterations = number of attestation data entries). | `BuildBlock.lean` | ~45 | X6-E1, X6-E2, X6-D2 |
| X6-E4 | **Define `buildBlock` top-level.** `buildBlock : State → List Attestation → Validators → GeneralizedXmssScheme → ValidatorIndex → Except ConsensusError (Block × State × List AggregatedAttestation × List AggregatedSignatureProof)`. Orchestrate: (1) Detect genesis parent → force `currentJustified = parentRoot`. (2) Aggregate attestations by data via `aggregateByData`. (3) Enter `buildBlockLoop` with initial `currentJustified`. (4) After convergence, compute `stateRoot := hashTreeRoot postState`. (5) Assemble final `Block` with correct `stateRoot`. Return block, post-state, attestation list, and signature proofs. | `BuildBlock.lean` | ~40 | X6-E3 |
| X6-E5 | **Prove buildBlock convergence.** `buildBlock_terminates : buildBlockLoop fuel ... = .ok result` for sufficient fuel. Proof: each iteration either advances `latestJustified.slot` (which is bounded by block slot) or exits. Since slot is finite, the loop terminates in ≤ `block.slot - genesis.slot` iterations. Also prove: `buildBlock_stateRoot_correct : result.block.stateRoot = hashTreeRoot result.postState`. | `BuildBlock.lean` | ~25 | X6-E3 |

### Group F: Test Suite (X6-F1 through X6-F4)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X6-F1 | **State transition positive test vectors.** Create `tests/StateTransitionSuite.lean`: genesis → first block (no attestations), verify slot advances and header updates. Multi-block chain (3 blocks), verify history grows correctly. Compare state roots against Python reference for each transition. | `tests/StateTransitionSuite.lean` | ~35 | X6-D2 |
| X6-F2 | **Attestation processing test vectors.** Test supermajority trigger: 4 validators, 3 attest → justification. Test finalization trigger: continuous justification chain → finalization advances. Test filter rejection: unjustifiable distance, already-justified target, zero-hash source. Compare `latestJustified` and `latestFinalized` against Python reference. | `tests/StateTransitionSuite.lean` | ~40 | X6-C16 |
| X6-F3 | **Negative state tests.** Test all error paths: invalid slot → `slotMismatch`, wrong proposer → `invalidProposer`, bad parent root → `parentMismatch`, bad state root → `stateRootMismatch`, slot regression → `slotRegression`. Verify correct error variant returned for each. | `tests/StateTransitionSuite.lean` | ~30 | X6-D2 |
| X6-F4 | **Block building test.** Test `buildBlock` with known attestation set. Verify greedy selection maximizes coverage. Verify fixed-point loop converges within 2 iterations. Compare output block against Python `build_block` reference. | `tests/StateTransitionSuite.lean` | ~25 | X6-E4 |

## 5. Key Technical Detail: Attestation Processing Flow

```
processAttestations(state, attestations)
    │
    ├── 1. Reconstruct JustificationTracker (X6-C2)
    │       roots = state.justificationsRoots
    │       votes[i] = state.justificationsValidators[i*N : (i+1)*N]
    │
    ├── 2. Filter attestations (X6-C4 through X6-C7)
    │       ├── F1: source justified?      ──→ reject if no
    │       ├── F2: target not justified?   ──→ reject if already justified
    │       ├── F3: source root non-zero?   ──→ reject if zero
    │       ├── F4: target root non-zero?   ──→ reject if zero
    │       ├── F5: roots on chain?         ──→ reject if missing from history
    │       ├── F6: forward time?           ──→ reject if target ≤ source
    │       └── F7: justifiable distance?   ──→ reject if not 3SF-mini valid
    │
    ├── 3. Record votes (X6-C8)
    │       For each valid attestation:
    │         tracker.votes[target.root][validatorId] := true
    │
    ├── 4. Detect supermajority (X6-C9)
    │       For each tracked root:
    │         if 3 * popcount(votes) ≥ 2 * numValidators:
    │           add to newlyJustified list
    │           remove from tracker
    │
    ├── 5. Update justifiedSlots (X6-C16, step 5)
    │       For each newly justified checkpoint:
    │         justifiedSlots.withJustified(finalized, target, true)
    │
    ├── 6. Advance finalization (X6-C11, X6-C12)
    │       For each newly justified, check continuous chain:
    │         if ALL intermediate justifiable slots are justified:
    │           finalize the source checkpoint
    │
    ├── 7. Rebase after finalization (X6-C14)
    │       If finalization advanced:
    │         shift justifiedSlots window
    │         prune stale roots from tracker
    │         prune stale validator bits
    │
    └── 8. Serialize tracker back to SSZ (X6-C3)
            Sort roots, flatten validator bits
```

## 6. Intra-phase Dependency Graph

```
X6-A1 → X6-A2 → X6-A3
              └→ X6-A4

X6-B1 → X6-B2
     → X6-B3 → X6-B5 → X6-B6
     → X6-B4 ──┘

X6-C1 → X6-C2 → X6-C3
     → X6-C8 → X6-C9 → X6-C10

X6-C4 → X6-C5 → X6-C6
              └→ X6-C7

X6-C11 → X6-C12 → X6-C13
X6-C14 → X6-C15

X6-C2, X6-C5, X6-C9, X6-C12, X6-C14, X6-C3 → X6-C16

X6-B1, X6-C16 → X6-D1 → X6-D2 → X6-D3
X6-E1 → X6-E2 → X6-E3 → X6-E4 → X6-E5

All → X6-F1, X6-F2, X6-F3, X6-F4
```

## 7. Exit Criteria

- [ ] Full pipeline: processSlots → processBlockHeader → processAttestations → stateTransition
- [ ] All 7 filter predicates individually defined and proved
- [ ] JustificationTracker reconstruct/serialize roundtrip proved
- [ ] Vote recording monotonicity proved
- [ ] Supermajority detection soundness proved
- [ ] Continuous chain detection defined and adjacent-slot base case proved
- [ ] Finalization monotonicity proved
- [ ] Post-finalization rebasing preserves future justified data (proved)
- [ ] Block building convergence proved
- [ ] processSlots: 12 properties proved (target, monotone, 8 preservation, 2 edge cases)
- [ ] processBlockHeader: 9 properties proved
- [ ] stateTransition: 5 composition properties proved
- [ ] State transition test suite passes with fixture match
- [ ] Negative state tests cover all error paths
- [ ] Zero sorry in state transition modules
