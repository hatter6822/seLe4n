# Phase X7: Consensus Safety Proofs — The Keystone

**Version**: v0.7.0
**Status**: PLANNED
**Sub-tasks**: 16 atomic units
**Dependencies**: X6 (State Transition), X5 (Containers)
**Estimated Lean LoC**: ~1,500 (proof-heavy)
**Files created**: 8 new files
**CRITICAL PATH**: This is the most important proof phase in the entire project

## 1. Objective

Prove the 3SF-mini consensus safety theorem: **no two conflicting blocks can
both be finalized under honest supermajority**. This is the mathematical
foundation that makes the Ethereum consensus layer trustworthy. These proofs
have no Python reference — they are novel formal verification contributions.

This phase also proves finalization monotonicity (finalization never reverts),
the justified ≥ finalized invariant, and conditional liveness (finalization
eventually advances under honest supermajority). Together, these constitute the
**consensus invariant bundle** that every state transition preserves.

## 2. Source Layout

```
LeanEth/Consensus/
├── Invariant/
│   ├── Defs.lean              Core invariant predicates
│   ├── Composition.lean       Composed invariant bundle + genesis proof
│   ├── Safety.lean            Top-level safety theorem
│   └── Liveness.lean          Conditional liveness theorem
└── StateTransition/Proofs/
    ├── SlotMonotonicity.lean      Slot always increases
    ├── HistoryAppendOnly.lean     History only grows
    ├── FinalizationSafety.lean    Finalization never reverts
    ├── JustifiedGeFinalized.lean  justified.slot ≥ finalized.slot
    ├── SupermajoritySafety.lean   Pigeonhole: conflicting 2/3 votes overlap
    ├── ThreeSFMini.lean           3SF-mini safety (KEYSTONE THEOREM)
    └── Preservation.lean          Per-operation invariant preservation
```

## 3. Sub-task Breakdown

### Group A: Invariant Definitions (X7-A1 through X7-A3)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X7-A1 | **Define core consensus invariant predicates.** `def slotMonotone (s : State) : Prop := s.slot ≥ s.latestBlockHeader.slot` (current slot ≥ header slot). `def historyBounded (s : State) : Prop := s.historicalBlockHashes.length ≤ HISTORICAL_ROOTS_LIMIT`. `def validatorsNonempty (s : State) : Prop := s.validators.length > 0`. `def configStable (s : State) (genesis : Config) : Prop := s.config = genesis`. These are structural invariants that constrain state well-formedness. | `Invariant/Defs.lean` | ~25 | X5 |
| X7-A2 | **Define consensus-specific invariant predicates.** `def justifiedGeFinalized (s : State) : Prop := s.latestJustified.slot ≥ s.latestFinalized.slot`. `def finalizationImpliesJustification (s : State) : Prop := s.justifiedSlots.isSlotJustified s.latestFinalized.slot s.latestFinalized.slot = true` (finalized slots are justified). `def supermajorityThreshold (votes totalValidators : Nat) : Prop := 3 * votes ≥ 2 * totalValidators`. | `Invariant/Defs.lean` | ~20 | X5 |
| X7-A3 | **Define trace-level predicates for safety theorem.** `def validTrace (genesis : State) (blocks : List Block) : Prop` — every block in the trace applies successfully via `stateTransition`. `def applyTrace (genesis : State) (blocks : List Block) : State` — fold `stateTransition` over block list. `def conflictingFinalization (s₁ s₂ : State) : Prop := s₁.latestFinalized.root ≠ s₂.latestFinalized.root ∧ s₁.latestFinalized.slot > 0 ∧ s₂.latestFinalized.slot > 0`. `def honestSupermajority (validators : Validators) : Prop := ∃ honest, 3 * honest ≥ 2 * validators.length ∧ (∀ v ∈ honestSet, v attests to at most one target per slot)`. | `Invariant/Defs.lean` | ~40 | X7-A1, X6 |

### Group B: Per-Operation Preservation Proofs (X7-B1 through X7-B5)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X7-B1 | **Prove slot monotonicity preservation.** `processSlots_preserves_slotMonotone : slotMonotone s → processSlots s t = .ok s' → slotMonotone s'`. `processBlockHeader_preserves_slotMonotone : slotMonotone s → processBlockHeader s b = .ok s' → slotMonotone s'`. `processAttestations_preserves_slotMonotone : slotMonotone s → slotMonotone (processAttestations s atts)`. Chain: `stateTransition_preserves_slotMonotone`. Proof strategy: processSlots sets slot = target; header sets slot = block.slot = state.slot; attestations don't change slot. | `StateTransition/Proofs/SlotMonotonicity.lean` | ~40 | X7-A1, X6 |
| X7-B2 | **Prove history append-only.** `processBlockHeader_history_extends : processBlockHeader s b = .ok s' → ∀ i < s.historicalBlockHashes.length, s'.historicalBlockHashes.get? i = s.historicalBlockHashes.get? i`. Existing entries are never overwritten. `processSlots_history_unchanged : processSlots s t = .ok s' → s'.historicalBlockHashes = s.historicalBlockHashes` (slot processing doesn't touch history). `processAttestations_history_unchanged` (attestation processing doesn't touch history). | `StateTransition/Proofs/HistoryAppendOnly.lean` | ~40 | X7-A1, X6 |
| X7-B3 | **Prove finalization monotonicity.** `stateTransition_finalization_monotone : stateTransition s b sigs = .ok s' → s'.latestFinalized.slot ≥ s.latestFinalized.slot`. **Proof strategy**: (a) processSlots doesn't touch latestFinalized (proved in X6-A2). (b) processBlockHeader doesn't decrease latestFinalized (genesis case only sets it if it was zero). (c) processAttestations only advances finalization when continuous justification chain is found (advanceFinalization only sets higher slot). | `StateTransition/Proofs/FinalizationSafety.lean` | ~50 | X7-A2, X6-C6 |
| X7-B4 | **Prove justified ≥ finalized preservation.** `stateTransition_preserves_justifiedGeFinalized : justifiedGeFinalized s → stateTransition s b sigs = .ok s' → justifiedGeFinalized s'`. **Proof strategy**: when finalization advances to checkpoint `cp`, that checkpoint was previously justified (supermajority was achieved), so latestJustified is already ≥ cp.slot. When justification advances without finalization, latestJustified only increases. | `StateTransition/Proofs/JustifiedGeFinalized.lean` | ~40 | X7-A2, X6-C6 |
| X7-B5 | **Prove per-operation preservation of full bundle.** Compose X7-B1 through X7-B4 plus structural invariants: `stateTransition_preserves_bundle : consensusInvariantBundle s → stateTransition s b sigs = .ok s' → consensusInvariantBundle s'`. This is the inductive step for the main safety theorem. | `StateTransition/Proofs/Preservation.lean` | ~30 | X7-B1, X7-B2, X7-B3, X7-B4 |

### Group C: Core Safety Lemmas (X7-C1 through X7-C3)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X7-C1 | **Prove supermajority safety lemma (pigeonhole).** `supermajority_overlap : supermajorityThreshold v₁ n → supermajorityThreshold v₂ n → v₁ + v₂ > n`. **Proof**: `3*v₁ ≥ 2*n` and `3*v₂ ≥ 2*n`, so `3*(v₁ + v₂) ≥ 4*n`, thus `v₁ + v₂ ≥ 4*n/3 > n` (since n > 0). Therefore the voting sets must overlap: `∃ validator, votedFor₁ validator ∧ votedFor₂ validator`. This is the fundamental Byzantine fault tolerance argument. | `StateTransition/Proofs/SupermajoritySafety.lean` | ~25 | X7-A2 |
| X7-C2 | **Prove honest validators don't equivocate.** `honest_no_equivocation : honestSupermajority validators → ∀ v ∈ honestSet, ∀ slot, v attests to at most one target at slot`. Combined with X7-C1: if two conflicting targets both achieve supermajority, at least one voter appears in both → must be honest (since honest is supermajority) → contradiction with no-equivocation. This is the bridge from the counting argument to the safety conclusion. | `StateTransition/Proofs/SupermajoritySafety.lean` | ~30 | X7-C1 |
| X7-C3 | **Prove 3SF-mini justifiable chain uniqueness.** `justifiable_chain_unique : ∀ f cp₁ cp₂, isJustifiableAfter cp₁.slot f → isJustifiableAfter cp₂.slot f → cp₁.slot = cp₂.slot → supermajorityJustified cp₁ → supermajorityJustified cp₂ → honestSupermajority → cp₁.root = cp₂.root`. At the same justifiable slot relative to the same finalized base, honest supermajority can only justify one block. **Proof**: by X7-C1 + X7-C2, two conflicting justifications at the same slot require equivocation, contradicting honesty. | `StateTransition/Proofs/ThreeSFMini.lean` | ~50 | X7-C1, X7-C2 |

### Group D: Keystone Theorems (X7-D1 through X7-D3)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X7-D1 | **Prove 3SF-mini finalization safety (THE KEYSTONE).** `threeSFMiniSafety : ∀ s₁ s₂ genesis, validTrace genesis trace₁ → validTrace genesis trace₂ → s₁ = applyTrace genesis trace₁ → s₂ = applyTrace genesis trace₂ → honestSupermajority s₁.validators → conflictingFinalization s₁ s₂ → False`. **Proof sketch**: (1) Both traces start from the same genesis, so they share the same validator set. (2) Finalization requires a continuous chain of justified checkpoints from a common ancestor. (3) At each justifiable slot in both chains, the justified checkpoint must be unique (by X7-C3). (4) Therefore the chains of justification are identical → the finalized checkpoints are identical → contradiction with `conflictingFinalization`. This proof requires induction on the justification chain length and appeals to X7-C3 at each step. | `StateTransition/Proofs/ThreeSFMini.lean` | ~80 | X7-C3, X7-B5 |
| X7-D2 | **Prove consensus invariant bundle composition.** `def consensusInvariantBundle (s : State) (genesis : Config) : Prop := slotMonotone s ∧ justifiedGeFinalized s ∧ historyBounded s ∧ validatorsNonempty s ∧ configStable s genesis ∧ finalizationImpliesJustification s`. Prove `genesis_satisfies_bundle : consensusInvariantBundle (generateGenesis t vs) cfg` (when `vs.length > 0`). Prove `bundle_preserved_by_trace : consensusInvariantBundle (applyTrace genesis blocks) cfg` (by induction using X7-B5). | `Invariant/Composition.lean` | ~40 | X7-B5, X5-E5 |
| X7-D3 | **Prove top-level safety theorem.** `consensusSafety : ∀ genesis trace₁ trace₂, genesis = generateGenesis t vs → vs.length > 0 → honestSupermajority vs → validTrace genesis trace₁ → validTrace genesis trace₂ → ¬conflictingFinalization (applyTrace genesis trace₁) (applyTrace genesis trace₂)`. Combines X7-D1 (3SF-mini safety) with X7-D2 (invariant bundle). This is the crown jewel of the formalization. | `Invariant/Safety.lean` | ~30 | X7-D1, X7-D2 |

### Group E: Liveness (X7-E1 through X7-E2)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X7-E1 | **Prove conditional liveness.** `consensusLiveness : ∀ s genesis, consensusInvariantBundle s genesis → honestSupermajority s.validators → ∃ blocks : List Block, validTrace s blocks ∧ let s' := applyTrace s blocks; s'.latestFinalized.slot > s.latestFinalized.slot`. Under honest supermajority, finalization eventually advances. **Proof**: honest validators can produce a block at the next slot, attest to it, achieve supermajority justification, and (given continuous justification chain) advance finalization. Constructive: exhibit the witness blocks and attestations. | `Invariant/Liveness.lean` | ~60 | X7-D2, X6-D3 |
| X7-E2 | **Prove finalization gap bound.** `finalization_gap_bounded : ∀ s s', stateTransition s b sigs = .ok s' → s'.latestFinalized.slot ≤ s'.slot` (finalized slot is always in the past). Also: `finalization_progress_bound : honestSupermajority → finalization advances within O(sqrt(LIFETIME)) slots` (3SF-mini distance pattern ensures justifiable checkpoints appear at regular intervals). | `Invariant/Liveness.lean` | ~40 | X7-E1 |

## 4. Proof Strategy Detail: 3SF-mini Safety

The 3SF-mini finalization rule requires a **continuous chain of justified
checkpoints** at justifiable distances from the finalized base. The justifiable
distance function `isJustifiableAfter` admits distances that are:
- ≤ 5 (immediate window)
- Perfect squares (1, 4, 9, 16, 25, ...)
- Pronic numbers (2, 6, 12, 20, 30, ...)

The key insight is that between any two consecutive justifiable distances, there
is exactly one slot that could be justified. This means:

1. At each justifiable slot, honest supermajority can justify exactly one block
2. Two finalized checkpoints require overlapping justification chains
3. If the chains diverge at any justifiable slot, supermajority overlap
   forces equivocation → contradiction with honesty

The proof proceeds by strong induction on the distance from the common
finalized ancestor to the conflicting finalized checkpoints:

```
Base case: distance = 0 → same checkpoint → not conflicting

Inductive case: assume safety holds for all shorter distances.
  Both chains pass through a justifiable slot at distance d₁ from the
  common finalized point. By X7-C3, the justified checkpoint at d₁ is
  unique. Therefore both chains agree at d₁, which is a new common
  finalized ancestor, reducing the distance → apply induction hypothesis.
```

## 5. Exit Criteria

- [ ] **3SF-mini safety theorem proved** (X7-D1 — the keystone)
- [ ] **Top-level consensus safety proved** (X7-D3)
- [ ] Consensus invariant bundle: 6 predicates, all preserved
- [ ] Genesis satisfies bundle
- [ ] Finalization monotonicity proved
- [ ] Justified ≥ finalized proved
- [ ] Supermajority pigeonhole proved
- [ ] Honest no-equivocation formalized
- [ ] Conditional liveness proved
- [ ] Zero sorry in all proof files
- [ ] `lake build LeanEth.Consensus.Invariant.Safety` succeeds
