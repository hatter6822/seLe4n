# Phase X7: Consensus Safety Proofs — The Keystone

**Version**: v0.7.0
**Status**: PLANNED
**Sub-tasks**: 30 atomic units
**Dependencies**: X6 (State Transition), X5 (Containers)
**Estimated Lean LoC**: ~2,000 (proof-heavy)
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
    ├── HistoryAppendOnly.lean     History only grows, never overwrites
    ├── FinalizationSafety.lean    Finalization never reverts
    ├── JustifiedGeFinalized.lean  justified.slot ≥ finalized.slot
    ├── SupermajoritySafety.lean   Pigeonhole: conflicting 2/3 votes overlap
    ├── ThreeSFMini.lean           3SF-mini safety (KEYSTONE THEOREM)
    └── Preservation.lean          Per-operation invariant preservation
```

## 3. Sub-task Breakdown

### Group A: Invariant Definitions (X7-A1 through X7-A5)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X7-A1 | **Define structural invariant predicates.** `def slotMonotone (s : State) : Prop := s.slot ≥ s.latestBlockHeader.slot` (current slot ≥ header slot — slot never goes backward relative to last block). `def historyBounded (s : State) : Prop := s.historicalBlockHashes.length ≤ HISTORICAL_ROOTS_LIMIT` (history stays within SSZ bounds). `def validatorsNonempty (s : State) : Prop := s.validators.length > 0` (at least one validator exists). `def configStable (s : State) (genesis : Config) : Prop := s.config = genesis` (config never mutates after genesis). These structural invariants constrain basic state well-formedness. | `Invariant/Defs.lean` | ~25 | X5 |
| X7-A2 | **Define consensus-specific invariant predicates.** `def justifiedGeFinalized (s : State) : Prop := s.latestJustified.slot ≥ s.latestFinalized.slot` (justified checkpoint is always at least as recent as finalized). `def finalizationImpliesJustification (s : State) : Prop := s.justifiedSlots.isSlotJustified s.latestFinalized.slot s.latestFinalized.slot = true` (finalized slots are marked justified). `def supermajorityThreshold (votes totalValidators : Nat) : Prop := 3 * votes ≥ 2 * totalValidators` (the ≥2/3 Byzantine fault tolerance bound). | `Invariant/Defs.lean` | ~20 | X5 |
| X7-A3 | **Define trace-level predicates.** `def validTrace (genesis : State) (blocks : List Block) : Prop` — every prefix of the block list applies successfully via `stateTransition`. Recursive: `validTrace g [] := True`; `validTrace g (b :: bs) := stateTransition g b true = .ok g' ∧ validTrace g' bs`. `def applyTrace (genesis : State) (blocks : List Block) : State` — fold `stateTransition` over the block list (partial: assumes `validTrace`). | `Invariant/Defs.lean` | ~20 | X6 |
| X7-A4 | **Define conflict and honesty predicates.** `def conflictingFinalization (s₁ s₂ : State) : Prop := s₁.latestFinalized.root ≠ s₂.latestFinalized.root ∧ s₁.latestFinalized.slot > 0 ∧ s₂.latestFinalized.slot > 0` (two states finalized different blocks, excluding genesis). `def honestSupermajority (validators : Validators) : Prop := ∃ honestSet : Finset ValidatorIndex, 3 * honestSet.card ≥ 2 * validators.length ∧ (∀ v ∈ honestSet, ∀ slot, attestsToAtMostOneTarget v slot)`. The honesty model: honest validators never equivocate (never attest to two different targets at the same slot). | `Invariant/Defs.lean` | ~25 | X7-A1 |
| X7-A5 | **Define `consensusInvariantBundle`.** `def consensusInvariantBundle (s : State) (genesis : Config) : Prop := slotMonotone s ∧ justifiedGeFinalized s ∧ historyBounded s ∧ validatorsNonempty s ∧ configStable s genesis ∧ finalizationImpliesJustification s`. This is the composed invariant that every state transition must preserve. Six conjuncts, each independently provable. | `Invariant/Defs.lean` | ~15 | X7-A1, X7-A2 |

### Group B: Per-Operation Preservation Proofs (X7-B1 through X7-B7)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X7-B1 | **Prove slot monotonicity preservation.** `processSlots_preserves_slotMonotone : slotMonotone s → processSlots s t = .ok s' → slotMonotone s'`. Proof: `processSlots` sets `s'.slot = t` and doesn't change `latestBlockHeader`, so `s'.slot = t ≥ s.slot ≥ s.latestBlockHeader.slot = s'.latestBlockHeader.slot`. Similarly prove for `processBlockHeader` (header slot = block.slot = state.slot) and `processAttestations` (doesn't touch slot or header). Chain: `stateTransition_preserves_slotMonotone`. | `Proofs/SlotMonotonicity.lean` | ~45 | X7-A1, X6 |
| X7-B2 | **Prove history append-only.** `processBlockHeader_history_extends : processBlockHeader s b = .ok s' → ∀ i < s.historicalBlockHashes.length, s'.historicalBlockHashes.get? i = s.historicalBlockHashes.get? i`. Existing entries are never overwritten — only new entries are appended. Prove separately: `processSlots_history_unchanged` and `processAttestations_history_unchanged` (neither touches history). Also prove `historyBounded` preservation: `s.historicalBlockHashes.length + 1 + gap ≤ HISTORICAL_ROOTS_LIMIT` (requires slot bound assumption). | `Proofs/HistoryAppendOnly.lean` | ~45 | X7-A1, X6 |
| X7-B3 | **Prove finalization monotonicity.** `stateTransition_finalization_monotone : stateTransition s b _ = .ok s' → s'.latestFinalized.slot ≥ s.latestFinalized.slot`. Proof decomposition: (a) `processSlots` doesn't touch `latestFinalized` (X6-A3). (b) `processBlockHeader` only sets `latestFinalized` in genesis case, and genesis sets it from zero → can only increase. (c) `processAttestations.advanceFinalization` only sets `latestFinalized` when continuous chain found, and the new finalized slot is strictly greater (X6-C13). Compose via transitivity. | `Proofs/FinalizationSafety.lean` | ~55 | X7-A2, X6-C13 |
| X7-B4 | **Prove justified ≥ finalized preservation.** `stateTransition_preserves_justifiedGeFinalized : justifiedGeFinalized s → stateTransition s b _ = .ok s' → justifiedGeFinalized s'`. Proof strategy: when finalization advances to checkpoint `cp`, that checkpoint's source was previously justified (supermajority was achieved before finalization can trigger). So `latestJustified.slot ≥ cp.slot` at the time of finalization. When justification advances without finalization, `latestJustified` only increases while `latestFinalized` stays the same. | `Proofs/JustifiedGeFinalized.lean` | ~45 | X7-A2, X6-C13 |
| X7-B5 | **Prove `finalizationImpliesJustification` preservation.** When finalization advances to a new checkpoint, that checkpoint was justified (it achieved supermajority). After rebasing, the new finalized slot's justification status must be `true` in the shifted bitfield. Prove: `rebaseAfterFinalization` correctly marks the new finalized slot as justified. Prove: `processAttestations` maintains the invariant through the justification→finalization→rebase pipeline. | `Proofs/FinalizationSafety.lean` | ~35 | X7-A2, X6-C14 |
| X7-B6 | **Prove configStable and validatorsNonempty preservation.** `stateTransition_preserves_configStable : configStable s g → stateTransition s b _ = .ok s' → configStable s' g`. Proof: none of processSlots, processBlockHeader, or processAttestations modify `config`. Similarly for `validatorsNonempty`: none modify `validators`. These are straightforward but must be explicitly proved for the bundle. | `Proofs/Preservation.lean` | ~20 | X7-A1, X6 |
| X7-B7 | **Prove per-operation preservation of full bundle.** Compose X7-B1 through X7-B6: `stateTransition_preserves_bundle : consensusInvariantBundle s g → stateTransition s b _ = .ok s' → consensusInvariantBundle s' g`. This is the inductive step for the main safety theorem. Proof: destruct the bundle into 6 conjuncts, apply the corresponding preservation theorem to each, recombine. | `Proofs/Preservation.lean` | ~25 | X7-B1 through X7-B6 |

### Group C: Core Safety Lemmas (X7-C1 through X7-C5)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X7-C1 | **Prove supermajority overlap (pigeonhole).** `supermajority_overlap : supermajorityThreshold v₁ n → supermajorityThreshold v₂ n → n > 0 → v₁ + v₂ > n`. Proof: `3*v₁ ≥ 2*n` and `3*v₂ ≥ 2*n`, so `3*(v₁+v₂) ≥ 4*n`, thus `v₁+v₂ ≥ 4*n/3 > n` (since `n > 0`). This is pure arithmetic — `omega` or manual Nat inequalities. Corollary: `supermajority_sets_intersect : |S₁| ≥ 2n/3 → |S₂| ≥ 2n/3 → S₁ ∩ S₂ ≠ ∅`. | `Proofs/SupermajoritySafety.lean` | ~30 | X7-A2 |
| X7-C2 | **Prove honest validators don't equivocate.** `honest_no_equivocation : honestSupermajority validators → ∀ v ∈ honestSet, ∀ slot target₁ target₂, attestsTo v slot target₁ → attestsTo v slot target₂ → target₁ = target₂`. This follows directly from the honesty predicate definition. The key insight: if two conflicting targets both achieve supermajority, the overlapping voter (from X7-C1) must be in the honest set (since honest is itself a supermajority), and honest validators attest to at most one target → contradiction. | `Proofs/SupermajoritySafety.lean` | ~30 | X7-C1, X7-A4 |
| X7-C3 | **Prove conflicting supermajority implies equivocation.** `conflicting_supermajority_implies_equivocation : target₁ ≠ target₂ → supermajorityJustified target₁ validators → supermajorityJustified target₂ validators → ∃ v ∈ validators, attestsTo v slot target₁ ∧ attestsTo v slot target₂`. Bridge lemma connecting X7-C1 (set overlap) with the voting model. Proof: by X7-C1, the two voting sets overlap; any validator in the overlap attested to both targets. | `Proofs/SupermajoritySafety.lean` | ~25 | X7-C1, X7-C2 |
| X7-C4 | **Prove justifiable chain uniqueness at each slot.** `justifiable_chain_unique : ∀ f cp₁ cp₂, isJustifiableAfter cp₁.slot f → isJustifiableAfter cp₂.slot f → cp₁.slot = cp₂.slot → supermajorityJustified cp₁ validators → supermajorityJustified cp₂ validators → honestSupermajority validators → cp₁.root = cp₂.root`. At the same justifiable slot relative to the same finalized base, honest supermajority can only justify one block. Proof: by X7-C3, conflicting justification at the same slot requires equivocation; by X7-C2, honest validators don't equivocate; since honest is a supermajority, the overlapping voter is honest → contradiction. | `Proofs/ThreeSFMini.lean` | ~50 | X7-C2, X7-C3 |
| X7-C5 | **Prove justification chain agreement lemma.** `justification_chains_agree : ∀ chain₁ chain₂, bothFromSameFinalized chain₁ chain₂ f → allJustifiable chain₁ f → allJustifiable chain₂ f → honestSupermajority → ∀ slot ∈ justifiableSlots f, chain₁.at slot = chain₂.at slot`. Two justification chains from the same finalized base agree at every justifiable slot. Proof: by X7-C4 applied pointwise at each justifiable slot. This is the key lemma that makes the inductive step of the keystone theorem work. | `Proofs/ThreeSFMini.lean` | ~40 | X7-C4 |

### Group D: Keystone Theorems (X7-D1 through X7-D5)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X7-D1 | **Prove 3SF-mini finalization safety — base case.** `threeSFMiniSafety_base : conflictingFinalization s₁ s₂ → s₁.latestFinalized.slot = s₂.latestFinalized.slot → s₁.latestFinalized.root = s₂.latestFinalized.root → False`. If both states finalize at the same slot but with different roots → contradiction (finalization at a given slot is unique under honest supermajority, by X7-C4). If roots are equal → not conflicting. This handles the case where the conflicting finalized checkpoints are at the same height. | `Proofs/ThreeSFMini.lean` | ~25 | X7-C4 |
| X7-D2 | **Prove 3SF-mini finalization safety — inductive step.** WLOG assume `s₁.latestFinalized.slot < s₂.latestFinalized.slot`. The finalization of `s₂` required a continuous justification chain from some earlier finalized point to `s₂.latestFinalized`. That chain passes through justifiable slots. By X7-C5, both traces agree at every justifiable slot in the chain. Therefore the chain in trace₂ is also valid in trace₁'s view — meaning trace₁ would have finalized the same checkpoint or a descendant. This contradicts the assumption that the finalized checkpoints conflict. Proof uses well-founded induction on `s₂.latestFinalized.slot - commonAncestor.slot`. | `Proofs/ThreeSFMini.lean` | ~80 | X7-C5, X7-D1 |
| X7-D3 | **Prove 3SF-mini finalization safety (THE KEYSTONE).** `threeSFMiniSafety : ∀ s₁ s₂ genesis, validTrace genesis trace₁ → validTrace genesis trace₂ → s₁ = applyTrace genesis trace₁ → s₂ = applyTrace genesis trace₂ → honestSupermajority s₁.validators → conflictingFinalization s₁ s₂ → False`. Combines base case (X7-D1) and inductive step (X7-D2). Both traces share the same genesis (common ancestor with finalized slot = 0). Apply the inductive argument to show finalized checkpoints must agree at every point → contradiction with `conflictingFinalization`. | `Proofs/ThreeSFMini.lean` | ~30 | X7-D1, X7-D2 |
| X7-D4 | **Prove consensus invariant bundle genesis + induction.** `genesis_satisfies_bundle : vs.length > 0 → consensusInvariantBundle (generateGenesis t vs) (generateGenesis t vs).config`. Proof: check each of 6 conjuncts against genesis state. Then: `bundle_preserved_by_trace : validTrace genesis blocks → consensusInvariantBundle genesis cfg → consensusInvariantBundle (applyTrace genesis blocks) cfg`. Proof: induction on `blocks` using X7-B7 at each step. | `Invariant/Composition.lean` | ~45 | X7-B7, X5-E5 |
| X7-D5 | **Prove top-level safety theorem.** `consensusSafety : ∀ genesis trace₁ trace₂, genesis = generateGenesis t vs → vs.length > 0 → honestSupermajority vs → validTrace genesis trace₁ → validTrace genesis trace₂ → ¬conflictingFinalization (applyTrace genesis trace₁) (applyTrace genesis trace₂)`. Combines X7-D3 (3SF-mini safety) with X7-D4 (invariant bundle). This is the crown jewel of the formalization — the machine-checked proof that the Lean Ethereum consensus is safe. | `Invariant/Safety.lean` | ~30 | X7-D3, X7-D4 |

### Group E: Liveness (X7-E1 through X7-E4)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X7-E1 | **Define liveness witness construction.** `constructLivenessWitness : State → GeneralizedXmssScheme → List Block`. Given a state with honest supermajority, construct the specific sequence of blocks and attestations that advances finalization: (a) produce a block at the next slot, (b) all honest validators attest to it, (c) the attestation achieves supermajority justification, (d) if a continuous chain exists, finalization advances. This is a constructive witness — we must actually build the `Block` values. | `Invariant/Liveness.lean` | ~50 | X7-D4, X6-E4 |
| X7-E2 | **Prove witness validity.** `liveness_witness_valid : ∀ s, consensusInvariantBundle s → honestSupermajority s.validators → validTrace s (constructLivenessWitness s scheme)`. The constructed blocks are valid: they pass all validation checks in `stateTransition`. Proof: the block has correct slot (next slot), correct proposer (round-robin), correct parent (hash of current header), valid attestations (from honest validators attesting to justified source), and correct state root (computed from post-state). | `Invariant/Liveness.lean` | ~40 | X7-E1 |
| X7-E3 | **Prove conditional liveness.** `consensusLiveness : ∀ s genesis, consensusInvariantBundle s genesis → honestSupermajority s.validators → ∃ blocks, validTrace s blocks ∧ (applyTrace s blocks).latestFinalized.slot > s.latestFinalized.slot`. Under honest supermajority, finalization eventually advances. Proof: apply X7-E1 to construct the witness, apply X7-E2 to show it's valid, then show `advanceFinalization` triggers because honest supermajority produces a continuous justification chain. | `Invariant/Liveness.lean` | ~35 | X7-E1, X7-E2 |
| X7-E4 | **Prove finalization gap bound.** `finalization_gap_bounded : stateTransition s b _ = .ok s' → s'.latestFinalized.slot ≤ s'.slot` (finalized slot is always in the past — you can't finalize a future slot). Also: `finalization_progress_bound : honestSupermajority → ∃ K, ∀ s, ∃ blocks, blocks.length ≤ K ∧ validTrace s blocks ∧ (applyTrace s blocks).latestFinalized.slot > s.latestFinalized.slot` — finalization advances within a bounded number of blocks. The 3SF-mini distance pattern (≤5, perfect squares, pronic numbers) ensures justifiable slots appear at sub-linear intervals: the gap between consecutive justifiable distances is O(√d), so finalization can advance in O(√d) steps. | `Invariant/Liveness.lean` | ~45 | X7-E3 |

## 4. Proof Strategy Detail: 3SF-mini Safety

The 3SF-mini finalization rule requires a **continuous chain of justified
checkpoints** at justifiable distances from the finalized base. The justifiable
distance function `isJustifiableAfter` admits distances that are:
- ≤ 5 (immediate window)
- Perfect squares (1, 4, 9, 16, 25, ...)
- Pronic numbers (2, 6, 12, 20, 30, ...)

### Why This Works

Between any two consecutive justifiable distances `d₁ < d₂`, there is exactly
one justifiable slot at distance `d₂` that the protocol can use as a stepping
stone toward finalization. Honest supermajority ensures that only one block can
be justified at each stepping stone (by pigeonhole + no-equivocation).

### Proof Architecture (4 layers)

```
Layer 1: Arithmetic Foundation
  ├── supermajority_overlap (pigeonhole on vote counts)
  └── honest_no_equivocation (from honesty definition)

Layer 2: Voting Safety
  ├── conflicting_supermajority_implies_equivocation
  └── justifiable_chain_unique (per-slot uniqueness)

Layer 3: Chain Agreement
  └── justification_chains_agree (pointwise agreement at all justifiable slots)

Layer 4: Finalization Safety
  ├── threeSFMiniSafety_base (same-slot case)
  ├── threeSFMiniSafety_inductive (different-slot case, well-founded induction)
  └── threeSFMiniSafety (combined keystone)
        │
        └── consensusSafety (top-level, with invariant bundle)
```

### Induction Structure

The proof of `threeSFMiniSafety` (X7-D3) proceeds by well-founded induction
on the distance from the latest common finalized ancestor to the conflicting
finalized checkpoints:

```
Base case: distance = 0 → same slot → justifiable_chain_unique → same root → ¬conflicting

Inductive case: distance > 0
  Both finalization chains pass through a justifiable slot d₁ from the common
  ancestor. By justifiable_chain_unique, the justified block at d₁ is the same
  in both chains. This block becomes a new common ancestor, reducing the
  distance by d₁ > 0. Apply the induction hypothesis.

  The well-founded measure is the distance: (s₂.latestFinalized.slot - commonAncestor.slot)
  which strictly decreases at each step since d₁ > 0.
```

## 5. Exit Criteria

- [ ] **3SF-mini safety theorem proved** (X7-D3 — the keystone)
- [ ] **Top-level consensus safety proved** (X7-D5)
- [ ] 5 invariant predicates defined (structural + consensus-specific)
- [ ] Consensus invariant bundle: 6 conjuncts, all preserved per-operation
- [ ] Genesis satisfies bundle (proved)
- [ ] Bundle preserved by trace induction (proved)
- [ ] Finalization monotonicity proved (X7-B3)
- [ ] Justified ≥ finalized proved (X7-B4)
- [ ] Supermajority pigeonhole proved (X7-C1)
- [ ] Honest no-equivocation formalized (X7-C2)
- [ ] Justifiable chain uniqueness proved (X7-C4)
- [ ] Chain agreement lemma proved (X7-C5)
- [ ] Conditional liveness proved with constructive witness (X7-E3)
- [ ] Finalization gap bound proved (X7-E4)
- [ ] Zero sorry in all proof files
- [ ] `lake build LeanEth.Consensus.Invariant.Safety` succeeds
