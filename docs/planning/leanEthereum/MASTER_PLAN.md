# Lean Ethereum — Formally Verified Consensus Client

**Status**: PLANNED
**Target versions**: v0.1.0–v1.0.0
**Hardware target**: Raspberry Pi 5 (ARM64)
**Reference spec**: hatter6822/leanSpec (Python Ethereum consensus specification)
**Lean toolchain**: 4.28.0
**Build system**: Lake
**Sorry budget**: 0 (all proofs machine-checked)
**Axiom budget**: 3 (cryptographic hardness assumptions — see Axiom Inventory)

## Overview

Lean Ethereum is a formally verified Ethereum consensus client written in
Lean 4, following the "formalize in Lean 4, enforce safety with Rust"
development approach pioneered by the seLe4n microkernel. Every consensus
state transition is an executable pure function with machine-checked proofs
of safety, liveness, and correctness. The Rust layer handles networking,
storage, and OS interaction with minimal `unsafe` blocks.

The project formalizes the complete `leanSpec` Python specification — covering
SSZ types, XMSS signatures, Poseidon2 hashing, state transitions, fork choice,
and node services — producing a client that can participate in the Ethereum
consensus network with cryptographic assurance of correctness.

## Goals

1. **Consensus safety proof** — Machine-checked 3SF-mini theorem proving no two
   conflicting blocks can both be finalized under honest supermajority
2. **SSZ correctness** — Serialization/deserialization roundtrip proofs for all
   consensus types, Merkleization collision resistance
3. **Cryptographic soundness** — XMSS sign/verify roundtrip, one-time key
   property, Poseidon2 permutation bijectivity
4. **Executable client** — Running consensus node connecting to Ethereum P2P
   network, processing blocks, producing attestations
5. **Microkernel integration** — Bridge to seLe4n kernel for a fully verified
   Ethereum node on a verified OS

## Phase Summary

| Phase | Name | Version | Sub-tasks | Critical Path |
|-------|------|---------|-----------|---------------|
| [X1](./PHASE_X1_FOUNDATION_TYPES.md) | Foundation Types & Prelude | v0.1.0 | 30 | Yes |
| [X2](./PHASE_X2_SSZ_MERKLEIZATION.md) | SSZ Merkleization & Hash Tree Root | v0.2.0 | 22 | Yes |
| [X3](./PHASE_X3_KOALABEAR_POSEIDON2.md) | KoalaBear Field & Poseidon2 Hash | v0.3.0 | 20 | Parallel |
| [X4](./PHASE_X4_XMSS_SIGNATURES.md) | XMSS Signature Scheme | v0.4.0 | 34 | Parallel |
| [X5](./PHASE_X5_CONSENSUS_CONTAINERS.md) | Consensus Containers | v0.5.0 | 26 | Yes |
| [X6](./PHASE_X6_STATE_TRANSITION.md) | State Transition — Core Operations | v0.6.0 | 38 | Yes |
| [X7](./PHASE_X7_CONSENSUS_SAFETY.md) | Consensus Safety Proofs (KEYSTONE) | v0.7.0 | 30 | Yes |
| [X8](./PHASE_X8_FORK_CHOICE.md) | Fork Choice (LMD GHOST) | v0.8.0 | 20 | No |
| [X9](./PHASE_X9_SNAPPY_NETWORKING.md) | Snappy Compression & Networking Types | v0.9.0 | 24 | Parallel |
| [X10](./PHASE_X10_NODE_SERVICES.md) | Node Services — Chain, Validator, Sync | v0.10.0 | 30 | No |
| [X11](./PHASE_X11_RUST_ABI.md) | Rust ABI Safety Layer | v0.11.0 | 28 | Parallel |
| [X12](./PHASE_X12_TESTING.md) | Testing Infrastructure & Trace Harness | v0.12.0 | 26 | No |
| [X13](./PHASE_X13_SELE4N_BRIDGE.md) | seLe4n Integration Bridge | v0.13.0 | 22 | No |
| [X14](./PHASE_X14_DOCUMENTATION.md) | Documentation, Audit, & Closure | v1.0.0 | 22 | No |
| **Total** | | | **372** | |

## Dependency Graph

```
X1 (Types) ─────────────────────────────────────────────────────────────┐
 │                                                                       │
 ├── X2 (SSZ Merkle) ──────────────────────────────────────────────┐     │
 │    │                                                             │     │
 │    └── X5 (Consensus Containers) ───────────────────────┐       │     │
 │         │                                                │       │     │
 │         ├── X6 (State Transition) ──────────────────┐   │       │     │
 │         │    │                                       │   │       │     │
 │         │    └── X7 (Safety Proofs) ◄── KEYSTONE    │   │       │     │
 │         │         │                                  │   │       │     │
 │         │         └── X8 (Fork Choice) ─────────┐   │   │       │     │
 │         │              │                         │   │   │       │     │
 │         │              └── X10 (Node Services) ──┤   │   │       │     │
 │         │                   │                    │   │   │       │     │
 │         │                   └── X12 (Testing) ───┤   │   │       │     │
 │         │                        │               │   │   │       │     │
 │         │                        └── X14 (Docs) ─┘   │   │       │     │
 │         │                                             │   │       │     │
 │         └── X9 (Snappy + Networking) ─────────────────┘   │       │     │
 │                                                           │       │     │
 ├── X3 (KoalaBear + Poseidon2) ──┐                         │       │     │
 │    │                             │                         │       │     │
 │    └── X4 (XMSS) ──────────────┘                         │       │     │
 │         │                                                 │       │     │
 │         └── X5 (Consensus Containers) ──[signatures]──────┘       │     │
 │                                                                   │     │
 └── X11 (Rust ABI) ────────────────────────────────────────────────┘     │
      │                                                                    │
      └── X12 (Testing / XVAL) ──────┐                                   │
           │                          │                                    │
           └── X13 (seLe4n Bridge) ───┘                                   │
                │                                                          │
                └── X14 (Documentation) ──────────────────────────────────┘
```

**Critical path**: X1 → X2 → X5 → X6 → X7 (3SF-mini safety proof)

**Parallelizable streams:**
- **Crypto stream**: X3 → X4 (can proceed alongside X2)
- **Rust stream**: X11 (can proceed alongside X6–X8)
- **Networking stream**: X9 (can proceed alongside X6–X7)
- **Node stream**: X10 starts after X5 + X8

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                    Lean 4 Proof Surface                         │
│                                                                 │
│  ┌──────────────────┐  ┌──────────────────┐  ┌──────────────┐  │
│  │ LeanEth/Types/   │  │ LeanEth/Crypto/  │  │ LeanEth/SSZ/ │  │
│  │  Uint.lean       │  │  KoalaBear.lean  │  │  Encode.lean  │  │
│  │  Bytes.lean      │  │  Poseidon2.lean  │  │  Decode.lean  │  │
│  │  Container.lean  │  │  XMSS.lean       │  │  Merkle.lean  │  │
│  │  BitFields.lean  │  │  Hash.lean       │  │  Proofs.lean  │  │
│  └────────┬─────────┘  └────────┬─────────┘  └──────┬───────┘  │
│           │                     │                    │          │
│  ┌────────▼─────────────────────▼────────────────────▼───────┐  │
│  │ LeanEth/Consensus/                                        │  │
│  │  Containers/ (Slot, Checkpoint, Validator, Block, State)  │  │
│  │  StateTransition/ (ProcessSlots, ProcessBlock, ...)       │  │
│  │  ForkChoice/ (Store, LMDGHOST, Attestation processing)    │  │
│  │  Invariant/ (Safety, Liveness, Monotonicity)              │  │
│  │  Proofs/ (3SF-mini safety, finalization, supermajority)   │  │
│  └────────┬──────────────────────────────────────────────────┘  │
│           │                                                     │
│  ┌────────▼──────────────────────────────────────────────────┐  │
│  │ LeanEth/Node/                                             │  │
│  │  Chain/ (SlotClock, BlockProduction)                       │  │
│  │  Validator/ (DutyScheduling, AttestationProduction)        │  │
│  │  Sync/ (CheckpointSync, HeadSync, BackfillSync)           │  │
│  │  API/ (REST endpoints, health, metrics)                    │  │
│  └────────┬──────────────────────────────────────────────────┘  │
│           │                                                     │
│  ┌────────▼──────────────────────────────────────────────────┐  │
│  │ LeanEth/Bridge/                                           │  │
│  │  SeLe4nIntegration.lean (IPC bridge to microkernel)       │  │
│  │  PlatformContract.lean (Ethereum node platform binding)    │  │
│  └───────────────────────────────────────────────────────────┘  │
│                                                                 │
├─────────────────────────────────────────────────────────────────┤
│                    Rust Safety Layer                             │
│                                                                 │
│  ┌──────────────┐  ┌───────────────┐  ┌──────────────────────┐  │
│  │ leaneth-types│  │ leaneth-net   │  │ leaneth-storage      │  │
│  │ (SSZ codec,  │  │ (libp2p QUIC, │  │ (SQLite, namespace   │  │
│  │  type defs)  │  │  gossipsub,   │  │  isolation, WAL)     │  │
│  │              │  │  discovery,   │  │                      │  │
│  │              │  │  req-resp)    │  │                      │  │
│  └──────────────┘  └───────────────┘  └──────────────────────┘  │
│                                                                 │
│  Safety boundary: all Rust crates are `no_std` where possible,  │
│  `unsafe` blocks only for OS syscalls and network I/O.          │
│  Cross-validated with Lean trace harness (XVAL pattern).        │
└─────────────────────────────────────────────────────────────────┘
```

## Development Principles

### Inherited from seLe4n

1. **Zero sorry/axiom** in production proof surface (3 declared axioms for
   cryptographic hardness carry `AXIOM-CRYPTO-*` annotations)
2. **Invariant/Operations split** — each subsystem has `Operations.lean`
   (transitions) and `Invariant.lean` (proofs)
3. **Typed identifiers** — `Slot`, `ValidatorIndex`, `Bytes32`, etc. are
   wrapper structures with sentinel conventions, not type aliases
4. **Deterministic semantics** — all transitions return explicit `Except` values
5. **Fixture-backed testing** — golden-output trace comparison at every tier
6. **Platform-agnostic core** — consensus logic is pure Lean; platform bindings
   are separate typeclasses
7. **Rust ABI with minimal unsafe** — networking and storage in Rust with
   cross-validation against Lean reference

### Ethereum-Specific

8. **Spec-faithful naming** — Lean definitions mirror leanSpec Python names
   with a documented naming map
9. **SSZ-first types** — all consensus containers derive SSZ serialization;
   Merkleization is a computable function with correctness proofs
10. **Fork-parameterized** — consensus logic parameterized over a `Fork`
    typeclass for future hard fork support
11. **Spec coverage tracking** — every Python function in leanSpec has a
    corresponding Lean definition with a traceability tag (`LS-*`)

## Axiom Inventory

| ID | Name | Statement | Justification |
|----|------|-----------|---------------|
| AXIOM-CRYPTO-1 | Hash collision resistance | `hashNodes a₁ b₁ = hashNodes a₂ b₂ → a₁ = a₂ ∧ b₁ = b₂` | Standard assumption for SHA-256/Poseidon2. Required for SSZ Merkleization correctness. |
| AXIOM-CRYPTO-2 | XMSS EU-CMA security | `Pr[forge without secret key] ≤ negl(λ)` | Post-quantum security for hash-based signatures. Based on hash function one-wayness. |
| AXIOM-CRYPTO-3 | Poseidon2 algebraic security | `Pr[algebraic relation exploit in sponge mode] ≤ negl(λ)` | Algebraic security for Poseidon2 S-box (x³). Based on Grassi et al. 2023. |

## Risk Matrix

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| 3SF-mini proof complexity | Medium | High | Break into sub-lemmas; consult Ethereum Foundation research |
| Poseidon2 constants too large for Lean kernel | Medium | Medium | Use `native_decide`; pre-compute and embed as literals |
| XMSS tree traversal termination | Medium | Medium | Well-founded recursion on tree depth |
| Lean compilation time for large proofs | High | Low | Split into ≤500-line modules; use `noncomputable` for proof-only defs |
| libp2p Rust API instability | Low | Medium | Pin crate versions; abstract behind trait interface |
| leanSpec evolves during formalization | Medium | Medium | Pin to specific commit; batch updates at phase boundaries |

## Metrics Targets

| Metric | Target |
|--------|--------|
| Total sub-tasks | 372 |
| Lean production LoC | ~15,000–20,000 |
| Lean proof LoC | ~8,000–12,000 |
| Rust LoC | ~4,000–5,500 |
| Test LoC | ~2,500–3,500 |
| Theorems/lemmas | ~350–450 |
| Sorry count | 0 |
| Axiom count | 3 |
| Rust unsafe blocks | ≤ 2 (FFI boundary only) |
| XVAL cross-validation cases | ≥ 25 |
| Test tiers | 4 (hygiene, build, functional, invariant) + nightly |
| Negative-state tests | ≥ 17 |
| Determinism assertions | ≥ 50 |
| Consensus-critical spec coverage | 100% |

## Glossary

| Term | Definition |
|------|-----------|
| 3SF-mini | Three-Slot Finality (mini) — consensus finality rule in the Lean spec |
| LMD GHOST | Latest Message Driven Greedy Heaviest Observed SubTree — fork choice |
| SSZ | Simple Serialize — Ethereum's canonical serialization format |
| XMSS | eXtended Merkle Signature Scheme — post-quantum hash-based signature |
| Poseidon2 | Algebraic hash function over prime fields |
| KoalaBear | Prime field with p = 2³¹ - 2²⁴ + 1 |
| EU-CMA | Existential Unforgeability under Chosen Message Attack |
| Gossipsub | Pub/sub protocol for P2P message dissemination |
| discv5 | Node discovery protocol v5 (UDP-based) |
| ENR | Ethereum Node Record — self-signed node identity |
| Devnet | Development network — current fork in leanSpec |
| Supermajority | ≥ 2/3 of validators agreeing on a checkpoint |
| Justification | A checkpoint achieving supermajority attestation |
| Finalization | An irreversible checkpoint with continuous justification chain |

## Traceability Map (Key Functions)

| Python Function | Lean Definition | Phase | Proof |
|----------------|-----------------|-------|-------|
| `BaseUint.__new__` | `BaseUint.ofNat` | X1-B2 | X1-B5: arithmetic |
| `BaseUint.encode_bytes` | `BaseUint.serialize` | X1-B4 | X1-B6: roundtrip |
| `BaseBitlist.encode_bytes` | `BaseBitlist.serialize` | X1-E3 | X1-E4: roundtrip |
| `BaseBitlist.shift_window` | `BaseBitlist.shiftWindow` | X1-E2 | X1-E5: correctness |
| `Container.serialize` | `containerSerialize` | X1-G1 | X1-G2: roundtrip |
| `merkleize` | `merkleize` | X2-B3 | X2-B5: properties |
| `hash_tree_root` (basic) | `hashTreeRoot` | X2-C1 | X2-D1: collision |
| `hash_tree_root` (list) | `hashTreeRoot` | X2-C2 | X2-D2: injectivity |
| `hash_tree_root` (container) | `containerHashTreeRoot` | X2-C4 | X2-D1: collision |
| `mix_in_length` | `mixInLength` | X2-B4 | X2-D2: injectivity |
| `mix_in_selector` | `mixInSelector` | X2-B4 | X2-D3: injectivity |
| `Fp.__init__` | `Fp.mk` | X3-A1 | X3-A4/A5: field laws |
| `Fp.__mul__` | `Fp.mul` | X3-A3 | X3-A5: mul_comm/assoc |
| `Fp.inverse` | `Fp.inv` | X3-A3 | X3-A6: inv_correct |
| `Poseidon2.permute` | `permute` | X3-B5 | X3-B6: bijectivity |
| `Poseidon2.hash` | `poseidon2Hash` | X3-B7 | X3-B8: test vectors |
| `target_sum_encode` | `targetSumEncode` | X4-B3 | X4-B4: constant sum |
| `GeneralizedXmssScheme.key_gen` | `keyGen` | X4-D3 | X4-H1: soundness |
| `GeneralizedXmssScheme.sign` | `sign` | X4-E3 | X4-H1: roundtrip |
| `GeneralizedXmssScheme.verify` | `verify` | X4-F1 | X4-H1: roundtrip |
| `aggregate_signatures` | `aggregateSignatures` | X4-G1 | X4-G3: correctness |
| `Slot.is_justifiable_after` | `isJustifiableAfter` | X5-A2 | X5-A3: properties |
| `State.generate_genesis` | `generateGenesis` | X5-D5 | X5-D5: invariants |
| `State.process_slots` | `processSlots` | X6-A1 | X6-A4: composition |
| `State.process_block_header` | `processBlockHeader` | X6-B5 | X6-B6: 4 proofs |
| `State.process_attestations` | `processAttestations` | X6-C16 | X7: safety |
| `filter_valid_attestations` | `filterValidAttestations` | X6-C5 | X6-C6: guarantees |
| `has_continuous_chain` | `hasContinuousChain` | X6-C11 | X6-C13: properties |
| `advance_finalization` | `advanceFinalization` | X6-C12 | X6-C13: monotone |
| `State.state_transition` | `stateTransition` | X6-D2 | X6-D3: composition |
| `State.build_block` | `buildBlock` | X6-E4 | X6-E5: convergence |
| `Store.from_anchor` | `Store.fromAnchor` | X8-A2 | X8-D2: consistency |
| `Store.validate_attestation` | `validateAttestation` | X8-C1 | X8-D2: consistency |
| `lmd_ghost` | `lmdGhost` | X8-B3 | X8-D1/D3: validity |
| `compress` | `compress` | X9-A3 | X9-A8: roundtrip |
| `decompress` | `decompress` | X9-A5 | X9-A8: roundtrip |
| `frame_compress` | `frameCompress` | X9-A7 | X9-A8: roundtrip |
| — (novel) | `threeSFMiniSafety` | X7-D3 | **KEYSTONE** |
| — (novel) | `consensusSafety` | X7-D5 | Top-level |
| — (novel) | `consensusLiveness` | X7-E3 | Conditional |
| — (bridge) | `bridge_preserves_kernel_invariants` | X13-D1 | Kernel safety |
| — (bridge) | `bridge_preserves_consensus_invariants` | X13-D2 | Consensus safety |

## Source Layout (Full)

```
LeanEth/
├── Prelude.lean                        Error types, monad, config, re-exports
├── Types/
│   ├── SSZBase.lean                    SSZSerializable typeclass
│   ├── Uint.lean                       BaseUint, Uint8/16/32/64
│   ├── Bytes.lean                      BaseBytes, BaseByteList, Bytes1..Bytes65
│   ├── Boolean.lean                    SSZ Boolean
│   ├── BitFields.lean                  BaseBitvector, BaseBitlist
│   ├── Collections.lean                SSZVector, SSZList
│   ├── Container.lean                  Container serialization framework
│   ├── RLP.lean                        RLP encode/decode
│   └── Proofs/
│       ├── UintProofs.lean             Uint roundtrip + arithmetic
│       ├── ByteProofs.lean             Byte roundtrip
│       ├── BitFieldProofs.lean         Bitfield roundtrip + ops
│       └── CollectionProofs.lean       Collection roundtrip + props
├── SSZ/
│   ├── Pack.lean                       packBytes, packBits
│   ├── Merkle.lean                     merkleize, mixIn*, zeroHashes
│   ├── HashTreeRoot.lean               Per-type hashTreeRoot dispatch
│   └── Proofs.lean                     Collision resistance, properties
├── Crypto/
│   ├── KoalaBear/
│   │   ├── Field.lean                  Fp type, arithmetic
│   │   └── Proofs.lean                 Field law proofs
│   ├── Poseidon2/
│   │   ├── Constants.lean              Round constants, MDS
│   │   ├── Permutation.lean            Round functions, permute
│   │   └── Proofs.lean                 Bijectivity
│   ├── XMSS/
│   │   ├── Types.lean                  Containers, config
│   │   ├── PRF.lean                    Pseudorandom function
│   │   ├── TweakHash.lean              Domain-separated hash
│   │   ├── TargetSum.lean              Winternitz encoding
│   │   ├── SubTree.lean                Merkle tree ops
│   │   ├── Interface.lean              keygen, sign, verify
│   │   ├── Aggregation.lean            Signature aggregation
│   │   └── Proofs.lean                 Soundness proofs
│   ├── Snappy/
│   │   ├── Types.lean                  SnappyOp, SnappyError, constants
│   │   ├── Compress.lean               Greedy matching, op serialization
│   │   ├── Decompress.lean             Tag parsing, backreference resolution
│   │   ├── Framing.lean                CRC32C, frame encode/decode
│   │   └── Proofs.lean                 Roundtrip, length bounds
│   └── Hash.lean                       Hash dispatch
├── Consensus/
│   ├── Containers/
│   │   ├── Slot.lean                   Slot, 3SF-mini predicates
│   │   ├── Checkpoint.lean             Checkpoint
│   │   ├── Validator.lean              Validator, ValidatorIndex
│   │   ├── Config.lean                 Config, constants, errors
│   │   ├── Attestation/
│   │   │   ├── Types.lean              AttestationData, Aggregated*
│   │   │   ├── Aggregation.lean        aggregateByData
│   │   │   └── Proofs.lean             Aggregation correctness
│   │   ├── Block/
│   │   │   ├── Types.lean              Block, BlockHeader, BlockBody
│   │   │   ├── Signatures.lean         SignedBlock, verification
│   │   │   └── Proofs.lean             Header chain integrity
│   │   └── State/
│   │       ├── Types.lean              HistoricalBlockHashes, JustifiedSlots
│   │       ├── State.lean              State container
│   │       ├── Genesis.lean            generateGenesis
│   │       └── Proofs.lean             Field well-formedness
│   ├── StateTransition/
│   │   ├── ProcessSlots.lean           Slot advancement, state root caching
│   │   ├── ProcessBlockHeader.lean     Header validation + history + genesis
│   │   ├── ProcessAttestations/
│   │   │   ├── Tracker.lean            JustificationTracker reconstruction
│   │   │   ├── Filter.lean             7 named predicates + composite filter
│   │   │   ├── Voting.lean             recordVote, supermajority detection
│   │   │   ├── Finalization.lean       Continuous chain, advancement, rebasing
│   │   │   ├── Pruning.lean            Rebase after finalization
│   │   │   └── Compose.lean            8-step processAttestations orchestration
│   │   ├── StateTransition.lean        processBlock + stateTransition
│   │   ├── BuildBlock.lean             Greedy selection, fixed-point loop
│   │   └── Proofs/
│   │       ├── SlotMonotonicity.lean
│   │       ├── HistoryAppendOnly.lean
│   │       ├── FinalizationSafety.lean
│   │       ├── JustifiedGeFinalized.lean
│   │       ├── SupermajoritySafety.lean
│   │       ├── ThreeSFMini.lean        ← KEYSTONE
│   │       └── Preservation.lean
│   ├── ForkChoice/
│   │   ├── Store.lean                  Fork choice store
│   │   ├── LMDGHOST.lean               Head selection
│   │   ├── AttestationProcessing.lean  Validation + integration
│   │   ├── Pruning.lean                Stale removal
│   │   └── Proofs/
│   │       ├── HeadValidity.lean
│   │       ├── Consistency.lean
│   │       └── Convergence.lean
│   └── Invariant/
│       ├── Defs.lean                   Invariant predicates
│       ├── Composition.lean            Bundle + genesis
│       ├── Safety.lean                 Top-level safety
│       └── Liveness.lean               Conditional liveness
├── Node/
│   ├── Chain/
│   │   ├── SlotClock.lean              Slot clock + monotonicity proofs
│   │   ├── Config.lean                 Chain configuration + errors
│   │   ├── Service.lean                ChainState, transitions, queries
│   │   └── Proofs.lean                 Chain service preservation
│   ├── Validator/
│   │   ├── Duties.lean                 Duty types, scheduling logic
│   │   ├── Registry.lean               Key management, signing
│   │   ├── Service.lean                Validator state machine
│   │   └── Proofs.lean                 Duty scheduling correctness
│   ├── Sync/
│   │   ├── StateMachine.lean           Sync phases + transitions
│   │   ├── CheckpointSync.lean         Checkpoint sync logic
│   │   ├── HeadSync.lean               Head sync + backfill
│   │   ├── BlockCache.lean             Pending block management
│   │   └── PeerManager.lean            Peer tracking, scoring
│   ├── Storage/
│   │   ├── Interface.lean              Database typeclass
│   │   └── Schema.lean                 Namespace defs, key encoding
│   ├── API/
│   │   └── Endpoints.lean              REST API type definitions
│   ├── Networking/
│   │   ├── Transport.lean              PeerId, NetworkMessage
│   │   ├── ENR.lean                    ENR structure, RLP encode/decode
│   │   ├── Gossipsub.lean              Topics, GossipsubAction
│   │   ├── ReqResp.lean                Request-response protocol
│   │   ├── Discovery.lean              discv5 abstractions
│   │   └── Config.lean                 Network configuration
│   └── Node.lean                       Top-level orchestrator
├── Bridge/
│   ├── SharedPrelude.lean              Shared identifiers, conversions
│   ├── PlatformContract.lean           EthNodePlatformBinding typeclass
│   ├── ResourceMapping.lean            Capabilities → kernel resources
│   ├── IPCProtocol.lean                Message format, encode/decode
│   ├── EventTranslation.lean           Kernel ↔ consensus event mapping
│   ├── Lifecycle.lean                  Node init, main loop, shutdown
│   ├── RPi5Extension.lean              BCM2712 Ethernet/SD abstractions
│   └── Proofs.lean                     Safety preservation (5 theorems)
├── Testing/
│   ├── TraceHarness.lean               Executable trace harness
│   ├── StateBuilder.lean               Test state construction helpers
│   ├── Fixtures.lean                   Fixture comparison framework
│   ├── Scenarios.lean                  Reusable test scenario definitions
│   └── Determinism.lean                Determinism checking utilities
└── Main.lean

rust/
├── Cargo.toml                          Workspace root
├── rust-toolchain.toml                 Pinned stable channel
├── SAFETY_AUDIT.md                     Unsafe block documentation
├── leaneth-types/
│   └── src/ (primitives, containers, errors, ssz/, merkle, snappy, crypto)
├── leaneth-net/
│   └── src/ (gossipsub, reqresp, discovery, ffi)
├── leaneth-storage/
│   └── src/ (schema, ops)
└── tests/ (xval.rs, integration.rs)

tests/
├── fixtures/ (golden outputs, scenario registry)
├── SSZRoundtripSuite.lean
├── MerkleizationSuite.lean
├── CryptoSuite.lean
├── ContainerSuite.lean
├── StateTransitionSuite.lean
├── ForkChoiceSuite.lean
├── NetworkSuite.lean
├── NodeServiceSuite.lean
├── NegativeStateSuite.lean
├── DeterminismSuite.lean
├── XvalSuite.lean
└── IntegrationSuite.lean

scripts/
├── test_tier0_hygiene.sh
├── test_tier1_build.sh
├── test_smoke.sh
├── test_full.sh
└── pre-commit-lean-build.sh
```
