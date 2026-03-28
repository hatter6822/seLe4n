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
| [X1](./PHASE_X1_FOUNDATION_TYPES.md) | Foundation Types & Prelude | v0.1.0 | 23 | Yes |
| [X2](./PHASE_X2_SSZ_MERKLEIZATION.md) | SSZ Merkleization & Hash Tree Root | v0.2.0 | 16 | Yes |
| [X3](./PHASE_X3_KOALABEAR_POSEIDON2.md) | KoalaBear Field & Poseidon2 Hash | v0.3.0 | 14 | Parallel |
| [X4](./PHASE_X4_XMSS_SIGNATURES.md) | XMSS Signature Scheme | v0.4.0 | 22 | Parallel |
| [X5](./PHASE_X5_CONSENSUS_CONTAINERS.md) | Consensus Containers | v0.5.0 | 20 | Yes |
| [X6](./PHASE_X6_STATE_TRANSITION.md) | State Transition — Core Operations | v0.6.0 | 18 | Yes |
| [X7](./PHASE_X7_CONSENSUS_SAFETY.md) | Consensus Safety Proofs (KEYSTONE) | v0.7.0 | 16 | Yes |
| [X8](./PHASE_X8_FORK_CHOICE.md) | Fork Choice (LMD GHOST) | v0.8.0 | 14 | No |
| [X9](./PHASE_X9_SNAPPY_NETWORKING.md) | Snappy Compression & Networking Types | v0.9.0 | 12 | Parallel |
| [X10](./PHASE_X10_NODE_SERVICES.md) | Node Services — Chain, Validator, Sync | v0.10.0 | 18 | No |
| [X11](./PHASE_X11_RUST_ABI.md) | Rust ABI Safety Layer | v0.11.0 | 16 | Parallel |
| [X12](./PHASE_X12_TESTING.md) | Testing Infrastructure & Trace Harness | v0.12.0 | 14 | No |
| [X13](./PHASE_X13_SELE4N_BRIDGE.md) | seLe4n Integration Bridge | v0.13.0 | 12 | No |
| [X14](./PHASE_X14_DOCUMENTATION.md) | Documentation, Audit, & Closure | v1.0.0 | 14 | No |
| **Total** | | | **229** | |

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
| Lean production LoC | ~15,000–20,000 |
| Lean proof LoC | ~8,000–12,000 |
| Rust LoC | ~3,000–5,000 |
| Test LoC | ~2,000–3,000 |
| Theorems/lemmas | ~300–400 |
| Sorry count | 0 |
| Axiom count | 3 |
| Rust unsafe blocks | ≤ 3 |
| XVAL cross-validation cases | ≥ 20 |
| Test tiers | 4 (hygiene, build, functional, invariant) |
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
| `BaseUint.__new__` | `BaseUint.ofNat` | X1-B2 | X1-B5: overflow |
| `BaseUint.encode_bytes` | `BaseUint.serialize` | X1-B4 | X1-B5: roundtrip |
| `BaseBitlist.encode_bytes` | `BaseBitlist.serialize` | X1-E3 | X1-E4: roundtrip |
| `Container.serialize` | `containerSerialize` | X1-G1 | X1-G2: roundtrip |
| `merkleize` | `merkleize` | X2-B3 | X2-D1: properties |
| `hash_tree_root` | `hashTreeRoot` | X2-C1/C2 | X2-D2: collision |
| `mix_in_length` | `mixInLength` | X2-B4 | X2-D3: injectivity |
| `Fp.__init__` | `Fp.mk` | X3-A1 | X3-A4: field laws |
| `Poseidon2.permute` | `permute` | X3-B3 | X3-B5: bijectivity |
| `GeneralizedXmssScheme.key_gen` | `keyGen` | X4-D2 | X4-F1: soundness |
| `GeneralizedXmssScheme.sign` | `sign` | X4-D3 | X4-F1: roundtrip |
| `GeneralizedXmssScheme.verify` | `verify` | X4-D4 | X4-F1: roundtrip |
| `Slot.is_justifiable_after` | `isJustifiableAfter` | X5-A2 | X5-A3: properties |
| `State.generate_genesis` | `generateGenesis` | X5-E5 | X5-E5: invariants |
| `State.process_slots` | `processSlots` | X6-A1 | X6-A2: preservation |
| `State.process_block_header` | `processBlockHeader` | X6-B1 | X6-B4: validation |
| `State.process_attestations` | `processAttestations` | X6-C5 | X7: safety |
| `State.state_transition` | `stateTransition` | X6-D2 | X7-B5: bundle |
| `State.build_block` | `buildBlock` | X6-D3 | — |
| `Store.from_anchor` | `Store.fromAnchor` | X8-A2 | X8-C2: consistency |
| `Store.validate_attestation` | `validateAttestation` | X8-B2 | X8-C2: consistency |
| `compress` | `compress` | X9-A1 | X9-A4: roundtrip |
| `decompress` | `decompress` | X9-A2 | X9-A4: roundtrip |
| — (novel) | `threeSFMiniSafety` | X7-D1 | **KEYSTONE** |
| — (novel) | `consensusSafety` | X7-D3 | Top-level |
| — (novel) | `consensusLiveness` | X7-E1 | Conditional |

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
│   └── Proofs.lean                     All roundtrip proofs
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
│   │   ├── Compress.lean               Compression
│   │   ├── Decompress.lean             Decompression
│   │   ├── Framing.lean                Streaming format
│   │   └── Proofs.lean                 Roundtrip
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
│   │   ├── ProcessSlots.lean           Slot advancement
│   │   ├── ProcessBlockHeader.lean     Header validation + history
│   │   ├── ProcessAttestations/
│   │   │   ├── Filter.lean             Attestation filtering
│   │   │   ├── Voting.lean             Supermajority voting
│   │   │   ├── Finalization.lean       Finalization advancement
│   │   │   └── Compose.lean            Full composition
│   │   ├── StateTransition.lean        Top-level function
│   │   ├── BuildBlock.lean             Block production
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
│   ├── Chain/ (SlotClock, Config, Service)
│   ├── Validator/ (Registry, Service)
│   ├── Sync/ (Checkpoint, Head, Backfill, BlockCache, PeerManager)
│   ├── Storage/ (Interface, Namespaces)
│   ├── API/ (Endpoints)
│   ├── Networking/ (Transport, ENR, Gossipsub, ReqResp, Discovery, Config)
│   └── Node.lean
├── Bridge/
│   ├── SharedPrelude.lean
│   ├── PlatformContract.lean
│   ├── SeLe4nIntegration.lean
│   ├── RPi5Extension.lean
│   └── Proofs.lean
├── Testing/ (TraceHarness, StateBuilder, Fixtures)
└── Main.lean

rust/
├── leaneth-types/ (SSZ codec, types, snappy)
├── leaneth-net/ (libp2p, gossipsub, discv5, reqresp, FFI)
├── leaneth-storage/ (SQLite persistence)
├── Cargo.toml (workspace)
└── SAFETY_AUDIT.md

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
