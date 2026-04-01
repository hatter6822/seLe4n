# WS-X: Lean Ethereum Formalization — Consensus Layer Specification in Lean 4

**Status**: PLANNED
**Target versions**: v0.23.0–v0.29.0
**Hardware target**: Raspberry Pi 5 (ARM64), shared with seLe4n microkernel
**Prerequisites**: WS-V complete (v0.22.7), leanSpec Python reference (hatter6822/leanSpec)
**Sub-task count**: 162 atomic units across 14 phases
**Axiom budget**: 3 (cryptographic hardness assumptions — see §6.8)
**Sorry budget**: 0 (all proofs machine-checked)
**Lean toolchain**: 4.28.0 (shared with seLe4n)
**Build system**: Lake (shared lakefile, separate library target)

## 1. Motivation

The Ethereum consensus layer ("Lean" specification, formerly Beacon Chain) is
currently specified as executable Python code in the `leanSpec` repository
(hatter6822/leanSpec). While executable, this specification lacks:

1. **Machine-checked safety proofs** — consensus safety (no two conflicting
   finalized blocks), liveness (finalization eventually advances), and
   cryptographic soundness are argued informally or not at all.
2. **Formal type safety** — Python's dynamic types allow runtime errors that a
   dependently-typed language would catch at compile time. SSZ serialization
   correctness is tested but not proved.
3. **Extraction path to verified execution** — no mechanism to compile the
   specification to a verified, high-performance binary.

seLe4n already demonstrates the "formalize in Lean 4, enforce safety with Rust"
approach: pure Lean functions define kernel transitions with machine-checked
invariant preservation, while Rust ABI crates provide the hardware interface
with a single `unsafe` block. This plan extends that architecture to create a
**formally verified Ethereum consensus client** that:

- Shares the seLe4n Lean 4 toolchain, build system, and proof methodology
- Proves consensus safety (3SF-mini), SSZ correctness, and XMSS soundness
- Provides a Rust networking/storage layer with safe FFI boundaries
- Runs on the same Raspberry Pi 5 hardware as the seLe4n microkernel
- Enables a future **verified Ethereum node on a verified microkernel**

## 2. Scope Boundary

**In scope:**
- Complete Lean 4 formalization of the leanSpec consensus specification
- SSZ type system with serialization/deserialization roundtrip proofs
- State transition function with invariant preservation proofs
- 3SF-mini consensus safety theorem (no conflicting finalization)
- Fork choice (LMD GHOST) formalization with safety properties
- XMSS hash-based signature scheme with correctness proofs
- Poseidon2 permutation over KoalaBear field with algebraic proofs
- Snappy compression with roundtrip correctness proof
- Rust ABI crate for networking (libp2p/QUIC), storage (SQLite), and OS
- Executable trace harness mirroring seLe4n's fixture-backed testing
- Integration bridge between seLe4n kernel and Ethereum consensus client

**Out of scope (deferred to future workstreams):**
- Ethereum execution layer (EVM, state trie, transaction processing)
- Validator key management HSM integration
- MEV/PBS infrastructure
- Cross-chain bridge protocols
- Slashing conditions (not present in current leanSpec Devnet fork)
- Execution layer engine API (requires EVM formalization first)

## 3. Architecture Overview

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

## 4. Development Principles

### 4.1 Inherited from seLe4n

1. **Zero sorry/axiom** in production proof surface (3 declared axioms for
   cryptographic hardness assumptions carry `AXIOM-CRYPTO-*` annotations)
2. **Invariant/Operations split** — each subsystem has `Operations.lean`
   (transitions) and `Invariant.lean` (proofs), following seLe4n's canonical
   pattern
3. **Typed identifiers** — `Slot`, `ValidatorIndex`, `Epoch`, `Bytes32`, etc.
   are wrapper structures with sentinel conventions, not type aliases
4. **Deterministic semantics** — all transitions return explicit `Except` values;
   no non-deterministic branches
5. **Fixture-backed testing** — golden-output trace comparison at every tier
6. **Platform-agnostic core** — consensus logic is pure Lean; platform bindings
   are separate typeclasses
7. **Rust ABI with minimal unsafe** — networking and storage in Rust with
   cross-validation against Lean reference

### 4.2 Ethereum-Specific Principles

8. **Spec-faithful naming** — Lean definitions mirror leanSpec Python names
   (e.g., `processSlots` ↔ `process_slots`, `stateTransition` ↔
   `state_transition`) with a documented naming map
9. **SSZ-first types** — all consensus containers derive SSZ serialization;
   Merkleization is a computable function with correctness proofs
10. **Fork-parameterized** — consensus logic is parameterized over a `Fork`
    typeclass to support future hard forks without rewriting proofs
11. **Spec coverage tracking** — every Python function in leanSpec has a
    corresponding Lean definition with a traceability tag (`LS-*`)

## 5. Source Layout

```
LeanEth/
├── Prelude.lean                        Typed identifiers, monad foundations, config
├── Types/
│   ├── Uint.lean                       Uint8, Uint16, Uint32, Uint64 with bit-width proofs
│   ├── Bytes.lean                      Bytes1..Bytes65, ByteList, ZERO_HASH
│   ├── Boolean.lean                    SSZ Boolean wrapper
│   ├── BitFields.lean                  Bitvector, Bitlist with length tracking
│   ├── Collections.lean                SSZList, SSZVector (length-indexed)
│   ├── Container.lean                  SSZ Container typeclass + derive macro
│   ├── RLP.lean                        RLP encode/decode (for ENR compatibility)
│   └── Proofs.lean                     Uint overflow, Bytes roundtrip, collection lemmas
├── SSZ/
│   ├── Encode.lean                     SSZ serialization (Container, List, Vector, Union)
│   ├── Decode.lean                     SSZ deserialization with scope tracking
│   ├── Merkle.lean                     merkleize, mixInLength, mixInSelector, zeroHashes
│   ├── HashTreeRoot.lean               Dispatched hash_tree_root per SSZ type
│   ├── Pack.lean                       packBytes, packBits chunk helpers
│   └── Proofs.lean                     Roundtrip, merkle path, collision resistance
├── Crypto/
│   ├── KoalaBear/
│   │   ├── Field.lean                  Fp type, field axioms, arithmetic, inverse
│   │   └── Proofs.lean                 Field law proofs, Fermat's little theorem
│   ├── Poseidon2/
│   │   ├── Permutation.lean            Poseidon2 permutation (S-box x³, MDS matrices)
│   │   ├── Constants.lean              Round constants, parameter sets (16, 24)
│   │   └── Proofs.lean                 Permutation bijectivity, algebraic properties
│   ├── XMSS/
│   │   ├── Types.lean                  PublicKey, SecretKey, Signature, KeyPair
│   │   ├── PRF.lean                    Pseudorandom function
│   │   ├── TweakHash.lean              Tweakable hash with domain separation
│   │   ├── TargetSum.lean              Winternitz target-sum encoding
│   │   ├── SubTree.lean                Hash subtree operations, path verification
│   │   ├── Interface.lean              GeneralizedXmssScheme (keygen, sign, verify)
│   │   ├── Aggregation.lean            Signature aggregation proofs
│   │   └── Proofs.lean                 EU-CMA security, no key reuse, path soundness
│   ├── Snappy/
│   │   ├── Compress.lean               Raw block compression
│   │   ├── Decompress.lean             Raw block decompression
│   │   ├── Framing.lean                Streaming framing format
│   │   └── Proofs.lean                 Roundtrip correctness
│   └── Hash.lean                       Hash dispatch (SHA256/Poseidon2 by fork)
├── Consensus/
│   ├── Containers/
│   │   ├── Slot.lean                   Slot type, justifiableAfter, immediateWindow
│   │   ├── Checkpoint.lean             Checkpoint (root + slot)
│   │   ├── Validator.lean              Validator, ValidatorIndex, proposer selection
│   │   ├── Config.lean                 Genesis config, chain constants
│   │   ├── Attestation/
│   │   │   ├── Types.lean              AttestationData, Attestation, AggregatedAttestation
│   │   │   ├── Aggregation.lean        aggregateByData, bit merging
│   │   │   └── Proofs.lean             Aggregation correctness, no double-counting
│   │   ├── Block/
│   │   │   ├── Types.lean              BlockHeader, BlockBody, Block, SignedBlock
│   │   │   ├── Signatures.lean         BlockSignatures, verification dispatch
│   │   │   └── Proofs.lean             Header chain integrity, body root consistency
│   │   └── State/
│   │       ├── Types.lean              HistoricalBlockHashes, JustifiedSlots, etc.
│   │       ├── State.lean              State container (all fields)
│   │       ├── Genesis.lean            generateGenesis function + genesis invariants
│   │       └── Proofs.lean             State field well-formedness lemmas
│   ├── StateTransition/
│   │   ├── ProcessSlots.lean           Slot-by-slot advancement
│   │   ├── ProcessBlockHeader.lean     Block header validation + historical tracking
│   │   ├── ProcessAttestations.lean    Attestation aggregation, supermajority, finalization
│   │   ├── ProcessBlock.lean           Full block processing (header + attestations)
│   │   ├── StateTransition.lean        Top-level state_transition function
│   │   ├── BuildBlock.lean             Block production (greedy aggregation)
│   │   └── Proofs/
│   │       ├── SlotMonotonicity.lean   Slot always increases
│   │       ├── HistoryAppendOnly.lean  Historical roots only grow
│   │       ├── FinalizationSafety.lean No finalization reversion
│   │       ├── JustifiedGeFinalized.lean justified.slot ≥ finalized.slot
│   │       ├── SupermajoritySafety.lean 2/3 agreement prevents equivocation
│   │       ├── ThreeSFMini.lean        3SF-mini safety theorem (keystone)
│   │       └── Preservation.lean       Per-operation invariant preservation
│   ├── ForkChoice/
│   │   ├── Store.lean                  Fork choice store (blocks, states, attestations)
│   │   ├── LMDGHOST.lean               LMD GHOST head selection algorithm
│   │   ├── AttestationProcessing.lean  Attestation validation + integration
│   │   ├── Pruning.lean                Stale data removal after finalization
│   │   └── Proofs/
│   │       ├── HeadValidity.lean       Selected head is always a descendant of finalized
│   │       ├── Consistency.lean        Store consistency after attestation processing
│   │       └── Convergence.lean        LMD GHOST convergence under honest majority
│   └── Invariant/
│       ├── Defs.lean                   Core consensus invariant predicates
│       ├── Composition.lean            Composed invariant bundle
│       ├── Safety.lean                 Top-level safety theorem
│       └── Liveness.lean               Finalization progress under honest majority
├── Node/
│   ├── Chain/
│   │   ├── SlotClock.lean              Wall-clock to slot conversion
│   │   ├── Config.lean                 Chain parameters (intervals, seconds per slot)
│   │   └── Service.lean                Chain service orchestration
│   ├── Validator/
│   │   ├── Registry.lean               Validator key management (abstract)
│   │   ├── DutyScheduler.lean          Block/attestation duty scheduling
│   │   └── Service.lean                Validator service orchestration
│   ├── Sync/
│   │   ├── CheckpointSync.lean         Weak subjectivity checkpoint sync
│   │   ├── HeadSync.lean               Recent block synchronization
│   │   ├── BackfillSync.lean           Historical block download
│   │   ├── PeerManager.lean            Peer tracking and selection
│   │   └── BlockCache.lean             Out-of-order block buffer
│   ├── API/
│   │   ├── Server.lean                 HTTP server abstraction
│   │   ├── Endpoints.lean              REST endpoint definitions
│   │   └── Types.lean                  Request/response types
│   ├── Storage/
│   │   ├── Interface.lean              Database typeclass (abstract)
│   │   └── Namespaces.lean             Storage namespace isolation
│   ├── Networking/
│   │   ├── Transport.lean              QUIC/TCP transport abstraction
│   │   ├── Discovery.lean              Peer discovery (discv5)
│   │   ├── Gossipsub.lean              Pubsub topic management
│   │   ├── ReqResp.lean                Request-response protocol
│   │   └── ENR.lean                    Ethereum Node Record encoding
│   └── Node.lean                       Top-level node orchestrator
├── Bridge/
│   ├── SeLe4nIntegration.lean          IPC bridge to seLe4n microkernel
│   ├── PlatformContract.lean           Ethereum node platform binding typeclass
│   └── SharedPrelude.lean              Shared typed identifiers (Bytes32, etc.)
├── Testing/
│   ├── TraceHarness.lean               Executable consensus trace harness
│   ├── StateBuilder.lean               Test state construction helpers
│   ├── Fixtures.lean                   Golden-output comparison framework
│   └── Generators.lean                 Property-based test generators
└── Main.lean                           Executable entry point

rust/
├── leaneth-types/                      SSZ codec, typed identifiers, error types
│   ├── src/lib.rs
│   └── Cargo.toml
├── leaneth-net/                        libp2p networking (QUIC, gossipsub, discv5)
│   ├── src/lib.rs
│   └── Cargo.toml
└── leaneth-storage/                    SQLite persistence layer
    ├── src/lib.rs
    └── Cargo.toml

tests/
├── fixtures/
│   ├── consensus_trace_smoke.expected  Golden trace output
│   ├── ssz_roundtrip.expected          SSZ encode/decode fixtures
│   └── scenario_registry.yaml          Test scenario metadata
├── SSZRoundtripSuite.lean              SSZ serialization tests
├── MerkleizationSuite.lean             Hash tree root tests
├── StateTransitionSuite.lean           State transition tests
├── ForkChoiceSuite.lean                Fork choice tests
├── CryptoSuite.lean                    XMSS/Poseidon2 tests
└── NegativeStateSuite.lean             Error-path tests
```

## 6. Phase Plan

### Phase X1: Foundation Types & Prelude (v0.23.0)

Establish the SSZ type system foundation in Lean 4. Pure type definitions with
decidable equality, serialization/deserialization, and basic arithmetic proofs.
No consensus logic — only the type substrate that all subsequent phases build on.

**New files**: `LeanEth/Prelude.lean`, `LeanEth/Types/*.lean`

**Ref**: `src/lean_spec/types/uint.py`, `src/lean_spec/types/ssz_base.py`,
`src/lean_spec/types/byte_arrays.py`, `src/lean_spec/types/boolean.py`,
`src/lean_spec/types/bitfields.py`, `src/lean_spec/types/collections.py`,
`src/lean_spec/types/container.py`

| ID | Ref | Description | Files | Est. |
|----|-----|-------------|-------|------|
| X1-A | LS-types/uint | **Define `BaseUint` structure and `Uint8`/`Uint16`/`Uint32`/`Uint64` instances.** Structure `BaseUint (bits : Nat) where val : Nat; h_bound : val < 2^bits`. Derive `DecidableEq`, `Repr`, `Inhabited`, `BEq`, `Ord`. Define `Uint8 := BaseUint 8`, etc. Add `ofNat` with modular reduction, `toNat`, little-endian `encodeBytes`/`decodeBytes`. ~80 lines | `Types/Uint.lean` | Small |
| X1-B | LS-types/uint | **Prove Uint arithmetic correctness.** Define `add`, `sub`, `mul`, `div`, `mod` with modular wraparound. Prove: `add_comm`, `add_assoc`, `mul_comm`, `mul_assoc`, `add_sub_cancel` (when no underflow), `encodeBytes_decodeBytes_roundtrip`, `decodeBytes_encodeBytes_roundtrip`. Prove `ofNat_toNat_id`. ~120 lines | `Types/Uint.lean`, `Types/Proofs.lean` | Medium |
| X1-C | LS-types/byte_arrays | **Define `BaseBytes` and fixed-size byte types.** Structure `BaseBytes (n : Nat) where data : ByteArray; h_len : data.size = n`. Define `Bytes1`, `Bytes4`, `Bytes12`, `Bytes16`, `Bytes20`, `Bytes32`, `Bytes33`, `Bytes52`, `Bytes64`, `Bytes65` as abbreviations. Define `ZERO_HASH : Bytes32` (all zeros). Add `BEq`, `Hashable`, `Repr`, `Inhabited`. ~60 lines | `Types/Bytes.lean` | Small |
| X1-D | LS-types/byte_arrays | **Define `BaseByteList` with length limit.** Structure `BaseByteList (limit : Nat) where data : ByteArray; h_bound : data.size ≤ limit`. Define `ByteListMiB := BaseByteList (1024 * 1024)`. Add `encodeBytes`/`decodeBytes` (identity for byte types). ~30 lines | `Types/Bytes.lean` | Trivial |
| X1-E | LS-types/boolean | **Define SSZ `Boolean` type.** Structure wrapping `Bool` with SSZ serialization (1 byte: 0x00 or 0x01). Prove `encode_decode_roundtrip`. ~20 lines | `Types/Boolean.lean` | Trivial |
| X1-F | LS-types/bitfields | **Define `BaseBitvector` with compile-time length.** Structure `BaseBitvector (len : Nat) where bits : Array Bool; h_len : bits.size = len`. SSZ encoding: little-endian bit packing within bytes, `get_byte_length = (len + 7) / 8`. Add `get`, `set`, `and`, `or`, `not`, `popcount`. ~60 lines | `Types/BitFields.lean` | Small |
| X1-G | LS-types/bitfields | **Define `BaseBitlist` with runtime length and limit.** Structure `BaseBitlist (limit : Nat) where bits : Array Bool; h_bound : bits.size ≤ limit`. SSZ encoding: bit packing + delimiter bit (highest set bit marks end of data). Add `get`, `set`, `extend`, `shiftWindow`, `length`. ~50 lines | `Types/BitFields.lean` | Small |
| X1-H | LS-types/bitfields | **Prove bitfield encode/decode roundtrip.** `bitvector_encode_decode_roundtrip : ∀ bv, decodeBitvector (encodeBitvector bv) = bv`. `bitlist_encode_decode_roundtrip : ∀ bl, decodeBitlist (encodeBitlist bl) = bl`. Prove delimiter bit correctness: the delimiter is always the highest set bit after encoding. ~60 lines | `Types/BitFields.lean`, `Types/Proofs.lean` | Small |
| X1-I | LS-types/collections | **Define `SSZVector` (fixed-length homogeneous collection).** Structure parameterized by element type and length: `SSZVector (α : Type) (len : Nat) [SSZSerializable α] where elems : Array α; h_len : elems.size = len`. Add `get`, `set`, `map`, `foldl`, `toList`. Fixed-size iff element is fixed-size. ~50 lines | `Types/Collections.lean` | Small |
| X1-J | LS-types/collections | **Define `SSZList` (variable-length homogeneous collection with limit).** Structure: `SSZList (α : Type) (limit : Nat) [SSZSerializable α] where elems : Array α; h_bound : elems.size ≤ limit`. Add `push`, `get?`, `length`, `map`, `filter`, `foldl`, `toList`. Always variable-size. ~50 lines | `Types/Collections.lean` | Small |
| X1-K | LS-types/container | **Define `SSZSerializable` typeclass.** `class SSZSerializable (α : Type) where isFixedSize : Bool; byteLength : (isFixedSize = true) → Nat; serialize : α → ByteArray; deserialize : ByteArray → Except SSZError α`. Provide instances for `BaseUint`, `Boolean`, `BaseBytes`, `BaseBitvector`, `BaseBitlist`, `SSZVector`, `SSZList`. ~80 lines | `Types/Container.lean` | Medium |
| X1-L | LS-types/container | **Define `SSZContainer` derive macro infrastructure.** A Lean 4 macro or typeclass that, given a structure with `SSZSerializable` fields, generates: `isFixedSize` (all fields fixed?), `serialize` (fixed fields + offset table + variable data), `deserialize` (reverse). Use the SSZ offset encoding rule: variable fields get `Uint32` offsets after fixed fields. ~100 lines | `Types/Container.lean` | Medium |
| X1-M | LS-types/rlp | **Define RLP encoding/decoding.** Functions `encodeRLP : RLPItem → ByteArray` and `decodeRLP : ByteArray → Except RLPError RLPItem` where `inductive RLPItem | bytes : ByteArray → RLPItem | list : List RLPItem → RLPItem`. Used only for ENR compatibility. Prove roundtrip. ~70 lines | `Types/RLP.lean` | Small |
| X1-N | — | **Define error types and prelude.** `inductive SSZError | typeMismatch | sizeMismatch | outOfBounds | deserializationFailed (msg : String)`. Define `LeanEthM α := Except LeanEthError α` monad. Define `LeanEnvMode` (`test` / `prod`) config. Import and re-export all type modules from `LeanEth/Prelude.lean`. ~40 lines | `Prelude.lean` | Trivial |
| X1-O | — | **Collection encode/decode roundtrip proofs.** Prove `sszVector_roundtrip : ∀ v : SSZVector α n, deserialize (serialize v) = .ok v` (given element roundtrip). Prove `sszList_roundtrip` similarly. Prove `container_roundtrip` for the derive macro. ~80 lines | `Types/Proofs.lean` | Medium |
| X1-P | — | **Build verification and test scaffold.** Add `LeanEth` library target to `lakefile.toml`. Create `tests/SSZRoundtripSuite.lean` with basic encode/decode tests for each type. Create `tests/fixtures/ssz_roundtrip.expected` with golden output. ~50 lines across files | `lakefile.toml`, `tests/` | Small |

**Intra-phase ordering constraints:**
- X1-A before X1-B (types before proofs)
- X1-A, X1-C, X1-E, X1-F, X1-G before X1-K (all base types before typeclass)
- X1-K before X1-L (typeclass before derive macro)
- X1-H, X1-O after their respective type definitions
- X1-P after all type definitions

**Exit criteria:**
- All SSZ base types compile with zero sorry
- Encode/decode roundtrip proofs for all types
- `lake build LeanEth.Types.Uint` (and all type modules) succeeds
- SSZRoundtripSuite passes with fixture match

---

### Phase X2: SSZ Merkleization & Hash Tree Root (v0.23.1)

Formalize SSZ Merkleization — the binary tree hashing algorithm that produces
the `hash_tree_root` for every consensus object. This is the cryptographic
backbone: state roots, block roots, attestation roots all depend on it.

**New files**: `LeanEth/SSZ/*.lean`

**Ref**: `src/lean_spec/subspecs/ssz/hash.py`, `src/lean_spec/subspecs/ssz/merkleization.py`,
`src/lean_spec/subspecs/ssz/pack.py`, `src/lean_spec/subspecs/ssz/constants.py`

| ID | Ref | Description | Files | Est. |
|----|-----|-------------|-------|------|
| X2-A | LS-ssz/constants | **Define SSZ Merkleization constants.** `BYTES_PER_CHUNK : Nat := 32`, `BITS_PER_CHUNK : Nat := 256`. Define `Chunk := Bytes32` type alias. Define `zeroChunk : Chunk := ZERO_HASH`. ~15 lines | `SSZ/Merkle.lean` | Trivial |
| X2-B | LS-ssz/pack | **Define chunk packing functions.** `packBytes : ByteArray → Array Chunk` — splits byte array into 32-byte chunks, zero-padding the last. `packBits : Array Bool → Array Chunk` — packs bits into chunks (little-endian within bytes). Prove `packBytes_length` and `packBits_length` bounds. ~50 lines | `SSZ/Pack.lean` | Small |
| X2-C | LS-ssz/merkleization | **Define pre-computed zero subtree roots.** `zeroTreeRoot : Nat → Bytes32` where `zeroTreeRoot 0 = ZERO_HASH` and `zeroTreeRoot (n+1) = hashNodes (zeroTreeRoot n) (zeroTreeRoot n)`. Use `Array.mkEmpty` cache for efficiency. Prove `zeroTreeRoot_deterministic`. ~30 lines | `SSZ/Merkle.lean` | Small |
| X2-D | LS-ssz/merkleization | **Define `hashNodes` and `merkleize`.** `hashNodes : Bytes32 → Bytes32 → Bytes32` — concatenate and hash (SHA256 or Poseidon2 depending on fork). `merkleize : Array Chunk → (limit : Option Nat) → Bytes32` — build balanced binary tree with zero-padding to next power of 2, capped by limit. Implement the efficient O(n·log(width)) algorithm from leanSpec. ~80 lines | `SSZ/Merkle.lean` | Medium |
| X2-E | LS-ssz/merkleization | **Define `mixInLength` and `mixInSelector`.** `mixInLength : Bytes32 → Nat → Bytes32 := hashNodes root (Uint256.encodeLE length)`. `mixInSelector : Bytes32 → Nat → Bytes32 := hashNodes root (Uint256.encodeLE selector)`. Used for variable-length types and unions respectively. ~20 lines | `SSZ/Merkle.lean` | Trivial |
| X2-F | LS-ssz/hash | **Define `hashTreeRoot` dispatch for basic types.** `hashTreeRoot [SSZSerializable α] : α → Bytes32`. Instances for `BaseUint` (pack + merkleize), `Boolean` (pack), `BaseBytes` (pack), `BaseByteList` (pack + mixInLength). ~40 lines | `SSZ/HashTreeRoot.lean` | Small |
| X2-G | LS-ssz/hash | **Define `hashTreeRoot` for composite types.** Instances for `SSZVector` (if basic: pack all elements; if composite: recursively hash each element, merkleize with limit=length). `SSZList` (same but mixInLength). `Container` (merkleize field hash roots). `SSZUnion` (mixInSelector). ~60 lines | `SSZ/HashTreeRoot.lean` | Small |
| X2-H | — | **Prove merkleize correctness properties.** (1) `merkleize_singleton : merkleize #[c] none = c`. (2) `merkleize_empty_limit : merkleize #[] (some n) = zeroTreeRoot (log2Ceil n)`. (3) `merkleize_deterministic : merkleize cs l = merkleize cs l` (function purity). (4) `merkleize_limit_ge : n ≥ cs.size → ...` (limit must not be smaller than input). ~60 lines | `SSZ/Proofs.lean` | Small |
| X2-I | — | **Prove hash tree root collision resistance (conditional).** Under assumption `hashNodes_collision_resistant` (axiom AXIOM-CRYPTO-1): `hashTreeRoot_injective_container : hashTreeRoot c₁ = hashTreeRoot c₂ → c₁ = c₂` for fixed-schema containers. This is the foundational SSZ binding property. ~50 lines | `SSZ/Proofs.lean` | Medium |
| X2-J | — | **Prove mixInLength preserves distinctness.** `mixInLength_injective : mixInLength r₁ n₁ = mixInLength r₂ n₂ → r₁ = r₂ ∧ n₁ = n₂` (under AXIOM-CRYPTO-1). Essential for list/vector type safety in Merkle trees. ~30 lines | `SSZ/Proofs.lean` | Small |
| X2-K | — | **Merkleization test suite.** Create `tests/MerkleizationSuite.lean` with test vectors from leanSpec's `tests/lean_spec/types/test_ssz_hash.py`. Compare Lean `hashTreeRoot` output against known Python outputs for basic types, containers, lists, and nested structures. ~60 lines | `tests/MerkleizationSuite.lean` | Small |

**Intra-phase ordering constraints:**
- X2-A, X2-B before X2-D (constants and packing before merkleize)
- X2-C before X2-D (zero hashes before merkleize)
- X2-D, X2-E before X2-F (merkleize before hash tree root)
- X2-F before X2-G (basic before composite)
- X2-D before X2-H, X2-I, X2-J (proofs after implementation)

**Exit criteria:**
- `merkleize` and `hashTreeRoot` compile with zero sorry
- Collision resistance proof under stated axiom
- MerkleizationSuite matches Python reference outputs
- `lake build LeanEth.SSZ.HashTreeRoot` succeeds

---

### Phase X3: KoalaBear Field & Poseidon2 Hash (v0.23.2)

Formalize the KoalaBear prime field and Poseidon2 permutation — the hash
function underlying XMSS signatures in the Lean consensus specification. This
is a prerequisite for all cryptographic proofs.

**New files**: `LeanEth/Crypto/KoalaBear/*.lean`, `LeanEth/Crypto/Poseidon2/*.lean`

**Ref**: `src/lean_spec/subspecs/koalabear/field.py`,
`src/lean_spec/subspecs/poseidon2/permutation.py`,
`src/lean_spec/subspecs/poseidon2/constants.py`

| ID | Ref | Description | Files | Est. |
|----|-----|-------------|-------|------|
| X3-A | LS-koalabear/field | **Define KoalaBear field prime and `Fp` type.** `def P : Nat := 2^31 - 2^24 + 1` (= 2013265921). Structure `Fp where val : Fin P`. Derive `DecidableEq`, `Repr`, `Inhabited`, `BEq`. Prove `P_prime : Nat.Prime P` (by `native_decide` or explicit witness). Define `P_BYTES : Nat := 4`. ~40 lines | `Crypto/KoalaBear/Field.lean` | Small |
| X3-B | LS-koalabear/field | **Define Fp field operations.** `add : Fp → Fp → Fp := ⟨(a.val + b.val) % P⟩`, `sub`, `mul`, `neg`, `inv` (Fermat's little theorem: `a^(P-2) mod P`), `div := a * b.inv`, `pow : Fp → Nat → Fp`. Define `zero : Fp := ⟨0⟩`, `one : Fp := ⟨1⟩`. Add SSZ serialization (4-byte little-endian). ~60 lines | `Crypto/KoalaBear/Field.lean` | Small |
| X3-C | LS-koalabear/field | **Prove KoalaBear field laws.** Prove `add_comm`, `add_assoc`, `add_zero`, `mul_comm`, `mul_assoc`, `mul_one`, `mul_inv_cancel` (for nonzero), `left_distrib`. These constitute a `Field` instance. Prove `inv_correct : a ≠ 0 → a * a.inv = 1`. Prove TWO_ADICITY: `∃ k, k = 24 ∧ 2^k ∣ (P - 1) ∧ ¬(2^(k+1) ∣ (P - 1))`. ~100 lines | `Crypto/KoalaBear/Proofs.lean` | Medium |
| X3-D | LS-poseidon2/constants | **Define Poseidon2 constants.** Round constants for 16-element and 24-element widths. `FULL_ROUNDS : Nat := 8`, `PARTIAL_ROUNDS_16 : Nat := 13`, `PARTIAL_ROUNDS_24 : Nat := 21`. S-box: `sbox : Fp → Fp := fun x => x * x * x` (cube). MDS matrix entries as `Array (Array Fp)`. External/internal round constant arrays. ~80 lines (constants are large but mechanical) | `Crypto/Poseidon2/Constants.lean` | Small |
| X3-E | LS-poseidon2/permutation | **Define Poseidon2 permutation structure.** `structure Poseidon2Params where width : Nat; fullRounds : Nat; partialRounds : Nat; mdsExternal : Array (Array Fp); mdsInternal : Array Fp; roundConstants : Array (Array Fp)`. Define `PARAMS_16 : Poseidon2Params` and `PARAMS_24 : Poseidon2Params` using X3-D constants. ~30 lines | `Crypto/Poseidon2/Permutation.lean` | Trivial |
| X3-F | LS-poseidon2/permutation | **Define Poseidon2 round functions.** `externalRound : Poseidon2Params → Array Fp → Nat → Array Fp` (add round constant, apply S-box to all elements, multiply by external MDS). `internalRound : Poseidon2Params → Array Fp → Nat → Array Fp` (add round constant, apply S-box to first element only, multiply by internal MDS). `initialLinearLayer : Poseidon2Params → Array Fp → Array Fp` (initial MDS multiplication). ~60 lines | `Crypto/Poseidon2/Permutation.lean` | Small |
| X3-G | LS-poseidon2/permutation | **Define full Poseidon2 permutation.** `permute : Poseidon2Params → Array Fp → Array Fp` — applies initial linear layer, first half of full rounds, all partial rounds, second half of full rounds. Prove `permute_preserves_width : (permute p s).size = s.size`. ~40 lines | `Crypto/Poseidon2/Permutation.lean` | Small |
| X3-H | — | **Prove Poseidon2 is a permutation (bijectivity).** Under the algebraic structure of the S-box (cube over prime field): prove `sbox_injective : sbox a = sbox b → a = b` (since `gcd(3, P-1) = 1` for KoalaBear). Lift to `permute_injective` via MDS matrix invertibility. This is critical: a non-bijective "hash" breaks collision resistance. ~80 lines | `Crypto/Poseidon2/Proofs.lean` | Medium |
| X3-I | — | **Define Poseidon2-based hash for SSZ.** `poseidon2Hash : ByteArray → Bytes32` — absorbs input in field-element chunks using a sponge construction over `permute`. `hashNodesPoseidon2 : Bytes32 → Bytes32 → Bytes32` — hash two 32-byte chunks. Wire into the `hashNodes` dispatch from X2-D (fork-dependent selection). ~40 lines | `Crypto/Hash.lean` | Small |
| X3-J | — | **Crypto test suite.** Create `tests/CryptoSuite.lean` with KoalaBear field arithmetic spot checks, Poseidon2 permutation test vectors (from leanSpec Python outputs), and hash function consistency tests. ~40 lines | `tests/CryptoSuite.lean` | Small |

**Exit criteria:**
- KoalaBear `Fp` has a `Field` instance with all laws proved
- Poseidon2 bijectivity proved (under MDS invertibility)
- `poseidon2Hash` matches Python reference for test vectors
- Zero sorry in all crypto modules

---

### Phase X4: XMSS Signature Scheme (v0.23.3–v0.23.4)

Formalize the XMSS (eXtended Merkle Signature Scheme) — the post-quantum
hash-based signature scheme used for all block and attestation signatures in
the Lean consensus specification. This is the most complex cryptographic
component, requiring careful formalization of Merkle tree traversal, one-time
signature key management, and aggregation.

**New files**: `LeanEth/Crypto/XMSS/*.lean`

**Ref**: `src/lean_spec/subspecs/xmss/interface.py`,
`src/lean_spec/subspecs/xmss/containers.py`,
`src/lean_spec/subspecs/xmss/prf.py`,
`src/lean_spec/subspecs/xmss/tweak_hash.py`,
`src/lean_spec/subspecs/xmss/target_sum.py`,
`src/lean_spec/subspecs/xmss/subtree.py`,
`src/lean_spec/subspecs/xmss/aggregation.py`

| ID | Ref | Description | Files | Est. |
|----|-----|-------------|-------|------|
| X4-A | LS-xmss/containers | **Define XMSS type containers.** `HashDigest := Array Fp`, `HashDigestList := SSZList HashDigest`, `HashDigestVector := SSZVector HashDigest`. `Parameter := Array Fp`. `PRFKey := Array Fp`. `Randomness := Array Fp`. `HashTreeOpening := Array HashDigest` (Merkle authentication path). Add SSZ serialization instances for all. ~50 lines | `Crypto/XMSS/Types.lean` | Small |
| X4-B | LS-xmss/containers | **Define PublicKey, SecretKey, Signature, KeyPair.** `structure PublicKey where root : HashDigestVector; parameter : Parameter`. `structure Signature where path : HashTreeOpening; rho : Randomness; hashes : HashDigestList` (fixed size = SIGNATURE_LEN_BYTES). `structure SecretKey where prfKey : PRFKey; parameter : Parameter; activationSlot : Slot; numActiveSlots : Uint64; topTree : HashSubTree; leftBottomTreeIndex : Uint64; leftBottomTree : HashSubTree; rightBottomTree : HashSubTree`. `structure KeyPair where public : PublicKey; secret : SecretKey`. ~60 lines | `Crypto/XMSS/Types.lean` | Small |
| X4-C | LS-xmss/constants | **Define XMSS configuration.** `structure XmssConfig where hashLenFe : Nat; lifetime : Nat; winternitzW : Nat; signatureLenBytes : Nat; publicKeyLenBytes : Nat`. Define `TEST_CONFIG` (fast, small tree) and `PROD_CONFIG` (full security). Define `TARGET_CONFIG` selected by `LeanEnvMode`. ~30 lines | `Crypto/XMSS/Types.lean` | Trivial |
| X4-D | LS-xmss/prf | **Define pseudorandom function.** `structure Prf where eval : PRFKey → Nat → Array Fp`. Test PRF: simple Poseidon2 application. Production PRF: full-strength Poseidon2 sponge. Define `TEST_PRF`, `PROD_PRF`. ~30 lines | `Crypto/XMSS/PRF.lean` | Trivial |
| X4-E | LS-xmss/tweak_hash | **Define tweakable hash with domain separation.** `structure TweakHasher where hash : Parameter → Nat → Array Fp → HashDigest; chainHash : Parameter → Nat → Nat → HashDigest → HashDigest`. Domain separation via position-dependent tweaks prevents cross-context hash collisions. Define `TEST_TWEAK_HASHER`, `PROD_TWEAK_HASHER`. ~40 lines | `Crypto/XMSS/TweakHash.lean` | Small |
| X4-F | LS-xmss/target_sum | **Define Winternitz target-sum encoding.** `structure TargetSumEncoder where encode : Array Fp → Array Nat; decode : Array Nat → Array Fp; targetSum : Nat`. The encoder maps message digests to Winternitz chain indices with a fixed target checksum. Prove `encode_decode_roundtrip`. ~50 lines | `Crypto/XMSS/TargetSum.lean` | Small |
| X4-G | LS-xmss/subtree | **Define HashSubTree for Merkle tree operations.** `inductive HashSubTree where | leaf : HashDigest → HashSubTree | node : HashDigest → HashSubTree → HashSubTree → HashSubTree`. Define `root : HashSubTree → HashDigest`, `depth : HashSubTree → Nat`, `getLeaf : HashSubTree → Nat → Option HashDigest`, `getPath : HashSubTree → Nat → Option HashTreeOpening`. ~60 lines | `Crypto/XMSS/SubTree.lean` | Small |
| X4-H | LS-xmss/subtree | **Define path verification and combination.** `verifyPath : HashDigest → HashTreeOpening → Nat → HashDigest → Bool` — verify that a leaf at a given index has the claimed Merkle path to the root. `combinedPath : HashTreeOpening → HashTreeOpening → Nat → Nat → HashTreeOpening` — combine authentication paths across tree layers (top + bottom). ~50 lines | `Crypto/XMSS/SubTree.lean` | Small |
| X4-I | LS-xmss/interface | **Define `GeneralizedXmssScheme` and key generation.** `structure GeneralizedXmssScheme where config : XmssConfig; prf : Prf; hasher : TweakHasher; encoder : TargetSumEncoder; rand : Rand`. `keyGen : GeneralizedXmssScheme → Slot → Uint64 → KeyPair` — generate keypair valid for `numActiveSlots` consecutive slots starting at `activationSlot`. Implements the top-bottom tree traversal: expand activation time to √(LIFETIME) boundaries, generate bottom trees, build top tree from roots. ~80 lines | `Crypto/XMSS/Interface.lean` | Medium |
| X4-J | LS-xmss/interface | **Define sign and verify.** `sign : GeneralizedXmssScheme → SecretKey → Slot → Bytes32 → Except XmssError Signature` — produces one-time signature for message at given slot. Computes bottom tree index, generates Winternitz chains, constructs authentication path. `verify : GeneralizedXmssScheme → PublicKey → Slot → Bytes32 → Signature → Bool` — verifies signature by reconstructing Winternitz chains and checking Merkle path to root. ~80 lines | `Crypto/XMSS/Interface.lean` | Medium |
| X4-K | LS-xmss/aggregation | **Define signature aggregation.** `structure AggregatedSignatureProof where ...` — aggregated proof for multiple validators attesting to the same data. `aggregate : List (ValidatorIndex × Signature) → Except AggregationError AggregatedSignatureProof`. `verifyAggregated : AggregatedSignatureProof → List (ValidatorIndex × PublicKey) → Bytes32 → Bool`. ~60 lines | `Crypto/XMSS/Aggregation.lean` | Small |
| X4-L | — | **Prove XMSS correctness: sign/verify roundtrip.** `sign_verify_correct : ∀ scheme sk pk slot msg, keyGen scheme = (pk, sk) → slot ∈ validSlots sk → verify scheme pk slot msg (sign scheme sk slot msg) = true`. This is the fundamental signature soundness property. ~60 lines | `Crypto/XMSS/Proofs.lean` | Medium |
| X4-M | — | **Prove no key reuse (one-time property).** `sign_slot_unique : ∀ scheme sk slot₁ slot₂, slot₁ ≠ slot₂ → sign scheme sk slot₁ msg₁ uses different OTS key than sign scheme sk slot₂ msg₂`. Formalize as: the bottom-tree leaf index is a function of slot, and distinct slots map to distinct leaves within the valid range. ~50 lines | `Crypto/XMSS/Proofs.lean` | Medium |
| X4-N | — | **Prove path verification soundness.** `verifyPath_correct : verifyPath leaf path idx root = true → getLeaf tree idx = some leaf ∧ tree.root = root` (under collision resistance axiom AXIOM-CRYPTO-1). This connects the authentication path to actual tree membership. ~40 lines | `Crypto/XMSS/Proofs.lean` | Small |
| X4-O | — | **Prove aggregation correctness.** `aggregate_verify_correct : verifyAggregated (aggregate sigs) keys msg = true ↔ ∀ (i, sig) ∈ sigs, verify scheme (keys i) slot msg sig = true`. Aggregation must be equivalent to verifying each individual signature. ~50 lines | `Crypto/XMSS/Proofs.lean` | Medium |
| X4-P | — | **XMSS test vectors.** Add XMSS keygen/sign/verify test cases to `tests/CryptoSuite.lean` using both TEST_CONFIG and PROD_CONFIG parameters. Verify against Python reference outputs. Test aggregation roundtrip. ~40 lines | `tests/CryptoSuite.lean` | Small |

**Exit criteria:**
- Complete XMSS implementation: keygen, sign, verify, aggregate
- Sign/verify roundtrip proved
- One-time key property proved
- Path soundness proved under collision resistance axiom
- Zero sorry in XMSS modules

---

### Phase X5: Consensus Containers (v0.24.0)

Formalize all consensus-layer data structures: Slot, Checkpoint, Validator,
AttestationData, Block, and State. These are the core types that the state
transition function operates on. Every container gets SSZ serialization and
`hashTreeRoot` automatically via the X1/X2 infrastructure.

**New files**: `LeanEth/Consensus/Containers/*.lean`

**Ref**: `src/lean_spec/subspecs/containers/slot.py`,
`src/lean_spec/subspecs/containers/checkpoint.py`,
`src/lean_spec/subspecs/containers/validator.py`,
`src/lean_spec/subspecs/containers/config.py`,
`src/lean_spec/subspecs/containers/attestation/`,
`src/lean_spec/subspecs/containers/block/`,
`src/lean_spec/subspecs/containers/state/`

| ID | Ref | Description | Files | Est. |
|----|-----|-------------|-------|------|
| X5-A | LS-containers/slot | **Define `Slot` type with 3SF-mini predicates.** `structure Slot where val : Uint64 deriving DecidableEq, Repr, Ord, BEq, Hashable`. Constants: `IMMEDIATE_JUSTIFICATION_WINDOW : Nat := 5`. Methods: `justifiedIndexAfter : Slot → Slot → Option Nat` (maps slot to bitfield index relative to finalized slot; `none` if implicitly justified). `isJustifiableAfter : Slot → Slot → Bool` (3SF-mini rule: delta ≤ 5, OR delta is perfect square, OR delta is pronic number where 4·delta+1 is an odd perfect square). ~50 lines | `Consensus/Containers/Slot.lean` | Small |
| X5-B | LS-containers/slot | **Prove Slot arithmetic properties.** `justifiedIndexAfter_some_gt : justifiedIndexAfter s f = some i → s > f`. `isJustifiableAfter_monotone_window : s.val - f.val ≤ 5 → isJustifiableAfter s f = true`. `isJustifiableAfter_square : isqrt(d)^2 = d → isJustifiableAfter (f + d) f = true`. `slot_add_comm`, `slot_lt_irrefl`, `slot_lt_trans`. ~40 lines | `Consensus/Containers/Slot.lean` | Small |
| X5-C | LS-containers/checkpoint | **Define `Checkpoint` container.** `structure Checkpoint where root : Bytes32; slot : Slot` deriving SSZSerializable, DecidableEq, Repr, BEq, Hashable. ~15 lines | `Consensus/Containers/Checkpoint.lean` | Trivial |
| X5-D | LS-containers/validator | **Define `Validator` and `ValidatorIndex`.** `structure ValidatorIndex where val : Uint64 deriving DecidableEq, Repr, Ord, BEq, Hashable`. `isProposerFor : ValidatorIndex → Slot → Uint64 → Bool := vi.val.toNat % numValidators.toNat == vi.val.toNat`. `isValid : ValidatorIndex → Uint64 → Bool := vi.val < numValidators`. `structure Validator where attestationPubkey : Bytes52; proposalPubkey : Bytes52; index : ValidatorIndex` deriving SSZSerializable. Define `Validators := SSZList Validator 4096`. ~40 lines | `Consensus/Containers/Validator.lean` | Small |
| X5-E | LS-containers/config | **Define `Config` container.** `structure Config where genesisTime : Uint64` deriving SSZSerializable, DecidableEq. Define chain constants: `HISTORICAL_ROOTS_LIMIT := 262144`, `VALIDATOR_REGISTRY_LIMIT := 4096`, `SECONDS_PER_SLOT := 4`, `INTERVALS_PER_SLOT := 5`, `JUSTIFICATION_LOOKBACK_SLOTS := 3`, `ATTESTATION_COMMITTEE_COUNT := 1`. ~30 lines | `Consensus/Containers/Config.lean` | Trivial |
| X5-F | LS-containers/attestation | **Define attestation types.** `structure AttestationData where slot : Slot; head : Checkpoint; target : Checkpoint; source : Checkpoint` deriving SSZSerializable, DecidableEq, BEq, Hashable. `dataRootBytes : AttestationData → Bytes32 := hashTreeRoot`. `structure Attestation where validatorId : ValidatorIndex; data : AttestationData`. `structure AggregatedAttestation where aggregationBits : AggregationBits; data : AttestationData` deriving SSZSerializable. `AggregationBits := BaseBitlist 4096`. `AggregatedAttestations := SSZList AggregatedAttestation 4096`. ~50 lines | `Consensus/Containers/Attestation/Types.lean` | Small |
| X5-G | LS-containers/attestation | **Define attestation aggregation.** `aggregateByData : List Attestation → List AggregatedAttestation` — groups attestations with identical `AttestationData`, merges `aggregationBits` via bitwise OR. Prove `aggregateByData_preserves_votes : ∀ v ∈ votes, ∃ agg ∈ aggregateByData votes, agg.aggregationBits.get v.validatorId = true`. ~40 lines | `Consensus/Containers/Attestation/Aggregation.lean` | Small |
| X5-H | LS-containers/block | **Define block types.** `structure BlockBody where attestations : AggregatedAttestations`. `structure BlockHeader where slot : Slot; proposerIndex : ValidatorIndex; parentRoot : Bytes32; stateRoot : Bytes32; bodyRoot : Bytes32` deriving SSZSerializable. `structure Block where slot : Slot; proposerIndex : ValidatorIndex; parentRoot : Bytes32; stateRoot : Bytes32; body : BlockBody` deriving SSZSerializable. ~40 lines | `Consensus/Containers/Block/Types.lean` | Small |
| X5-I | LS-containers/block | **Define signed block and signature verification.** `structure BlockSignatures where attestationSignatures : AttestationSignatures; proposerSignature : Signature`. `structure SignedBlock where block : Block; signature : BlockSignatures`. `verifySignatures : SignedBlock → State → GeneralizedXmssScheme → Bool` — verifies proposer signature over block root and each attestation signature by participating validators. ~50 lines | `Consensus/Containers/Block/Signatures.lean` | Small |
| X5-J | LS-containers/state/types | **Define state support types.** `HistoricalBlockHashes := SSZList Bytes32 262144`. `JustificationRoots := SSZList Bytes32 262144`. `JustifiedSlots := BaseBitlist 262144` with methods: `isSlotJustified : JustifiedSlots → Slot → Slot → Bool`, `withJustified : JustifiedSlots → Slot → Slot → Bool → JustifiedSlots`, `extendToSlot : JustifiedSlots → Slot → Slot → JustifiedSlots`, `shiftWindow : JustifiedSlots → Nat → JustifiedSlots`. `JustificationValidators := BaseBitlist (262144 * 4096)`. ~60 lines | `Consensus/Containers/State/Types.lean` | Small |
| X5-K | LS-containers/state | **Define `State` container.** `structure State where config : Config; slot : Slot; latestBlockHeader : BlockHeader; latestJustified : Checkpoint; latestFinalized : Checkpoint; historicalBlockHashes : HistoricalBlockHashes; justifiedSlots : JustifiedSlots; validators : Validators; justificationsRoots : JustificationRoots; justificationsValidators : JustificationValidators` deriving SSZSerializable. ~30 lines | `Consensus/Containers/State/State.lean` | Small |
| X5-L | LS-containers/state | **Define `generateGenesis`.** `generateGenesis : Uint64 → Validators → State` — creates genesis state with Slot(0), empty historical hashes, zero-hash justified/finalized checkpoints. Prove `genesis_slot_zero : (generateGenesis t vs).slot = Slot.mk 0`. Prove `genesis_justified_eq_finalized : (generateGenesis t vs).latestJustified = (generateGenesis t vs).latestFinalized`. ~40 lines | `Consensus/Containers/State/Genesis.lean` | Small |
| X5-M | — | **State field well-formedness lemmas.** Prove: `historicalHashes_length_le_limit`, `justifiedSlots_length_le_limit`, `validators_length_le_limit`, `justificationsRoots_length_le_limit`. Prove `justifiedSlots_extend_preserves : isSlotJustified js f s₁ = true → isSlotJustified (extendToSlot js f s₂) f s₁ = true` (extension doesn't lose existing data). ~50 lines | `Consensus/Containers/State/Proofs.lean` | Small |
| X5-N | — | **Container test suite.** Create `tests/ContainerSuite.lean` with SSZ roundtrip tests for every consensus container. Test hashTreeRoot for State, Block, Attestation against Python reference values. Test genesis generation. ~50 lines | `tests/ContainerSuite.lean` | Small |

**Exit criteria:**
- All consensus containers compile with SSZ serialization
- hashTreeRoot computed correctly for all types
- Genesis generation proved correct
- JustifiedSlots operations proved sound
- Container SSZ roundtrip tests pass

---

### Phase X6: State Transition — Core Operations (v0.24.1–v0.24.2)

Formalize the heart of the consensus layer: the state transition function. This
is the most critical phase — every block applied to the beacon state flows
through these functions. Following seLe4n's invariant/operations split, we
define transitions in `StateTransition/*.lean` and prove preservation separately.

**New files**: `LeanEth/Consensus/StateTransition/*.lean`

**Ref**: `src/lean_spec/subspecs/containers/state/state.py` (methods
`process_slots`, `process_block_header`, `process_attestations`,
`process_block`, `state_transition`, `build_block`)

| ID | Ref | Description | Files | Est. |
|----|-----|-------------|-------|------|
| X6-A | LS-state/process_slots | **Define `processSlots`.** `processSlots : State → Slot → Except ConsensusError State` — advances state through empty slots up to (but not including) `targetSlot`. For each intermediate slot: if `latestBlockHeader.stateRoot = ZERO_HASH`, cache current state root in header. Increment slot by 1. Uses `State.model_copy` pattern (functional update). ~40 lines | `StateTransition/ProcessSlots.lean` | Small |
| X6-B | LS-state/process_slots | **Prove `processSlots` properties.** (1) `processSlots_slot_eq : processSlots s t = .ok s' → s'.slot = t`. (2) `processSlots_monotone : processSlots s t = .ok s' → s.slot ≤ s'.slot`. (3) `processSlots_preserves_validators : processSlots s t = .ok s' → s'.validators = s.validators`. (4) `processSlots_preserves_config : processSlots s t = .ok s' → s'.config = s.config`. (5) `processSlots_preserves_finalized : processSlots s t = .ok s' → s'.latestFinalized = s.latestFinalized`. ~60 lines | `StateTransition/ProcessSlots.lean` | Small |
| X6-C | LS-state/process_block_header | **Define `processBlockHeader`.** `processBlockHeader : State → Block → Except ConsensusError State`. Validation: (1) block.slot = state.slot, (2) block.slot > parentHeader.slot (monotonic), (3) proposerIndex satisfies `isProposerFor`, (4) block.parentRoot = hashTreeRoot(latestBlockHeader). Genesis special case: if parent slot = 0, mark parent as justified + finalized. Append parent_root + ZERO_HASH gap entries to historicalBlockHashes. Extend justifiedSlots bitfield. Update latestBlockHeader (with empty stateRoot). ~80 lines | `StateTransition/ProcessBlockHeader.lean` | Medium |
| X6-D | LS-state/process_block_header | **Prove `processBlockHeader` validation soundness.** (1) `processBlockHeader_rejects_wrong_slot : b.slot ≠ s.slot → processBlockHeader s b = .error ...`. (2) `processBlockHeader_rejects_wrong_proposer`. (3) `processBlockHeader_rejects_wrong_parent`. (4) `processBlockHeader_preserves_validators`. (5) `processBlockHeader_extends_history : processBlockHeader s b = .ok s' → s'.historicalBlockHashes.length ≥ s.historicalBlockHashes.length`. ~60 lines | `StateTransition/ProcessBlockHeader.lean` | Small |
| X6-E | LS-state/process_attestations | **Define `processAttestations` — attestation filtering.** First half of the complex attestation processing logic. For each `AggregatedAttestation` in the block body, apply filter checks: (1) source must be justified, (2) target must not be justified, (3) source/target not ZERO_HASH, (4) source/target roots exist in historicalBlockHashes, (5) target.slot > source.slot, (6) target.slot satisfies `isJustifiableAfter(finalizedSlot)`. Collect valid attestations into a working set. ~60 lines | `StateTransition/ProcessAttestations.lean` | Small |
| X6-F | LS-state/process_attestations | **Define `processAttestations` — supermajority voting and justification.** Second half: reconstruct justification map (root → validator bitvector). For each valid attestation, mark participating validators. Check supermajority threshold: `3 * votesFor(root) ≥ 2 * totalValidators`. If met, mark target as justified, remove from tracking. Check finalization: if continuous chain from source to target is justifiable, advance `latestFinalized`. Prune stale roots and rebase justifiedSlots bitfield. ~80 lines | `StateTransition/ProcessAttestations.lean` | Medium |
| X6-G | LS-state/process_attestations | **Define `processAttestations` — finalization and pruning.** Third section: after justification, check if finalization can advance. Condition: source is justified AND target is justified AND all intermediate slots in the chain are justifiable (3SF-mini pattern). If so, set `latestFinalized = target checkpoint`. Prune: remove all `justificationsRoots` entries for slots ≤ new finalized. Shift `justifiedSlots` window. Convert tracking structures back to SSZ format (sorted roots, flattened validator bits). ~60 lines | `StateTransition/ProcessAttestations.lean` | Medium |
| X6-H | LS-state/process_block | **Define `processBlock` and `stateTransition`.** `processBlock : State → Block → Except ConsensusError State := processBlockHeader s b >>= fun s' => processAttestations s' b.body.attestations`. `stateTransition : State → Block → Bool → Except ConsensusError State := processSlots s b.slot >>= processBlock · b >>= fun s' => if b.stateRoot = hashTreeRoot s' then .ok s' else .error stateRootMismatch`. ~30 lines | `StateTransition/StateTransition.lean` | Small |
| X6-I | LS-state/build_block | **Define `buildBlock`.** `buildBlock : State → List Attestation → Validators → GeneralizedXmssScheme → ValidatorIndex → Except ConsensusError (Block × State × List AggregatedAttestation × List AggregatedSignatureProof)` — greedy aggregation: find attestations matching current justified checkpoint, select proofs maximizing new validator coverage, iterate until justification stabilizes. ~60 lines | `StateTransition/BuildBlock.lean` | Medium |
| X6-J | — | **Define consensus error type.** `inductive ConsensusError | slotMismatch | parentMismatch | invalidProposer | stateRootMismatch | attestationFilterFailed (reason : String) | supermajorityNotReached | finalizationFailed | invalidSignature | buildBlockFailed`. ~15 lines | `Consensus/Containers/Config.lean` | Trivial |
| X6-K | — | **State transition test suite.** Create `tests/StateTransitionSuite.lean` with test vectors from leanSpec: genesis → first block, multi-block chain, attestation processing, justification trigger, finalization trigger. Compare state roots against Python reference. ~60 lines | `tests/StateTransitionSuite.lean` | Small |

**Intra-phase ordering constraints:**
- X6-A before X6-B (implementation before proofs)
- X6-C before X6-D
- X6-E before X6-F before X6-G (attestation processing is sequential)
- X6-A, X6-C, X6-E–G before X6-H (components before composition)
- X6-J can proceed in parallel with any task

**Exit criteria:**
- Full state transition pipeline compiles: processSlots → processBlockHeader →
  processAttestations → stateTransition
- All validation checks match Python reference behavior
- State transition test suite passes with fixture match
- Zero sorry in state transition modules

---

### Phase X7: Consensus Safety Proofs — The Keystone (v0.25.0–v0.25.2)

This is the most important proof phase. We prove the 3SF-mini consensus safety
theorem: no two conflicting blocks can both be finalized under honest
supermajority. This is the mathematical foundation that makes the Ethereum
consensus layer trustworthy. These proofs have no Python reference — they are
novel formal verification contributions.

**New files**: `LeanEth/Consensus/StateTransition/Proofs/*.lean`,
`LeanEth/Consensus/Invariant/*.lean`

| ID | Ref | Description | Files | Est. |
|----|-----|-------------|-------|------|
| X7-A | — | **Define core consensus invariant predicates.** `slotMonotone (s : State) : Prop := s.slot.val ≥ s.latestBlockHeader.slot.val`. `justifiedGeFinalized (s : State) : Prop := s.latestJustified.slot ≥ s.latestFinalized.slot`. `historyConsistent (s : State) : Prop := s.historicalBlockHashes.length ≤ HISTORICAL_ROOTS_LIMIT ∧ ∀ i < s.historicalBlockHashes.length, s.historicalBlockHashes[i]! ≠ ZERO_HASH → (∃ slot, ...)`. `validatorsStable (s : State) : Prop := s.validators.length > 0`. ~40 lines | `Consensus/Invariant/Defs.lean` | Small |
| X7-B | — | **Define finalization invariants.** `finalizationMonotone (s s' : State) : Prop := s'.latestFinalized.slot ≥ s.latestFinalized.slot` (finalization never reverts). `finalizationImpliesJustification (s : State) : Prop := ∀ cp, cp = s.latestFinalized → s.justifiedSlots.isSlotJustified s.latestFinalized.slot cp.slot = true` (finalized blocks are justified). `supermajorityThreshold (votes totalValidators : Nat) : Prop := 3 * votes ≥ 2 * totalValidators`. ~30 lines | `Consensus/Invariant/Defs.lean` | Small |
| X7-C | — | **Prove slot monotonicity preservation.** `processSlots_preserves_slotMonotone`, `processBlockHeader_preserves_slotMonotone`, `processAttestations_preserves_slotMonotone`, `stateTransition_preserves_slotMonotone`. Each operation maintains `slotMonotone`. ~40 lines | `StateTransition/Proofs/SlotMonotonicity.lean` | Small |
| X7-D | — | **Prove history append-only property.** `processBlockHeader_history_extends : processBlockHeader s b = .ok s' → ∀ i < s.historicalBlockHashes.length, s'.historicalBlockHashes[i]! = s.historicalBlockHashes[i]!`. No existing history entry is overwritten — only new entries are appended. ~40 lines | `StateTransition/Proofs/HistoryAppendOnly.lean` | Small |
| X7-E | — | **Prove finalization monotonicity.** `stateTransition_finalization_monotone : stateTransition s b sig = .ok s' → s'.latestFinalized.slot ≥ s.latestFinalized.slot`. The finalized checkpoint slot never decreases across any state transition. This is the core irreversibility guarantee. Proof strategy: show processAttestations only advances finalization (via the continuous justification chain check), and processSlots/processBlockHeader don't touch latestFinalized. ~50 lines | `StateTransition/Proofs/FinalizationSafety.lean` | Medium |
| X7-F | — | **Prove justified ≥ finalized invariant.** `stateTransition_preserves_justifiedGeFinalized : justifiedGeFinalized s → stateTransition s b sig = .ok s' → justifiedGeFinalized s'`. The justified checkpoint is always at least as recent as the finalized one. Proof: when finalization advances to a new checkpoint, that checkpoint was previously justified, so justification is at least as high. ~40 lines | `StateTransition/Proofs/JustifiedGeFinalized.lean` | Small |
| X7-G | — | **Prove supermajority safety lemma.** `supermajority_unique : supermajorityThreshold v₁ n → supermajorityThreshold v₂ n → v₁ + v₂ > n → ∃ validator, votedFor₁ validator ∧ votedFor₂ validator`. If two conflicting proposals both achieve 2/3 supermajority, at least one validator voted for both (pigeonhole). This is the fundamental Byzantine safety argument. ~30 lines | `StateTransition/Proofs/SupermajoritySafety.lean` | Small |
| X7-H | — | **Prove 3SF-mini finalization safety (KEYSTONE THEOREM).** `threeSFMiniSafety : ∀ s₁ s₂ : State, commonAncestor s₁ s₂ → supermajorityHonest s₁.validators → s₁.latestFinalized = cp₁ → s₂.latestFinalized = cp₂ → cp₁.root ≠ cp₂.root → cp₁.slot ≠ cp₂.slot → False`. **Informal proof sketch**: Two finalized blocks at different slots require two continuous justification chains. Each justification requires 2/3 vote. By supermajority_unique, the voting sets must overlap. But an honest validator only attests to one chain → contradiction. The 3SF-mini justifiable slot pattern ensures chain continuity. ~80 lines | `StateTransition/Proofs/ThreeSFMini.lean` | Large |
| X7-I | — | **Define and prove consensus invariant bundle.** `consensusInvariantBundle (s : State) : Prop := slotMonotone s ∧ justifiedGeFinalized s ∧ historyConsistent s ∧ validatorsStable s ∧ finalizationImpliesJustification s`. Prove `genesis_satisfies_bundle : consensusInvariantBundle (generateGenesis t vs)`. Prove `stateTransition_preserves_bundle : consensusInvariantBundle s → stateTransition s b sig = .ok s' → consensusInvariantBundle s'`. ~60 lines | `Consensus/Invariant/Composition.lean` | Medium |
| X7-J | — | **Prove top-level safety theorem.** `consensusSafety : ∀ trace : List Block, validTrace genesis trace → let finalState := applyTrace genesis trace; consensusInvariantBundle finalState ∧ (∀ otherTrace, validTrace genesis otherTrace → let otherFinal := applyTrace genesis otherTrace; ¬conflictingFinalization finalState otherFinal)`. This combines the invariant bundle preservation with 3SF-mini safety to state: any valid trace from genesis produces a state that does not conflict with any other valid trace's finalization. ~50 lines | `Consensus/Invariant/Safety.lean` | Medium |
| X7-K | — | **Prove liveness under honest supermajority (conditional).** `consensusLiveness : ∀ s : State, consensusInvariantBundle s → honestSupermajority s.validators → ∃ b : Block, stateTransition s b true = .ok s' ∧ s'.latestFinalized.slot > s.latestFinalized.slot` (eventually, finalization advances). This is conditional on honest behavior — formalized as "there exists a valid block that honest validators can produce". ~50 lines | `Consensus/Invariant/Liveness.lean` | Medium |

**Intra-phase ordering constraints:**
- X7-A, X7-B before X7-C–F (definitions before proofs)
- X7-G before X7-H (supermajority lemma before 3SF-mini)
- X7-C–F before X7-I (individual preservation before bundle)
- X7-H, X7-I before X7-J (safety + bundle before top-level)

**Exit criteria:**
- 3SF-mini safety theorem proved (the keystone)
- Consensus invariant bundle preserved across all operations
- Finalization monotonicity proved
- Top-level safety theorem combining all properties
- Zero sorry in all proof files

---

### Phase X8: Fork Choice (LMD GHOST) (v0.25.3–v0.25.4)

Formalize the fork choice algorithm — the local decision rule each validator
uses to select the canonical chain head. LMD GHOST (Latest Message Driven
Greedy Heaviest Observed SubTree) is the mechanism that ensures all honest
validators converge on the same chain view.

**New files**: `LeanEth/Consensus/ForkChoice/*.lean`

**Ref**: `src/lean_spec/subspecs/forkchoice/store.py`

| ID | Ref | Description | Files | Est. |
|----|-----|-------------|-------|------|
| X8-A | LS-forkchoice/store | **Define `Store` structure.** `structure Store where time : Uint64; config : Config; head : Bytes32; safeTarget : Bytes32; latestJustified : Checkpoint; latestFinalized : Checkpoint; blocks : HashMap Bytes32 Block; states : HashMap Bytes32 State; validatorId : Option ValidatorIndex; attestationSignatures : HashMap AttestationData (List AttestationSignatureEntry); latestNewAggregatedPayloads : HashMap AttestationData (List AggregatedSignatureProof); latestKnownAggregatedPayloads : HashMap AttestationData (List AggregatedSignatureProof)`. `structure AttestationSignatureEntry where validatorId : ValidatorIndex; signature : Signature`. ~40 lines | `ForkChoice/Store.lean` | Small |
| X8-B | LS-forkchoice/store | **Define `Store.fromAnchor`.** `fromAnchor : State → Block → Option ValidatorIndex → Except ForkChoiceError Store` — initialize from anchor state and block. Validates `anchor_block.stateRoot = hashTreeRoot state`. Computes `anchorRoot = hashTreeRoot anchor_block`. Sets head, safeTarget, justified, finalized to anchor. ~30 lines | `ForkChoice/Store.lean` | Small |
| X8-C | LS-forkchoice/store | **Define attestation validation.** `validateAttestation : Store → Attestation → Except ForkChoiceError Unit`. Checks: (1) source, target, head blocks exist in store, (2) source.slot < target.slot, (3) head is at least as recent as source and target, (4) checkpoint slots match block slots, (5) vote is not for a future slot. ~40 lines | `ForkChoice/AttestationProcessing.lean` | Small |
| X8-D | — | **Define LMD GHOST head selection.** `lmdGhost : Store → Bytes32` — starting from justified checkpoint root, at each fork choose the child with the most recent attestation weight. Terminate when reaching a leaf. Weight function counts latest attestations per validator (each validator's most recent vote counts once). ~60 lines | `ForkChoice/LMDGHOST.lean` | Medium |
| X8-E | — | **Define store update operations.** `onBlock : Store → SignedBlock → State → Except ForkChoiceError Store` (add block + post-state, update justified/finalized if advanced). `onAttestation : Store → Attestation → Except ForkChoiceError Store` (validate + store attestation). `onTick : Store → Uint64 → Store` (advance time). `pruneStaleAttestationData : Store → Store` (remove finalized attestations). ~60 lines | `ForkChoice/Store.lean` | Small |
| X8-F | — | **Prove head is descendant of finalized.** `lmdGhost_descendant_of_finalized : ∀ store, storeConsistent store → isDescendant store.blocks (lmdGhost store) store.latestFinalized.root`. The selected head always extends the finalized chain — LMD GHOST never selects a fork that contradicts finalization. ~40 lines | `ForkChoice/Proofs/HeadValidity.lean` | Medium |
| X8-G | — | **Prove store consistency preservation.** `onBlock_preserves_consistency`, `onAttestation_preserves_consistency`, `onTick_preserves_consistency`. Define `storeConsistent` predicate: all referenced blocks exist, justified/finalized roots are in store, block parent chains are valid. ~50 lines | `ForkChoice/Proofs/Consistency.lean` | Small |
| X8-H | — | **Prove LMD GHOST convergence (conditional).** `lmdGhost_convergence : honestSupermajority validators → ∀ store₁ store₂, sameAttestations store₁ store₂ → lmdGhost store₁ = lmdGhost store₂`. Under honest supermajority with the same attestation set, all stores converge to the same head. ~50 lines | `ForkChoice/Proofs/Convergence.lean` | Medium |
| X8-I | — | **Fork choice test suite.** Create `tests/ForkChoiceSuite.lean` with scenarios: simple chain (no forks), single fork (two competing blocks), attestation-driven reorg, justification advancement, finalization pruning. Compare head selection against Python reference. ~50 lines | `tests/ForkChoiceSuite.lean` | Small |

**Exit criteria:**
- LMD GHOST algorithm correctly selects chain head
- Head always descends from finalized block (proved)
- Store consistency preserved across all operations
- Convergence under honest supermajority (proved)
- Fork choice test suite passes

---

### Phase X9: Snappy Compression & Networking Types (v0.26.0)

Formalize the Snappy compression algorithm (used for Ethereum P2P message
encoding) and define the networking type abstractions. The Lean formalization
provides roundtrip correctness proofs; the actual networking implementation
will be in Rust.

**New files**: `LeanEth/Crypto/Snappy/*.lean`, `LeanEth/Node/Networking/*.lean`

**Ref**: `src/lean_spec/snappy/`, `src/lean_spec/subspecs/networking/`

| ID | Ref | Description | Files | Est. |
|----|-----|-------------|-------|------|
| X9-A | LS-snappy/compress | **Define Snappy raw block compression.** `compress : ByteArray → ByteArray` — implement Snappy block compression (literal copies, length-offset backreferences). Define internal types: `inductive SnappyOp | literal : ByteArray → SnappyOp | copy : (offset : Nat) → (length : Nat) → SnappyOp`. ~60 lines | `Crypto/Snappy/Compress.lean` | Small |
| X9-B | LS-snappy/decompress | **Define Snappy raw block decompression.** `decompress : ByteArray → Except SnappyError ByteArray` — decode compressed blocks, resolve backreferences. Handle error cases: invalid offset, length exceeds buffer, truncated input. ~50 lines | `Crypto/Snappy/Decompress.lean` | Small |
| X9-C | LS-snappy/framing | **Define Snappy framing format.** `frameCompress : ByteArray → ByteArray` (streaming format with chunk headers). `frameDecompress : ByteArray → Except SnappyError ByteArray`. Used for Ethereum network messages. ~40 lines | `Crypto/Snappy/Framing.lean` | Small |
| X9-D | — | **Prove Snappy roundtrip correctness.** `snappy_roundtrip : ∀ data, decompress (compress data) = .ok data`. `frame_roundtrip : ∀ data, frameDecompress (frameCompress data) = .ok data`. ~40 lines | `Crypto/Snappy/Proofs.lean` | Small |
| X9-E | LS-networking | **Define networking type abstractions.** `structure PeerId where bytes : Bytes32`. `inductive NetworkMessage | gossipBlock : SignedBlock → NetworkMessage | gossipAttestation : SignedAttestation → NetworkMessage | reqRespBlocksByRange : Slot → Uint64 → NetworkMessage | reqRespBlocksByRoot : List Bytes32 → NetworkMessage | statusMessage : Checkpoint → Checkpoint → NetworkMessage`. `inductive SubnetId where mk : Uint64 → SubnetId`. ~40 lines | `Node/Networking/Transport.lean` | Small |
| X9-F | LS-networking/enr | **Define ENR (Ethereum Node Record) encoding.** `structure ENR where seq : Uint64; pairs : List (String × ByteArray); signature : ByteArray`. `encodeENR : ENR → ByteArray` (RLP encoding using X1-M). `decodeENR : ByteArray → Except ENRError ENR`. ~40 lines | `Node/Networking/ENR.lean` | Small |
| X9-G | LS-networking/gossipsub | **Define Gossipsub topic abstractions.** `structure Topic where name : String`. `inductive GossipsubAction | subscribe : Topic → GossipsubAction | unsubscribe : Topic → GossipsubAction | publish : Topic → ByteArray → GossipsubAction | receive : Topic → ByteArray → PeerId → GossipsubAction`. Define consensus topics: `beaconBlock`, `beaconAttestation`, `aggregateAttestation`. ~30 lines | `Node/Networking/Gossipsub.lean` | Small |
| X9-H | LS-networking/reqresp | **Define request-response protocol types.** `inductive ReqRespMethod | blocksByRange | blocksByRoot | status | metadata | ping | goodbye`. `structure ReqRespMessage where method : ReqRespMethod; payload : ByteArray`. SSZ-encode payloads with Snappy compression (composing X9-A with SSZ serialization). ~30 lines | `Node/Networking/ReqResp.lean` | Small |
| X9-I | LS-networking/discovery | **Define peer discovery types (discv5).** `structure DiscoveryConfig where bootstrapNodes : List ENR; listenPort : Uint16; maxPeers : Nat`. `structure RoutingTable where buckets : Array (List PeerId)`. Abstract interface — actual implementation in Rust. ~30 lines | `Node/Networking/Discovery.lean` | Small |

**Exit criteria:**
- Snappy compression/decompression roundtrip proved
- All networking types defined with SSZ serialization
- ENR encoding matches RLP specification
- Zero sorry in Snappy and networking modules

---

### Phase X10: Node Services — Chain, Validator, Sync (v0.26.1–v0.26.2)

Formalize the node service layer that orchestrates consensus operations: slot
clock, validator duties, synchronization, and storage. These are the
higher-level abstractions that connect the pure consensus logic to the outside
world (via Rust ABI boundaries).

**New files**: `LeanEth/Node/*.lean`

**Ref**: `src/lean_spec/subspecs/chain/`, `src/lean_spec/subspecs/validator/`,
`src/lean_spec/subspecs/sync/`, `src/lean_spec/subspecs/storage/`,
`src/lean_spec/subspecs/api/`, `src/lean_spec/subspecs/node/`

| ID | Ref | Description | Files | Est. |
|----|-----|-------------|-------|------|
| X10-A | LS-chain/clock | **Define `SlotClock`.** `structure SlotClock where genesisTime : Uint64; secondsPerSlot : Nat; intervalsPerSlot : Nat`. `currentSlot : SlotClock → Uint64 → Slot` (wallclock → slot). `currentInterval : SlotClock → Uint64 → Nat` (sub-slot position). `slotStartTime : SlotClock → Slot → Uint64`. Prove `currentSlot_monotone : t₁ ≤ t₂ → currentSlot clock t₁ ≤ currentSlot clock t₂`. ~40 lines | `Node/Chain/SlotClock.lean` | Small |
| X10-B | LS-chain/config | **Define chain service configuration.** Re-export chain constants from X5-E. Add `structure ChainConfig where slotClock : SlotClock; genesisState : State; genesisBlock : Block`. `initChainService : ChainConfig → Except ChainError ChainState`. ~20 lines | `Node/Chain/Config.lean` | Trivial |
| X10-C | LS-chain/service | **Define `ChainService` state machine.** `structure ChainState where store : Store; currentSlot : Slot; synced : Bool`. `onSlotBoundary : ChainState → Slot → ChainState` (advance slot, trigger duties). `onNewBlock : ChainState → SignedBlock → Except ChainError ChainState` (validate, apply state transition, update store). `onNewAttestation : ChainState → SignedAttestation → Except ChainError ChainState`. ~50 lines | `Node/Chain/Service.lean` | Small |
| X10-D | LS-validator/service | **Define `ValidatorService`.** `structure ValidatorState where registry : ValidatorRegistry; currentDuties : List ValidatorDuty`. `inductive ValidatorDuty | proposeBlock : Slot → ValidatorIndex → ValidatorDuty | attest : Slot → ValidatorIndex → ValidatorDuty`. `scheduleDuties : ValidatorState → Slot → List ValidatorDuty` (based on proposer selection and committee assignment). ~40 lines | `Node/Validator/Service.lean` | Small |
| X10-E | LS-validator/registry | **Define `ValidatorRegistry`.** `structure ValidatorRegistry where keys : HashMap ValidatorIndex KeyPair; scheme : GeneralizedXmssScheme`. `signBlock : ValidatorRegistry → ValidatorIndex → Block → Except ValidatorError SignedBlock`. `signAttestation : ValidatorRegistry → ValidatorIndex → AttestationData → Except ValidatorError SignedAttestation`. Abstract key loading — concrete implementation in Rust. ~40 lines | `Node/Validator/Registry.lean` | Small |
| X10-F | LS-sync/service | **Define `SyncService` state machine.** `inductive SyncPhase | checkpointSync | headSync | backfillSync | synced`. `structure SyncState where phase : SyncPhase; peers : List PeerId; pendingBlocks : BlockCache`. `onPeerConnected`, `onBlockReceived`, `onSyncComplete` transitions. ~40 lines | `Node/Sync/Service.lean` | Small |
| X10-G | LS-sync/checkpoint | **Define checkpoint sync.** `checkpointSync : SyncState → Checkpoint → List PeerId → SyncState` — download state at weak subjectivity checkpoint. Validate: state root matches checkpoint, apply state transition forward. ~30 lines | `Node/Sync/CheckpointSync.lean` | Small |
| X10-H | LS-sync/head_sync | **Define head sync and backfill.** `headSync : SyncState → List SignedBlock → SyncState` — process recently received blocks in order. `backfillSync : SyncState → Slot → Slot → List PeerId → SyncState` — request historical blocks by range. ~30 lines | `Node/Sync/HeadSync.lean` | Small |
| X10-I | LS-sync/block_cache | **Define `BlockCache`.** `structure BlockCache where pending : HashMap Bytes32 SignedBlock; ordered : List Bytes32`. `insert : BlockCache → SignedBlock → BlockCache`. `popReady : BlockCache → Bytes32 → Option (SignedBlock × BlockCache)` (return next block if parent matches). ~30 lines | `Node/Sync/BlockCache.lean` | Small |
| X10-J | LS-sync/peer_manager | **Define `PeerManager`.** `structure PeerManager where connected : HashMap PeerId PeerInfo; maxPeers : Nat`. `structure PeerInfo where enr : ENR; status : PeerStatus; score : Int`. `inductive PeerStatus | connected | disconnected | banned`. Peer scoring: increment on good blocks, decrement on invalid messages. ~30 lines | `Node/Sync/PeerManager.lean` | Small |
| X10-K | LS-storage | **Define storage interface.** `class Database (db : Type) where get : db → Namespace → ByteArray → IO (Option ByteArray); put : db → Namespace → ByteArray → ByteArray → IO Unit; delete : db → Namespace → ByteArray → IO Unit`. `inductive Namespace | blocks | states | checkpoints | metadata`. Abstract interface — SQLite implementation in Rust. ~30 lines | `Node/Storage/Interface.lean` | Small |
| X10-L | LS-api | **Define API endpoint types.** `inductive APIEndpoint | getState : Bytes32 → APIEndpoint | getBlock : Bytes32 → APIEndpoint | getForkChoice → APIEndpoint | getHealth → APIEndpoint | getCheckpoints → APIEndpoint`. `structure APIResponse where status : Nat; body : ByteArray`. Route dispatch: `handleRequest : ChainState → APIEndpoint → APIResponse`. ~40 lines | `Node/API/Endpoints.lean` | Small |
| X10-M | LS-node | **Define top-level `Node` orchestrator.** `structure NodeConfig where chain : ChainConfig; validator : Option ValidatorRegistry; network : NetworkConfig; storage : DatabaseConfig`. `structure NodeState where chain : ChainState; validator : Option ValidatorState; sync : SyncState; peers : PeerManager`. `processEvent : NodeState → NodeEvent → Except NodeError NodeState` where `inductive NodeEvent | tick : Uint64 → NodeEvent | blockReceived : SignedBlock → NodeEvent | attestationReceived : SignedAttestation → NodeEvent | peerConnected : PeerId → NodeEvent | ...`. ~50 lines | `Node/Node.lean` | Small |
| X10-N | — | **Node service test suite.** Create test scenarios: slot advancement, block proposal duty triggered at correct slot, attestation duty at correct interval, sync state machine transitions, peer scoring. ~40 lines | `tests/NodeServiceSuite.lean` | Small |

**Exit criteria:**
- All node services compile with deterministic state machines
- Slot clock monotonicity proved
- Duty scheduling matches proposer selection from consensus layer
- Sync state machine covers all phases
- Zero sorry in node modules

---

### Phase X11: Rust ABI Layer (v0.27.0–v0.27.2)

Build the Rust safety layer following seLe4n's proven pattern: `no_std` crates
with minimal `unsafe`, cross-validated against the Lean reference implementation.
The Rust layer handles networking I/O, persistent storage, and OS interaction —
everything the pure Lean model cannot do.

**New directories**: `rust/leaneth-types/`, `rust/leaneth-net/`,
`rust/leaneth-storage/`

**Ref**: seLe4n `rust/sele4n-types/`, `rust/sele4n-abi/`, `rust/sele4n-sys/`
(pattern reference); leanSpec `src/lean_spec/subspecs/networking/`,
`src/lean_spec/subspecs/storage/`

| ID | Ref | Description | Files | Est. |
|----|-----|-------------|-------|------|
| X11-A | — | **Create `leaneth-types` crate skeleton.** `no_std` Rust crate mirroring Lean type definitions. Newtype wrappers: `Slot(u64)`, `ValidatorIndex(u64)`, `Bytes32([u8; 32])`, `Checkpoint { root: Bytes32, slot: Slot }`. Error type: `ConsensusError` enum (34+ variants mirroring Lean). `Cargo.toml` with `#![no_std]`, `#![forbid(unsafe_code)]`. ~80 lines | `rust/leaneth-types/` | Small |
| X11-B | — | **SSZ codec in Rust.** `SszEncode` and `SszDecode` traits with `encode(&self) -> Vec<u8>` and `decode(bytes: &[u8]) -> Result<Self, SszError>`. Derive macros for structs (Container pattern). Implement for all primitive types (u8..u64, bool, [u8; N]). Implement for `Vec<T>` (SSZList) and `[T; N]` (SSZVector). ~120 lines | `rust/leaneth-types/src/ssz.rs` | Medium |
| X11-C | — | **SSZ Merkleization in Rust.** `hash_tree_root<T: SszHashable>(value: &T) -> Bytes32`. `merkleize(chunks: &[Bytes32], limit: Option<usize>) -> Bytes32`. Pre-computed zero hashes. Must produce identical output to Lean `hashTreeRoot` for all types. ~80 lines | `rust/leaneth-types/src/merkle.rs` | Small |
| X11-D | — | **Create `leaneth-net` crate skeleton.** Networking crate using `libp2p` (Rust). QUIC transport, gossipsub, discv5, req-resp. Define `NetworkConfig`, `NetworkService`, `NetworkEvent`. Single `unsafe` block for QUIC TLS initialization (if required by library). Target: connect to Ethereum consensus P2P network. ~100 lines skeleton | `rust/leaneth-net/` | Medium |
| X11-E | — | **Implement gossipsub handler.** Subscribe to consensus topics: `/eth2/beacon_block/ssz_snappy`, `/eth2/beacon_attestation_{subnet}/ssz_snappy`, `/eth2/beacon_aggregate_and_proof/ssz_snappy`. Decode SSZ+Snappy payloads. Route to Lean consensus functions via FFI boundary. ~80 lines | `rust/leaneth-net/src/gossipsub.rs` | Small |
| X11-F | — | **Implement req-resp handler.** Handle: `BlocksByRange`, `BlocksByRoot`, `Status`, `Metadata`, `Ping`, `Goodbye`. SSZ+Snappy encode/decode. Rate limiting per peer. ~60 lines | `rust/leaneth-net/src/reqresp.rs` | Small |
| X11-G | — | **Implement discv5 peer discovery.** UDP-based discovery using `discv5` crate. ENR encoding/decoding (must match Lean X9-F). Bootstrap node list configuration. Automatic peer discovery and connection. ~60 lines | `rust/leaneth-net/src/discovery.rs` | Small |
| X11-H | — | **Create `leaneth-storage` crate.** SQLite persistence layer using `rusqlite`. Namespace isolation (blocks, states, checkpoints, metadata). WAL mode for concurrent reads. Batch writes for block import. Interface matches Lean `Database` typeclass from X10-K. ~80 lines | `rust/leaneth-storage/` | Small |
| X11-I | — | **Define Lean↔Rust FFI boundary.** Define the C ABI bridge between Lean and Rust. Functions: `lean_on_block(block_bytes: *const u8, len: usize) -> i32`, `lean_on_attestation(...)`, `lean_get_head() -> Bytes32`, `lean_get_state(root: Bytes32, out: *mut u8) -> i32`. Exactly 2 `unsafe` blocks: FFI boundary crossing (both directions). All data passes as SSZ-encoded byte arrays — no pointer sharing. ~60 lines | `rust/leaneth-net/src/ffi.rs` | Small |
| X11-J | — | **Cross-validation test suite (XVAL).** Following seLe4n's XVAL pattern: Lean trace harness produces expected SSZ encodings and hash tree roots; Rust test suite independently computes the same values and compares. Cover: all consensus container SSZ encodings, Merkle roots, Snappy compression, state transition outputs. Minimum 20 XVAL test cases. ~80 lines | `rust/tests/xval.rs`, `tests/XvalSuite.lean` | Medium |
| X11-K | — | **Unsafe audit and documentation.** Document every `unsafe` block with: (1) why it's necessary, (2) what invariants it relies on, (3) how the invariant is maintained. Target: ≤ 3 `unsafe` blocks total across all Rust crates. Create `rust/SAFETY_AUDIT.md`. ~30 lines | `rust/SAFETY_AUDIT.md` | Trivial |

**Exit criteria:**
- Three Rust crates compile with `cargo build --release`
- SSZ codec produces identical output to Lean for all types (XVAL)
- Networking crate connects to devnet peers
- Storage crate reads/writes blocks correctly
- ≤ 3 `unsafe` blocks with documented justification
- Cross-validation suite passes (≥ 20 XVAL cases)

---

### Phase X12: Executable Trace Harness & Testing Infrastructure (v0.27.3)

Build the executable trace harness and testing infrastructure, mirroring
seLe4n's four-tier validation pipeline. This creates the "executable
specification" that demonstrates the Lean formalization produces correct
consensus behavior.

**New files**: `LeanEth/Testing/*.lean`, `tests/*.lean`, `scripts/*.sh`

| ID | Ref | Description | Files | Est. |
|----|-----|-------------|-------|------|
| X12-A | — | **Create consensus trace harness.** `LeanEth/Testing/TraceHarness.lean` — executable main that: (1) generates genesis state from test config, (2) applies a sequence of test blocks, (3) prints state transitions in pipe-delimited format: `[SCENARIO-ID] | SUBSYSTEM | action | result`. Mirror seLe4n's `MainTraceHarness.lean` pattern. ~80 lines | `Testing/TraceHarness.lean` | Small |
| X12-B | — | **Create state builder for tests.** `LeanEth/Testing/StateBuilder.lean` — helpers: `buildGenesisState : Nat → State` (create genesis with N validators), `buildTestBlock : State → List Attestation → Block`, `buildTestAttestation : State → ValidatorIndex → AttestationData`, `applyBlocks : State → List Block → Except ConsensusError State`. ~60 lines | `Testing/StateBuilder.lean` | Small |
| X12-C | — | **Create fixture comparison framework.** `LeanEth/Testing/Fixtures.lean` — `compareOutput : String → String → Bool` (compare actual vs expected trace). `loadFixture : String → IO String`. `assertFixtureMatch : String → String → IO Unit`. ~30 lines | `Testing/Fixtures.lean` | Small |
| X12-D | — | **Create golden trace fixture.** `tests/fixtures/consensus_trace_smoke.expected` — golden output from the trace harness for a canonical test scenario: genesis → 5 blocks with attestations → justification → finalization. ~40 lines | `tests/fixtures/` | Small |
| X12-E | — | **Create scenario registry.** `tests/fixtures/scenario_registry.yaml` — YAML metadata for all test scenarios: ID, description, subsystem, source function, expected outcome. Mirror seLe4n's registry format. ~30 lines | `tests/fixtures/` | Trivial |
| X12-F | — | **Create test_tier0_hygiene.sh.** Tier 0: shellcheck on scripts, YAML validation, traceability tag consistency. ~30 lines | `scripts/test_tier0_hygiene.sh` | Trivial |
| X12-G | — | **Create test_tier1_build.sh.** Tier 1: `lake build LeanEth` + `cargo build --release` (Rust crates). ~20 lines | `scripts/test_tier1_build.sh` | Trivial |
| X12-H | — | **Create test_smoke.sh (Tier 0+1+2).** Tier 2: run trace harness, compare against golden fixture. Run SSZ roundtrip suite. Run state transition suite. Run negative-state tests (invalid blocks, wrong proposer, bad signatures). ~40 lines | `scripts/test_smoke.sh` | Small |
| X12-I | — | **Create test_full.sh (Tier 0-3).** Tier 3: `#check` validation of anchor theorems (3SF-mini safety, finalization monotonicity, SSZ roundtrip). ~30 lines | `scripts/test_full.sh` | Small |
| X12-J | — | **Create negative-state test suite.** `tests/NegativeStateSuite.lean` — verify all error paths: invalid slot (error), wrong proposer (error), bad parent root (error), bad state root (error), future attestation (filtered), double-justified target (filtered), non-justifiable slot (filtered). Minimum 15 negative test cases. ~60 lines | `tests/NegativeStateSuite.lean` | Small |
| X12-K | — | **Integrate into seLe4n lakefile.** Add `LeanEth` as a separate library target in the shared `lakefile.toml`. Ensure `lake build` builds both `SeLe4n` and `LeanEth`. Add `leaneth` executable target for the trace harness. ~15 lines | `lakefile.toml` | Trivial |

**Exit criteria:**
- Trace harness produces golden output matching fixture
- All four test tiers pass
- Negative-state suite covers all error paths
- `lake build LeanEth` succeeds alongside `lake build SeLe4n`
- Scenario registry documents all test cases

---

### Phase X13: seLe4n Integration Bridge (v0.28.0–v0.28.1)

Connect the Lean Ethereum consensus client to the seLe4n microkernel. This
creates the bridge that allows the verified consensus client to run as a
verified process on a verified kernel — the ultimate goal of the project.

**New files**: `LeanEth/Bridge/*.lean`, extensions to `SeLe4n/Platform/`

| ID | Ref | Description | Files | Est. |
|----|-----|-------------|-------|------|
| X13-A | — | **Define shared prelude.** `LeanEth/Bridge/SharedPrelude.lean` — shared typed identifiers between seLe4n and LeanEth: `Bytes32` (used by both for hashing), `PAddr`/`VAddr` (kernel memory), `ObjId` (kernel objects). Import both `SeLe4n.Prelude` and `LeanEth.Prelude`. Define conversion functions with correctness proofs. ~40 lines | `Bridge/SharedPrelude.lean` | Small |
| X13-B | — | **Define Ethereum node platform contract.** `LeanEth/Bridge/PlatformContract.lean` — typeclass `EthNodePlatformBinding` extending `PlatformBinding` with: `networkAvailable : Prop` (network I/O is accessible), `storageAvailable : Prop` (persistent storage is accessible), `timerAvailable : Prop` (wall clock is accessible), `maxPeers : Nat` (resource limit). ~30 lines | `Bridge/PlatformContract.lean` | Small |
| X13-C | — | **Define IPC bridge to seLe4n kernel.** `LeanEth/Bridge/SeLe4nIntegration.lean` — the consensus client communicates with the kernel via seLe4n IPC endpoints. Define: `sendToKernel : ObjId → ByteArray → KernelM Unit` (send message via endpoint capability), `recvFromKernel : ObjId → KernelM ByteArray` (receive via endpoint). Map consensus events to kernel IPC messages. ~50 lines | `Bridge/SeLe4nIntegration.lean` | Small |
| X13-D | — | **Define resource management bridge.** Map Ethereum consensus resource requirements to seLe4n capabilities: (1) memory for block/state storage → VSpace mappings, (2) network I/O → device capabilities, (3) timer access → platform timer capability. Define `EthNodeCapabilities` structure listing required capabilities. ~30 lines | `Bridge/SeLe4nIntegration.lean` | Small |
| X13-E | — | **Prove bridge safety.** (1) `bridge_preserves_kernel_invariants : ∀ ks ethEvent, kernelInvariantBundle ks → processEthEvent ks ethEvent = .ok ks' → kernelInvariantBundle ks'`. The Ethereum client cannot violate kernel invariants. (2) `bridge_preserves_consensus_invariants : ∀ cs kernelEvent, consensusInvariantBundle cs → processKernelEvent cs kernelEvent = .ok cs' → consensusInvariantBundle cs'`. Kernel events cannot violate consensus invariants. ~60 lines | `Bridge/Proofs.lean` | Medium |
| X13-F | — | **Define Ethereum node lifecycle.** `initEthNode : NodeConfig → KernelM NodeState` (create node process with required capabilities). `shutdownEthNode : NodeState → KernelM Unit` (release capabilities, flush storage). `ethNodeMainLoop : NodeState → KernelM NodeState` (process one event: timer tick, network message, or IPC from kernel). ~40 lines | `Bridge/SeLe4nIntegration.lean` | Small |
| X13-G | — | **RPi5 platform binding for Ethereum node.** Extend `SeLe4n/Platform/RPi5/` with Ethernet NIC abstraction for networking, SD card storage abstraction for persistence. Define hardware address ranges for BCM2712 Ethernet controller. ~40 lines | `SeLe4n/Platform/RPi5/EthNode.lean` | Small |
| X13-H | — | **Integration test suite.** Test: kernel boots → creates Ethereum node process → node initializes genesis state → processes test blocks via IPC → state transitions are correct → node shuts down cleanly. ~50 lines | `tests/IntegrationSuite.lean` | Small |

**Exit criteria:**
- Bridge compiles with both SeLe4n and LeanEth imports
- Kernel invariants proved preserved across bridge
- Consensus invariants proved preserved across bridge
- Integration test demonstrates end-to-end flow
- Zero sorry in bridge modules

---

### Phase X14: Documentation, Audit, & Closure (v0.29.0)

Final phase: documentation synchronization, comprehensive audit, spec coverage
verification, and workstream closure. Ensures the formalization is complete,
well-documented, and ready for production use.

| ID | Ref | Description | Files | Est. |
|----|-----|-------------|-------|------|
| X14-A | — | **Spec coverage audit.** Generate traceability matrix: every Python function in leanSpec → corresponding Lean definition. Identify any gaps. Target: 100% coverage of consensus-critical functions (state transition, fork choice, attestation processing). Document coverage in `docs/LEAN_ETH_SPEC_COVERAGE.md`. ~60 lines | `docs/LEAN_ETH_SPEC_COVERAGE.md` | Small |
| X14-B | — | **Proof inventory.** Catalog all theorems/lemmas proved: safety properties, roundtrip proofs, invariant preservation, correctness properties. Generate statistics: total theorem count, lines of proof, axiom inventory. Update `docs/codebase_map.json`. ~40 lines | `docs/codebase_map.json` | Small |
| X14-C | — | **Update SELE4N_SPEC.md.** Add Ethereum consensus client section: architecture, safety guarantees, integration bridge, Rust ABI layer. ~30 lines | `docs/spec/SELE4N_SPEC.md` | Small |
| X14-D | — | **Update DEVELOPMENT.md.** Add build/test instructions for LeanEth modules. Document Rust crate build process. Add contribution guidelines for consensus-layer work. ~30 lines | `docs/DEVELOPMENT.md` | Small |
| X14-E | — | **Update README.md.** Add Ethereum consensus client metrics: Lean LoC, theorem count, test count, Rust crate count. Update architecture diagram. ~20 lines | `README.md` | Trivial |
| X14-F | — | **Update WORKSTREAM_HISTORY.md.** Record WS-X completion: all 14 phases, sub-task counts, version history, key theorems proved. ~30 lines | `docs/WORKSTREAM_HISTORY.md` | Small |
| X14-G | — | **Update CLAIM_EVIDENCE_INDEX.md.** Add claims for consensus safety (3SF-mini theorem), SSZ correctness (roundtrip proofs), XMSS soundness (sign/verify correctness). ~20 lines | `docs/CLAIM_EVIDENCE_INDEX.md` | Trivial |
| X14-H | — | **Create GitBook chapter.** `docs/gitbook/15-ethereum-consensus-formalization.md` — public-facing documentation of the Lean Ethereum formalization: motivation, architecture, key theorems, how to build and test. ~60 lines | `docs/gitbook/` | Small |
| X14-I | — | **Final sorry/axiom audit.** Grep entire LeanEth codebase for `sorry` and `axiom`. Verify: 0 sorry, exactly 3 axioms (AXIOM-CRYPTO-1: hash collision resistance, AXIOM-CRYPTO-2: XMSS EU-CMA security, AXIOM-CRYPTO-3: Poseidon2 algebraic security). Document each axiom with justification. ~20 lines | Audit output | Trivial |
| X14-J | — | **Run full validation pipeline.** Execute `test_full.sh` on complete codebase. Verify all tiers pass. Verify cross-validation (XVAL) passes. Verify integration test passes. Record timing and resource metrics. ~15 lines | CI output | Trivial |
| X14-K | — | **Update website link manifest.** Add new file paths to `scripts/website_link_manifest.txt` to prevent 404s on the project website. ~10 lines | `scripts/website_link_manifest.txt` | Trivial |

**Exit criteria:**
- 100% spec coverage for consensus-critical functions
- Zero sorry, exactly 3 documented axioms
- All documentation synchronized
- Full test pipeline passes
- Workstream history updated
- GitBook chapter published

## 7. Phase Dependency Graph

```
X1 (Types)
 ├── X2 (SSZ Merkle) ──────────────────────────────────────────┐
 │    └── X5 (Consensus Containers) ───┐                       │
 │         ├── X6 (State Transition) ──┤                       │
 │         │    └── X7 (Safety Proofs) │  ← KEYSTONE           │
 │         │         └── X8 (Fork Choice)                      │
 │         │              └── X10 (Node Services)              │
 │         │                   └── X12 (Testing)               │
 │         │                        └── X14 (Documentation)    │
 │         └── X9 (Snappy + Networking Types)                  │
 │              └── X10 (Node Services)                        │
 ├── X3 (KoalaBear + Poseidon2) ──┐                           │
 │    └── X4 (XMSS) ─────────────┘                            │
 │         └── X5 (Consensus Containers) ──[via signatures]    │
 └── X11 (Rust ABI) ──────────────────────────────────────────┘
      └── X12 (Testing / XVAL)
           └── X13 (seLe4n Bridge)
                └── X14 (Documentation)
```

**Critical path**: X1 → X2 → X5 → X6 → X7 (3SF-mini safety proof)

**Parallelizable work**:
- X3 + X4 (crypto) can proceed in parallel with X2 (SSZ Merkle)
- X9 (Snappy/networking) can proceed in parallel with X6–X7 (state transition/proofs)
- X11 (Rust ABI) can proceed in parallel with X7–X8 (safety proofs/fork choice)
- X10 (node services) can begin once X5 + X8 are complete

## 8. Axiom Inventory

| ID | Name | Statement | Justification |
|----|------|-----------|---------------|
| AXIOM-CRYPTO-1 | Hash collision resistance | `hashNodes a₁ b₁ = hashNodes a₂ b₂ → a₁ = a₂ ∧ b₁ = b₂` | Standard cryptographic assumption for SHA-256 and Poseidon2. Collision resistance is a fundamental property of any hash function used in Merkle trees. Without this axiom, SSZ Merkleization correctness is unprovable. |
| AXIOM-CRYPTO-2 | XMSS EU-CMA security | `∀ adversary, Pr[adversary forges valid signature without secret key] ≤ negl(λ)` | Post-quantum security assumption for XMSS hash-based signatures. Based on the one-wayness of the underlying hash function (Poseidon2 over KoalaBear). Standard assumption from [Buchmann et al., 2011]. |
| AXIOM-CRYPTO-3 | Poseidon2 algebraic security | `∀ adversary, Pr[adversary finds algebraic relation exploitable in sponge mode] ≤ negl(λ)` | Algebraic security assumption for the Poseidon2 permutation. The S-box (x³ over KoalaBear) resists Gröbner basis attacks. Based on [Grassi et al., 2023] security analysis. |

All three axioms are standard cryptographic hardness assumptions. They are
**not** bugs in the formalization — they represent the irreducible trust
assumptions that any cryptographic system requires. The formal proofs are
conditioned on these axioms, making the trust boundary explicit and auditable.

## 9. Risk Analysis

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| 3SF-mini proof complexity exceeds estimate | Medium | High | Break X7-H into sub-lemmas; consider Lean 4 tactic automation. Consult Ethereum Foundation consensus safety research. |
| Poseidon2 constants too large for Lean kernel | Medium | Medium | Use `native_decide` for constant validation. Pre-compute and embed as `Array Fp` literals. |
| XMSS tree traversal termination proof difficulty | Medium | Medium | Use well-founded recursion on tree depth. May require custom `WellFoundedRelation` instance. |
| Lean 4 compilation time for large proof files | High | Low | Follow seLe4n pattern: split large files into ≤500-line modules. Use `noncomputable` for proof-only definitions. |
| libp2p Rust library API instability | Low | Medium | Pin exact crate versions in `Cargo.lock`. Abstract networking behind trait interface. |
| leanSpec Python spec evolves during formalization | Medium | Medium | Pin to specific leanSpec commit. Track upstream changes in `VERSIONS.md`. Batch updates at phase boundaries. |
| SSZ serialization edge cases | Low | Low | Comprehensive roundtrip test suite (X12-J). Cross-validate against Rust SSZ library. |
| seLe4n integration conflicts | Low | Medium | Shared `lakefile.toml` with separate library targets. No circular dependencies. Bridge module is the only coupling point. |

## 10. Metrics Summary

| Metric | Target |
|--------|--------|
| Total phases | 14 |
| Total atomic sub-tasks | 162 |
| Lean production LoC (estimated) | ~15,000–20,000 |
| Lean proof LoC (estimated) | ~8,000–12,000 |
| Rust LoC (estimated) | ~3,000–5,000 |
| Test LoC (estimated) | ~2,000–3,000 |
| Theorems/lemmas (estimated) | ~300–400 |
| Sorry count (target) | 0 |
| Axiom count (target) | 3 |
| Unsafe blocks (Rust, target) | ≤ 3 |
| XVAL cross-validation cases | ≥ 20 |
| Test tier coverage | 4 tiers (hygiene, build, functional, invariant surface) |
| Spec coverage (consensus-critical) | 100% |
| Python→Lean traceability tags | LS-* prefix, one per function |

## 11. Traceability Map (Key Functions)

| Python Function | Lean Definition | Phase | Proof |
|----------------|-----------------|-------|-------|
| `BaseUint.__new__` | `BaseUint.ofNat` | X1-A | X1-B: overflow |
| `BaseUint.encode_bytes` | `BaseUint.encodeBytes` | X1-A | X1-B: roundtrip |
| `BaseBitlist.encode_bytes` | `BaseBitlist.encodeBytes` | X1-G | X1-H: roundtrip |
| `Container.serialize` | `SSZSerializable.serialize` | X1-L | X1-O: roundtrip |
| `merkleize` | `merkleize` | X2-D | X2-H: correctness |
| `hash_tree_root` | `hashTreeRoot` | X2-F/G | X2-I: collision |
| `mix_in_length` | `mixInLength` | X2-E | X2-J: injectivity |
| `Fp.__init__` | `Fp.mk` | X3-A | X3-C: field laws |
| `Poseidon2.permute` | `permute` | X3-G | X3-H: bijectivity |
| `GeneralizedXmssScheme.key_gen` | `keyGen` | X4-I | X4-L: soundness |
| `GeneralizedXmssScheme.sign` | `sign` | X4-J | X4-L: roundtrip |
| `GeneralizedXmssScheme.verify` | `verify` | X4-J | X4-L: roundtrip |
| `Slot.is_justifiable_after` | `isJustifiableAfter` | X5-A | X5-B: properties |
| `State.generate_genesis` | `generateGenesis` | X5-L | X5-L: invariants |
| `State.process_slots` | `processSlots` | X6-A | X6-B: preservation |
| `State.process_block_header` | `processBlockHeader` | X6-C | X6-D: validation |
| `State.process_attestations` | `processAttestations` | X6-E/F/G | X7: safety |
| `State.state_transition` | `stateTransition` | X6-H | X7-I: bundle |
| `State.build_block` | `buildBlock` | X6-I | — |
| `Store.from_anchor` | `Store.fromAnchor` | X8-B | X8-G: consistency |
| `Store.validate_attestation` | `validateAttestation` | X8-C | X8-G: consistency |
| `compress` | `compress` | X9-A | X9-D: roundtrip |
| `decompress` | `decompress` | X9-B | X9-D: roundtrip |
| — (novel) | `threeSFMiniSafety` | X7-H | KEYSTONE |
| — (novel) | `consensusSafety` | X7-J | Top-level |
| — (novel) | `consensusLiveness` | X7-K | Conditional |

## 12. Glossary

| Term | Definition |
|------|-----------|
| 3SF-mini | Three-Slot Finality (mini variant) — the consensus finality rule used by the Lean specification |
| LMD GHOST | Latest Message Driven Greedy Heaviest Observed SubTree — the fork choice rule |
| SSZ | Simple Serialize — Ethereum's canonical serialization format |
| XMSS | eXtended Merkle Signature Scheme — post-quantum hash-based signature |
| Poseidon2 | Algebraic hash function over prime fields, optimized for SNARKs |
| KoalaBear | Prime field with p = 2³¹ - 2²⁴ + 1, chosen for efficient arithmetic |
| EU-CMA | Existential Unforgeability under Chosen Message Attack — signature security model |
| Gossipsub | Pub/sub protocol for P2P message dissemination |
| discv5 | Node discovery protocol v5 (UDP-based) |
| ENR | Ethereum Node Record — self-signed node identity |
| Devnet | Development network — the current fork implemented in leanSpec |
| Supermajority | ≥ 2/3 of validators agreeing on a checkpoint |
| Justification | A checkpoint achieving supermajority attestation |
| Finalization | An irreversible checkpoint with a continuous justification chain |

---

*This workstream plan was created for the seLe4n project to formalize the
Lean Ethereum consensus specification in Lean 4 with machine-checked proofs
and Rust safety enforcement. The plan follows seLe4n's proven development
methodology: invariant/operations split, typed identifiers, zero sorry,
fixture-backed testing, and minimal-unsafe Rust ABI.*
