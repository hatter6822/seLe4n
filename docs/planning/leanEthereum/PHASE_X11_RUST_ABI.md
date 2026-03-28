# Phase X11: Rust ABI Safety Layer

**Version**: v0.11.0
**Status**: PLANNED
**Sub-tasks**: 28 atomic units
**Dependencies**: X1 (Types — for SSZ codec), X2 (SSZ — for Merkle)
**Estimated Lean LoC**: ~250 (Lean-side FFI definitions)
**Estimated Rust LoC**: ~4,500
**Crates created**: 3 (`leaneth-types`, `leaneth-net`, `leaneth-storage`)
**Parallelizable with**: X6–X8 (consensus logic)

## 1. Objective

Build the Rust safety layer following seLe4n's proven pattern: `no_std` crates
with minimal `unsafe`, cross-validated against the Lean reference. The Rust
layer handles networking I/O, persistent storage, and OS interaction.

## 2. Source Layout

```
rust/
├── Cargo.toml                    Workspace root
├── SAFETY_AUDIT.md               Unsafe block documentation
├── leaneth-types/
│   ├── Cargo.toml
│   └── src/
│       ├── lib.rs                Type re-exports
│       ├── primitives.rs         Slot, ValidatorIndex, Bytes32, etc.
│       ├── containers.rs         Checkpoint, Block, State, etc.
│       ├── errors.rs             ConsensusError enum
│       ├── ssz/
│       │   ├── mod.rs            SszEncode, SszDecode traits
│       │   ├── encode.rs         Encoding implementations
│       │   ├── decode.rs         Decoding implementations
│       │   └── derive.rs         Derive macros for structs
│       ├── merkle.rs             hash_tree_root, merkleize
│       └── snappy.rs             Compression wrapper
├── leaneth-net/
│   ├── Cargo.toml
│   └── src/
│       ├── lib.rs                Network service
│       ├── gossipsub.rs          Topic subscription, message routing
│       ├── reqresp.rs            Request-response handlers
│       ├── discovery.rs          discv5 peer discovery
│       └── ffi.rs                Lean↔Rust C ABI bridge
├── leaneth-storage/
│   ├── Cargo.toml
│   └── src/
│       ├── lib.rs                Storage service
│       ├── schema.rs             Namespace, key encoding
│       └── ops.rs                Block/state persistence
└── tests/
    ├── xval.rs                   Cross-validation suite
    └── integration.rs            End-to-end smoke test
```

## 3. Sub-task Breakdown

### Group A: Types Crate — Primitives (X11-A1 through X11-A3)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X11-A1 | **Create `leaneth-types` crate skeleton.** `no_std` Rust crate with `#![forbid(unsafe_code)]`. Cargo.toml with minimal deps: `sha2`, `tiny-keccak` (for hashing). Feature flags: `std` (default off), `serde` (optional). Newtype wrappers with `derive(Clone, Copy, PartialEq, Eq, Hash, Debug)`: `Slot(u64)`, `ValidatorIndex(u64)`, `Bytes32([u8; 32])`, `Uint64(u64)`. Implement `Display`, `From<u64>`, arithmetic ops for `Slot`. | `rust/leaneth-types/` | ~80 | — |
| X11-A2 | **Define consensus container types in Rust.** `Checkpoint { root: Bytes32, slot: Slot }`, `BlockHeader { slot: Slot, proposer_index: ValidatorIndex, parent_root: Bytes32, state_root: Bytes32, body_root: Bytes32 }`, `AttestationData { slot: Slot, head: Checkpoint, target: Checkpoint, source: Checkpoint }`, `Block`, `State` (matching Lean definitions field-for-field). All types: `#[derive(Clone, PartialEq, Eq, Debug)]`. | `rust/leaneth-types/src/containers.rs` | ~70 | X11-A1 |
| X11-A3 | **Define error types in Rust.** `enum ConsensusError` with 34+ variants matching Lean's `ConsensusError`. `enum SszError { TypeMismatch, SizeMismatch, OutOfBounds, DeserializationFailed, OffsetOverflow }`. `enum SnappyError { InvalidOffset, TruncatedInput, ... }`. Implement `std::error::Error` (behind `std` feature), `Display` for all. | `rust/leaneth-types/src/errors.rs` | ~50 | X11-A1 |

### Group B: Types Crate — SSZ Codec (X11-B1 through X11-B4)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X11-B1 | **Define SSZ traits.** `trait SszEncode { fn ssz_encode(&self) -> Vec<u8>; fn is_fixed_size() -> bool; fn fixed_byte_length() -> Option<usize>; }`. `trait SszDecode: Sized { fn ssz_decode(data: &[u8]) -> Result<Self, SszError>; }`. Helper: `encode_then_decode<T: SszEncode + SszDecode>(x: &T) -> Result<T, SszError>`. | `rust/leaneth-types/src/ssz/mod.rs` | ~25 | X11-A1 |
| X11-B2 | **Implement SSZ encoding.** Primitive impls: `u8`, `u16`, `u32`, `u64` (little-endian), `bool` (0x00/0x01), `[u8; N]` (direct copy). `Vec<T>` where T is fixed-size: concatenate encodings. `Vec<T>` where T is variable-size: offset table + concatenated data. Bitfield: packed LE with delimiter bit for `Bitlist`. Must produce byte-identical output to Lean `serialize`. | `rust/leaneth-types/src/ssz/encode.rs` | ~80 | X11-B1 |
| X11-B3 | **Implement SSZ decoding.** Primitive: read exact bytes, LE decode. `Vec<T>` fixed: divide by element size. `Vec<T>` variable: parse offset table, extract slices. Bitfield: unpack LE, find delimiter. Bounds checking on all reads. Reject: trailing bytes for fixed types, offset out of range, zero-length variable where disallowed. | `rust/leaneth-types/src/ssz/decode.rs` | ~80 | X11-B1 |
| X11-B4 | **Implement SSZ derive for containers.** Procedural macro or manual impl for each container: `Checkpoint`, `BlockHeader`, `AttestationData`, `Block`, `State`. Container encode: fixed fields in order, offset table for variable fields, variable data appended. Container decode: parse offsets, extract field slices, decode each. | `rust/leaneth-types/src/ssz/derive.rs` | ~60 | X11-B2, X11-B3, X11-A2 |

### Group C: Types Crate — Merkle & Snappy (X11-C1 through X11-C3)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X11-C1 | **Implement SSZ Merkleization in Rust.** `hash_tree_root<T: SszEncode>(value: &T) -> Bytes32`. `merkleize(chunks: &[Bytes32], limit: Option<usize>) -> Bytes32` — bottom-up binary tree, zero-padding, pre-computed zero hashes up to depth 64. `mix_in_length(root: Bytes32, length: usize) -> Bytes32`. `mix_in_selector(root: Bytes32, selector: usize) -> Bytes32`. SHA-256 backend (default) + Poseidon2 backend (feature-gated). Output must match Lean `hashTreeRoot` for all types. | `rust/leaneth-types/src/merkle.rs` | ~90 | X11-B2 |
| X11-C2 | **Implement Snappy compression in Rust.** Wrapper around `snap` crate for raw block compression/decompression. Framing format: stream identifier + chunk headers (type + length + CRC32C + data). `compress(data: &[u8]) -> Vec<u8>`, `decompress(data: &[u8]) -> Result<Vec<u8>, SnappyError>`. `frame_compress`, `frame_decompress`. Must match Lean Snappy roundtrip byte-for-byte. | `rust/leaneth-types/src/snappy.rs` | ~50 | X11-A1 |
| X11-C3 | **Implement KoalaBear field and Poseidon2 in Rust.** `struct Fp(u32)` with modular arithmetic (p = 2013265921). `poseidon2_permute(state: &mut [Fp])` — external/internal round functions matching Lean. `poseidon2_hash(input: &[u8]) -> Bytes32` — sponge construction. Feature-gated behind `poseidon2`. | `rust/leaneth-types/src/crypto.rs` | ~80 | X11-A1 |

### Group D: Networking Crate (X11-D1 through X11-D5)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X11-D1 | **Create `leaneth-net` crate skeleton.** Networking crate using `libp2p` (QUIC transport via `quinn`). `struct NetworkService { swarm: Swarm, config: NetworkConfig, event_tx: Sender<NetworkEvent> }`. Define `NetworkConfig`, `NetworkEvent` matching Lean types from X9. | `rust/leaneth-net/` | ~60 | X11-A1 |
| X11-D2 | **Implement gossipsub handler.** Subscribe to consensus topics (beacon block, attestation per subnet, aggregate proof). Decode incoming: SSZ+Snappy decompress → deserialize. Encode outgoing: serialize → Snappy compress. Route received messages to event channel. Message validation: reject duplicates, reject future slots, reject invalid SSZ. | `rust/leaneth-net/src/gossipsub.rs` | ~80 | X11-D1, X11-C2, X11-B2 |
| X11-D3 | **Implement req-resp handler.** Handle 6 methods: `BlocksByRange`, `BlocksByRoot`, `Status`, `Metadata`, `Ping`, `Goodbye`. SSZ+Snappy encode/decode for each. Per-peer rate limiting with configurable quotas. Timeout handling: configurable per-method. Response streaming for `BlocksByRange`. | `rust/leaneth-net/src/reqresp.rs` | ~70 | X11-D1, X11-C2 |
| X11-D4 | **Implement discv5 discovery.** UDP-based peer discovery using `discv5` crate. ENR encoding/decoding matching Lean X9-B3. Bootstrap node list from config. Periodic peer refresh. Subnet-based peer selection. | `rust/leaneth-net/src/discovery.rs` | ~50 | X11-D1 |
| X11-D5 | **Define Lean↔Rust FFI boundary.** C ABI bridge functions: `extern "C" fn lean_on_block(ssz_data: *const u8, len: usize) -> i32`, `lean_on_attestation`, `lean_get_head(out: *mut u8) -> i32`, `lean_get_state(root: *const u8, out: *mut u8, out_len: *mut usize) -> i32`. All data passes as SSZ-encoded byte arrays — zero pointer sharing of structured data. Exactly 2 `unsafe` blocks: (1) FFI entry from Lean → Rust (pointer dereference + slice creation), (2) FFI callback from Rust → Lean (function pointer call). Document invariants for each: pointer validity, length bounds, alignment. | `rust/leaneth-net/src/ffi.rs` | ~70 | X11-D1 |

### Group E: Storage Crate (X11-E1 through X11-E3)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X11-E1 | **Create `leaneth-storage` crate.** SQLite via `rusqlite`. `struct Storage { conn: Connection }`. WAL journal mode for concurrent reads. Batch write support via transactions. `fn init(path: &str) -> Result<Storage, StorageError>` — create tables for each namespace. | `rust/leaneth-storage/` | ~50 | — |
| X11-E2 | **Define storage schema and namespace isolation.** Tables: `blocks(root BLOB PRIMARY KEY, slot INTEGER, data BLOB)`, `states(root BLOB PRIMARY KEY, slot INTEGER, data BLOB)`, `checkpoints(slot INTEGER PRIMARY KEY, root BLOB)`, `metadata(key TEXT PRIMARY KEY, value BLOB)`. Indexes: `blocks_by_slot`, `states_by_slot`. | `rust/leaneth-storage/src/schema.rs` | ~30 | X11-E1 |
| X11-E3 | **Implement block/state persistence operations.** `store_block(block: &SignedBlock)`, `get_block(root: &Bytes32) -> Option<SignedBlock>`, `store_state(state: &State)`, `get_state(root: &Bytes32) -> Option<State>`, `store_checkpoint(cp: &Checkpoint)`, `get_latest_finalized() -> Option<Checkpoint>`, `prune_before_slot(slot: Slot)` (cleanup). All ops: SSZ serialize/deserialize at storage boundary. Interface matches Lean `Database` typeclass semantics. | `rust/leaneth-storage/src/ops.rs` | ~60 | X11-E2, X11-B2 |

### Group F: Cross-Validation & Safety (X11-F1 through X11-F7)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X11-F1 | **Create XVAL test harness — Lean side.** `tests/XvalSuite.lean`: produce SSZ encodings + `hashTreeRoot` for all consensus containers with known test data. Output pipe-delimited: `XVAL | TYPE | ENCODING_HEX | ROOT_HEX`. Cover: Uint8/16/32/64, Bytes32, Bool, Checkpoint, AttestationData, Block, State, Snappy roundtrip (≥ 5 inputs). Minimum 25 XVAL pairs. | `tests/XvalSuite.lean` | ~50 | X2, X5, X6 |
| X11-F2 | **Create XVAL test harness — Rust side.** `rust/tests/xval.rs`: independently compute SSZ encodings + `hash_tree_root` for same test data. Compare hex output against Lean fixture file. Byte-exact match required. Fail on any divergence with detailed diff. | `rust/tests/xval.rs` | ~50 | X11-B2, X11-C1 |
| X11-F3 | **Rust unit tests — SSZ.** Roundtrip tests for all primitive types. Container encode/decode for every consensus type. Edge cases: empty list, max-size list, zero-valued fields, max-valued fields. Minimum 30 test cases. | `rust/leaneth-types/tests/ssz_tests.rs` | ~60 | X11-B2, X11-B3, X11-B4 |
| X11-F4 | **Rust unit tests — Merkle & Snappy.** `hash_tree_root` for all types vs known values. `merkleize` edge cases: empty, single chunk, power-of-two, non-power-of-two. Snappy roundtrip: empty, small, large, repetitive. Minimum 15 test cases. | `rust/leaneth-types/tests/merkle_tests.rs` | ~30 | X11-C1, X11-C2 |
| X11-F5 | **Rust unit tests — Storage.** SQLite: create, store, retrieve, delete for blocks and states. Checkpoint persistence. Prune operation. Concurrent read test (WAL mode). Minimum 10 test cases. | `rust/leaneth-storage/tests/storage_tests.rs` | ~30 | X11-E3 |
| X11-F6 | **Unsafe audit and safety documentation.** Document every `unsafe` block: (1) exact location (file:line), (2) why `unsafe` is necessary (FFI boundary), (3) invariants relied upon (pointer non-null, length within bounds, aligned), (4) how invariants are maintained (checked at call site). Target: exactly 2 `unsafe` blocks. Create `rust/SAFETY_AUDIT.md`. | `rust/SAFETY_AUDIT.md` | ~30 | All X11-* |
| X11-F7 | **Cargo workspace and CI configuration.** Root `Cargo.toml` workspace with all three crates. CI: `cargo build --release`, `cargo test`, `cargo clippy -- -D warnings`, `cargo fmt -- --check`. Pin dependency versions. `rust-toolchain.toml` pinning stable channel. Integration smoke test: Rust binary that initializes networking → discovers peers → receives one block via gossipsub → decodes SSZ+Snappy → passes to Lean FFI → stores result. | `rust/Cargo.toml`, `rust/tests/integration.rs` | ~60 | All X11-* |

## 4. Exit Criteria

- [ ] Three Rust crates compile with `cargo build --release`
- [ ] `cargo clippy` passes with zero warnings
- [ ] `cargo fmt` passes
- [ ] SSZ codec byte-identical to Lean (≥ 25 XVAL cases)
- [ ] `hash_tree_root` byte-identical to Lean for all types
- [ ] Snappy roundtrip matches Lean
- [ ] Networking connects to devnet peers
- [ ] Storage reads/writes/prunes correctly
- [ ] Exactly 2 `unsafe` blocks, both documented
- [ ] `rust/SAFETY_AUDIT.md` complete
- [ ] ≥ 85 Rust unit tests pass
- [ ] Integration smoke test passes end-to-end
