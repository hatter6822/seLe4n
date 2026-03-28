# Phase X11: Rust ABI Safety Layer

**Version**: v0.11.0
**Status**: PLANNED
**Sub-tasks**: 16 atomic units
**Dependencies**: X1 (Types — for SSZ codec), X2 (SSZ — for Merkle)
**Estimated Lean LoC**: ~200 (Lean-side FFI definitions)
**Estimated Rust LoC**: ~3,500
**Crates created**: 3 (`leaneth-types`, `leaneth-net`, `leaneth-storage`)
**Parallelizable with**: X6–X8 (consensus logic)

## 1. Objective

Build the Rust safety layer following seLe4n's proven pattern: `no_std` crates
with minimal `unsafe`, cross-validated against the Lean reference. The Rust
layer handles networking I/O, persistent storage, and OS interaction.

## 2. Sub-task Breakdown

### Group A: Types Crate (X11-A1 through X11-A4)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X11-A1 | **Create `leaneth-types` crate skeleton.** `no_std` Rust crate. `#![forbid(unsafe_code)]`. Newtype wrappers: `Slot(u64)`, `ValidatorIndex(u64)`, `Bytes32([u8; 32])`, `Checkpoint`, `BlockHeader`. Error enum: `ConsensusError` (34+ variants). Cargo.toml with minimal dependencies. | `rust/leaneth-types/` | ~80 | — |
| X11-A2 | **Implement SSZ codec in Rust.** `SszEncode` and `SszDecode` traits. Derive macros for structs. Primitive impls (u8..u64, bool, [u8; N]). `Vec<T>` (SSZList), `[T; N]` (SSZVector). Bitfield encoding with delimiter bit. Must produce byte-identical output to Lean. | `rust/leaneth-types/src/ssz.rs` | ~120 | X11-A1 |
| X11-A3 | **Implement SSZ Merkleization in Rust.** `hash_tree_root`, `merkleize`, pre-computed zero hashes. SHA-256 and Poseidon2 hash backends. Output must match Lean `hashTreeRoot` for all types. | `rust/leaneth-types/src/merkle.rs` | ~80 | X11-A2 |
| X11-A4 | **Implement Snappy compression in Rust.** Wrapper around `snap` crate for raw compression. Framing format with CRC32C. Must match Lean Snappy roundtrip. | `rust/leaneth-types/src/snappy.rs` | ~40 | X11-A1 |

### Group B: Networking Crate (X11-B1 through X11-B5)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X11-B1 | **Create `leaneth-net` crate skeleton.** Networking crate using `libp2p`. QUIC transport (via `quinn`). Define `NetworkConfig`, `NetworkService`, `NetworkEvent` matching Lean types from X9. | `rust/leaneth-net/` | ~60 | X11-A1 |
| X11-B2 | **Implement gossipsub handler.** Subscribe to consensus topics. Decode SSZ+Snappy payloads. Publish blocks and attestations. Route received messages to event channel. | `rust/leaneth-net/src/gossipsub.rs` | ~80 | X11-B1, X11-A4 |
| X11-B3 | **Implement req-resp handler.** Handle `BlocksByRange`, `BlocksByRoot`, `Status`, `Metadata`, `Ping`, `Goodbye`. SSZ+Snappy encode/decode. Per-peer rate limiting. | `rust/leaneth-net/src/reqresp.rs` | ~60 | X11-B1 |
| X11-B4 | **Implement discv5 discovery.** UDP-based peer discovery using `discv5` crate. ENR encoding/decoding matching Lean. Bootstrap node configuration. | `rust/leaneth-net/src/discovery.rs` | ~50 | X11-B1 |
| X11-B5 | **Define Lean↔Rust FFI boundary.** C ABI bridge functions: `lean_on_block`, `lean_on_attestation`, `lean_get_head`, `lean_get_state`. All data passes as SSZ-encoded byte arrays — no pointer sharing. Exactly 2 `unsafe` blocks: FFI boundary (Lean→Rust, Rust→Lean). Document invariants for each. | `rust/leaneth-net/src/ffi.rs` | ~60 | X11-B1 |

### Group C: Storage Crate (X11-C1 through X11-C2)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X11-C1 | **Create `leaneth-storage` crate.** SQLite via `rusqlite`. Namespace isolation (blocks, states, checkpoints, metadata). WAL mode. Batch writes. Interface matches Lean `Database` typeclass. | `rust/leaneth-storage/` | ~80 | — |
| X11-C2 | **Implement block/state persistence.** `store_block`, `get_block`, `store_state`, `get_state`, `store_checkpoint`, `get_latest_finalized`. Indexed by root hash (Bytes32). | `rust/leaneth-storage/src/ops.rs` | ~50 | X11-C1 |

### Group D: Cross-Validation & Safety (X11-D1 through X11-D5)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X11-D1 | **Create XVAL cross-validation test suite.** Lean trace harness produces expected SSZ encodings and hash tree roots. Rust test suite independently computes same values and compares. Cover: all consensus container SSZ, Merkle roots, Snappy, state transitions. ≥ 20 XVAL cases. | `rust/tests/xval.rs`, `tests/XvalSuite.lean` | ~80 | X11-A2, X11-A3 |
| X11-D2 | **Rust unit tests.** SSZ roundtrip tests for all types. Merkleization tests. Snappy roundtrip. Storage read/write/delete. | `rust/leaneth-types/tests/`, `rust/leaneth-storage/tests/` | ~60 | All X11-* |
| X11-D3 | **Unsafe audit.** Document every `unsafe` block: why necessary, what invariants it relies on, how maintained. Target: ≤ 3 total. Create `rust/SAFETY_AUDIT.md`. | `rust/SAFETY_AUDIT.md` | ~30 | All X11-* |
| X11-D4 | **Cargo workspace configuration.** Root `Cargo.toml` workspace with all three crates. CI build: `cargo build --release`, `cargo test`, `cargo clippy`. Pin dependency versions. | `rust/Cargo.toml` | ~20 | All X11-* |
| X11-D5 | **Integration smoke test.** Rust binary that: (1) initializes networking, (2) discovers peers, (3) receives one block via gossipsub, (4) decodes SSZ+Snappy, (5) passes to Lean FFI, (6) stores result. End-to-end validation. | `rust/tests/integration.rs` | ~40 | All X11-* |

## 3. Exit Criteria

- [ ] Three Rust crates compile with `cargo build --release`
- [ ] `cargo clippy` passes with zero warnings
- [ ] SSZ codec byte-identical to Lean (≥ 20 XVAL cases)
- [ ] Networking connects to devnet peers
- [ ] Storage reads/writes correctly
- [ ] ≤ 3 `unsafe` blocks, all documented
- [ ] `rust/SAFETY_AUDIT.md` complete
