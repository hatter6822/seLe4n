# Phase X2: SSZ Merkleization & Hash Tree Root

**Version**: v0.2.0
**Status**: PLANNED
**Sub-tasks**: 22 atomic units
**Dependencies**: X1 (Foundation Types)
**Estimated Lean LoC**: ~750
**Files created**: 5 new files

## 1. Objective

Formalize SSZ Merkleization — the binary tree hashing algorithm that produces
the `hash_tree_root` for every consensus object. State roots, block roots,
attestation data roots — all flow through this function. This phase delivers
the `hashTreeRoot` dispatch plus the collision resistance proof that underpins
the entire SSZ binding property.

## 2. Reference Files

| Python File | Lean Target | Description |
|-------------|-------------|-------------|
| `src/lean_spec/subspecs/ssz/constants.py` | `LeanEth/SSZ/Merkle.lean` | Chunk size constants |
| `src/lean_spec/subspecs/ssz/pack.py` | `LeanEth/SSZ/Pack.lean` | Chunk packing |
| `src/lean_spec/subspecs/ssz/merkleization.py` | `LeanEth/SSZ/Merkle.lean` | Core merkleize algorithm |
| `src/lean_spec/subspecs/ssz/hash.py` | `LeanEth/SSZ/HashTreeRoot.lean` | Per-type hash dispatch |

## 3. Source Layout

```
LeanEth/SSZ/
├── Pack.lean              packBytes, packBits chunk helpers
├── Merkle.lean            Constants, zeroHashes, hashNodes, merkleize, mixIn*
├── HashTreeRoot.lean      hashTreeRoot dispatch per SSZ type
└── Proofs.lean            Collision, merkle path, properties
```

## 4. Sub-task Breakdown

### Group A: Constants & Packing (X2-A1 through X2-A4)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X2-A1 | **Define SSZ Merkleization constants.** `BYTES_PER_CHUNK := 32`. `BITS_PER_CHUNK := 256`. `abbrev Chunk := Bytes32`. `zeroChunk := ZERO_HASH`. `getPowerOfTwoCeil : Nat → Nat`. Prove `getPowerOfTwoCeil_ge` and `getPowerOfTwoCeil_isPow2`. | `SSZ/Merkle.lean` | ~30 | X1 |
| X2-A2 | **Define `packBytes`.** `packBytes : ByteArray → Array Chunk` — split into 32-byte chunks, zero-pad last. Prove `packBytes_nonempty` and `packBytes_length`. | `SSZ/Pack.lean` | ~35 | X2-A1 |
| X2-A3 | **Define `packBits`.** `packBits : Array Bool → Array Chunk` — pack booleans little-endian within bytes, 256 bits per chunk. Prove `packBits_length`. | `SSZ/Pack.lean` | ~35 | X2-A1 |
| X2-A4 | **Prove packing roundtrip helpers.** `packBytes_unpack_roundtrip : unpackBytes (packBytes data) data.size = data`. `packBits_unpack_roundtrip`. These ensure packing preserves information. | `SSZ/Proofs.lean` | ~25 | X2-A2, X2-A3 |

### Group B: Core Merkleization (X2-B1 through X2-B5)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X2-B1 | **Define `hashNodes` and `HashFunction` typeclass.** `class HashFunction (h : Type) where hash64 : ByteArray → Bytes32`. `hashNodes : Bytes32 → Bytes32 → Bytes32` — concatenate two 32-byte values, hash via selected backend. Instance for SHA-256 (standard Ethereum). Poseidon2 instance added in X3. | `SSZ/Merkle.lean` | ~25 | X1 |
| X2-B2 | **Define pre-computed zero subtree roots.** `zeroTreeRoot : Nat → Bytes32` where `zeroTreeRoot 0 = ZERO_HASH`, `zeroTreeRoot (n+1) = hashNodes (zeroTreeRoot n) (zeroTreeRoot n)`. Cache via `Array.ofFn` up to depth 64. Prove `zeroTreeRoot_deterministic`. | `SSZ/Merkle.lean` | ~25 | X2-B1 |
| X2-B3 | **Define `merkleize` — efficient bottom-up algorithm.** `merkleize : Array Chunk → Option Nat → Bytes32`. Build balanced binary tree with zero-padding to next power of 2, capped by optional limit. O(n·log(width)) via level-by-level pairing: at each level, pair adjacent nodes (using `zeroTreeRoot` for missing right siblings), hash pairs. Handle: empty→zero root, single chunk→return directly. | `SSZ/Merkle.lean` | ~60 | X2-B1, X2-B2 |
| X2-B4 | **Define `mixInLength` and `mixInSelector`.** `mixInLength : Bytes32 → Nat → Bytes32 := hashNodes root (Uint256LE.encode length)`. `mixInSelector : Bytes32 → Nat → Bytes32 := hashNodes root (Uint256LE.encode selector)`. Define `Uint256LE.encode : Nat → Bytes32` (32-byte little-endian). Prove `Uint256LE_encode_injective`. | `SSZ/Merkle.lean` | ~25 | X2-B1 |
| X2-B5 | **Prove merkleize basic properties.** (1) `merkleize_singleton`. (2) `merkleize_empty`. (3) `merkleize_empty_limit`. (4) `merkleize_two`. (5) `merkleize_idempotent_padding`. | `SSZ/Proofs.lean` | ~40 | X2-B3 |

### Group C: Hash Tree Root Dispatch (X2-C1 through X2-C4)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X2-C1 | **Define `hashTreeRoot` for basic types.** `class SSZHashable (α : Type) where hashTreeRoot : α → Bytes32`. Instances for `BaseUint`, `SSZBoolean`, `BaseBytes`, `Fp`. | `SSZ/HashTreeRoot.lean` | ~40 | X2-B3, X2-A2 |
| X2-C2 | **Define `hashTreeRoot` for variable-length basic types.** Instances for `BaseByteList` (pack → merkleize with limit → mixInLength) and `BaseBitlist` (packBits → merkleize with limit → mixInLength). | `SSZ/HashTreeRoot.lean` | ~25 | X2-C1, X2-B4, X2-A3 |
| X2-C3 | **Define `hashTreeRoot` for composite types.** Instances for `SSZVector` (basic: pack elements; composite: hash each → merkleize), `SSZList` (same + mixInLength), `BaseBitvector` (packBits → merkleize). | `SSZ/HashTreeRoot.lean` | ~40 | X2-C1, X2-C2 |
| X2-C4 | **Define `hashTreeRoot` for containers and unions.** `containerHashTreeRoot : Array Bytes32 → Bytes32 := merkleize fieldRoots none`. Union: `mixInSelector (hashTreeRoot value) selectorIndex`. | `SSZ/HashTreeRoot.lean` | ~20 | X2-C1 |

### Group D: Correctness Proofs (X2-D1 through X2-D5)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X2-D1 | **Declare AXIOM-CRYPTO-1 and prove container collision resistance.** `axiom hashNodes_collision_resistant : hashNodes a₁ b₁ = hashNodes a₂ b₂ → a₁ = a₂ ∧ b₁ = b₂`. Under this axiom: `hashTreeRoot_injective_container : hashTreeRoot c₁ = hashTreeRoot c₂ → fieldRoots c₁ = fieldRoots c₂`. | `SSZ/Proofs.lean` | ~40 | X2-C4 |
| X2-D2 | **Prove mixInLength injectivity.** `mixInLength_injective : mixInLength r₁ n₁ = mixInLength r₂ n₂ → r₁ = r₂ ∧ n₁ = n₂` (under AXIOM-CRYPTO-1 + Uint256LE injectivity). Essential for list type safety. | `SSZ/Proofs.lean` | ~25 | X2-D1 |
| X2-D3 | **Prove mixInSelector injectivity.** Same structure as X2-D2. Essential for union type safety. | `SSZ/Proofs.lean` | ~15 | X2-D1 |
| X2-D4 | **Prove hashTreeRoot consistency across types.** Vector vs list share inner root but list mixes in length. `hashTreeRoot_deterministic`. | `SSZ/Proofs.lean` | ~25 | X2-C1, X2-C3 |
| X2-D5 | **Merkleization test suite.** Test `hashTreeRoot` for all type families against Python reference. Minimum 8 test vectors. | `tests/MerkleizationSuite.lean` | ~35 | All X2-* |

## 5. Exit Criteria

- [ ] `merkleize` and `hashTreeRoot` compile with zero sorry
- [ ] AXIOM-CRYPTO-1 declared with annotation
- [ ] Container collision resistance proved (under axiom)
- [ ] `mixInLength` and `mixInSelector` injectivity proved
- [ ] 5 basic merkleize properties proved
- [ ] Packing roundtrip helpers proved
- [ ] `tests/MerkleizationSuite.lean` matches Python reference
- [ ] `lake build LeanEth.SSZ.HashTreeRoot` succeeds
