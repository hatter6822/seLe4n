# Phase X2: SSZ Merkleization & Hash Tree Root

**Version**: v0.2.0
**Status**: PLANNED
**Sub-tasks**: 16 atomic units
**Dependencies**: X1 (Foundation Types)
**Estimated Lean LoC**: ~600
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
└── Proofs.lean            Roundtrip, collision, merkle path proofs
```

## 4. Sub-task Breakdown

### Group A: Constants & Packing (X2-A1 through X2-A3)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X2-A1 | **Define SSZ Merkleization constants.** `def BYTES_PER_CHUNK : Nat := 32`. `def BITS_PER_CHUNK : Nat := 256`. `abbrev Chunk := Bytes32`. `def zeroChunk : Chunk := ZERO_HASH`. Define `getPowerOfTwoCeil : Nat → Nat` (smallest power of 2 ≥ n). Prove `getPowerOfTwoCeil_ge : getPowerOfTwoCeil n ≥ n`. Prove `getPowerOfTwoCeil_isPow2`. | `SSZ/Merkle.lean` | ~30 | X1 |
| X2-A2 | **Define `packBytes` chunk function.** `packBytes : ByteArray → Array Chunk` — split byte array into 32-byte chunks, zero-padding the last chunk if needed. Implementation: iterate in 32-byte strides, extract slice, pad with zeros if `remaining < 32`. Prove `packBytes_nonempty : data.size > 0 → (packBytes data).size > 0`. Prove `packBytes_length : (packBytes data).size = (data.size + 31) / 32`. | `SSZ/Pack.lean` | ~35 | X2-A1 |
| X2-A3 | **Define `packBits` chunk function.** `packBits : Array Bool → Array Chunk` — pack boolean array into chunks (little-endian within bytes, 256 bits per chunk). Implementation: group bits into 256-bit chunks, within each chunk pack 8 bits per byte (bit[i] → byte `i/8`, position `i%8`), zero-pad last chunk. Prove `packBits_length : (packBits bits).size = (bits.size + 255) / 256`. | `SSZ/Pack.lean` | ~35 | X2-A1 |

### Group B: Core Merkleization (X2-B1 through X2-B5)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X2-B1 | **Define `hashNodes` function.** `hashNodes : Bytes32 → Bytes32 → Bytes32` — concatenate two 32-byte values and hash. Initially use SHA-256 (standard Ethereum). The hash function is parameterized via a `HashFunction` typeclass to support Poseidon2 in later phases: `class HashFunction (h : Type) where hash64 : ByteArray → Bytes32` with `instance : HashFunction SHA256`. | `SSZ/Merkle.lean` | ~25 | X1 |
| X2-B2 | **Define pre-computed zero subtree roots.** `def zeroTreeRoot : Nat → Bytes32` where `zeroTreeRoot 0 = ZERO_HASH` and `zeroTreeRoot (n+1) = hashNodes (zeroTreeRoot n) (zeroTreeRoot n)`. Cache via `Array.ofFn` up to depth 64 (sufficient for any SSZ type). Prove `zeroTreeRoot_deterministic : zeroTreeRoot n is a pure function of n`. | `SSZ/Merkle.lean` | ~25 | X2-B1 |
| X2-B3 | **Define `merkleize` (core algorithm).** `merkleize : Array Chunk → Option Nat → Bytes32` — build balanced binary tree with zero-padding to next power of 2, capped by optional limit. Implement the efficient O(n·log(width)) algorithm from leanSpec: at each level, pair adjacent nodes (using `zeroTreeRoot` for missing right siblings), hash pairs, repeat until single root. Handle edge cases: empty input → `zeroTreeRoot (log2Ceil limit)`; single chunk → return directly; limit < input size → error (but we return the correct result for well-formed input). | `SSZ/Merkle.lean` | ~60 | X2-B1, X2-B2 |
| X2-B4 | **Define `mixInLength`.** `mixInLength : Bytes32 → Nat → Bytes32 := fun root length => hashNodes root (Uint256LE.encode length)` where `Uint256LE.encode` is a 32-byte little-endian encoding of a natural number. Used for all variable-length types (SSZList, Bitlist, ByteList). | `SSZ/Merkle.lean` | ~15 | X2-B1 |
| X2-B5 | **Define `mixInSelector`.** `mixInSelector : Bytes32 → Nat → Bytes32 := fun root selector => hashNodes root (Uint256LE.encode selector)`. Used for SSZ union types. Same encoding as `mixInLength` but semantically represents a type discriminator. | `SSZ/Merkle.lean` | ~10 | X2-B1 |

### Group C: Hash Tree Root Dispatch (X2-C1 through X2-C3)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X2-C1 | **Define `hashTreeRoot` for basic types.** `class SSZHashable (α : Type) where hashTreeRoot : α → Bytes32`. Instances for `BaseUint bits` (pack encoded bytes → merkleize), `SSZBoolean` (pack 1 byte → merkleize), `BaseBytes n` (pack raw bytes → merkleize), `BaseByteList limit` (pack raw bytes → merkleize with limit → mixInLength), `Fp` (pack 4-byte LE → merkleize). | `SSZ/HashTreeRoot.lean` | ~50 | X2-B3, X2-B4, X2-A2 |
| X2-C2 | **Define `hashTreeRoot` for composite types.** Instance for `SSZVector α len`: if `α` is basic (Uint/Bool/Fp), pack all elements' encodings → merkleize with limit; if composite, recursively hash each element → merkleize with limit=len. Instance for `SSZList α limit`: same as vector but always `mixInLength`. Instance for `BaseBitvector len`: `packBits` → merkleize. Instance for `BaseBitlist limit`: `packBits` → merkleize with limit → mixInLength. | `SSZ/HashTreeRoot.lean` | ~50 | X2-C1, X2-A3 |
| X2-C3 | **Define `hashTreeRoot` for containers and unions.** Container: merkleize the array of field hash roots (each field's `hashTreeRoot`). Provide `containerHashTreeRoot : (fieldRoots : Array Bytes32) → Bytes32 := merkleize fieldRoots none`. Union: `mixInSelector (hashTreeRoot value) selectorIndex`. Null union (no value): `mixInSelector ZERO_HASH 0`. | `SSZ/HashTreeRoot.lean` | ~30 | X2-C1 |

### Group D: Correctness Proofs (X2-D1 through X2-D5)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X2-D1 | **Prove merkleize basic properties.** (1) `merkleize_singleton : merkleize #[c] none = c`. (2) `merkleize_empty : merkleize #[] none = ZERO_HASH`. (3) `merkleize_empty_limit : merkleize #[] (some n) = zeroTreeRoot (log2Ceil n)`. (4) `merkleize_two : merkleize #[a, b] none = hashNodes a b`. (5) `merkleize_idempotent_padding : adding zero chunks beyond the power-of-2 width doesn't change the result`. | `SSZ/Proofs.lean` | ~40 | X2-B3 |
| X2-D2 | **Prove hash tree root collision resistance (AXIOM-CRYPTO-1).** Axiom declaration: `axiom hashNodes_collision_resistant : hashNodes a₁ b₁ = hashNodes a₂ b₂ → a₁ = a₂ ∧ b₁ = b₂`. Under this axiom, prove: `hashTreeRoot_injective_container : ∀ (c₁ c₂ : Container), hashTreeRoot c₁ = hashTreeRoot c₂ → fieldRoots c₁ = fieldRoots c₂`. This is the SSZ binding property: distinct containers produce distinct roots. | `SSZ/Proofs.lean` | ~40 | X2-C3 |
| X2-D3 | **Prove mixInLength injectivity.** `mixInLength_injective : mixInLength r₁ n₁ = mixInLength r₂ n₂ → r₁ = r₂ ∧ n₁ = n₂` (under AXIOM-CRYPTO-1). Proof: `mixInLength r n = hashNodes r (encode n)`, so by `hashNodes_collision_resistant`, `r₁ = r₂` and `encode n₁ = encode n₂`. Since LE encoding is injective for Nat, `n₁ = n₂`. Essential for list type safety. | `SSZ/Proofs.lean` | ~25 | X2-D2 |
| X2-D4 | **Prove mixInSelector injectivity.** `mixInSelector_injective : mixInSelector r₁ s₁ = mixInSelector r₂ s₂ → r₁ = r₂ ∧ s₁ = s₂`. Same structure as X2-D3. Essential for union type safety. | `SSZ/Proofs.lean` | ~15 | X2-D2 |
| X2-D5 | **Prove hashTreeRoot consistency across types.** (1) `hashTreeRoot_vector_list_equiv : ∀ (v : SSZVector α n) (l : SSZList α m), v.toList = l.toList → v.elems.size = l.elems.size → hashTreeRoot v = merkleize ... ∧ hashTreeRoot l = mixInLength (merkleize ...) l.length` (they share the same inner root but list mixes in length). (2) `hashTreeRoot_deterministic : hashTreeRoot x = hashTreeRoot x` (trivial but documents purity). | `SSZ/Proofs.lean` | ~30 | X2-C1, X2-C2 |

## 5. Intra-phase Dependency Graph

```
X2-A1 ──→ X2-A2 ──→ X2-C1
     └──→ X2-A3 ──→ X2-C2
     └──→ X2-B1 ──→ X2-B2 ──→ X2-B3 ──→ X2-C1 ──→ X2-C3 ──→ X2-D2
               └──→ X2-B4 ──→ X2-C1         │               └→ X2-D3
               └──→ X2-B5 ──→ X2-C3         └──→ X2-D1      └→ X2-D4
                                                              └→ X2-D5
```

## 6. Exit Criteria

- [ ] `merkleize` and `hashTreeRoot` compile with zero sorry
- [ ] AXIOM-CRYPTO-1 declared with `AXIOM-CRYPTO-1` annotation
- [ ] Collision resistance proof for container roots (under axiom)
- [ ] `mixInLength` and `mixInSelector` injectivity proved
- [ ] 5 basic merkleize properties proved
- [ ] `tests/MerkleizationSuite.lean` matches Python reference outputs
- [ ] `lake build LeanEth.SSZ.HashTreeRoot` succeeds
