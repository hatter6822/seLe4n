# Phase X1: Foundation Types & Prelude

**Version**: v0.1.0
**Status**: PLANNED
**Sub-tasks**: 30 atomic units
**Dependencies**: None (foundation phase)
**Estimated Lean LoC**: ~1,100
**Files created**: 10 new files

## 1. Objective

Establish the SSZ type system foundation in Lean 4. This phase creates the
typed substrate that every subsequent phase builds upon: unsigned integers with
bit-width constraints, fixed and variable-length byte arrays, bitfields,
typed collections, and the SSZ Container serialization framework.

No consensus logic is introduced — only the type infrastructure. Every type
gets `DecidableEq`, `Repr`, `BEq`, `Hashable`, and `SSZSerializable` instances.
Every serialization function gets a machine-checked roundtrip proof.

## 2. Reference Files (leanSpec Python)

| Python File | Lean Target | Description |
|-------------|-------------|-------------|
| `src/lean_spec/types/uint.py` | `LeanEth/Types/Uint.lean` | Unsigned integer types |
| `src/lean_spec/types/ssz_base.py` | `LeanEth/Types/SSZBase.lean` | SSZ type interface |
| `src/lean_spec/types/byte_arrays.py` | `LeanEth/Types/Bytes.lean` | Fixed/variable byte arrays |
| `src/lean_spec/types/boolean.py` | `LeanEth/Types/Boolean.lean` | SSZ boolean |
| `src/lean_spec/types/bitfields.py` | `LeanEth/Types/BitFields.lean` | Bitvector, Bitlist |
| `src/lean_spec/types/collections.py` | `LeanEth/Types/Collections.lean` | SSZList, SSZVector |
| `src/lean_spec/types/container.py` | `LeanEth/Types/Container.lean` | Container derive |
| `src/lean_spec/types/rlp.py` | `LeanEth/Types/RLP.lean` | RLP encoding (ENR compat) |
| `src/lean_spec/types/exceptions.py` | `LeanEth/Prelude.lean` | Error types |

## 3. Source Layout

```
LeanEth/
├── Prelude.lean              Error types, LeanEthM monad, config, re-exports
├── Types/
│   ├── SSZBase.lean          SSZSerializable typeclass
│   ├── Uint.lean             BaseUint, Uint8/16/32/64
│   ├── Bytes.lean            BaseBytes, BaseByteList, Bytes1..Bytes65
│   ├── Boolean.lean          SSZ Boolean wrapper
│   ├── BitFields.lean        BaseBitvector, BaseBitlist
│   ├── Collections.lean      SSZVector, SSZList
│   ├── Container.lean        SSZ Container derive infrastructure
│   ├── RLP.lean              RLP encode/decode
│   └── Proofs/
│       ├── UintProofs.lean   Uint roundtrip + arithmetic proofs
│       ├── ByteProofs.lean   Byte roundtrip proofs
│       ├── BitFieldProofs.lean  Bitfield roundtrip + operation proofs
│       └── CollectionProofs.lean  Collection roundtrip + property proofs
```

## 4. Sub-task Breakdown

### Group A: Core Infrastructure (X1-A1 through X1-A3)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X1-A1 | **Define `SSZError` inductive type.** Variants: `typeMismatch (expected actual : String)`, `sizeMismatch (expected actual : Nat)`, `outOfBounds (index limit : Nat)`, `deserializationFailed (msg : String)`, `offsetOverflow`, `delimiterNotFound`. This is the shared error type for all SSZ operations. | `Prelude.lean` | ~15 | — |
| X1-A2 | **Define `LeanEthError` inductive and `LeanEthM` monad.** `LeanEthError` wraps `SSZError` plus consensus-specific errors (added in later phases). `LeanEthM α := Except LeanEthError α`. Prove `LawfulMonad LeanEthM` (inherits from `Except`). Define `LeanEnvMode : Type := { test, prod }` config. | `Prelude.lean` | ~25 | X1-A1 |
| X1-A3 | **Define `SSZSerializable` typeclass.** `class SSZSerializable (α : Type) where isFixedSize : Bool; fixedByteLength : isFixedSize = true → Nat; serialize : α → ByteArray; deserialize : ByteArray → Except SSZError α`. Add helper: `encodeThenDecode [SSZSerializable α] (x : α) : Except SSZError α := deserialize (serialize x)`. | `Types/SSZBase.lean` | ~30 | X1-A1 |

### Group B: Unsigned Integers (X1-B1 through X1-B6)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X1-B1 | **Define `BaseUint` structure.** `structure BaseUint (bits : Nat) where val : Nat; h_bound : val < 2 ^ bits`. Derive `DecidableEq`, `Repr`, `Inhabited` (default 0). Add `BEq` via `DecidableEq`. Add `Ord` via `val` comparison. Add `Hashable` via `hash val`. | `Types/Uint.lean` | ~30 | — |
| X1-B2 | **Define concrete Uint types and constructors.** `abbrev Uint8 := BaseUint 8`, `Uint16 := BaseUint 16`, `Uint32 := BaseUint 32`, `Uint64 := BaseUint 64`. For each: `ofNat` (modular reduction), `toNat`, `max` (all bits set), `isReserved` (zero sentinel). | `Types/Uint.lean` | ~40 | X1-B1 |
| X1-B3 | **Define Uint arithmetic operations.** For `BaseUint bits`: `add` (modular), `sub` (wrapping), `mul`, `div`, `mod`. Comparisons: `lt`, `le`, `gt`, `ge`. Bitwise: `land`, `lor`, `lxor`, `shiftLeft`, `shiftRight`. | `Types/Uint.lean` | ~60 | X1-B2 |
| X1-B4 | **Define Uint SSZ serialization.** `SSZSerializable` instance: `isFixedSize := true`, `fixedByteLength := bits / 8`. Serialize as little-endian bytes. Deserialize with bounds check. | `Types/Uint.lean` | ~40 | X1-B2, X1-A3 |
| X1-B5 | **Prove Uint arithmetic properties.** (1) `add_comm`. (2) `add_assoc`. (3) `mul_comm`. (4) `mul_assoc`. (5) `ofNat_toNat_id`. (6) `add_sub_cancel` (no-wrap). | `Types/Proofs/UintProofs.lean` | ~45 | X1-B3 |
| X1-B6 | **Prove Uint serialization roundtrip.** (1) `uint_encode_decode_roundtrip : ∀ x, deserialize (serialize x) = .ok x`. (2) `uint_decode_encode_roundtrip : ∀ bs, bs.size = bits/8 → serialize (deserialize bs).get! = bs`. | `Types/Proofs/UintProofs.lean` | ~35 | X1-B4 |

### Group C: Byte Types (X1-C1 through X1-C3)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X1-C1 | **Define `BaseBytes` and `BaseByteList`.** `BaseBytes n` (fixed-size), `BaseByteList limit` (variable with bound). Concrete types: `Bytes1` through `Bytes65`. `ZERO_HASH : Bytes32`. SSZ instances. | `Types/Bytes.lean` | ~80 | — |
| X1-C2 | **Define byte operations.** `BaseByteList`: `length`, `get?`, `append`, `slice`, `toByteArray`. | `Types/Bytes.lean` | ~30 | X1-C1 |
| X1-C3 | **Prove byte roundtrip properties.** `bytes_encode_decode_roundtrip`, `bytelist_encode_decode_roundtrip`, `ZERO_HASH_size`. | `Types/Proofs/ByteProofs.lean` | ~35 | X1-C1, X1-C2, X1-A3 |

### Group D: Boolean (X1-D1)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X1-D1 | **Define SSZ `Boolean` type.** `structure SSZBoolean where val : Bool`. SSZ: 1 byte (0x00/0x01). Reject byte > 1. Prove `boolean_encode_decode_roundtrip` and `boolean_deserialize_rejects_invalid`. | `Types/Boolean.lean` | ~35 | X1-A3 |

### Group E: Bitfields (X1-E1 through X1-E5)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X1-E1 | **Define `BaseBitvector`.** Fixed-length bit array. Ops: `get`, `set`, `and`, `or`, `not`, `popcount`. | `Types/BitFields.lean` | ~50 | — |
| X1-E2 | **Define `BaseBitlist`.** Variable-length bit array with limit. Ops: `get`, `set`, `length`, `extend`, `shiftWindow`, `append`, `toValidatorIndices` (extract set-bit positions). | `Types/BitFields.lean` | ~55 | — |
| X1-E3 | **Define bitfield SSZ serialization.** Bitvector: packed little-endian, fixed-size. Bitlist: packed + delimiter bit, variable-size. | `Types/BitFields.lean` | ~60 | X1-E1, X1-E2, X1-A3 |
| X1-E4 | **Prove bitfield roundtrip properties.** `bitvector_encode_decode_roundtrip`, `bitlist_encode_decode_roundtrip`, `bitlist_delimiter_correct`. | `Types/Proofs/BitFieldProofs.lean` | ~40 | X1-E3 |
| X1-E5 | **Prove bitfield operation correctness.** `bitvector_and_comm`, `popcount_or_le`, `extend_preserves_existing`, `shiftWindow_length`, `shiftWindow_correctness`, `toValidatorIndices_sound`. | `Types/Proofs/BitFieldProofs.lean` | ~45 | X1-E1, X1-E2 |

### Group F: Collections (X1-F1 through X1-F4)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X1-F1 | **Define `SSZVector`.** Fixed-length typed collection. Ops: `get`, `set`, `map`, `foldl`, `toList`. SSZ: fixed-size if elements fixed; offset table otherwise. | `Types/Collections.lean` | ~60 | X1-A3 |
| X1-F2 | **Define `SSZList`.** Variable-length typed collection with limit. Ops: `push`, `get?`, `length`, `map`, `filter`, `foldl`, `toList`, `isEmpty`. SSZ: always variable-size. | `Types/Collections.lean` | ~60 | X1-A3 |
| X1-F3 | **Prove collection roundtrip.** `sszVector_roundtrip`, `sszList_roundtrip`, `sszVector_length_preserved`. | `Types/Proofs/CollectionProofs.lean` | ~35 | X1-F1, X1-F2 |
| X1-F4 | **Prove collection operation correctness.** `sszList_push_length`, `sszVector_get_set`, `sszVector_get_set_ne`. | `Types/Proofs/CollectionProofs.lean` | ~30 | X1-F1, X1-F2 |

### Group G: Container Derive & RLP (X1-G1 through X1-G3)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X1-G1 | **Define SSZ Container serialization framework.** `containerSerialize`: write fixed fields in order, offset table for variable fields, then variable data. `containerDeserialize`: parse offsets, extract fields. `mkContainerSSZ`: helper to produce `SSZSerializable` from field serializers. | `Types/Container.lean` | ~80 | X1-A3, X1-B4 |
| X1-G2 | **Prove Container roundtrip.** `container_roundtrip` (given all field roundtrips). `container_offset_correctness` (offsets point to correct data). | `Types/Proofs/CollectionProofs.lean` | ~50 | X1-G1 |
| X1-G3 | **Define RLP encoding/decoding.** `inductive RLPItem | bytes | list`. `encodeRLP`, `decodeRLP`. Prove `rlp_roundtrip`. Used only for ENR (X9). | `Types/RLP.lean` | ~70 | — |

### Group H: Build & Test Scaffold (X1-H1 through X1-H2)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X1-H1 | **Create project scaffold.** `lakefile.toml` with `LeanEth` library target. `lean-toolchain` pinned to v4.28.0. `LeanEth.lean` re-export hub. Verify `lake build LeanEth` succeeds. | `lakefile.toml`, `lean-toolchain`, `LeanEth.lean` | ~40 | All X1-* |
| X1-H2 | **Create SSZ roundtrip test suite.** `tests/SSZRoundtripSuite.lean`: Uint8/16/32/64, Bytes32, Boolean, Bitvector, Bitlist, Vector, List, Container roundtrips. Golden fixture `tests/fixtures/ssz_roundtrip.expected`. | `tests/SSZRoundtripSuite.lean`, `tests/fixtures/ssz_roundtrip.expected` | ~50 | X1-H1 |

## 5. Intra-phase Dependency Graph

```
X1-A1 → X1-A2 → X1-A3 ─────────────────────────────────────────┐
                  │                                               │
X1-B1 → X1-B2 → X1-B3 → X1-B5                                  │
              └→ X1-B4 → X1-B6                                   │
                                                                  │
X1-C1 → X1-C2 → X1-C3                                           │
X1-D1 ────────────┘                                               │
                                                                  │
X1-E1 → X1-E3 → X1-E4                                           │
X1-E2 ──┘    └→ X1-E5                                            │
                                                                  │
X1-F1 → X1-F3                                                    │
X1-F2 ──┘ → X1-F4                                                │
                                                                  │
X1-G1 → X1-G2                                                    │
X1-G3 (independent)                                               │
                                                                  │
All → X1-H1 → X1-H2 ────────────────────────────────────────────┘
```

**Parallelizable**: B, C, D, E, F, G3 can all proceed once A1-A3 are complete.

## 6. Exit Criteria

- [ ] All 10+ Lean files compile with `lake build LeanEth`
- [ ] Zero `sorry` in all modules
- [ ] Encode/decode roundtrip proofs for all 8 type families
- [ ] Uint arithmetic proofs: commutativity, associativity, roundtrip
- [ ] Bitfield operation proofs: extend, shift, popcount, toValidatorIndices
- [ ] Collection proofs: get/set, length preservation, push
- [ ] Container offset correctness proved
- [ ] `tests/SSZRoundtripSuite.lean` passes with fixture match
- [ ] `lake build LeanEth.Types.Uint` (and each module individually) succeeds
