# Phase X1: Foundation Types & Prelude

**Version**: v0.1.0
**Status**: PLANNED
**Sub-tasks**: 23 atomic units
**Dependencies**: None (foundation phase)
**Estimated Lean LoC**: ~900
**Files created**: 9 new files

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
│   └── Proofs.lean           All roundtrip and arithmetic proofs
```

## 4. Sub-task Breakdown

### Group A: Core Infrastructure (X1-A1 through X1-A3)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X1-A1 | **Define `SSZError` inductive type.** Variants: `typeMismatch (expected actual : String)`, `sizeMismatch (expected actual : Nat)`, `outOfBounds (index limit : Nat)`, `deserializationFailed (msg : String)`, `offsetOverflow`, `delimiterNotFound`. This is the shared error type for all SSZ operations. | `Prelude.lean` | ~15 | — |
| X1-A2 | **Define `LeanEthError` inductive and `LeanEthM` monad.** `LeanEthError` wraps `SSZError` plus consensus-specific errors (added in later phases). `LeanEthM α := Except LeanEthError α`. Prove `LawfulMonad LeanEthM` (inherits from `Except`). Define `LeanEnvMode : Type := { test, prod }` config. | `Prelude.lean` | ~25 | X1-A1 |
| X1-A3 | **Define `SSZSerializable` typeclass.** `class SSZSerializable (α : Type) where isFixedSize : Bool; fixedByteLength : isFixedSize = true → Nat; serialize : α → ByteArray; deserialize : ByteArray → Except SSZError α`. This is the interface all SSZ types implement. Add helper: `encodeThenDecode [SSZSerializable α] (x : α) : Except SSZError α := deserialize (serialize x)`. | `Types/SSZBase.lean` | ~30 | X1-A1 |

### Group B: Unsigned Integers (X1-B1 through X1-B5)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X1-B1 | **Define `BaseUint` structure.** `structure BaseUint (bits : Nat) where val : Nat; h_bound : val < 2 ^ bits`. Derive `DecidableEq`, `Repr`, `Inhabited` (default 0). Add `BEq` instance via `DecidableEq`. Add `Ord` instance via `val` comparison. Add `Hashable` instance via `hash val`. | `Types/Uint.lean` | ~30 | — |
| X1-B2 | **Define concrete Uint types and constructors.** `abbrev Uint8 := BaseUint 8`, `Uint16 := BaseUint 16`, `Uint32 := BaseUint 32`, `Uint64 := BaseUint 64`. For each, define `ofNat : Nat → UintN` with modular reduction (`val := n % 2^bits`, proof by `Nat.mod_lt`). Define `toNat : UintN → Nat := (·.val)`. Define `max : UintN` (all bits set). Define sentinel: `isReserved : UintN → Bool := (·.val == 0)`. | `Types/Uint.lean` | ~40 | X1-B1 |
| X1-B3 | **Define Uint arithmetic operations.** For each `BaseUint bits`: `add (a b : BaseUint bits) : BaseUint bits := ofNat (a.val + b.val)` (modular). Similarly `sub` (wrapping: `(a.val + 2^bits - b.val) % 2^bits`), `mul`, `div`, `mod`. Define `lt`, `le`, `gt`, `ge` comparisons. Define `land`, `lor`, `lxor`, `shiftLeft`, `shiftRight` bitwise ops. | `Types/Uint.lean` | ~60 | X1-B2 |
| X1-B4 | **Define Uint SSZ serialization.** `SSZSerializable` instance for `BaseUint bits`: `isFixedSize := true`, `fixedByteLength := bits / 8`. `serialize`: little-endian encoding to `bits/8` bytes. `deserialize`: little-endian decoding with bounds check. Implementation: extract bytes via repeated `val / 256` and `val % 256`. | `Types/Uint.lean` | ~40 | X1-B2, X1-A3 |
| X1-B5 | **Prove Uint arithmetic and roundtrip properties.** Theorems: (1) `add_comm : add a b = add b a`. (2) `add_assoc`. (3) `mul_comm`. (4) `mul_assoc`. (5) `ofNat_toNat_id : toNat (ofNat n) = n % 2^bits`. (6) `uint_encode_decode_roundtrip : ∀ (x : BaseUint bits), deserialize (serialize x) = .ok x`. (7) `uint_decode_encode_roundtrip : ∀ bs, bs.size = bits/8 → serialize (deserialize bs).get! = bs`. (8) `add_sub_cancel : b.val ≤ a.val → sub (add a b) b = a` (no-wrap case). | `Types/Proofs.lean` | ~80 | X1-B3, X1-B4 |

### Group C: Byte Types (X1-C1 through X1-C3)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X1-C1 | **Define `BaseBytes` (fixed-size byte array).** `structure BaseBytes (n : Nat) where data : ByteArray; h_len : data.size = n`. Derive `DecidableEq`, `Repr`, `BEq`, `Hashable`. Define concrete types: `Bytes1 := BaseBytes 1`, `Bytes4 := BaseBytes 4`, `Bytes12 := BaseBytes 12`, `Bytes16 := BaseBytes 16`, `Bytes20 := BaseBytes 20`, `Bytes32 := BaseBytes 32`, `Bytes33 := BaseBytes 33`, `Bytes52 := BaseBytes 52`, `Bytes64 := BaseBytes 64`, `Bytes65 := BaseBytes 65`. Define `ZERO_HASH : Bytes32` (32 zero bytes). Define `Bytes32.zero := ZERO_HASH`. | `Types/Bytes.lean` | ~50 | — |
| X1-C2 | **Define `BaseByteList` (variable-length byte array with limit).** `structure BaseByteList (limit : Nat) where data : ByteArray; h_bound : data.size ≤ limit`. Define `ByteListMiB := BaseByteList (1024 * 1024)`. Add `length`, `get?`, `append`, `slice`, `toByteArray`. SSZ serialization: `isFixedSize := false`, serialize is identity (raw bytes), deserialize checks length ≤ limit. | `Types/Bytes.lean` | ~40 | — |
| X1-C3 | **Define SSZ instances and byte roundtrip proofs.** `SSZSerializable` instance for `BaseBytes n`: `isFixedSize := true`, `fixedByteLength := n`, serialize/deserialize are identity on the underlying `ByteArray` with length validation. Prove: `bytes_encode_decode_roundtrip : deserialize (serialize x) = .ok x`. Prove: `bytelist_encode_decode_roundtrip`. Prove: `ZERO_HASH_size : ZERO_HASH.data.size = 32`. | `Types/Bytes.lean`, `Types/Proofs.lean` | ~40 | X1-C1, X1-C2, X1-A3 |

### Group D: Boolean (X1-D1)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X1-D1 | **Define SSZ `Boolean` type.** `structure SSZBoolean where val : Bool`. SSZ encoding: 1 byte, `0x00` for false, `0x01` for true. Deserialize rejects any byte > 1. Derive `DecidableEq`, `Repr`, `BEq`. Add `SSZSerializable` instance. Prove `boolean_encode_decode_roundtrip`. Prove `boolean_deserialize_rejects_invalid : bs.get! 0 > 1 → deserialize bs = .error ...`. | `Types/Boolean.lean` | ~35 | X1-A3 |

### Group E: Bitfields (X1-E1 through X1-E4)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X1-E1 | **Define `BaseBitvector` (compile-time fixed-length bit array).** `structure BaseBitvector (len : Nat) where bits : Array Bool; h_len : bits.size = len`. Add `get : Fin len → Bool`, `set : Fin len → Bool → BaseBitvector len`, `and : BaseBitvector len → BaseBitvector len → BaseBitvector len` (pointwise), `or`, `not`. Add `popcount : BaseBitvector len → Nat` (count true bits). Derive `DecidableEq`, `Repr`, `BEq`. | `Types/BitFields.lean` | ~50 | — |
| X1-E2 | **Define `BaseBitlist` (runtime variable-length bit array with limit).** `structure BaseBitlist (limit : Nat) where bits : Array Bool; h_bound : bits.size ≤ limit`. Add `get : Nat → Option Bool`, `set : Nat → Bool → BaseBitlist limit`, `length : Nat := bits.size`, `extend : Nat → BaseBitlist limit` (grow to new length, false-fill), `shiftWindow : Nat → BaseBitlist limit` (drop first N bits), `append : Bool → BaseBitlist limit`. | `Types/BitFields.lean` | ~50 | — |
| X1-E3 | **Define bitfield SSZ serialization.** Bitvector encoding: pack bits little-endian within bytes (`bit[i]` → byte `i/8`, position `i%8`). Byte count = `(len + 7) / 8`. Bitvector `isFixedSize := true`. Bitlist encoding: same packing + delimiter bit (set highest bit to 1 after all data bits). Bitlist `isFixedSize := false`. Deserialize: bitvector reads exact bytes and unpacks; bitlist finds delimiter (highest set bit in last byte), strips it. | `Types/BitFields.lean` | ~60 | X1-E1, X1-E2, X1-A3 |
| X1-E4 | **Prove bitfield roundtrip and operation correctness.** (1) `bitvector_encode_decode_roundtrip`. (2) `bitlist_encode_decode_roundtrip`. (3) `bitvector_delimiter_not_needed` (bitvectors don't use delimiters). (4) `bitlist_delimiter_correct : ∀ bl, the delimiter bit is the highest set bit in the encoded output`. (5) `bitvector_and_comm : and a b = and b a`. (6) `popcount_or_le : popcount (or a b) ≤ popcount a + popcount b`. (7) `extend_preserves_existing : ∀ i < bl.length, (bl.extend n).get i = bl.get i`. (8) `shiftWindow_length : (bl.shiftWindow n).length = bl.length - n` (clamped). | `Types/Proofs.lean` | ~70 | X1-E1, X1-E2, X1-E3 |

### Group F: Collections (X1-F1 through X1-F3)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X1-F1 | **Define `SSZVector` (fixed-length typed collection).** `structure SSZVector (α : Type) (len : Nat) [SSZSerializable α] where elems : Array α; h_len : elems.size = len`. Add `get : Fin len → α`, `set : Fin len → α → SSZVector α len`, `map : (α → β) → SSZVector β len`, `foldl : (β → α → β) → β → β`, `toList : List α`, `toArray : Array α`. SSZ: `isFixedSize := SSZSerializable.isFixedSize α`. Serialize: if fixed-size elements, concatenate encodings; if variable-size, write offset table (Uint32 each) then variable data. | `Types/Collections.lean` | ~60 | X1-A3 |
| X1-F2 | **Define `SSZList` (variable-length typed collection with limit).** `structure SSZList (α : Type) (limit : Nat) [SSZSerializable α] where elems : Array α; h_bound : elems.size ≤ limit`. Add `push : α → Option (SSZList α limit)` (returns none if at limit), `get? : Nat → Option α`, `length : Nat`, `map`, `filter`, `foldl`, `toList`, `toArray`, `isEmpty`. SSZ: `isFixedSize := false` (always variable — length must be mixed in). Serialize: same as vector but without fixed length assumption. | `Types/Collections.lean` | ~60 | X1-A3 |
| X1-F3 | **Prove collection roundtrip and length properties.** (1) `sszVector_roundtrip : ∀ v, deserialize (serialize v) = .ok v` (given element roundtrip). (2) `sszList_roundtrip` (similarly). (3) `sszVector_length_preserved : (deserialize (serialize v)).get!.elems.size = len`. (4) `sszList_push_length : (l.push x).map (·.length) = if l.length < limit then some (l.length + 1) else none`. (5) `sszVector_get_set : (v.set i x).get i = x`. (6) `sszVector_get_set_ne : i ≠ j → (v.set i x).get j = v.get j`. | `Types/Proofs.lean` | ~60 | X1-F1, X1-F2 |

### Group G: Container Derive & RLP (X1-G1 through X1-G3)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X1-G1 | **Define SSZ Container serialization framework.** Rather than a Lean 4 derive macro (complex metaprogramming), define a manual pattern: for any structure with `SSZSerializable` fields, provide a function `containerSerialize` that: (a) writes all fixed-size fields in declaration order, (b) for each variable-size field writes a Uint32 offset, (c) appends all variable-size field data. Similarly `containerDeserialize`. Provide a helper `mkContainerSSZ` that takes field serializers and produces an `SSZSerializable` instance. | `Types/Container.lean` | ~80 | X1-A3, X1-B4 |
| X1-G2 | **Prove Container serialization roundtrip.** `container_roundtrip : ∀ c, containerDeserialize (containerSerialize c) = .ok c` (given all field roundtrips hold and no offset overflow). Prove `container_offset_correctness : all offsets in serialized output correctly point to variable field data`. | `Types/Proofs.lean` | ~50 | X1-G1 |
| X1-G3 | **Define RLP encoding/decoding.** `inductive RLPItem | bytes : ByteArray → RLPItem | list : List RLPItem → RLPItem`. `encodeRLP : RLPItem → ByteArray` (single byte < 0x80; short string 0x80+len; long string 0xb7+lenlen; short list 0xc0+len; long list 0xf7+lenlen). `decodeRLP : ByteArray → Except RLPError RLPItem`. Prove `rlp_roundtrip : decodeRLP (encodeRLP item) = .ok item`. Used only for ENR encoding (Phase X9). | `Types/RLP.lean` | ~70 | — |

### Group H: Build & Test Scaffold (X1-H1)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X1-H1 | **Create project scaffold and build verification.** Create `lakefile.toml` with `LeanEth` library target. Create `lean-toolchain` pinned to `leanprover/lean4:v4.28.0`. Create `LeanEth.lean` re-export hub importing all type modules. Create `tests/SSZRoundtripSuite.lean` with test cases: Uint8/16/32/64 roundtrip, Bytes32 roundtrip, Boolean roundtrip, Bitvector/Bitlist roundtrip, Vector/List roundtrip, Container roundtrip. Create `tests/fixtures/ssz_roundtrip.expected` golden output. Verify: `lake build LeanEth` succeeds. | `lakefile.toml`, `lean-toolchain`, `LeanEth.lean`, `tests/SSZRoundtripSuite.lean`, `tests/fixtures/ssz_roundtrip.expected` | ~80 | All X1-* |

## 5. Intra-phase Dependency Graph

```
X1-A1 ──→ X1-A2 ──→ X1-A3 ──────────────────────────────────────┐
                      │                                            │
X1-B1 → X1-B2 → X1-B3                                            │
              │       │                                            │
              └→ X1-B4 ─→ X1-B5                                   │
                   │                                               │
X1-C1 ─→ X1-C3 ──┘                                               │
X1-C2 ──┘  │                                                      │
           │                                                       │
X1-D1 ────┘                                                       │
                                                                   │
X1-E1 ──→ X1-E3 ──→ X1-E4                                        │
X1-E2 ──┘                                                         │
                                                                   │
X1-F1 ──→ X1-F3                                                   │
X1-F2 ──┘                                                         │
                                                                   │
X1-G1 ──→ X1-G2                                                   │
X1-G3 (independent)                                                │
                                                                   │
All ──→ X1-H1 (build verification) ───────────────────────────────┘
```

**Parallelizable groups**: B, C, D, E, F, G3 can all proceed in parallel once
A1-A3 are complete (they only need the SSZSerializable typeclass).

## 6. Exit Criteria

- [ ] All 9 Lean files compile with `lake build LeanEth`
- [ ] Zero `sorry` in all modules
- [ ] Encode/decode roundtrip proofs for: Uint8/16/32/64, Bytes (all sizes),
      Boolean, Bitvector, Bitlist, SSZVector, SSZList, Container, RLP
- [ ] Uint arithmetic proofs: commutativity, associativity, roundtrip
- [ ] Bitfield operation proofs: extend preserves, shift correctness
- [ ] Collection proofs: get/set, length preservation
- [ ] `tests/SSZRoundtripSuite.lean` passes with fixture match
- [ ] `lake build LeanEth.Types.Uint` (and each module individually) succeeds

## 7. Acceptance Test

```bash
# Build all type modules
source ~/.elan/env && lake build LeanEth

# Run roundtrip test suite
lake exe ssz_roundtrip_suite

# Verify zero sorry
grep -r "sorry" LeanEth/Types/ LeanEth/Prelude.lean && echo "FAIL: sorry found" || echo "PASS: no sorry"
```
