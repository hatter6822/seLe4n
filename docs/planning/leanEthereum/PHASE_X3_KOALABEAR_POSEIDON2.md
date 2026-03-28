# Phase X3: KoalaBear Field & Poseidon2 Hash

**Version**: v0.3.0
**Status**: PLANNED
**Sub-tasks**: 20 atomic units
**Dependencies**: X1 (Foundation Types)
**Estimated Lean LoC**: ~850
**Files created**: 6 new files
**Parallelizable with**: X2 (SSZ Merkleization)

## 1. Objective

Formalize the KoalaBear prime field (p = 2^31 - 2^24 + 1) and the Poseidon2
permutation — the algebraic hash function used for XMSS signatures and
SSZ Merkleization in the Lean consensus specification. This phase delivers
a `Field` instance with all laws proved and a bijectivity proof for the
Poseidon2 permutation.

## 2. Reference Files

| Python File | Lean Target | Description |
|-------------|-------------|-------------|
| `src/lean_spec/subspecs/koalabear/field.py` | `LeanEth/Crypto/KoalaBear/Field.lean` | Field arithmetic |
| `src/lean_spec/subspecs/poseidon2/permutation.py` | `LeanEth/Crypto/Poseidon2/Permutation.lean` | Permutation |
| `src/lean_spec/subspecs/poseidon2/constants.py` | `LeanEth/Crypto/Poseidon2/Constants.lean` | Round constants |

## 3. Source Layout

```
LeanEth/Crypto/
├── KoalaBear/
│   ├── Field.lean            Fp type, arithmetic operations
│   └── Proofs.lean           Field law proofs, primality
├── Poseidon2/
│   ├── Constants.lean        Round constants, MDS matrices
│   ├── Permutation.lean      Round functions, full permutation
│   └── Proofs.lean           Bijectivity, algebraic properties
└── Hash.lean                 Hash dispatch (SHA256/Poseidon2)
```

## 4. Sub-task Breakdown

### Group A: KoalaBear Field (X3-A1 through X3-A7)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X3-A1 | **Define KoalaBear prime and `Fp` type.** `def P : Nat := 2013265921` (= 2^31 - 2^24 + 1). `structure Fp where val : Fin P`. Derive instances. SSZ: 4-byte LE. | `Crypto/KoalaBear/Field.lean` | ~35 | X1 |
| X3-A2 | **Prove P is prime.** `theorem P_prime : Nat.Prime P`. Via `native_decide` or explicit witness. Prove `P_gt_two` and `P_odd`. | `Crypto/KoalaBear/Proofs.lean` | ~15 | X3-A1 |
| X3-A3 | **Define Fp arithmetic.** `zero`, `one`, `add`, `sub`, `neg`, `mul`, `pow` (repeated squaring), `inv` (Fermat: a^(P-2)), `div`. | `Crypto/KoalaBear/Field.lean` | ~50 | X3-A1 |
| X3-A4 | **Prove additive field laws.** (1) `add_comm`. (2) `add_assoc`. (3) `add_zero`. (4) `add_neg`. | `Crypto/KoalaBear/Proofs.lean` | ~30 | X3-A3 |
| X3-A5 | **Prove multiplicative field laws.** (1) `mul_comm`. (2) `mul_assoc`. (3) `mul_one`. (4) `left_distrib`. | `Crypto/KoalaBear/Proofs.lean` | ~30 | X3-A3 |
| X3-A6 | **Prove inverse and instantiate Field.** `inv_correct : a ≠ zero → mul a (inv a) = one`. Proof via Fermat's little theorem. `two_adicity : 2^24 ∣ (P-1) ∧ ¬(2^25 ∣ (P-1))`. `fp_ssz_roundtrip`. Instantiate `Field Fp`. | `Crypto/KoalaBear/Proofs.lean` | ~40 | X3-A2, X3-A4, X3-A5 |
| X3-A7 | **KoalaBear test vectors.** Spot checks: add, mul, inv on known values from Python. Verify `inv(inv(x)) = x`, `a * inv(a) = 1` for samples. | `tests/CryptoSuite.lean` | ~20 | X3-A3 |

### Group B: Poseidon2 Permutation (X3-B1 through X3-B8)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X3-B1 | **Define Poseidon2 parameters structure.** `structure Poseidon2Params where width : Nat; fullRounds : Nat; partialRounds : Nat; mdsExternal : Array (Array Fp); mdsInternal : Array Fp; roundConstants : Array (Array Fp)`. Constants: `FULL_ROUNDS := 8`, `PARTIAL_ROUNDS_16 := 20`, `PARTIAL_ROUNDS_24 := 21`. | `Crypto/Poseidon2/Constants.lean` | ~40 | X3-A1 |
| X3-B2 | **Define round constant arrays.** Embed pre-computed Fp constants for external rounds (width×fullRounds entries), internal rounds (partialRounds entries), and MDS matrices (4×4 circulant external, diagonal internal). These are large literal arrays — use `native_decide` or pre-computed `Fin P` values. | `Crypto/Poseidon2/Constants.lean` | ~60 | X3-B1, X3-A1 |
| X3-B3 | **Define S-box and linear layers.** `sbox : Fp → Fp := fun x => mul x (mul x x)` (x^3). `externalLinearLayer : Poseidon2Params → Array Fp → Array Fp` — M4×M4 block structure with circulant outer layer. `internalLinearLayer : Poseidon2Params → Array Fp → Array Fp` — M = J + D (all-ones + diagonal), O(width) computation. | `Crypto/Poseidon2/Permutation.lean` | ~50 | X3-B1, X3-A3 |
| X3-B4 | **Define round functions.** `externalRound : Poseidon2Params → Array Fp → Nat → Array Fp` — add constants to ALL state, S-box ALL, external linear layer. `internalRound : Poseidon2Params → Array Fp → Nat → Array Fp` — add constant to state[0] only, S-box state[0] only, internal linear layer. `initialLinearLayer : Poseidon2Params → Array Fp → Array Fp`. | `Crypto/Poseidon2/Permutation.lean` | ~40 | X3-B3 |
| X3-B5 | **Define full permutation.** `permute : Poseidon2Params → Array Fp → Array Fp`: (1) initialLinearLayer, (2) first fullRounds/2 external rounds, (3) all partialRounds internal rounds, (4) last fullRounds/2 external rounds. Define `PARAMS_16` and `PARAMS_24`. Prove `permute_preserves_width`. | `Crypto/Poseidon2/Permutation.lean` | ~35 | X3-B4 |
| X3-B6 | **Document S-box non-bijectivity and prove full permutation bijectivity.** Since `gcd(3, P-1) = 3`, x^3 is NOT injective on F_P alone. Prove bijectivity of the full permutation structurally: MDS matrices are invertible (det ≠ 0), round constant addition is invertible, composition of invertible layers is invertible. If fully algebraic proof is intractable, rely on AXIOM-CRYPTO-3. | `Crypto/Poseidon2/Proofs.lean` | ~55 | X3-A2, X3-B5 |
| X3-B7 | **Define Poseidon2-based hash for SSZ integration.** `poseidon2Hash : ByteArray → Bytes32` — sponge construction over `permute`. `hashNodesPoseidon2 : Bytes32 → Bytes32 → Bytes32`. Register as `HashFunction` instance. Define fork-parameterized dispatch. | `Crypto/Hash.lean` | ~35 | X3-B5, X2-B1 |
| X3-B8 | **Poseidon2 test vectors.** Permute known inputs for PARAMS_16 and PARAMS_24, compare against Python. Hash integration test. Minimum 6 test vectors. | `tests/CryptoSuite.lean` | ~25 | X3-B5, X3-B7 |

## 5. Key Technical Note: S-box Bijectivity

The KoalaBear prime `P = 2013265921` has `P - 1 = 2013265920`. Since
`gcd(3, P-1) = 3`, the cube map `x → x^3` is **not** a permutation on F_P.

However, the Poseidon2 permutation does not rely on the S-box being a
permutation in isolation. The security argument is that the composition of
nonlinear S-box layers with linear MDS layers across multiple rounds creates
an overall permutation. This is standard for algebraic hash constructions.

**Approach**: Structural bijectivity proof or AXIOM-CRYPTO-3 fallback.

## 6. Exit Criteria

- [ ] KoalaBear `Fp` with all arithmetic, `Field Fp` instance
- [ ] 8 field law proofs + inverse correctness
- [ ] Poseidon2 permutation for width-16 and width-24
- [ ] S-box documented; bijectivity proof (structural or axiomatic)
- [ ] `poseidon2Hash` matches Python reference
- [ ] Zero sorry (AXIOM-CRYPTO-3 if needed is declared)
- [ ] `lake build LeanEth.Crypto.Poseidon2.Permutation` succeeds
