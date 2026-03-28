# Phase X3: KoalaBear Field & Poseidon2 Hash

**Version**: v0.3.0
**Status**: PLANNED
**Sub-tasks**: 14 atomic units
**Dependencies**: X1 (Foundation Types)
**Estimated Lean LoC**: ~700
**Files created**: 5 new files
**Parallelizable with**: X2 (SSZ Merkleization)

## 1. Objective

Formalize the KoalaBear prime field (p = 2³¹ - 2²⁴ + 1) and the Poseidon2
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
│   └── Proofs.lean           Field law proofs
├── Poseidon2/
│   ├── Constants.lean        Round constants, MDS matrices
│   ├── Permutation.lean      Round functions, full permutation
│   └── Proofs.lean           Bijectivity, algebraic properties
└── Hash.lean                 Hash dispatch (SHA256/Poseidon2)
```

## 4. Sub-task Breakdown

### Group A: KoalaBear Field (X3-A1 through X3-A5)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X3-A1 | **Define KoalaBear prime and `Fp` type.** `def P : Nat := 2^31 - 2^24 + 1` (= 2013265921). `def P_BYTES : Nat := 4`. `def TWO_ADICITY : Nat := 24`. `structure Fp where val : Fin P`. Derive `DecidableEq`, `Repr`, `Inhabited` (default 0), `BEq`, `Hashable`. Add `SSZSerializable` instance: `isFixedSize := true`, `fixedByteLength := 4`, serialize as 4-byte LE, deserialize with bounds check `< P`. | `Crypto/KoalaBear/Field.lean` | ~40 | X1 |
| X3-A2 | **Prove P is prime.** `theorem P_prime : Nat.Prime P`. Strategy: use `native_decide` if available for this size, or provide an explicit Miller-Rabin witness. Also prove `P_gt_two : P > 2` and `P_odd : P % 2 = 1`. These are prerequisites for field law proofs. | `Crypto/KoalaBear/Proofs.lean` | ~15 | X3-A1 |
| X3-A3 | **Define Fp arithmetic operations.** `zero : Fp := ⟨0, by omega⟩`. `one : Fp := ⟨1, by omega⟩`. `add (a b : Fp) : Fp := ⟨(a.val + b.val) % P, Nat.mod_lt _ P_pos⟩`. `sub (a b : Fp) : Fp := ⟨(a.val + P - b.val) % P, ...⟩`. `neg (a : Fp) : Fp := sub zero a`. `mul (a b : Fp) : Fp := ⟨(a.val * b.val) % P, ...⟩`. `pow (a : Fp) (n : Nat) : Fp` (by repeated squaring). `inv (a : Fp) : Fp := pow a (P - 2)` (Fermat's little theorem). `div (a b : Fp) : Fp := mul a (inv b)`. | `Crypto/KoalaBear/Field.lean` | ~50 | X3-A1 |
| X3-A4 | **Prove KoalaBear field laws.** (1) `add_comm : add a b = add b a`. (2) `add_assoc : add (add a b) c = add a (add b c)`. (3) `add_zero : add a zero = a`. (4) `add_neg : add a (neg a) = zero`. (5) `mul_comm : mul a b = mul b a`. (6) `mul_assoc : mul (mul a b) c = mul a (mul b c)`. (7) `mul_one : mul a one = a`. (8) `left_distrib : mul a (add b c) = add (mul a b) (mul a c)`. These together with X3-A5 constitute a `Field` instance. | `Crypto/KoalaBear/Proofs.lean` | ~60 | X3-A3 |
| X3-A5 | **Prove multiplicative inverse and TWO_ADICITY.** (1) `inv_correct : a ≠ zero → mul a (inv a) = one`. Proof: Fermat's little theorem — `a^(P-1) = 1 mod P` for nonzero `a` in a prime field, so `a * a^(P-2) = a^(P-1) = 1`. (2) `two_adicity : ∃ k, k = 24 ∧ 2^k ∣ (P - 1) ∧ ¬(2^(k+1) ∣ (P - 1))`. (3) `fp_ssz_roundtrip : ∀ (x : Fp), deserialize (serialize x) = .ok x`. Instantiate `Field Fp` using X3-A4 + X3-A5. | `Crypto/KoalaBear/Proofs.lean` | ~40 | X3-A2, X3-A4 |

### Group B: Poseidon2 Permutation (X3-B1 through X3-B6)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X3-B1 | **Define Poseidon2 round constants.** Arrays of `Fp` values for external and internal rounds. `FULL_ROUNDS : Nat := 8`. `PARTIAL_ROUNDS_16 : Nat := 13`. `PARTIAL_ROUNDS_24 : Nat := 21`. External MDS matrix entries (4×4 circulant). Internal MDS diagonal entries. Per-round additive constants. Define `structure Poseidon2Params where width : Nat; fullRounds : Nat; partialRounds : Nat; mdsExternal : Array (Array Fp); mdsInternal : Array Fp; roundConstants : Array (Array Fp)`. | `Crypto/Poseidon2/Constants.lean` | ~80 | X3-A1 |
| X3-B2 | **Define S-box and round functions.** `sbox : Fp → Fp := fun x => mul x (mul x x)` (x³). `externalRound : Poseidon2Params → Array Fp → Nat → Array Fp` — for each element: add round constant, apply S-box, then multiply state by external MDS matrix. `internalRound : Poseidon2Params → Array Fp → Nat → Array Fp` — add round constant to first element only, apply S-box to first element only, then multiply by internal (diagonal) MDS. `initialLinearLayer : Poseidon2Params → Array Fp → Array Fp` — multiply by external MDS. | `Crypto/Poseidon2/Permutation.lean` | ~50 | X3-B1, X3-A3 |
| X3-B3 | **Define full Poseidon2 permutation.** `permute : Poseidon2Params → Array Fp → Array Fp`: (1) apply `initialLinearLayer`, (2) apply first `fullRounds/2` external rounds, (3) apply all `partialRounds` internal rounds, (4) apply last `fullRounds/2` external rounds. Define `PARAMS_16 : Poseidon2Params` (width=16) and `PARAMS_24 : Poseidon2Params` (width=24). Prove `permute_preserves_width : (permute p s).size = s.size` (when `s.size = p.width`). | `Crypto/Poseidon2/Permutation.lean` | ~40 | X3-B2 |
| X3-B4 | **Prove S-box bijectivity.** `sbox_injective : sbox a = sbox b → a = b`. Proof: since `gcd(3, P-1) = 1` for KoalaBear (because `P - 1 = 2013265920 = 2²⁴ × 3 × 5 × ...` — wait, need to verify. Actually: `P-1 = 2013265920`. Check if `3 ∣ (P-1)`: `2013265920 / 3 = 671088640`. So `gcd(3, P-1) = 3 ≠ 1`. This means x³ is NOT injective on all of F_P! Need to verify this carefully against leanSpec — the S-box may need to be `x^d` for a different `d`. If x³ is indeed used, then the permutation relies on the full structure (MDS + round keys) for bijectivity, not just the S-box. Document this subtlety. | `Crypto/Poseidon2/Proofs.lean` | ~30 | X3-A2, X3-B2 |
| X3-B5 | **Prove permutation bijectivity (structural).** Since the S-box alone may not be bijective, prove bijectivity of the full permutation structurally: (1) the MDS matrices are invertible over F_P (compute and verify determinant ≠ 0), (2) round constant addition is trivially invertible, (3) the composition of invertible functions is invertible. For the S-box: prove that `x → x³` composed with the linear layer and round constants produces a bijective round function. This may require AXIOM-CRYPTO-3 if a fully algebraic proof is intractable. | `Crypto/Poseidon2/Proofs.lean` | ~50 | X3-B4 |
| X3-B6 | **Define Poseidon2-based hash for SSZ integration.** `poseidon2Hash : ByteArray → Bytes32` — absorb input as F_P elements using a sponge construction over `permute`. `hashNodesPoseidon2 : Bytes32 → Bytes32 → Bytes32` — hash two 32-byte values. Register as `HashFunction` instance (from X2-B1). Define fork-parameterized dispatch: `def hashNodesForFork (fork : Fork) : Bytes32 → Bytes32 → Bytes32` selecting SHA256 or Poseidon2 based on fork. | `Crypto/Hash.lean` | ~35 | X3-B3, X2-B1 |

### Group C: Test & Integration (X3-C1 through X3-C3)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X3-C1 | **KoalaBear field arithmetic test vectors.** Add to `tests/CryptoSuite.lean`: spot checks for add, mul, inv on known values from Python reference. Verify `inv(inv(x)) = x` for sample values. Verify `a * inv(a) = 1` for nonzero samples. | `tests/CryptoSuite.lean` | ~25 | X3-A3 |
| X3-C2 | **Poseidon2 permutation test vectors.** Add test cases: permute known input state, compare output against Python `Poseidon2.permute()` for both PARAMS_16 and PARAMS_24. Minimum 4 test vectors (2 per width). | `tests/CryptoSuite.lean` | ~25 | X3-B3 |
| X3-C3 | **Hash function integration test.** Verify `poseidon2Hash` and `hashNodesPoseidon2` produce correct output for known inputs. Compare against Python `hash_tree_root` when using Poseidon2 mode. | `tests/CryptoSuite.lean` | ~15 | X3-B6 |

## 5. Key Technical Note: S-box Bijectivity

The KoalaBear prime `P = 2013265921` has `P - 1 = 2013265920 = 2²⁴ × 119`. Since
`gcd(3, P-1) = 3` (as `119 = 7 × 17`, and `P-1` is divisible by 3), the cube
map `x → x³` is **not** a permutation on `F_P`. Specifically, it is a 3-to-1
map on cubic residues.

However, the Poseidon2 permutation does not rely on the S-box being a
permutation in isolation. The security argument is that the composition of
nonlinear S-box layers with linear MDS layers across multiple rounds creates
an overall permutation. This is standard for algebraic hash constructions.

**Approach**: We prove the overall permutation is bijective by either:
1. Computing the inverse permutation explicitly (feasible for fixed constants)
2. Relying on AXIOM-CRYPTO-3 for the algebraic security claim

This is documented clearly in the axiom inventory.

## 6. Exit Criteria

- [ ] KoalaBear `Fp` type with all arithmetic operations
- [ ] `Field Fp` instance with 8 field law proofs
- [ ] `inv_correct` (multiplicative inverse) proved
- [ ] Poseidon2 permutation defined for both width-16 and width-24
- [ ] S-box behavior documented; bijectivity proof (structural or axiomatic)
- [ ] `poseidon2Hash` matches Python reference for test vectors
- [ ] Zero sorry in all crypto modules (AXIOM-CRYPTO-3 if needed is declared)
- [ ] `lake build LeanEth.Crypto.Poseidon2.Permutation` succeeds
