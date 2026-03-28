# Phase X4: XMSS Signature Scheme

**Version**: v0.4.0
**Status**: PLANNED
**Sub-tasks**: 22 atomic units
**Dependencies**: X3 (KoalaBear + Poseidon2), X1 (Types)
**Estimated Lean LoC**: ~1,200
**Files created**: 8 new files

## 1. Objective

Formalize the XMSS (eXtended Merkle Signature Scheme) — the post-quantum
hash-based signature scheme used for all block and attestation signatures in
the Lean consensus specification. XMSS is the most complex cryptographic
component, involving Merkle tree construction, Winternitz one-time signatures,
top-bottom tree traversal for key management, and signature aggregation.

This phase delivers: keygen, sign, verify, aggregate, plus machine-checked
proofs of sign/verify roundtrip, one-time key safety, and aggregation correctness.

## 2. Reference Files

| Python File | Lean Target | Description |
|-------------|-------------|-------------|
| `src/lean_spec/subspecs/xmss/containers.py` | `Crypto/XMSS/Types.lean` | Data structures |
| `src/lean_spec/subspecs/xmss/constants.py` | `Crypto/XMSS/Types.lean` | Configuration |
| `src/lean_spec/subspecs/xmss/prf.py` | `Crypto/XMSS/PRF.lean` | Pseudorandom function |
| `src/lean_spec/subspecs/xmss/tweak_hash.py` | `Crypto/XMSS/TweakHash.lean` | Tweakable hash |
| `src/lean_spec/subspecs/xmss/target_sum.py` | `Crypto/XMSS/TargetSum.lean` | Winternitz encoding |
| `src/lean_spec/subspecs/xmss/subtree.py` | `Crypto/XMSS/SubTree.lean` | Merkle tree ops |
| `src/lean_spec/subspecs/xmss/interface.py` | `Crypto/XMSS/Interface.lean` | Main API |
| `src/lean_spec/subspecs/xmss/aggregation.py` | `Crypto/XMSS/Aggregation.lean` | Aggregation |

## 3. Source Layout

```
LeanEth/Crypto/XMSS/
├── Types.lean              Containers: PublicKey, SecretKey, Signature, KeyPair, Config
├── PRF.lean                Pseudorandom function (test + prod variants)
├── TweakHash.lean          Tweakable hash with domain separation
├── TargetSum.lean          Winternitz target-sum encoding
├── SubTree.lean            Hash subtree: build, path, verify
├── Interface.lean          GeneralizedXmssScheme: keygen, sign, verify
├── Aggregation.lean        Signature aggregation + proof
└── Proofs.lean             Soundness: roundtrip, one-time, path, aggregation
```

## 4. Sub-task Breakdown

### Group A: Data Structures & Configuration (X4-A1 through X4-A4)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X4-A1 | **Define XMSS hash-level types.** `abbrev HashDigest := Array Fp`. `def HashDigestList := SSZList HashDigest HASH_DIGEST_LIST_LIMIT`. `def HashDigestVector (n : Nat) := SSZVector HashDigest n`. `abbrev Parameter := Array Fp`. `abbrev PRFKey := Array Fp`. `abbrev Randomness := Array Fp`. `def HashTreeOpening := Array HashDigest` (authentication path — list of sibling hashes from leaf to root). Add SSZ serialization instances for all types. | `Crypto/XMSS/Types.lean` | ~40 | X3-A1 |
| X4-A2 | **Define XMSS configuration.** `structure XmssConfig where hashLenFe : Nat; lifetime : Nat; winternitzW : Nat; sqrtLifetime : Nat; signatureLenBytes : Nat; publicKeyLenBytes : Nat; h_sqrt : sqrtLifetime * sqrtLifetime ≤ lifetime; h_lifetime_pos : lifetime > 0`. Define `TEST_CONFIG : XmssConfig` (small tree for fast tests, e.g., lifetime=16, sqrt=4). Define `PROD_CONFIG : XmssConfig` (full security, e.g., lifetime=2^20). Define `TARGET_CONFIG : XmssConfig` selected by `LeanEnvMode`. | `Crypto/XMSS/Types.lean` | ~30 | — |
| X4-A3 | **Define key and signature containers.** `structure PublicKey where root : HashDigestVector CONFIG.hashLenFe; parameter : Parameter` deriving SSZSerializable. `structure Signature where path : HashTreeOpening; rho : Randomness; hashes : HashDigestList` with `isFixedSize := true`, `byteLength := CONFIG.signatureLenBytes`. `structure SecretKey where prfKey : PRFKey; parameter : Parameter; activationSlot : Slot; numActiveSlots : Uint64; topTree : HashSubTree; leftBottomTreeIndex : Uint64; leftBottomTree : HashSubTree; rightBottomTree : HashSubTree`. `structure KeyPair where public : PublicKey; secret : SecretKey`. | `Crypto/XMSS/Types.lean` | ~50 | X4-A1, X4-A2 |
| X4-A4 | **Define XMSS error type.** `inductive XmssError | slotOutOfRange (slot : Slot) (validStart validEnd : Slot) | keyExhausted | invalidSignature | aggregationFailed (msg : String) | treeDepthMismatch | invalidPath`. | `Crypto/XMSS/Types.lean` | ~10 | — |

### Group B: Cryptographic Primitives (X4-B1 through X4-B4)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X4-B1 | **Define pseudorandom function.** `structure Prf where eval : PRFKey → Nat → Array Fp; h_deterministic : ∀ k n, eval k n = eval k n`. `TEST_PRF`: simple single Poseidon2 application `fun k n => permute PARAMS_16 (k ++ encode(n))`. `PROD_PRF`: full-strength Poseidon2 sponge with proper padding. Define `TARGET_PRF` selected by config. | `Crypto/XMSS/PRF.lean` | ~30 | X3-B3 |
| X4-B2 | **Define tweakable hash with domain separation.** `structure TweakHasher where hash : Parameter → Nat → Array Fp → HashDigest; chainHash : Parameter → Nat → Nat → HashDigest → HashDigest`. Domain separation: position-dependent tweaks prevent cross-context collisions. `hash p pos input = poseidon2(p ++ encode(pos) ++ input)`. `chainHash p pos step prev = poseidon2(p ++ encode(pos) ++ encode(step) ++ prev)`. Define test and prod variants. | `Crypto/XMSS/TweakHash.lean` | ~40 | X3-B3 |
| X4-B3 | **Define Winternitz target-sum encoding.** `structure TargetSumEncoder where encode : Array Fp → Array Nat; targetSum : Nat; h_encode_sum : ∀ msg, (encode msg).foldl (· + ·) 0 = targetSum`. The encoder maps a message digest to Winternitz chain indices such that the sum of all indices equals a fixed constant (the checksum). `encode`: split digest into base-W digits, compute checksum digits, concatenate. Prove `encode_deterministic` and `encode_length`. | `Crypto/XMSS/TargetSum.lean` | ~40 | X3-A3 |
| X4-B4 | **Define Winternitz one-time signature (internal).** `winternitzSign : TweakHasher → Parameter → PRFKey → Nat → Array Nat → Signature` — for each chain index `i` in the encoded message, compute chain hash from position 0 to `target[i]`. `winternitzVerify : TweakHasher → Parameter → Array Nat → Signature → HashDigest` — for each chain, continue hashing from `target[i]` to `W-1`, producing the public verification leaf. This is the core one-time signature mechanic. | `Crypto/XMSS/Interface.lean` | ~40 | X4-B2, X4-B3 |

### Group C: Merkle Tree Operations (X4-C1 through X4-C4)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X4-C1 | **Define `HashSubTree` inductive type.** `inductive HashSubTree where | leaf : HashDigest → HashSubTree | node : HashDigest → HashSubTree → HashSubTree → HashSubTree`. Add `root : HashSubTree → HashDigest` (extract cached root hash). Add `depth : HashSubTree → Nat`. Add `numLeaves : HashSubTree → Nat := 2^depth`. Add `isComplete : HashSubTree → Bool` (all leaves present). | `Crypto/XMSS/SubTree.lean` | ~30 | X4-A1 |
| X4-C2 | **Define tree construction.** `buildTree : TweakHasher → Parameter → PRFKey → Nat → Nat → HashSubTree` — build a complete binary tree of given depth, computing leaf hashes via PRF and internal nodes via `hash(left.root ++ right.root)`. Uses `Nat.rec` or well-founded recursion on depth. Define `buildLeaf : TweakHasher → Parameter → PRFKey → Nat → HashDigest` (single leaf computation). | `Crypto/XMSS/SubTree.lean` | ~35 | X4-C1, X4-B1, X4-B2 |
| X4-C3 | **Define path extraction and verification.** `getPath : HashSubTree → Nat → Option HashTreeOpening` — extract authentication path (sibling hashes from leaf to root) for leaf at given index. `verifyPath : TweakHasher → HashDigest → HashTreeOpening → Nat → HashDigest → Bool` — verify that a leaf at index `idx` has authentication path leading to claimed root. Implementation: walk from leaf to root, at each level hash with sibling (left or right based on index bit). | `Crypto/XMSS/SubTree.lean` | ~50 | X4-C1 |
| X4-C4 | **Define combined path across tree layers.** `combinedPath : HashTreeOpening → HashTreeOpening → Nat → Nat → HashTreeOpening` — merge authentication paths from bottom tree and top tree. Used in the top-bottom tree traversal scheme: the bottom tree provides the path within a subtree, the top tree provides the path from subtree root to global root. | `Crypto/XMSS/SubTree.lean` | ~25 | X4-C3 |

### Group D: Key Generation & Signing (X4-D1 through X4-D4)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X4-D1 | **Define `GeneralizedXmssScheme`.** `structure GeneralizedXmssScheme where config : XmssConfig; prf : Prf; hasher : TweakHasher; encoder : TargetSumEncoder; rand : Rand`. Define `TEST_SCHEME : GeneralizedXmssScheme` (using test primitives) and `PROD_SCHEME`. Define `Rand` as a deterministic PRNG: `structure Rand where generate : PRFKey → Nat → Randomness`. | `Crypto/XMSS/Interface.lean` | ~30 | X4-B1, X4-B2, X4-B3 |
| X4-D2 | **Define `keyGen`.** `keyGen : GeneralizedXmssScheme → Slot → Uint64 → KeyPair`. Steps: (1) expand activation time to √(LIFETIME) boundary: `expandedStart = (slot / sqrtLifetime) * sqrtLifetime`. (2) Generate PRF key. (3) Build first two bottom trees (prepared window). (4) Build remaining bottom tree roots. (5) Build top tree from all bottom tree roots. (6) Assemble PublicKey (top tree root + parameter) and SecretKey (PRF key + trees + activation metadata). | `Crypto/XMSS/Interface.lean` | ~50 | X4-D1, X4-C2 |
| X4-D3 | **Define `sign`.** `sign : GeneralizedXmssScheme → SecretKey → Slot → Bytes32 → Except XmssError Signature`. Steps: (1) Check slot is in valid range `[activationSlot, activationSlot + numActiveSlots)`. (2) Compute bottom tree index from slot. (3) If needed, advance prepared window (rebuild bottom trees). (4) Compute leaf index within bottom tree. (5) Generate randomness via PRF. (6) Encode message via target-sum encoder. (7) Produce Winternitz one-time signature. (8) Extract authentication path (bottom + top combined). (9) Assemble Signature (path + randomness + chain hashes). | `Crypto/XMSS/Interface.lean` | ~60 | X4-D1, X4-B4, X4-C3, X4-C4 |
| X4-D4 | **Define `verify`.** `verify : GeneralizedXmssScheme → PublicKey → Slot → Bytes32 → Signature → Bool`. Steps: (1) Compute expected leaf index from slot. (2) Re-encode message via target-sum. (3) Recompute Winternitz verification leaf from signature chains. (4) Verify authentication path from leaf to public key root. (5) Return true iff path verification succeeds. | `Crypto/XMSS/Interface.lean` | ~40 | X4-D1, X4-B4, X4-C3 |

### Group E: Aggregation (X4-E1 through X4-E2)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X4-E1 | **Define signature aggregation.** `structure AggregatedSignatureProof where data : AttestationData; validatorBits : BaseBitlist VALIDATOR_LIMIT; proof : ByteArray`. `aggregate : List (ValidatorIndex × Signature) → AttestationData → Except XmssError AggregatedSignatureProof` — combine multiple individual signatures into a single aggregate proof. Implementation depends on XMSS aggregation structure from leanSpec. | `Crypto/XMSS/Aggregation.lean` | ~40 | X4-D3 |
| X4-E2 | **Define aggregate verification.** `verifyAggregated : GeneralizedXmssScheme → AggregatedSignatureProof → List (ValidatorIndex × PublicKey) → Bytes32 → Bool` — verify that the aggregate proof is valid for the claimed set of validators. Each participating validator (indicated by validatorBits) must have a valid individual signature. | `Crypto/XMSS/Aggregation.lean` | ~30 | X4-E1, X4-D4 |

### Group F: Correctness Proofs (X4-F1 through X4-F4)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X4-F1 | **Prove sign/verify roundtrip.** `sign_verify_correct : ∀ scheme sk pk slot msg, (pk, sk) = keyGen scheme startSlot numSlots → slot ∈ [startSlot, startSlot + numSlots) → sign scheme sk slot msg = .ok sig → verify scheme pk slot msg sig = true`. Proof sketch: signing produces a Winternitz chain + path; verification recomputes the chain and checks the path; by construction of `keyGen`, the path leads to `pk.root`. | `Crypto/XMSS/Proofs.lean` | ~60 | X4-D3, X4-D4 |
| X4-F2 | **Prove one-time key property.** `sign_uses_distinct_keys : ∀ scheme sk slot₁ slot₂, slot₁ ≠ slot₂ → slot₁ ∈ validRange → slot₂ ∈ validRange → leafIndex slot₁ ≠ leafIndex slot₂`. The leaf index is a function of slot, and distinct valid slots map to distinct leaves. This prevents one-time key reuse. Proof: `leafIndex slot = (slot - activationSlot)`, which is injective on the valid range. | `Crypto/XMSS/Proofs.lean` | ~30 | X4-D2 |
| X4-F3 | **Prove path verification soundness.** `verifyPath_implies_membership : verifyPath hasher leaf path idx root = true → ∃ tree, tree.root = root ∧ tree.getLeaf idx = some leaf'` (under AXIOM-CRYPTO-1). The authentication path correctly witnesses tree membership. | `Crypto/XMSS/Proofs.lean` | ~40 | X4-C3 |
| X4-F4 | **Prove aggregation correctness.** `aggregate_verify_sound : verifyAggregated scheme (aggregate sigs data) keys msg = true → ∀ (vi, sig) ∈ sigs, verify scheme (keys vi) slot msg sig = true`. Aggregate verification implies individual signature validity. | `Crypto/XMSS/Proofs.lean` | ~40 | X4-E1, X4-E2 |

## 5. Exit Criteria

- [ ] Complete XMSS: keygen, sign, verify, aggregate
- [ ] Sign/verify roundtrip proved (X4-F1)
- [ ] One-time key property proved (X4-F2)
- [ ] Path soundness proved under AXIOM-CRYPTO-1 (X4-F3)
- [ ] Aggregation correctness proved (X4-F4)
- [ ] Test vectors match Python reference (CryptoSuite)
- [ ] Zero sorry in XMSS modules
- [ ] `lake build LeanEth.Crypto.XMSS.Interface` succeeds
