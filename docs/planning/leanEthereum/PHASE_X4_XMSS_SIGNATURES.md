# Phase X4: XMSS Signature Scheme

**Version**: v0.4.0
**Status**: PLANNED
**Sub-tasks**: 34 atomic units
**Dependencies**: X3 (KoalaBear + Poseidon2), X1 (Types)
**Estimated Lean LoC**: ~1,400
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
├── Types.lean              Containers, config, error type
├── PRF.lean                Pseudorandom function (test + prod)
├── TweakHash.lean          Tweakable hash with domain separation
├── TargetSum.lean          Winternitz target-sum encoding
├── SubTree.lean            Hash subtree: build, path, verify, combined path
├── Interface.lean          GeneralizedXmssScheme: keygen, sign, verify
├── Aggregation.lean        Signature aggregation + verification
└── Proofs.lean             Soundness: roundtrip, one-time, path, aggregation
```

## 4. Sub-task Breakdown

### Group A: Data Structures & Configuration (X4-A1 through X4-A5)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X4-A1 | **Define XMSS hash-level types.** `abbrev HashDigest := Array Fp`. `def HashDigestList := SSZList HashDigest HASH_DIGEST_LIST_LIMIT`. `def HashDigestVector (n : Nat) := SSZVector HashDigest n`. `abbrev Parameter := Array Fp` (length `PARAMETER_LEN = 5`). `abbrev PRFKey := Array Fp`. `abbrev Randomness := Array Fp` (length `RAND_LEN_FE = 7`). `def HashTreeOpening := Array HashDigest` (authentication path — list of sibling hashes from leaf to root). Add SSZ serialization instances for all types. | `Crypto/XMSS/Types.lean` | ~40 | X3-A1 |
| X4-A2 | **Define XMSS configuration.** `structure XmssConfig where hashLenFe : Nat; logLifetime : Nat; dimension : Nat; base : Nat; finalLayer : Nat; targetSum : Nat; maxTries : Nat; parameterLen : Nat; tweakLenFe : Nat; msgLenFe : Nat; randLenFe : Nat; capacity : Nat; h_sqrt : (logLifetime / 2) * 2 = logLifetime` (logLifetime must be even for top-bottom split). Define `TEST_CONFIG` (small: logLifetime=8, dimension=16, base=4) and `PROD_CONFIG` (full: logLifetime=32, dimension=64, base=8, targetSum=375, maxTries=100000). `leavesPerBottomTree : XmssConfig → Nat := fun c => 2 ^ (c.logLifetime / 2)`. `numBottomTrees : XmssConfig → Nat → Nat → Nat` (from activation range). | `Crypto/XMSS/Types.lean` | ~40 | — |
| X4-A3 | **Define key and signature containers.** `structure PublicKey where root : HashDigestVector CONFIG.hashLenFe; parameter : Parameter` deriving SSZSerializable. `structure Signature where path : HashTreeOpening; rho : Randomness; hashes : HashDigestList` with `isFixedSize := true`, `byteLength := CONFIG.signatureLenBytes`. `structure SecretKey where prfKey : PRFKey; parameter : Parameter; activationSlot : Slot; numActiveSlots : Uint64; topTree : HashSubTree; leftBottomTreeIndex : Uint64; leftBottomTree : HashSubTree; rightBottomTree : HashSubTree`. `structure KeyPair where public : PublicKey; secret : SecretKey`. | `Crypto/XMSS/Types.lean` | ~50 | X4-A1, X4-A2 |
| X4-A4 | **Define XMSS error type.** `inductive XmssError | slotOutOfRange (slot : Slot) (validStart validEnd : Slot) | keyExhausted | invalidSignature | aggregationFailed (msg : String) | treeDepthMismatch | invalidPath | encodingFailed (attempts : Nat)`. Each variant corresponds to a specific failure mode in the XMSS pipeline. | `Crypto/XMSS/Types.lean` | ~10 | — |
| X4-A5 | **Define tweak types for domain separation.** `inductive TweakDomain | treeHash | chainHash`. `structure TreeTweak where level : Nat; index : Nat`. `structure ChainTweak where epoch : Nat; chainIndex : Nat; step : Nat`. `encodeTweak : TreeTweak → Nat := fun t => (t.level <<< 40) ||| (t.index <<< 8) ||| 0x01`. `encodeChainTweak : ChainTweak → Nat := fun t => (t.epoch <<< 24) ||| (t.chainIndex <<< 16) ||| (t.step <<< 8) ||| 0x00`. These packed integers serve as Poseidon2 input domain separators. | `Crypto/XMSS/TweakHash.lean` | ~25 | — |

### Group B: Cryptographic Primitives (X4-B1 through X4-B5)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X4-B1 | **Define pseudorandom function.** `structure Prf where eval : PRFKey → Nat → Nat → Array Fp; getRand : PRFKey → Slot → Bytes32 → Uint64 → Randomness`. `eval key epoch chainIndex` produces `HASH_LEN_FE` (8) field elements — this is the per-chain starting digest. Input domain: `DOMAIN_SEP ++ 0x00 ++ key ++ encode(epoch, 4B) ++ encode(chainIndex, 8B)`, hashed via Poseidon2 sponge. `getRand key slot message attempts` produces `RAND_LEN_FE` (7) elements — the per-signing randomness. Input: `DOMAIN_SEP ++ 0x01 ++ key ++ encode(slot, 4B) ++ message(32B) ++ encode(attempts, 8B)`. Define `TEST_PRF` (single Poseidon2 call) and `PROD_PRF` (full sponge). | `Crypto/XMSS/PRF.lean` | ~40 | X3-B3 |
| X4-B2 | **Define tweakable hash functions.** `structure TweakHasher where treeHash : Parameter → TreeTweak → Array Fp → HashDigest; chainHash : Parameter → ChainTweak → HashDigest → HashDigest; leafHash : Parameter → Nat → Array HashDigest → HashDigest`. `treeHash p tweak input` — Poseidon2 with domain-separated tweak for internal tree nodes (width-24 for 2 digests). `chainHash p tweak prev` — single Poseidon2 step in the Winternitz hash chain (width-16). `leafHash p leafIndex chains` — sponge over all chain endpoints to produce the one-time public key leaf (multiple Poseidon2 absorptions). Define test and prod variants. | `Crypto/XMSS/TweakHash.lean` | ~45 | X3-B3, X4-A5 |
| X4-B3 | **Define Winternitz target-sum encoding.** `structure TargetSumEncoder where config : XmssConfig; encode : Parameter → Bytes32 → Randomness → Slot → Option (Array Nat)`. The encoder: (1) Hash `(parameter, message, rho, slot)` via Poseidon2 sponge → `MSG_LEN_FE` field elements. (2) Split each element into base-`W` digits → get `DIMENSION` (64) chain indices. (3) Compute checksum: `targetSum - sum(digits)`. (4) If checksum < 0, return `none` (encoding failed — try next `rho`). (5) Encode checksum as base-`W` digits, append to data digits. (6) Return full codeword of length `DIMENSION + checksumDigits`. Prove `encode_deterministic : encode p m r s = encode p m r s` (trivial but documents purity). | `Crypto/XMSS/TargetSum.lean` | ~45 | X3-B3, X4-A2 |
| X4-B4 | **Prove target-sum encoding properties.** (1) `encode_sum_constant : encode p m r s = some cw → cw.foldl (· + ·) 0 = config.targetSum`. The codeword digit sum is always exactly `targetSum` (375 in prod). (2) `encode_length : encode p m r s = some cw → cw.size = config.dimension + checksumDigits`. (3) `encode_bounded : ∀ i, cw[i] < config.base` (every digit is in `[0, base)`). (4) `encode_retry_independent : encode p m r₁ s = some cw₁ → encode p m r₂ s = some cw₂ → cw₁.foldl (· + ·) 0 = cw₂.foldl (· + ·) 0` (sum is constant regardless of which rho succeeds). | `Crypto/XMSS/TargetSum.lean` | ~30 | X4-B3 |
| X4-B5 | **Define Winternitz one-time signature (internal).** `winternitzSign : TweakHasher → Parameter → PRFKey → Slot → Array Nat → Array HashDigest` — for each chain index `i` with codeword digit `cw[i]`: compute starting digest via `prf.eval key slot i`, then walk the chain `cw[i]` steps via `chainHash`. Output = array of partially-evaluated chain digests. `winternitzVerify : TweakHasher → Parameter → Slot → Array Nat → Array HashDigest → HashDigest` — for each chain `i`: walk from step `cw[i]` to `base - 1` (the remaining steps), producing chain endpoints. Hash all endpoints together via `leafHash` to reconstruct the one-time public key leaf. | `Crypto/XMSS/Interface.lean` | ~45 | X4-B2, X4-B3 |

### Group C: Merkle Tree Operations (X4-C1 through X4-C5)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X4-C1 | **Define `HashSubTree` inductive type.** `inductive HashSubTree where | leaf : HashDigest → HashSubTree | node : HashDigest → HashSubTree → HashSubTree → HashSubTree`. `root : HashSubTree → HashDigest` (extract cached root hash). `depth : HashSubTree → Nat`. `numLeaves : HashSubTree → Nat := 2 ^ depth`. `isComplete : HashSubTree → Bool` (all paths to leaves have same length). `getLeaf : HashSubTree → Nat → Option HashDigest` (retrieve leaf at given index). | `Crypto/XMSS/SubTree.lean` | ~30 | X4-A1 |
| X4-C2 | **Define tree construction.** `buildLeaf : TweakHasher → Parameter → PRFKey → Nat → Nat → HashDigest` — compute one leaf: evaluate PRF for all `DIMENSION` chains at the given epoch/leaf position, walk each chain to `base - 1`, hash all chain endpoints via `leafHash`. `buildTree : TweakHasher → Parameter → PRFKey → Nat → Nat → Nat → HashSubTree` — build a complete binary tree of given depth. Uses well-founded recursion on depth: `buildTree depth=0 = leaf (buildLeaf ...)`, `buildTree depth+1 = node (treeHash left.root right.root) left right`. | `Crypto/XMSS/SubTree.lean` | ~40 | X4-C1, X4-B1, X4-B2 |
| X4-C3 | **Define path extraction.** `getPath : HashSubTree → Nat → Option HashTreeOpening` — extract authentication path (sibling hashes from leaf to root) for leaf at given index. At each level: if going left (index bit = 0), record right sibling; if going right (index bit = 1), record left sibling. Path length = tree depth. Return `none` if index ≥ `numLeaves`. | `Crypto/XMSS/SubTree.lean` | ~30 | X4-C1 |
| X4-C4 | **Define path verification.** `verifyPath : TweakHasher → Parameter → HashDigest → HashTreeOpening → Nat → HashDigest → Bool` — verify that leaf at `index` with given authentication path leads to claimed `root`. Walk from leaf to root: at each level `l`, combine current hash with `path[l]` (left or right based on index bit at level `l`) via `treeHash`, producing next level's hash. Final hash must equal `root`. | `Crypto/XMSS/SubTree.lean` | ~30 | X4-C1, X4-B2 |
| X4-C5 | **Define combined path for top-bottom tree scheme.** `combinedPath : HashTreeOpening → HashTreeOpening → Nat → Nat → HashTreeOpening` — merge authentication paths from bottom tree and top tree. The bottom tree path covers levels `[0, bottomDepth)` and the top tree path covers levels `[bottomDepth, totalDepth)`. Combined path = `bottomPath ++ topPath[bottomTreeIndex portion]`. The `bottomTreeIndex` determines which branch in the top tree the bottom tree root sits at. Prove `combinedPath_length : (combinedPath bp tp bd td).size = bd + (td - bd)`. | `Crypto/XMSS/SubTree.lean` | ~30 | X4-C3 |

### Group D: Key Generation (X4-D1 through X4-D4)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X4-D1 | **Define activation time expansion.** `expandActivation : XmssConfig → Nat → Nat → (Nat × Nat)` — expand `(activationSlot, numSlots)` to √(LIFETIME) boundaries. `startBottomTreeIndex := activationSlot / leavesPerBottomTree`. `endBottomTreeIndex := (activationSlot + numSlots + leavesPerBottomTree - 1) / leavesPerBottomTree`. This ensures the key covers complete bottom trees. Prove `expandActivation_covers_range : ∀ s ∈ [activationSlot, activationSlot + numSlots), s / leavesPerBottomTree ∈ [start, end)`. | `Crypto/XMSS/Interface.lean` | ~25 | X4-A2 |
| X4-D2 | **Define bottom tree generation.** `generateBottomTrees : TweakHasher → Prf → Parameter → PRFKey → Nat → Nat → (HashSubTree × HashSubTree × Array HashDigest)`. Generate the first two bottom trees fully (in-memory for the prepared window) and remaining bottom trees as roots only. Steps: (1) Build `leftBottomTree` at `startIndex`. (2) Build `rightBottomTree` at `startIndex + 1`. (3) For indices `startIndex + 2` to `endIndex - 1`: build full tree, extract root, discard tree. (4) Return `(left, right, allRoots)`. | `Crypto/XMSS/Interface.lean` | ~35 | X4-C2, X4-B1 |
| X4-D3 | **Define top tree construction and `keyGen`.** `buildTopTree : TweakHasher → Parameter → Array HashDigest → Nat → Nat → HashSubTree` — construct the top-level tree from bottom tree roots. The top tree has depth `logLifetime / 2` and its leaves are the bottom tree roots. `keyGen : GeneralizedXmssScheme → Slot → Uint64 → KeyPair`. Orchestrate: (1) Expand activation via X4-D1. (2) Generate parameter and PRF key. (3) Generate bottom trees via X4-D2. (4) Build top tree via `buildTopTree`. (5) Assemble `PublicKey` (top tree root + parameter) and `SecretKey`. | `Crypto/XMSS/Interface.lean` | ~45 | X4-D1, X4-D2 |
| X4-D4 | **Define prepared window advancement.** `advancePreparation : SecretKey → TweakHasher → Prf → SecretKey`. When all leaves in the left bottom tree are exhausted, shift the window: `leftBottomTree := rightBottomTree`, `rightBottomTree := buildTree(nextIndex)`, `leftBottomTreeIndex += 1`. This maintains exactly 2 fully-expanded bottom trees at any time. Prove `advancePreparation_preserves_publicKey : advancePreparation sk ... → sk.topTree = sk'.topTree` (top tree doesn't change). | `Crypto/XMSS/Interface.lean` | ~30 | X4-D2, X4-C2 |

### Group E: Signing (X4-E1 through X4-E3)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X4-E1 | **Define message encoding with retry loop.** `encodeMessage : GeneralizedXmssScheme → SecretKey → Slot → Bytes32 → Except XmssError (Array Nat × Randomness)`. Loop up to `maxTries` times: (1) Generate randomness `rho := prf.getRand sk.prfKey slot message (Uint64.ofNat attempt)`. (2) Try `encoder.encode sk.parameter message rho slot`. (3) If `some cw`, return `(cw, rho)`. (4) If `none`, increment attempt. If all attempts fail, return `encodingFailed maxTries`. Prove `encodeMessage_deterministic : same inputs → same output`. | `Crypto/XMSS/Interface.lean` | ~30 | X4-B3, X4-B1 |
| X4-E2 | **Define one-time signature production.** `produceOTS : GeneralizedXmssScheme → SecretKey → Slot → Array Nat → Array HashDigest`. For each chain index `i` in `[0, dimension)`: (1) Compute start digest: `prf.eval sk.prfKey slot i`. (2) Walk chain `cw[i]` steps: `hasher.chainHash sk.parameter (ChainTweak slot i step) prev` for `step ∈ [0, cw[i])`. (3) Output = array of partially-walked chain digests. These are the signature's hash chain values. | `Crypto/XMSS/Interface.lean` | ~25 | X4-B5, X4-B1 |
| X4-E3 | **Define `sign` — full orchestration.** `sign : GeneralizedXmssScheme → SecretKey → Slot → Bytes32 → Except XmssError (Signature × SecretKey)`. Steps: (1) Validate slot in range `[activationSlot, activationSlot + numActiveSlots)` → `slotOutOfRange` error. (2) Determine which bottom tree: `bottomTreeIdx := slot / leavesPerBottomTree`. (3) If `bottomTreeIdx` requires window advance, call `advancePreparation`. (4) Encode message via X4-E1 → `(cw, rho)`. (5) Produce OTS via X4-E2 → `otsHashes`. (6) Select correct bottom tree (left or right). (7) Get bottom path: `getPath bottomTree leafIndex`. (8) Get top path portion from top tree. (9) Combine paths: `combinedPath bottomPath topPath`. (10) Return `(Signature { path, rho, hashes := otsHashes }, updatedSk)`. | `Crypto/XMSS/Interface.lean` | ~50 | X4-E1, X4-E2, X4-D4, X4-C5 |

### Group F: Verification (X4-F1 through X4-F2)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X4-F1 | **Define `verify`.** `verify : GeneralizedXmssScheme → PublicKey → Slot → Bytes32 → Signature → Bool`. Steps: (1) Check slot < lifetime → `false` if out of range. (2) Re-encode message: `encoder.encode pk.parameter message sig.rho slot` → `none` means invalid. (3) For each chain `i`: walk from `sig.hashes[i]` for `base - 1 - cw[i]` steps via `chainHash` → chain endpoints. (4) Hash all chain endpoints via `leafHash` → reconstructed one-time public key leaf. (5) Verify Merkle path: `verifyPath hasher pk.parameter leaf sig.path slot pk.root`. (6) Return result. | `Crypto/XMSS/Interface.lean` | ~40 | X4-B5, X4-C4, X4-B3 |
| X4-F2 | **Prove verify is deterministic and total.** `verify_deterministic : verify s pk slot msg sig = verify s pk slot msg sig` (trivial, documents purity). `verify_total : ∀ inputs, verify s pk slot msg sig = true ∨ verify s pk slot msg sig = false` (Bool is decidable). `verify_rejects_bad_slot : slot ≥ lifetime → verify ... = false`. | `Crypto/XMSS/Proofs.lean` | ~15 | X4-F1 |

### Group G: Aggregation (X4-G1 through X4-G3)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X4-G1 | **Define signature aggregation.** `structure AggregatedSignatureProof where data : AttestationData; validatorBits : BaseBitlist VALIDATOR_LIMIT; proof : ByteArray; participants : Finset ValidatorIndex`. `aggregate : List (ValidatorIndex × Signature) → AttestationData → Except XmssError AggregatedSignatureProof` — combine multiple individual signatures sharing the same `AttestationData` into a single aggregate proof. The `validatorBits` bitfield records which validators contributed. `participants` is the set of contributing validator indices. | `Crypto/XMSS/Aggregation.lean` | ~35 | X4-E3 |
| X4-G2 | **Define aggregate verification.** `verifyAggregated : GeneralizedXmssScheme → AggregatedSignatureProof → (ValidatorIndex → PublicKey) → Bytes32 → Bool`. For each validator index `i` where `proof.validatorBits.get i = true`: reconstruct the individual verification using the validator's public key. All must pass. This decomposes aggregate verification into per-validator checks. | `Crypto/XMSS/Aggregation.lean` | ~30 | X4-G1, X4-F1 |
| X4-G3 | **Prove aggregation-verification equivalence.** `aggregate_verify_sound : verifyAggregated scheme (aggregate sigs data) keyLookup msg = true → ∀ (vi, sig) ∈ sigs, verify scheme (keyLookup vi) slot msg sig = true`. Aggregate verification implies every individual signature is valid. Also: `aggregate_preserves_participants : (aggregate sigs data).participants = sigs.map Prod.fst |>.toFinset`. | `Crypto/XMSS/Proofs.lean` | ~30 | X4-G1, X4-G2 |

### Group H: Correctness Proofs (X4-H1 through X4-H5)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X4-H1 | **Prove sign/verify roundtrip.** `sign_verify_correct : ∀ scheme sk pk slot msg, (pk, sk) = keyGen scheme startSlot numSlots → slot ∈ [startSlot, startSlot + numSlots) → sign scheme sk slot msg = .ok (sig, sk') → verify scheme pk slot msg sig = true`. Proof sketch: signing produces chain digests walked `cw[i]` steps; verification walks `base-1-cw[i]` more steps, reaching the same endpoints as `buildLeaf`; `leafHash` produces the same leaf; `combinedPath` leads to `pk.root` by construction of `keyGen`. | `Crypto/XMSS/Proofs.lean` | ~60 | X4-E3, X4-F1, X4-D3 |
| X4-H2 | **Prove one-time key safety (distinct leaf indices).** `sign_uses_distinct_leaves : ∀ scheme sk slot₁ slot₂, slot₁ ≠ slot₂ → slot₁ ∈ validRange → slot₂ ∈ validRange → leafIndex slot₁ ≠ leafIndex slot₂`. The leaf index is a direct function of the slot within the tree: `leafIndex slot = slot - activationSlot`. Since slots are distinct and the mapping is injective on the valid range, leaves are distinct. This prevents one-time key reuse (critical for hash-based signature security). | `Crypto/XMSS/Proofs.lean` | ~25 | X4-D1 |
| X4-H3 | **Prove path verification soundness.** `verifyPath_implies_membership : verifyPath hasher param leaf path idx root = true → ∃ tree, tree.root = root ∧ tree.getLeaf idx = some leaf` (under AXIOM-CRYPTO-1). Authentication path verification correctly witnesses Merkle tree membership. Proof: by induction on path length; at each level, `hashNodes` collision resistance ensures the child hash is correct. | `Crypto/XMSS/Proofs.lean` | ~40 | X4-C4 |
| X4-H4 | **Prove window advancement preserves signing capability.** `advancePreparation_still_signs : sign scheme sk' slot msg = sign scheme (advancePreparation sk) slot msg` (when slot is in the new right tree's range). The top tree path is unchanged; only the bottom tree reference shifts. | `Crypto/XMSS/Proofs.lean` | ~25 | X4-D4, X4-E3 |
| X4-H5 | **XMSS test vectors.** Add to `tests/CryptoSuite.lean`: keygen with test config, sign known message, verify signature. Compare intermediate values (chain digests, tree roots) against Python reference. Test rejection: wrong slot → false, wrong message → false, tampered signature → false. Minimum 6 test cases. | `tests/CryptoSuite.lean` | ~35 | All X4-* |

## 5. Key Technical Detail: Top-Bottom Tree Traversal

```
Top Tree (depth = logLifetime / 2)
┌─────────────────────────────────────────────────┐
│                    root (= pk.root)              │
│                   /              \               │
│                 ...              ...             │
│               /    \           /    \            │
│         BT_root₀  BT_root₁  BT_root₂  ...     │
└─────────────────────────────────────────────────┘
                │          │
    ┌───────────┘          └───────────┐
    ▼ (left bottom tree)               ▼ (right bottom tree)
┌──────────────┐                ┌──────────────┐
│  depth = L/2 │                │  depth = L/2 │
│  2^(L/2)     │                │  2^(L/2)     │
│  leaves      │                │  leaves      │
│  (in memory) │                │  (in memory) │
└──────────────┘                └──────────────┘

Prepared Window: exactly 2 bottom trees are fully expanded.
When signing exhausts the left tree, advancePreparation() shifts:
  left := right, right := build(nextIndex)

Combined path for slot S:
  1. Bottom tree path: getPath(bottomTree, S % leavesPerBottomTree)
  2. Top tree path: getPath(topTree, S / leavesPerBottomTree)
  3. Merge: bottomPath ++ topPath
```

## 6. Exit Criteria

- [ ] Complete XMSS: keygen, sign, verify, aggregate
- [ ] Sign/verify roundtrip proved (X4-H1)
- [ ] One-time key property proved (X4-H2)
- [ ] Path soundness proved under AXIOM-CRYPTO-1 (X4-H3)
- [ ] Window advancement preserves signing (X4-H4)
- [ ] Aggregation correctness proved (X4-G3)
- [ ] Target-sum constant proved (X4-B4)
- [ ] Test vectors match Python reference (CryptoSuite)
- [ ] Zero sorry in XMSS modules
- [ ] `lake build LeanEth.Crypto.XMSS.Interface` succeeds
