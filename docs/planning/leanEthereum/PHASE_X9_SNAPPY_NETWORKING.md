# Phase X9: Snappy Compression & Networking Types

**Version**: v0.9.0
**Status**: PLANNED
**Sub-tasks**: 12 atomic units
**Dependencies**: X1 (Types), X5 (Containers — for message types)
**Estimated Lean LoC**: ~550
**Files created**: 9 new files
**Parallelizable with**: X6–X7 (State Transition / Safety Proofs)

## 1. Objective

Formalize Snappy compression (used for P2P message encoding) and define
networking type abstractions. Lean provides roundtrip proofs; actual networking
will be in Rust (Phase X11).

## 2. Sub-task Breakdown

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X9-A1 | **Define Snappy compression internals.** `inductive SnappyOp | literal (data : ByteArray) | copy (offset : Nat) (length : Nat)`. `compressBlock : ByteArray → Array SnappyOp` — greedy matching with sliding window. `serializeOps : Array SnappyOp → ByteArray` — encode ops to Snappy byte format. `compress : ByteArray → ByteArray := serializeOps ∘ compressBlock`. | `Crypto/Snappy/Compress.lean` | ~50 | X1 |
| X9-A2 | **Define Snappy decompression.** `decompress : ByteArray → Except SnappyError ByteArray` — decode compressed blocks, resolve backreferences. Error cases: invalid offset (> window), length exceeds buffer, truncated input, invalid tag byte. | `Crypto/Snappy/Decompress.lean` | ~45 | X1 |
| X9-A3 | **Define Snappy framing format.** `frameCompress : ByteArray → ByteArray` — streaming format with chunk headers (chunk type + length + CRC32C + data). `frameDecompress : ByteArray → Except SnappyError ByteArray` — parse framing headers, validate CRC, decompress each chunk. Used for Ethereum network messages. | `Crypto/Snappy/Framing.lean` | ~40 | X9-A1, X9-A2 |
| X9-A4 | **Prove Snappy roundtrip correctness.** `snappy_roundtrip : ∀ data, decompress (compress data) = .ok data`. `frame_roundtrip : ∀ data, frameDecompress (frameCompress data) = .ok data`. Proof strategy: compress produces valid SnappyOps; decompress correctly resolves each op; composition is identity. | `Crypto/Snappy/Proofs.lean` | ~35 | X9-A1, X9-A2, X9-A3 |
| X9-B1 | **Define networking type abstractions.** `structure PeerId where bytes : Bytes32`. `structure SubnetId where val : Uint64`. `inductive NetworkMessage | gossipBlock (block : SignedBlock) | gossipAttestation (att : SignedAttestation) | gossipAggregateProof (proof : SignedAggregatedAttestation) | reqRespBlocksByRange (startSlot : Slot, count : Uint64) | reqRespBlocksByRoot (roots : List Bytes32) | statusMessage (justified finalized : Checkpoint)`. | `Node/Networking/Transport.lean` | ~35 | X5 |
| X9-B2 | **Define ENR encoding.** `structure ENR where seq : Uint64; pairs : List (String × ByteArray); signature : ByteArray`. `encodeENR : ENR → ByteArray` via RLP (from X1-G3). `decodeENR : ByteArray → Except ENRError ENR`. Prove `enr_roundtrip`. | `Node/Networking/ENR.lean` | ~35 | X1 |
| X9-B3 | **Define Gossipsub topic abstractions.** `structure Topic where name : String`. `inductive GossipsubAction | subscribe (topic : Topic) | unsubscribe (topic : Topic) | publish (topic : Topic) (data : ByteArray) | receive (topic : Topic) (data : ByteArray) (peer : PeerId)`. Define consensus topics: `beaconBlockTopic`, `beaconAttestationTopic (subnet : SubnetId)`, `aggregateProofTopic`. | `Node/Networking/Gossipsub.lean` | ~25 | X9-B1 |
| X9-B4 | **Define request-response protocol types.** `inductive ReqRespMethod | blocksByRange | blocksByRoot | status | metadata | ping | goodbye`. `structure ReqRespRequest where method : ReqRespMethod; payload : ByteArray`. `structure ReqRespResponse where status : Uint8; payload : ByteArray`. SSZ-encode payloads, Snappy-compress for wire format. | `Node/Networking/ReqResp.lean` | ~25 | X9-A1, X9-B1 |
| X9-B5 | **Define discovery types (discv5).** `structure DiscoveryConfig where bootstrapNodes : List ENR; listenPort : Uint16; maxPeers : Nat`. `structure RoutingTable where buckets : Array (List PeerId); selfId : PeerId`. Abstract interface — implementation in Rust. | `Node/Networking/Discovery.lean` | ~20 | X9-B2 |
| X9-B6 | **Define network configuration.** `structure NetworkConfig where discoveryConfig : DiscoveryConfig; gossipsubParams : GossipsubParams; reqRespTimeout : Uint64; maxPeers : Nat`. `structure GossipsubParams where meshSize : Nat; meshLow : Nat; meshHigh : Nat; gossipFactor : Nat`. | `Node/Networking/Config.lean` | ~20 | X9-B5 |
| X9-C1 | **Define `SnappyError` and `ENRError`.** `inductive SnappyError | invalidOffset | truncatedInput | lengthExceedsBuffer | invalidTag | crcMismatch`. `inductive ENRError | invalidRLP | missingSignature | invalidSequence`. | `Crypto/Snappy/Compress.lean`, `Node/Networking/ENR.lean` | ~15 | — |
| X9-C2 | **Snappy and ENR test suite.** Roundtrip tests for compression. ENR encode/decode against known test vectors. Wire format tests for SSZ+Snappy network messages. | `tests/NetworkSuite.lean` | ~30 | All X9-* |

## 3. Exit Criteria

- [ ] Snappy roundtrip proved (raw and framing)
- [ ] ENR roundtrip proved
- [ ] All networking types defined with SSZ serialization
- [ ] Zero sorry in Snappy and networking modules
