# Phase X9: Snappy Compression & Networking Types

**Version**: v0.9.0
**Status**: PLANNED
**Sub-tasks**: 24 atomic units
**Dependencies**: X1 (Types), X5 (Containers — for message types)
**Estimated Lean LoC**: ~700
**Files created**: 11 new files
**Parallelizable with**: X6–X7 (State Transition / Safety Proofs)

## 1. Objective

Formalize Snappy compression (used for P2P message encoding) and define
networking type abstractions. Lean provides roundtrip proofs; actual networking
will be in Rust (Phase X11).

## 2. Source Layout

```
LeanEth/
├── Crypto/Snappy/
│   ├── Types.lean             SnappyOp, SnappyError, constants
│   ├── Compress.lean          Greedy matching, op serialization
│   ├── Decompress.lean        Tag parsing, backreference resolution
│   ├── Framing.lean           CRC32C, frame encode/decode
│   └── Proofs.lean            Roundtrip, length bounds
├── Node/Networking/
│   ├── Transport.lean         PeerId, SubnetId, NetworkMessage
│   ├── ENR.lean               ENR structure, RLP encode/decode
│   ├── Gossipsub.lean         Topic, GossipsubAction, params
│   ├── ReqResp.lean           Request-response protocol types
│   ├── Discovery.lean         discv5 abstractions
│   └── Config.lean            Network configuration bundle
```

## 3. Sub-task Breakdown

### Group A: Snappy Internals (X9-A1 through X9-A8)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X9-A1 | **Define Snappy types and constants.** `inductive SnappyOp | literal (data : ByteArray) | copy (offset : Nat) (length : Nat)`. `SNAPPY_MAX_BLOCK_SIZE := 65536`. `SNAPPY_WINDOW_SIZE := 32768`. `inductive SnappyError | invalidOffset | truncatedInput | lengthExceedsBuffer | invalidTag | crcMismatch | blockTooLarge | emptyInput`. | `Crypto/Snappy/Types.lean` | ~20 | X1 |
| X9-A2 | **Define Snappy compression — greedy matching.** `findLongestMatch : ByteArray → Nat → HashTable → Option (Nat × Nat)` — sliding window hash lookup, minimum match length 4. `compressBlock : ByteArray → Array SnappyOp` — iterate through input, emit literal or copy ops. Hash table uses 4-byte keys for fast prefix matching. Prove `compressBlock_covers_input : totalBytes (compressBlock data) = data.size`. | `Crypto/Snappy/Compress.lean` | ~45 | X9-A1 |
| X9-A3 | **Define Snappy op serialization.** `serializeLiteral : ByteArray → ByteArray` — tag byte encoding (1-byte, 2-byte, 4-byte length variants). `serializeCopy : Nat → Nat → ByteArray` — tag byte with offset/length encoding (1-byte, 2-byte, 4-byte offset variants). `serializeOps : Array SnappyOp → ByteArray`. `compress : ByteArray → ByteArray := fun data => varintEncode data.size ++ serializeOps (compressBlock data)`. | `Crypto/Snappy/Compress.lean` | ~40 | X9-A2 |
| X9-A4 | **Define Snappy tag parsing.** `parseTag : ByteArray → Nat → Except SnappyError (SnappyOp × Nat)` — decode one op from byte stream. Tag byte bits [1:0] determine type: 00 = literal, 01 = 1-byte copy, 10 = 2-byte copy, 11 = 4-byte copy. Extract length and offset fields from remaining tag bits and subsequent bytes. `parseVarint : ByteArray → Nat → Except SnappyError (Nat × Nat)` — decode LEB128 uncompressed length prefix. | `Crypto/Snappy/Decompress.lean` | ~35 | X9-A1 |
| X9-A5 | **Define Snappy decompression — backreference resolution.** `resolveOps : Array SnappyOp → Nat → Except SnappyError ByteArray` — process ops sequentially: literals append directly, copies resolve against output buffer. Validate: copy offset ≤ current output length, copy doesn't exceed declared uncompressed size. `decompress : ByteArray → Except SnappyError ByteArray` — parse varint length, parse all ops, resolve, validate final length matches declared. | `Crypto/Snappy/Decompress.lean` | ~40 | X9-A4 |
| X9-A6 | **Define CRC32C for Snappy framing.** `crc32cTable : Array UInt32` — pre-computed lookup table (256 entries, Castagnoli polynomial 0x1EDC6F41). `crc32c : ByteArray → UInt32` — table-driven computation. `maskCrc : UInt32 → UInt32` — Snappy masking: `((crc >>> 15) ||| (crc <<< 17)) + 0xa282ead8`. Prove `crc32c_deterministic`. | `Crypto/Snappy/Framing.lean` | ~30 | X1 |
| X9-A7 | **Define Snappy framing format.** `inductive FrameChunkType | compressed | uncompressed | padding | skippable (id : UInt8)`. `frameCompress : ByteArray → ByteArray` — split input into ≤ 65536-byte blocks, compress each, emit frame header (chunk type 1 byte + length 3 bytes LE + masked CRC 4 bytes + data). Prepend stream identifier chunk (`0xff 0x06 0x00 0x00 "sNaPpY"`). `frameDecompress : ByteArray → Except SnappyError ByteArray` — validate stream identifier, parse chunks, validate CRC, decompress compressed chunks, concatenate. | `Crypto/Snappy/Framing.lean` | ~45 | X9-A3, X9-A5, X9-A6 |
| X9-A8 | **Prove Snappy roundtrip correctness.** (1) `serializeOps_parseOps_roundtrip : parseAllOps (serializeOps ops) = .ok ops`. (2) `resolveOps_compressBlock_id : resolveOps (compressBlock data) data.size = .ok data`. (3) `snappy_roundtrip : decompress (compress data) = .ok data` — composition of (1) and (2). (4) `frame_roundtrip : frameDecompress (frameCompress data) = .ok data`. (5) `crc32c_frame_integrity : crc validated on each chunk`. (6) `compress_length_bounded : (compress data).size ≤ data.size + data.size / 6 + 32` (worst-case expansion). | `Crypto/Snappy/Proofs.lean` | ~50 | X9-A3, X9-A5, X9-A7 |

### Group B: Networking Types (X9-B1 through X9-B8)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X9-B1 | **Define core networking identifiers.** `structure PeerId where bytes : Bytes32`. `structure SubnetId where val : Uint64`. `structure Multiaddr where encoded : ByteArray`. `structure ProtocolId where name : String; version : Uint8`. Derive `DecidableEq`, `BEq`, `Hashable` for all. | `Node/Networking/Transport.lean` | ~25 | X1 |
| X9-B2 | **Define network message types.** `inductive NetworkMessage | gossipBlock (block : SignedBlock) | gossipAttestation (att : Attestation) | gossipAggregateProof (agg : AggregatedAttestation) | reqRespBlocksByRange (startSlot : Slot) (count : Uint64) | reqRespBlocksByRoot (roots : List Bytes32) | statusMessage (justified finalized : Checkpoint) | metadata (seqNum : Uint64) | ping (seqNum : Uint64) | goodbye (reason : Uint64)`. `encodeMessage : NetworkMessage → ByteArray` (SSZ + Snappy). `decodeMessage : ProtocolId → ByteArray → Except NetworkError NetworkMessage`. | `Node/Networking/Transport.lean` | ~35 | X9-B1, X5, X9-A3 |
| X9-B3 | **Define ENR structure and encoding.** `structure ENR where seq : Uint64; pairs : List (String × ByteArray); signature : ByteArray`. `encodeENR : ENR → ByteArray` via RLP (from X1-G3). `decodeENR : ByteArray → Except ENRError ENR` — parse RLP, extract key-value pairs, validate signature field present. `inductive ENRError | invalidRLP | missingSignature | invalidSequence | unknownScheme`. Prove `enr_roundtrip : decodeENR (encodeENR enr) = .ok enr`. | `Node/Networking/ENR.lean` | ~35 | X1-G3, X9-B1 |
| X9-B4 | **Define Gossipsub topic abstractions.** `structure Topic where name : String`. Consensus topics: `beaconBlockTopic : Topic`, `beaconAttestationTopic : SubnetId → Topic`, `aggregateProofTopic : Topic`. `inductive GossipsubAction | subscribe (topic : Topic) | unsubscribe (topic : Topic) | publish (topic : Topic) (data : ByteArray) | receive (topic : Topic) (data : ByteArray) (peer : PeerId)`. `structure GossipsubParams where meshSize : Nat; meshLow : Nat; meshHigh : Nat; gossipFactor : Nat; heartbeatInterval : Uint64; historyLength : Nat; historyGossip : Nat`. | `Node/Networking/Gossipsub.lean` | ~30 | X9-B1 |
| X9-B5 | **Define request-response protocol.** `inductive ReqRespMethod | blocksByRange | blocksByRoot | status | metadata | ping | goodbye`. `structure ReqRespRequest where method : ReqRespMethod; payload : ByteArray`. `inductive ReqRespStatus | success | invalidRequest | serverError | resourceUnavailable`. `structure ReqRespResponse where status : ReqRespStatus; payload : ByteArray`. `encodeReqResp : ReqRespRequest → ByteArray` — SSZ payload + Snappy compression + length prefix. `decodeReqResp : ByteArray → Except NetworkError ReqRespResponse`. | `Node/Networking/ReqResp.lean` | ~30 | X9-A3, X9-B1 |
| X9-B6 | **Define discovery types (discv5).** `structure DiscoveryConfig where bootstrapNodes : List ENR; listenPort : Uint16; maxPeers : Nat; refreshInterval : Uint64`. `structure RoutingTable where buckets : Array (List PeerId); selfId : PeerId; bucketSize : Nat`. `findNode : RoutingTable → PeerId → List PeerId` — k-bucket lookup. Abstract interface — full implementation in Rust. | `Node/Networking/Discovery.lean` | ~25 | X9-B3 |
| X9-B7 | **Define network configuration and error types.** `structure NetworkConfig where discoveryConfig : DiscoveryConfig; gossipsubParams : GossipsubParams; reqRespTimeout : Uint64; maxPeers : Nat; targetPeers : Nat; listenAddresses : List Multiaddr`. `inductive NetworkError | snappyError (e : SnappyError) | sszError (e : SSZError) | enrError (e : ENRError) | timeout | peerDisconnected | invalidProtocol | rateLimited`. | `Node/Networking/Config.lean` | ~25 | X9-B6, X9-A1 |
| X9-B8 | **Snappy and networking test suite.** (1) Snappy raw roundtrip: ≥ 5 test vectors (empty, small, repetitive, random-like, max block size). (2) Snappy framing roundtrip: ≥ 3 vectors. (3) CRC32C spot checks against known values. (4) ENR encode/decode against Ethereum test vectors. (5) SSZ+Snappy wire format: encode/decode for each `NetworkMessage` variant. (6) ReqResp encode/decode roundtrip. Minimum 20 test cases total. | `tests/NetworkSuite.lean` | ~40 | All X9-* |

## 4. Exit Criteria

- [ ] Snappy raw roundtrip proved
- [ ] Snappy framing roundtrip proved
- [ ] CRC32C determinism proved
- [ ] Compress length bounded (worst-case expansion)
- [ ] ENR roundtrip proved
- [ ] All networking types defined with SSZ serialization
- [ ] Network message encode/decode for all 9 variants
- [ ] ≥ 20 test cases in NetworkSuite
- [ ] Zero sorry in Snappy and networking modules
