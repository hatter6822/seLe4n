# Phase X13: seLe4n Integration Bridge

**Version**: v0.13.0
**Status**: PLANNED
**Sub-tasks**: 22 atomic units
**Dependencies**: X10 (Node Services), X12 (Testing), seLe4n codebase
**Estimated Lean LoC**: ~550
**Files created**: 8 new files

## 1. Objective

Connect the Lean Ethereum consensus client to the seLe4n microkernel. The
bridge allows the verified consensus client to run as a verified process on a
verified kernel — the ultimate goal of the combined project. This creates the
world's first formally verified Ethereum node on a formally verified OS.

## 2. Source Layout

```
LeanEth/Bridge/
├── SharedPrelude.lean            Shared typed identifiers, conversions
├── PlatformContract.lean         EthNodePlatformBinding typeclass
├── ResourceMapping.lean          Capabilities → kernel resources
├── IPCProtocol.lean              Message format, encode/decode
├── EventTranslation.lean         Kernel ↔ consensus event translation
├── Lifecycle.lean                Node init, main loop, shutdown
├── RPi5Extension.lean            BCM2712 Ethernet/SD abstractions
└── Proofs.lean                   Safety preservation proofs
```

## 3. Sub-task Breakdown

### Group A: Shared Foundation (X13-A1 through X13-A4)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X13-A1 | **Define shared typed identifier conversions.** Bidirectional conversions between seLe4n and LeanEth identifiers: `Bytes32` (both use for hashing — prove compatible), `PAddr`/`VAddr` (kernel memory addresses → LeanEth memory references), `ObjId` (kernel object IDs → LeanEth endpoint references). `toSeLe4n : LeanEth.Bytes32 → SeLe4n.Bytes32`. `fromSeLe4n : SeLe4n.Bytes32 → LeanEth.Bytes32`. Prove `fromSeLe4n_toSeLe4n_roundtrip : fromSeLe4n (toSeLe4n x) = x`. Prove `toSeLe4n_fromSeLe4n_roundtrip : toSeLe4n (fromSeLe4n y) = y`. Handle: field width differences, endianness alignment. | `Bridge/SharedPrelude.lean` | ~35 | seLe4n, X1 |
| X13-A2 | **Define Ethereum node platform contract.** `class EthNodePlatformBinding extends PlatformBinding where networkAvailable : Prop; storageAvailable : Prop; timerAvailable : Prop; maxPeers : Nat; maxBlockCacheSize : Nat; networkLatencyBound : Nat; storageSizeBound : Nat`. Simulation instance: all `True`, generous bounds. RPi5 instance: concrete bounds from hardware specs (1GB network buffer, 32GB storage, 100ms timer). | `Bridge/PlatformContract.lean` | ~30 | seLe4n |
| X13-A3 | **Define resource mapping — capabilities to kernel resources.** `structure EthNodeCapabilities where memoryRegion : VSpaceRegion; networkEndpoint : ObjId; timerEndpoint : ObjId; storageEndpoint : ObjId; logEndpoint : Option ObjId`. `capsValid : EthNodeCapabilities → Prop` — all endpoints exist in kernel state, memory region is mapped, capabilities are authorized. `requiredMemory : NodeConfig → Nat` — compute memory needed for block cache + state storage. | `Bridge/ResourceMapping.lean` | ~25 | X13-A2, seLe4n |
| X13-A4 | **Define IPC message protocol.** `inductive IPCMessageType | blockNotification | attestationForward | timerEvent | syncRequest | syncResponse | shutdownRequest | healthCheck`. `structure IPCMessage where msgType : IPCMessageType; payload : ByteArray; seqNum : Uint64`. `encodeIPCMessage : IPCMessage → ByteArray` — fixed header (type 1 byte + seqNum 8 bytes + length 4 bytes) + payload. `decodeIPCMessage : ByteArray → Except IPCError IPCMessage`. Prove `ipcMessage_roundtrip`. `inductive IPCError | invalidType | truncatedMessage | payloadTooLarge | invalidSeqNum`. | `Bridge/IPCProtocol.lean` | ~35 | X13-A1 |

### Group B: Event Translation & IPC (X13-B1 through X13-B5)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X13-B1 | **Define kernel → consensus event translation.** `kernelEventToNodeEvent : KernelEvent → Option NodeEvent` — translate seLe4n IPC receive events to consensus events. Map: IPC receive on network endpoint → `blockReceived` or `attestationReceived` (decode SSZ payload). Timer interrupt → `tick`. IPC on storage endpoint → sync response. Return `none` for irrelevant kernel events (scheduler ticks, capability operations). | `Bridge/EventTranslation.lean` | ~30 | X13-A4, X10-E4 |
| X13-B2 | **Define consensus → kernel response translation.** `nodeResponseToKernelResponse : List NetworkMessage → List IPCMessage` — translate outbound consensus messages to kernel IPC messages. Gossip block/attestation → IPC send on network endpoint. Storage write → IPC send on storage endpoint. API response → IPC reply. | `Bridge/EventTranslation.lean` | ~25 | X13-B1 |
| X13-B3 | **Define kernel IPC send/receive primitives.** `sendToKernel : ObjId → ByteArray → KernelM Unit` — construct IPC send syscall, encode payload as SSZ byte array, call via seLe4n endpoint. `recvFromKernel : ObjId → KernelM ByteArray` — blocking receive on endpoint, decode IPC message. `sendBatch : ObjId → List ByteArray → KernelM Unit` — send multiple messages (for gossip fan-out). Error handling: timeout, endpoint busy, message too large. | `Bridge/IPCProtocol.lean` | ~25 | seLe4n, X13-A4 |
| X13-B4 | **Define node lifecycle — initialization.** `initEthNode : NodeConfig → EthNodeCapabilities → KernelM NodeState` — (1) validate capabilities via `capsValid`, (2) request memory mapping from kernel, (3) initialize genesis state via X10 `initChainService`, (4) register with network endpoint, (5) register timer for slot clock ticks, (6) return initial `NodeState`. Error: capability insufficient → graceful failure with diagnostic. | `Bridge/Lifecycle.lean` | ~30 | X13-B3, X10-A3 |
| X13-B5 | **Define node lifecycle — main loop and shutdown.** `ethNodeMainLoop : NodeState → KernelM NodeState` — (1) receive event from kernel, (2) translate via `kernelEventToNodeEvent`, (3) process via `processEvent` (X10), (4) translate responses via `nodeResponseToKernelResponse`, (5) send responses to kernel. `shutdownEthNode : NodeState → KernelM Unit` — (1) flush pending storage writes, (2) unregister from network endpoint, (3) release memory mapping, (4) cancel timer, (5) send shutdown acknowledgment. | `Bridge/Lifecycle.lean` | ~30 | X13-B4, X13-B1, X13-B2 |

### Group C: RPi5 Platform Extension (X13-C1 through X13-C3)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X13-C1 | **Define BCM2712 Ethernet NIC abstraction.** `structure EthernetConfig where baseAddr : PAddr; irqLine : Nat; macAddress : Bytes6; mtu : Nat := 1500`. Map to seLe4n device capability. `ethernetAvailable : EthNodePlatformBinding` instance field — proved from BCM2712 board spec. | `Bridge/RPi5Extension.lean` | ~20 | X13-A2, seLe4n |
| X13-C2 | **Define SD card storage abstraction.** `structure SDCardConfig where baseAddr : PAddr; blockSize : Nat := 512; maxBlocks : Nat`. Map to seLe4n device capability for persistent storage. `storageAvailable : EthNodePlatformBinding` instance field — proved from RPi5 board spec. | `Bridge/RPi5Extension.lean` | ~15 | X13-A2, seLe4n |
| X13-C3 | **Define RPi5 `EthNodePlatformBinding` instance.** Combine Ethernet + SD card + ARM timer. `instance : EthNodePlatformBinding RPi5Platform where networkAvailable := ethernetAvailable; storageAvailable := sdCardAvailable; timerAvailable := armTimerAvailable; maxPeers := 50; maxBlockCacheSize := 1024; networkLatencyBound := 100; storageSizeBound := 32 * 1024 * 1024 * 1024`. | `Bridge/RPi5Extension.lean` | ~20 | X13-C1, X13-C2 |

### Group D: Safety Proofs (X13-D1 through X13-D5)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X13-D1 | **Prove bridge preserves kernel invariants.** `bridge_preserves_kernel_invariants : ∀ ks ethEvent, kernelInvariantBundle ks → processEthEvent ks ethEvent = .ok ks' → kernelInvariantBundle ks'`. Proof strategy: Ethereum node operations reduce to standard kernel IPC operations; each IPC operation preserves kernel invariants (from seLe4n proofs); bridge introduces no new state modifications outside IPC channel. | `Bridge/Proofs.lean` | ~40 | X13-B4, X13-B5, seLe4n |
| X13-D2 | **Prove bridge preserves consensus invariants.** `bridge_preserves_consensus_invariants : ∀ cs kernelEvent, consensusInvariantBundle cs → processKernelEvent cs kernelEvent = .ok cs' → consensusInvariantBundle cs'`. Proof strategy: kernel events are translated to valid consensus events; each consensus event preserves consensus invariants (from X7 proofs); translation introduces no new state that bypasses consensus validation. | `Bridge/Proofs.lean` | ~40 | X13-B1, X7 |
| X13-D3 | **Prove capability sufficiency.** `ethNodeCapabilities_sufficient : ∀ caps : EthNodeCapabilities, capsValid caps → ∀ event, processEvent event requiredCap → caps provides requiredCap`. Enumerate all operations in `processEvent`, identify capability requirements, verify `EthNodeCapabilities` covers all cases. | `Bridge/Proofs.lean` | ~25 | X13-A3, X10-E4 |
| X13-D4 | **Prove IPC protocol safety.** `ipcMessage_no_buffer_overflow : (encodeIPCMessage msg).size ≤ MAX_IPC_SIZE`. `ipcMessage_authenticated : decodeIPCMessage validates seqNum monotonicity`. `ipcProtocol_liveness : well-formed message always decodes successfully`. | `Bridge/Proofs.lean` | ~20 | X13-A4 |
| X13-D5 | **Prove lifecycle correctness.** `initEthNode_capsValid_required : initEthNode succeeds only if capsValid`. `shutdownEthNode_releases_all : after shutdown, no capabilities held`. `mainLoop_terminates_on_shutdown : mainLoop processes shutdown request and returns`. | `Bridge/Proofs.lean` | ~20 | X13-B4, X13-B5 |

### Group E: Integration Tests (X13-E1 through X13-E3)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X13-E1 | **End-to-end integration test — happy path.** Kernel boots → creates Eth node process → node initializes genesis → processes 3 test blocks via IPC → state transitions correct → queries head via API → node shuts down cleanly. Verify: kernel invariants hold at each step, consensus invariants hold at each step, no resource leaks. | `tests/IntegrationSuite.lean` | ~40 | All X13-* |
| X13-E2 | **Cross-invariant composition test.** Multi-step trace alternating kernel operations and consensus transitions: (1) kernel schedules timer, (2) timer fires → consensus slot advance, (3) kernel delivers IPC → consensus processes block, (4) consensus sends IPC → kernel routes to network. Verify composed invariant (kernel ∧ consensus) holds at every step. | `tests/IntegrationSuite.lean` | ~25 | X13-D1, X13-D2 |
| X13-E3 | **Error recovery test.** (1) Network endpoint unavailable → node handles gracefully. (2) Invalid block received → consensus rejects, kernel unaffected. (3) Storage full → node degrades, no crash. (4) Timer missed → node recovers on next tick. Verify: invariants preserved across all error paths. | `tests/IntegrationSuite.lean` | ~20 | X13-B5 |

## 4. Exit Criteria

- [ ] Bridge compiles with both SeLe4n and LeanEth imports
- [ ] Kernel invariants preserved across bridge (proved)
- [ ] Consensus invariants preserved across bridge (proved)
- [ ] Capability sufficiency proved
- [ ] IPC protocol safety proved (no overflow, authenticated, liveness)
- [ ] Lifecycle correctness proved (init requires caps, shutdown releases all)
- [ ] IPC message roundtrip proved
- [ ] RPi5 platform binding with Ethernet + SD + timer
- [ ] End-to-end integration test demonstrates full flow
- [ ] Cross-invariant composition test passes
- [ ] Error recovery test passes (4 scenarios)
- [ ] Zero sorry in bridge modules
