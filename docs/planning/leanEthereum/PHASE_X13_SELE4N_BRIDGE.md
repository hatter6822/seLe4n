# Phase X13: seLe4n Integration Bridge

**Version**: v0.13.0
**Status**: PLANNED
**Sub-tasks**: 12 atomic units
**Dependencies**: X10 (Node Services), X12 (Testing), seLe4n codebase
**Estimated Lean LoC**: ~400
**Files created**: 5 new files

## 1. Objective

Connect the Lean Ethereum consensus client to the seLe4n microkernel. The
bridge allows the verified consensus client to run as a verified process on a
verified kernel — the ultimate goal of the combined project. This creates the
world's first formally verified Ethereum node on a formally verified OS.

## 2. Sub-task Breakdown

### Group A: Shared Foundation (X13-A1 through X13-A3)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X13-A1 | **Define shared prelude.** Shared typed identifiers between seLe4n and LeanEth: `Bytes32` (both use for hashing), `PAddr`/`VAddr` (kernel memory addresses), `ObjId` (kernel object identifiers). Import both `SeLe4n.Prelude` and `LeanEth.Prelude`. Define bidirectional conversion functions. Prove conversion roundtrip: `fromSeLe4n (toSeLe4n x) = x`. | `Bridge/SharedPrelude.lean` | ~35 | seLe4n, X1 |
| X13-A2 | **Define Ethereum node platform contract.** Typeclass `EthNodePlatformBinding` extending seLe4n's `PlatformBinding`: `networkAvailable : Prop`, `storageAvailable : Prop`, `timerAvailable : Prop`, `maxPeers : Nat`, `maxBlockCacheSize : Nat`. Simulation and RPi5 instances. | `Bridge/PlatformContract.lean` | ~30 | seLe4n, X10 |
| X13-A3 | **Define resource mapping.** Map Ethereum resource requirements to seLe4n capabilities: memory for block/state storage → VSpace mappings, network I/O → device capabilities, timer → platform timer capability. `structure EthNodeCapabilities where memoryRegion : VSpaceRegion; networkEndpoint : ObjId; timerEndpoint : ObjId; storageEndpoint : ObjId`. | `Bridge/SeLe4nIntegration.lean` | ~25 | X13-A2 |

### Group B: IPC Bridge (X13-B1 through X13-B4)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X13-B1 | **Define kernel IPC interface.** `sendToKernel : ObjId → ByteArray → KernelM Unit` — send SSZ-encoded message via seLe4n IPC endpoint. `recvFromKernel : ObjId → KernelM ByteArray` — receive via endpoint. Messages: block notifications, attestation forwarding, timer events. | `Bridge/SeLe4nIntegration.lean` | ~25 | seLe4n, X13-A3 |
| X13-B2 | **Define event translation.** `kernelEventToNodeEvent : KernelEvent → Option NodeEvent` — translate seLe4n IPC messages to Ethereum consensus events. `nodeResponseToKernelResponse : NodeResponse → ByteArray` — translate consensus responses to kernel IPC messages. | `Bridge/SeLe4nIntegration.lean` | ~25 | X13-B1, X10-D3 |
| X13-B3 | **Define node lifecycle.** `initEthNode : NodeConfig → EthNodeCapabilities → KernelM NodeState`. `shutdownEthNode : NodeState → KernelM Unit` (release capabilities, flush storage). `ethNodeMainLoop : NodeState → KernelM NodeState` (process one event from kernel). | `Bridge/SeLe4nIntegration.lean` | ~30 | X13-B1, X13-B2 |
| X13-B4 | **RPi5 platform binding extension.** Add Ethernet NIC abstraction for BCM2712 networking. SD card storage abstraction. Define hardware address ranges. | `Bridge/RPi5Extension.lean` | ~25 | X13-A2 |

### Group C: Safety Proofs (X13-C1 through X13-C3)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X13-C1 | **Prove bridge preserves kernel invariants.** `bridge_preserves_kernel_invariants : ∀ ks ethEvent, kernelInvariantBundle ks → processEthEvent ks ethEvent = .ok ks' → kernelInvariantBundle ks'`. The Ethereum client cannot violate kernel safety. | `Bridge/Proofs.lean` | ~40 | X13-B1, seLe4n |
| X13-C2 | **Prove bridge preserves consensus invariants.** `bridge_preserves_consensus_invariants : ∀ cs kernelEvent, consensusInvariantBundle cs → processKernelEvent cs kernelEvent = .ok cs' → consensusInvariantBundle cs'`. Kernel events cannot violate consensus safety. | `Bridge/Proofs.lean` | ~40 | X13-B2, X7 |
| X13-C3 | **Prove capability sufficiency.** `ethNodeCapabilities_sufficient : ∀ caps : EthNodeCapabilities, capsValid caps → ∀ event, processEvent requiresCap → caps provides requiresCap`. The declared capabilities are sufficient for all node operations. | `Bridge/Proofs.lean` | ~20 | X13-A3 |

### Group D: Integration Test (X13-D1 through X13-D2)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X13-D1 | **End-to-end integration test.** Kernel boots → creates Eth node process → node initializes genesis → processes test blocks via IPC → state transitions correct → node shuts down. | `tests/IntegrationSuite.lean` | ~40 | All X13-* |
| X13-D2 | **Cross-invariant composition test.** Verify that the composed invariant (kernel + consensus) holds across a multi-step trace that alternates kernel operations and consensus transitions. | `tests/IntegrationSuite.lean` | ~20 | X13-C1, X13-C2 |

## 3. Exit Criteria

- [ ] Bridge compiles with both SeLe4n and LeanEth imports
- [ ] Kernel invariants preserved across bridge (proved)
- [ ] Consensus invariants preserved across bridge (proved)
- [ ] Capability sufficiency proved
- [ ] Integration test demonstrates end-to-end flow
- [ ] Zero sorry in bridge modules
