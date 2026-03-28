# Phase X10: Node Services — Chain, Validator, Sync

**Version**: v0.10.0
**Status**: PLANNED
**Sub-tasks**: 18 atomic units
**Dependencies**: X5 (Containers), X8 (Fork Choice), X9 (Networking Types)
**Estimated Lean LoC**: ~850
**Files created**: 14 new files

## 1. Objective

Formalize the node service layer: slot clock, chain service, validator duties,
synchronization, storage interface, and REST API types. These abstractions
connect pure consensus logic to the outside world via Rust ABI boundaries.

## 2. Sub-task Breakdown

### Group A: Chain Service (X10-A1 through X10-A4)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X10-A1 | **Define `SlotClock`.** `structure SlotClock where genesisTime : Uint64; secondsPerSlot : Nat; intervalsPerSlot : Nat`. `currentSlot : SlotClock → Uint64 → Slot := fun clock now => Slot.mk (Uint64.ofNat ((now.toNat - clock.genesisTime.toNat) / clock.secondsPerSlot))`. `currentInterval : SlotClock → Uint64 → Nat`. `slotStartTime : SlotClock → Slot → Uint64`. Prove `currentSlot_monotone : t₁ ≤ t₂ → currentSlot c t₁ ≤ currentSlot c t₂`. | `Node/Chain/SlotClock.lean` | ~35 | X5-A1 |
| X10-A2 | **Define chain configuration.** `structure ChainConfig where slotClock : SlotClock; genesisState : State; genesisBlock : Block`. `initChainService : ChainConfig → Except ChainError ChainState`. | `Node/Chain/Config.lean` | ~15 | X10-A1, X5 |
| X10-A3 | **Define `ChainState` and transitions.** `structure ChainState where store : Store; currentSlot : Slot; synced : Bool`. `onSlotBoundary : ChainState → Slot → ChainState`. `onNewBlock : ChainState → SignedBlock → Except ChainError ChainState` — validate signatures, apply state transition, update store. `onNewAttestation : ChainState → SignedAttestation → Except ChainError ChainState`. | `Node/Chain/Service.lean` | ~45 | X10-A2, X8 |
| X10-A4 | **Define `ChainError`.** `inductive ChainError | consensusError (e : ConsensusError) | forkChoiceError (e : ForkChoiceError) | signatureInvalid | blockAlreadyKnown | notSynced`. | `Node/Chain/Config.lean` | ~10 | — |

### Group B: Validator Service (X10-B1 through X10-B3)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X10-B1 | **Define `ValidatorDuty` and scheduler.** `inductive ValidatorDuty | proposeBlock (slot : Slot) (index : ValidatorIndex) | attest (slot : Slot) (index : ValidatorIndex)`. `scheduleDuties : Validators → Slot → List ValidatorDuty` — proposer = `slot % validators.length`, attesters = all validators at interval 1. | `Node/Validator/Service.lean` | ~30 | X5-A5 |
| X10-B2 | **Define `ValidatorRegistry`.** `structure ValidatorRegistry where keys : HashMap ValidatorIndex KeyPair; scheme : GeneralizedXmssScheme`. `signBlock : ValidatorRegistry → ValidatorIndex → Block → Except ValidatorError SignedBlock`. `signAttestation : ValidatorRegistry → ValidatorIndex → AttestationData → Except ValidatorError SignedAttestation`. | `Node/Validator/Registry.lean` | ~35 | X4, X5-D2 |
| X10-B3 | **Define `ValidatorState` and service.** `structure ValidatorState where registry : ValidatorRegistry; pendingDuties : List ValidatorDuty`. `executeDuty : ValidatorState → ChainState → ValidatorDuty → Except ValidatorError (ValidatorState × Option NetworkMessage)` — produce block or attestation based on duty type. | `Node/Validator/Service.lean` | ~30 | X10-B1, X10-B2 |

### Group C: Sync Service (X10-C1 through X10-C5)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X10-C1 | **Define sync state machine.** `inductive SyncPhase | checkpointSync | headSync | backfillSync | synced`. `structure SyncState where phase : SyncPhase; targetSlot : Slot; currentSlot : Slot; pendingBlocks : BlockCache`. | `Node/Sync/Service.lean` | ~20 | X5 |
| X10-C2 | **Define checkpoint sync.** `checkpointSync : SyncState → Checkpoint → State → Except SyncError SyncState` — verify state root matches checkpoint, transition to headSync. | `Node/Sync/CheckpointSync.lean` | ~20 | X10-C1 |
| X10-C3 | **Define head sync and backfill.** `headSync : SyncState → List SignedBlock → Except SyncError SyncState` — apply blocks in order, transition to synced when caught up. `backfillSync : SyncState → Slot → Slot → SyncState` — request historical blocks by range. | `Node/Sync/HeadSync.lean` | ~25 | X10-C1 |
| X10-C4 | **Define `BlockCache`.** `structure BlockCache where pending : HashMap Bytes32 SignedBlock; ordered : List Bytes32`. `insert`, `popReady : BlockCache → Bytes32 → Option (SignedBlock × BlockCache)`. | `Node/Sync/BlockCache.lean` | ~25 | X5-D2 |
| X10-C5 | **Define `PeerManager`.** `structure PeerManager where connected : HashMap PeerId PeerInfo; maxPeers : Nat`. `structure PeerInfo where enr : ENR; status : PeerStatus; score : Int`. `inductive PeerStatus | connected | disconnected | banned`. | `Node/Sync/PeerManager.lean` | ~25 | X9-B1, X9-B2 |

### Group D: Storage & API (X10-D1 through X10-D3)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X10-D1 | **Define storage interface.** `class Database (db : Type) where get : db → Namespace → ByteArray → IO (Option ByteArray); put : db → Namespace → ByteArray → ByteArray → IO Unit; delete : db → Namespace → ByteArray → IO Unit`. `inductive Namespace | blocks | states | checkpoints | metadata`. | `Node/Storage/Interface.lean` | ~25 | X1 |
| X10-D2 | **Define API endpoint types.** `inductive APIEndpoint | getState (root : Bytes32) | getBlock (root : Bytes32) | getForkChoice | getHealth | getCheckpoints | getValidators`. `structure APIResponse where status : Nat; body : ByteArray`. `handleRequest : ChainState → APIEndpoint → APIResponse`. | `Node/API/Endpoints.lean` | ~30 | X8 |
| X10-D3 | **Define top-level `Node` orchestrator.** `structure NodeConfig where chain : ChainConfig; validator : Option ValidatorRegistry; network : NetworkConfig; storage : DatabaseConfig`. `structure NodeState where chain : ChainState; validator : Option ValidatorState; sync : SyncState; peers : PeerManager`. `inductive NodeEvent | tick (time : Uint64) | blockReceived (block : SignedBlock) | attestationReceived (att : SignedAttestation) | peerConnected (peer : PeerId) | syncComplete`. `processEvent : NodeState → NodeEvent → Except NodeError NodeState`. | `Node/Node.lean` | ~45 | All X10-* |

### Group E: Tests (X10-E1 through X10-E3)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X10-E1 | **Slot clock tests.** Verify currentSlot monotonicity. Verify slot boundaries. | `tests/NodeServiceSuite.lean` | ~15 | X10-A1 |
| X10-E2 | **Duty scheduling tests.** Verify proposer selection matches round-robin. Verify all validators attest each slot. | `tests/NodeServiceSuite.lean` | ~15 | X10-B1 |
| X10-E3 | **Sync state machine tests.** Phase transitions: checkpoint → head → synced. Block cache ordering. | `tests/NodeServiceSuite.lean` | ~15 | X10-C1 |

## 3. Exit Criteria

- [ ] All node services compile with deterministic state machines
- [ ] Slot clock monotonicity proved
- [ ] Duty scheduling matches proposer selection
- [ ] Sync state machine covers all phases
- [ ] Node orchestrator handles all event types
- [ ] Zero sorry in node modules
