# Phase X10: Node Services — Chain, Validator, Sync

**Version**: v0.10.0
**Status**: PLANNED
**Sub-tasks**: 30 atomic units
**Dependencies**: X5 (Containers), X8 (Fork Choice), X9 (Networking Types)
**Estimated Lean LoC**: ~1,050
**Files created**: 16 new files

## 1. Objective

Formalize the node service layer: slot clock, chain service, validator duties,
synchronization, storage interface, and REST API types. These abstractions
connect pure consensus logic to the outside world via Rust ABI boundaries.

## 2. Source Layout

```
LeanEth/Node/
├── Chain/
│   ├── SlotClock.lean         Slot clock with monotonicity proof
│   ├── Config.lean            Chain configuration, error types
│   ├── Service.lean           ChainState transitions
│   └── Proofs.lean            Chain service preservation proofs
├── Validator/
│   ├── Duties.lean            Duty types, scheduling logic
│   ├── Registry.lean          Key management, signing
│   ├── Service.lean           Validator state machine
│   └── Proofs.lean            Duty scheduling correctness
├── Sync/
│   ├── StateMachine.lean      Sync phases, transitions
│   ├── CheckpointSync.lean    Checkpoint sync logic
│   ├── HeadSync.lean          Head sync + backfill
│   ├── BlockCache.lean        Pending block management
│   └── PeerManager.lean       Peer tracking, scoring
├── Storage/
│   ├── Interface.lean         Database typeclass
│   └── Schema.lean            Namespace definitions, key encoding
├── API/
│   └── Endpoints.lean         REST API type definitions
└── Node.lean                  Top-level orchestrator
```

## 3. Sub-task Breakdown

### Group A: Slot Clock (X10-A1 through X10-A3)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X10-A1 | **Define `SlotClock` structure.** `structure SlotClock where genesisTime : Uint64; secondsPerSlot : Nat; intervalsPerSlot : Nat; h_secondsPos : secondsPerSlot > 0; h_intervalsPos : intervalsPerSlot > 0`. `currentSlot : SlotClock → Uint64 → Slot` — `(now - genesisTime) / secondsPerSlot`. `currentInterval : SlotClock → Uint64 → Nat` — `((now - genesisTime) % secondsPerSlot) * intervalsPerSlot / secondsPerSlot`. `slotStartTime : SlotClock → Slot → Uint64` — `genesisTime + slot * secondsPerSlot`. `intervalStartTime : SlotClock → Slot → Nat → Uint64`. | `Node/Chain/SlotClock.lean` | ~35 | X5-A1 |
| X10-A2 | **Prove slot clock properties.** (1) `currentSlot_monotone : t₁ ≤ t₂ → currentSlot c t₁ ≤ currentSlot c t₂`. (2) `slotStartTime_currentSlot : slotStartTime c (currentSlot c t) ≤ t`. (3) `currentSlot_slotStartTime : currentSlot c (slotStartTime c s) = s`. (4) `interval_bounded : currentInterval c t < c.intervalsPerSlot`. (5) `slotStartTime_injective : slotStartTime c s₁ = slotStartTime c s₂ → s₁ = s₂`. | `Node/Chain/SlotClock.lean` | ~30 | X10-A1 |
| X10-A3 | **Define chain configuration and errors.** `structure ChainConfig where slotClock : SlotClock; genesisState : State; genesisBlock : Block; config : Config`. `initChainService : ChainConfig → Except ChainError ChainState` — validate genesis state well-formedness, initialize store from anchor. `inductive ChainError | consensusError (e : ConsensusError) | forkChoiceError (e : ForkChoiceError) | signatureInvalid | blockAlreadyKnown | notSynced | genesisInvalid (msg : String) | stateRootMismatch`. | `Node/Chain/Config.lean` | ~25 | X10-A1, X5, X8 |

### Group B: Chain Service (X10-B1 through X10-B4)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X10-B1 | **Define `ChainState` structure.** `structure ChainState where store : Store; currentSlot : Slot; synced : Bool; headRoot : Bytes32; finalizedCheckpoint : Checkpoint; justifiedCheckpoint : Checkpoint; lastProcessedSlot : Slot`. | `Node/Chain/Service.lean` | ~15 | X10-A3, X8 |
| X10-B2 | **Define chain state transitions.** `onSlotBoundary : ChainState → Slot → ChainState` — advance slot, trigger `onTick` in store, update head. `onNewBlock : ChainState → SignedBlock → Except ChainError ChainState` — validate signatures, verify slot ≥ current, apply state transition via X6, call `store.onBlock`, update head/justified/finalized. `onNewAttestation : ChainState → Attestation → Except ChainError ChainState` — validate via store, call `store.onAttestation`. | `Node/Chain/Service.lean` | ~45 | X10-B1, X6, X8-C2 |
| X10-B3 | **Define chain queries.** `getHead : ChainState → Bytes32`. `getState : ChainState → Bytes32 → Option State`. `getBlock : ChainState → Bytes32 → Option Block`. `getFinalizedState : ChainState → State`. `getJustifiedState : ChainState → State`. `isOptimistic : ChainState → Bytes32 → Bool` (block not yet fully validated). | `Node/Chain/Service.lean` | ~20 | X10-B1 |
| X10-B4 | **Prove chain service properties.** (1) `onSlotBoundary_monotone : cs.currentSlot ≤ (onSlotBoundary cs s).currentSlot`. (2) `onNewBlock_updates_head : head after block = lmdGhost updated_store`. (3) `onNewBlock_finalized_monotone : cs.finalizedCheckpoint.slot ≤ cs'.finalizedCheckpoint.slot`. (4) `chain_state_consistent : storeConsistent (onNewBlock cs b).store`. | `Node/Chain/Proofs.lean` | ~30 | X10-B2 |

### Group C: Validator Service (X10-C1 through X10-C5)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X10-C1 | **Define validator duty types.** `inductive ValidatorDuty | proposeBlock (slot : Slot) (index : ValidatorIndex) | attest (slot : Slot) (index : ValidatorIndex)`. `structure DutySchedule where duties : List ValidatorDuty; epoch : Slot`. | `Node/Validator/Duties.lean` | ~15 | X5-A5 |
| X10-C2 | **Define duty scheduling logic.** `getProposer : Validators → Slot → ValidatorIndex` — round-robin: `slot.val % validators.length`. `getAttesters : Validators → Slot → List ValidatorIndex` — all validators attest each slot. `scheduleDuties : Validators → Slot → DutySchedule` — combine proposer + attesters for slot. Prove `getProposer_total : validators.length > 0 → getProposer vs s < validators.length`. Prove `getAttesters_complete : ∀ vi ∈ validators, vi ∈ getAttesters vs s`. | `Node/Validator/Duties.lean` | ~30 | X10-C1 |
| X10-C3 | **Define validator key registry.** `structure ValidatorRegistry where keys : HashMap ValidatorIndex KeyPair; scheme : GeneralizedXmssScheme`. `lookupKey : ValidatorRegistry → ValidatorIndex → Option KeyPair`. `signBlock : ValidatorRegistry → ValidatorIndex → Block → Except ValidatorError SignedBlock` — lookup key, produce XMSS signature over `hashTreeRoot block`. `signAttestation : ValidatorRegistry → ValidatorIndex → AttestationData → Except ValidatorError Attestation` — sign attestation data. `inductive ValidatorError | keyNotFound (vi : ValidatorIndex) | signingFailed (msg : String) | keyExhausted`. | `Node/Validator/Registry.lean` | ~35 | X4, X5 |
| X10-C4 | **Define validator state machine.** `structure ValidatorState where registry : ValidatorRegistry; pendingDuties : List ValidatorDuty; executedDuties : List (ValidatorDuty × Slot)`. `executeDuty : ValidatorState → ChainState → ValidatorDuty → Except ValidatorError (ValidatorState × Option NetworkMessage)` — for propose: build block via X6-E4 `buildBlock`, sign, emit gossip message. For attest: construct `AttestationData` from chain head, sign, emit gossip. `pruneExecutedDuties : ValidatorState → Slot → ValidatorState` — remove duties older than finalized. | `Node/Validator/Service.lean` | ~35 | X10-C2, X10-C3 |
| X10-C5 | **Prove validator service properties.** (1) `executeDuty_proposeBlock_valid : executeDuty vs cs (proposeBlock s vi) = .ok (vs', msg) → msg matches gossipBlock`. (2) `executeDuty_attest_valid : attestation head matches chain head`. (3) `scheduleDuties_one_proposer : exactly one proposer per slot`. (4) `pruneExecutedDuties_monotone : only removes, never adds`. | `Node/Validator/Proofs.lean` | ~25 | X10-C4 |

### Group D: Sync Service (X10-D1 through X10-D6)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X10-D1 | **Define sync state machine.** `inductive SyncPhase | idle | checkpointSync | headSync | backfillSync | synced`. `structure SyncState where phase : SyncPhase; targetSlot : Slot; currentSlot : Slot; pendingBlocks : BlockCache; checkpointRoot : Option Bytes32; syncStartTime : Option Uint64`. State machine diagram: idle → checkpointSync → headSync → synced, with backfillSync as parallel optional phase. | `Node/Sync/StateMachine.lean` | ~25 | X5 |
| X10-D2 | **Define sync phase transitions.** `startCheckpointSync : SyncState → Checkpoint → SyncState`. `checkpointSyncComplete : SyncState → State → Except SyncError SyncState` — verify state root matches checkpoint, transition to headSync. `headSyncProgress : SyncState → List SignedBlock → Except SyncError SyncState` — apply blocks in order. `headSyncComplete : SyncState → SyncState` — transition to synced when `currentSlot ≥ targetSlot`. `startBackfill : SyncState → Slot → SyncState`. `inductive SyncError | invalidCheckpoint | blockValidationFailed (e : ConsensusError) | gapInBlockSequence | targetRegressed`. | `Node/Sync/StateMachine.lean` | ~30 | X10-D1 |
| X10-D3 | **Define checkpoint sync logic.** `requestCheckpointState : Checkpoint → ReqRespRequest` — build `blocksByRoot` request for checkpoint block. `validateCheckpointState : Checkpoint → State → Bool` — `hashTreeRoot state = checkpoint.root`. `applyCheckpointState : SyncState → ChainState → Checkpoint → State → Except SyncError (SyncState × ChainState)` — initialize store from checkpoint anchor, transition sync phase. | `Node/Sync/CheckpointSync.lean` | ~25 | X10-D1, X8-A2 |
| X10-D4 | **Define head sync and backfill.** `requestBlockRange : Slot → Uint64 → ReqRespRequest` — `blocksByRange` request. `processBlockBatch : SyncState → ChainState → List SignedBlock → Except SyncError (SyncState × ChainState)` — validate each block in order, apply to chain state, update sync progress. `backfillRequest : SyncState → ReqRespRequest` — request next batch of historical blocks. `backfillProcess : SyncState → List SignedBlock → Except SyncError SyncState` — store blocks without full validation (header-only check). | `Node/Sync/HeadSync.lean` | ~30 | X10-D2 |
| X10-D5 | **Define `BlockCache`.** `structure BlockCache where pending : HashMap Bytes32 SignedBlock; ordered : List Bytes32; maxSize : Nat`. `insert : BlockCache → SignedBlock → BlockCache` — add by block root, maintain ordered list. `popReady : BlockCache → Bytes32 → Option (SignedBlock × BlockCache)` — remove block matching expected parent. `prune : BlockCache → Slot → BlockCache` — remove blocks older than slot. `size : BlockCache → Nat`. Prove `insert_size : (insert bc b).size = bc.size + 1 ∨ (insert bc b).size = bc.size` (dedup). | `Node/Sync/BlockCache.lean` | ~30 | X5 |
| X10-D6 | **Define `PeerManager`.** `structure PeerManager where connected : HashMap PeerId PeerInfo; maxPeers : Nat; targetPeers : Nat`. `structure PeerInfo where enr : ENR; status : PeerStatus; score : Int; lastSeen : Uint64; syncStatus : Option Checkpoint`. `inductive PeerStatus | connected | disconnected | banned`. `addPeer`, `removePeer`, `updateScore`, `getBestPeers : PeerManager → Nat → List PeerId` (sorted by score), `banPeer : PeerManager → PeerId → PeerManager`. | `Node/Sync/PeerManager.lean` | ~30 | X9-B1, X9-B3 |

### Group E: Storage & API (X10-E1 through X10-E4)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X10-E1 | **Define storage interface.** `class Database (db : Type) where get : db → Namespace → ByteArray → IO (Option ByteArray); put : db → Namespace → ByteArray → ByteArray → IO Unit; delete : db → Namespace → ByteArray → IO Unit; exists : db → Namespace → ByteArray → IO Bool`. `inductive Namespace | blocks | states | checkpoints | metadata | validators`. | `Node/Storage/Interface.lean` | ~20 | X1 |
| X10-E2 | **Define storage schema and key encoding.** `blockKey : Bytes32 → ByteArray` — root hash as key. `stateKey : Bytes32 → ByteArray`. `checkpointKey : Slot → ByteArray`. `metadataKey : String → ByteArray`. `slotIndexKey : Slot → ByteArray` — secondary index for slot-based lookups. `structure StorageOps (db : Type) [Database db] where storeBlock : db → SignedBlock → IO Unit; getBlock : db → Bytes32 → IO (Option SignedBlock); storeState : db → State → IO Unit; getState : db → Bytes32 → IO (Option State); storeCheckpoint : db → Checkpoint → IO Unit; getLatestFinalized : db → IO (Option Checkpoint)`. | `Node/Storage/Schema.lean` | ~30 | X10-E1, X5 |
| X10-E3 | **Define API endpoint types.** `inductive APIEndpoint | getState (root : Bytes32) | getBlock (root : Bytes32) | getBlockBySlot (slot : Slot) | getForkChoice | getHealth | getCheckpoints | getValidators | getHead | getSyncStatus`. `structure APIResponse where status : Nat; contentType : String; body : ByteArray`. `handleRequest : ChainState → SyncState → APIEndpoint → APIResponse` — pure function returning response based on current state. | `Node/API/Endpoints.lean` | ~30 | X8, X10-B3 |
| X10-E4 | **Define top-level `Node` orchestrator.** `structure NodeConfig where chain : ChainConfig; validator : Option ValidatorRegistry; network : NetworkConfig; databasePath : String`. `structure NodeState where chain : ChainState; validator : Option ValidatorState; sync : SyncState; peers : PeerManager`. `inductive NodeEvent | tick (time : Uint64) | slotBoundary (slot : Slot) | blockReceived (block : SignedBlock) (peer : PeerId) | attestationReceived (att : Attestation) (peer : PeerId) | peerConnected (peer : PeerId) (enr : ENR) | peerDisconnected (peer : PeerId) | syncComplete | apiRequest (endpoint : APIEndpoint)`. `processEvent : NodeState → NodeEvent → Except NodeError (NodeState × List NetworkMessage)` — dispatch to appropriate service, collect outbound messages. `inductive NodeError | chainError (e : ChainError) | syncError (e : SyncError) | validatorError (e : ValidatorError) | networkError (e : NetworkError)`. | `Node/Node.lean` | ~50 | All X10-* |

### Group F: Tests (X10-F1 through X10-F4)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X10-F1 | **Slot clock test suite.** (1) Monotonicity: t₁ < t₂ implies slot₁ ≤ slot₂ across 10 timestamps. (2) Boundary: slotStartTime round-trips correctly. (3) Interval: currentInterval stays within bounds. (4) Genesis: currentSlot at genesisTime = 0. | `tests/NodeServiceSuite.lean` | ~20 | X10-A1 |
| X10-F2 | **Duty scheduling test suite.** (1) Proposer selection matches round-robin for slots 0-10. (2) All validators appear as attesters each slot. (3) Exactly one proposer per slot. (4) Proposer index < validator count. | `tests/NodeServiceSuite.lean` | ~20 | X10-C2 |
| X10-F3 | **Sync state machine test suite.** (1) Phase transition: idle → checkpoint → head → synced. (2) Block cache: insert + popReady ordering. (3) Backfill: runs in parallel with head sync. (4) Error: gap in block sequence detected. (5) Error: invalid checkpoint rejected. | `tests/NodeServiceSuite.lean` | ~20 | X10-D1 |
| X10-F4 | **Node orchestrator test suite.** (1) Tick event advances slot clock. (2) Block received triggers chain + sync update. (3) API request returns correct head. (4) Validator produces block on duty. (5) Peer management: add, score, ban. | `tests/NodeServiceSuite.lean` | ~20 | X10-E4 |

## 4. Exit Criteria

- [ ] All node services compile with deterministic state machines
- [ ] Slot clock monotonicity proved (5 properties)
- [ ] Chain service finalized-monotone proved
- [ ] Duty scheduling correctness proved (4 properties)
- [ ] Sync state machine covers all phases with valid transitions
- [ ] Block cache insert/pop correctness proved
- [ ] Node orchestrator handles all 8 event types
- [ ] Storage interface and schema defined
- [ ] API endpoints cover all 9 query types
- [ ] ≥ 20 test cases across 4 suites
- [ ] Zero sorry in node modules
