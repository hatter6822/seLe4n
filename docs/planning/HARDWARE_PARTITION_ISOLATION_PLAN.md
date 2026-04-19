# WS-W: Hardware Partition Isolation — ARM CCA + MPAM Integration Plan

**Status**: PLANNED
**Target versions**: v0.22.0–v0.22.9
**Hardware target**: Raspberry Pi 5 successor SoCs (BCM2712 successor with ARMv9-A)
**Prerequisite**: WS-U complete (v0.21.7), RPi5 hardware binding foundation
**Sub-task count**: 130 atomic units across 10 phases
**Axiom budget**: 1 (`realmMemoryIsolation` — hardware GPT guarantee)

## 1. Motivation

seLe4n's information flow model (`Projection.lean:305–337`) documents four
accepted covert channels beyond software-only mitigation:

| ID | Channel | Current Status | Target Status |
|----|---------|----------------|---------------|
| CC-1 | Scheduling state (`activeDomain`, `domainSchedule`, `domainTimeRemaining`) | Unconditionally visible (scheduling transparency) | **Narrowed**: cache amplification eliminated by MPAM; schedule visibility retained by design |
| CC-2 | Machine timer (`CNTVCT_EL0`) | Excluded from `ObservableState` but hardware-readable | **Closed**: per-domain virtual counter offset via `CNTVOFF_EL2` |
| CC-3 | TCB metadata (priority, IPC state) | Visible to thread-observable observers | **Narrowed**: preemption-pattern inference bounded by partition isolation |
| CC-4 | Object store metadata (cache-timing during allocator ops) | Cache side channel during cross-domain retype/delete | **Closed**: MPAM cache way partitioning isolates allocator cache footprint |

This plan extends the formal NI guarantee from **functional non-interference**
to **functional + microarchitectural non-interference** by integrating ARM
Confidential Compute Architecture (CCA) realm isolation and Memory Partitioning
and Monitoring (MPAM) cache/bandwidth partitioning, with the kernel proving
correct partition assignment.

## 2. Scope Boundary

**In scope:**
- Formal model of MPAM partition IDs, cache partition sets, and bandwidth groups
- Formal model of CCA realm boundaries and realm-domain correspondence
- Partition correctness theorem: `securityFlowsTo` label separation ⟹ hardware
  partition separation
- Extension of `PlatformBinding` with partition-aware contracts
- Extension of `ObservableState` with partition-aware projection strengthening
- Platform instantiation for BCM2712-successor (ARMv9-A + MPAM + RME)
- Simulation platform instantiation for test/validation without hardware

**Out of scope:**
- Bare-metal device driver implementation (deferred to WS-X)
- EL3 firmware / TF-A integration (trust anchor, not kernel responsibility)
- Spectre/Meltdown-class transient execution mitigations (orthogonal)
- Physical side channels (power, EM emanation)

## 3. Architecture Overview

```
┌───────────────────────────────────────────────────────────┐
│ Security Domain A                                         │
│ SecurityLabel { .high, .trusted }                         │
│ PartitionId 1 ──→ MPAM PARTID 1 ──→ Cache Ways {0..3}     │
│                                  ──→ BW Group 1 (40%)     │
│ RealmId 1 ──→ CCA Realm Descriptor ──→ GPA isolation      │
├───────────────────────────────────────────────────────────┤
│ Security Domain B                                         │
│ SecurityLabel { .low, .untrusted }                        │
│ PartitionId 2 ──→ MPAM PARTID 2 ──→ Cache Ways {4..7}     │
│                                  ──→ BW Group 2 (30%)     │
│ RealmId 2 ──→ CCA Realm Descriptor ──→ GPA isolation      │
├───────────────────────────────────────────────────────────┤
│ seLe4n Kernel (EL1 / Realm EL1)                           │
│  PartitionBoundaryContract:                               │
│  - partitionAssignment : DomainId → PartitionId           │
│  - partitionSeparation : ¬flowsTo ⟹ distinct partitions  │
│  - cacheWayDisjoint : distinct partitions ⟹ disjoint ways│
│  - cacheFlushOnSwitch : DomainId → DomainId → FlushSpec   │
├───────────────────────────────────────────────────────────┤
│ Hardware (ARMv9-A + MPAM + RME)                           │
│  MPAM MSC: cache way partitioning per PARTID              │
│  MPAM MBW: memory bandwidth allocation per PARTID         │
│  RME: realm granule protection, GPA isolation             │
│  CNTVOFF_EL2: per-realm virtual counter offset            │
└───────────────────────────────────────────────────────────┘
```

## 4. Phase Plan

### Phase W1: Foundation Types (v0.22.0)

Introduce core typed identifiers and structures for hardware partitioning.
Pure type definitions — no behavioral changes, no proof obligations.

**New file**: `SeLe4n/Kernel/HardwarePartition/Types.lean`

| ID | Ref | Description | Files | Est. |
|----|-----|-------------|-------|------|
| W1-A | CC-4 | **Define `PartitionId` typed wrapper.** Follow Prelude.lean pattern: `structure PartitionId where val : Nat deriving DecidableEq, Repr, Inhabited`. Add `Hashable` instance (`hash a := hash a.val`). Add namespace with `ofNat`, `toNat`, `ToString`, `isReserved` (val 0 sentinel), `valid` predicate. ~30 lines | `Types.lean` | Trivial |
| W1-B | CC-4 | **Define `MpamPartId` and `MpamPmg` typed wrappers.** `MpamPartId` represents the hardware PARTID field (ARM MPAM §5.1, 16-bit max). `MpamPmg` represents Performance Monitoring Group. Same pattern as W1-A. Add `MpamPartId.maxBits : Nat := 16` constant, `isValid (id : MpamPartId) : Bool := id.val < 2^maxBits`. ~40 lines | `Types.lean` | Trivial |
| W1-C | CC-4 | **Define `CacheWayMask` and `BandwidthPercent`.** `CacheWayMask` wraps a `Nat` bitmask where bit `i` means "cache way `i` is assigned to this partition". Add `CacheWayMask.wayCount : CacheWayMask → Nat` (popcount), `CacheWayMask.disjoint : CacheWayMask → CacheWayMask → Bool` (`a.val &&& b.val == 0`), `CacheWayMask.subset`, `CacheWayMask.union`. `BandwidthPercent` wraps a `Nat` in range 0–100; add `isValid : BandwidthPercent → Bool := (·.val ≤ 100)`. ~50 lines | `Types.lean` | Small |
| W1-D | CC-4 | **Define `MpamConfig` structure.** Records per-partition hardware configuration: `cacheWays : CacheWayMask`, `bandwidthLimit : BandwidthPercent`, `monitoringGroup : MpamPmg`. Derive `DecidableEq, Repr`. Add `MpamConfig.valid : MpamConfig → Bool` combining field validity predicates. ~20 lines | `Types.lean` | Trivial |
| W1-E | CC-4 | **Define `RealmId` and `RealmState`.** `RealmId` follows standard typed wrapper pattern. `RealmState` is an inductive: `.inactive`, `.active`, `.activating`, `.deactivating`, `.destroying`. Derive `DecidableEq, Repr` on both. ~25 lines | `Types.lean` | Trivial |
| W1-F | CC-4 | **Define `GranuleState` inductive.** Models ARM RME granule protection table entries: `.realm (rid : RealmId)`, `.nonSecure`, `.secure`, `.root`. Derive `DecidableEq, Repr`. This is the per-page ownership tag enforced by hardware at the interconnect level. ~15 lines | `Types.lean` | Trivial |
| W1-G | CC-1 | **Define `CacheFlushSpec` inductive.** Models microarchitectural cleanup on domain switch: `.none` (same partition, no flush needed), `.fullFlush` (flush all cache ways), `.wayFlush (ways : CacheWayMask)` (flush specific ways via `DC CISW`), `.asidFlush (asid : ASID)` (TLB flush only, cache shared). Derive `DecidableEq, Repr`. ~15 lines | `Types.lean` | Trivial |
| W1-H | CC-2 | **Define `TimerOffsetConfig`.** Structure wrapping `offsets : DomainId → Nat` (CNTVOFF_EL2 value per domain). Add `distinctOffsets : TimerOffsetConfig → DomainId → DomainId → Bool` predicate that checks two domains have different offsets. ~15 lines | `Types.lean` | Trivial |
| W1-I | — | **Define assignment map types.** `PartitionAssignment` as `structure PartitionAssignment where assign : DomainId → PartitionId`. `RealmAssignment` as `structure RealmAssignment where assign : DomainId → Option RealmId`. Both derive `DecidableEq`. Total functions ensure every domain has a deterministic mapping. ~15 lines | `Types.lean` | Trivial |
| W1-J | — | **Add BEq consistency lemmas.** Prove `PartitionId.beq_iff_eq`, `MpamPartId.beq_iff_eq`, `RealmId.beq_iff_eq` matching the `EquivBEq`/`LawfulBEq` pattern from Prelude.lean (WS-H14d). Required for RHTable compatibility if any of these types are used as keys. ~30 lines | `Types.lean` | Small |
| W1-K | — | **Create re-export hub.** Write `SeLe4n/Kernel/HardwarePartition.lean` as thin import-only file: `import SeLe4n.Kernel.HardwarePartition.Types`. This follows the re-export hub pattern used by `SeLe4n/Kernel/IPC/Operations.lean`, `SeLe4n/Kernel/Capability/Invariant.lean`, etc. ~5 lines | `HardwarePartition.lean` | Trivial |

**Intra-phase ordering constraints:**
- W1-A → W1-B (MpamPartId uses same pattern, but independent type)
- W1-A → W1-C (CacheWayMask referenced by MpamConfig)
- W1-B + W1-C → W1-D (MpamConfig bundles MpamPartId fields + CacheWayMask + BandwidthPercent)
- W1-E → W1-F (GranuleState references RealmId)
- W1-G and W1-H are independent of each other and of W1-E/F
- W1-I depends on W1-A (PartitionId) and W1-E (RealmId)
- W1-J depends on W1-A, W1-B, W1-E (all identifier types)
- W1-K depends on all of W1-A through W1-J
- **Parallel chains**: {W1-A→W1-B, W1-C}→W1-D and {W1-E→W1-F} and {W1-G} and {W1-H} are 4 independent chains

**Gate**: `lake build SeLe4n.Kernel.HardwarePartition.Types` and
`lake build SeLe4n.Kernel.HardwarePartition` succeed. Zero `sorry`/`axiom`.

---

### Phase W2: Partition Contract (v0.22.1)

Define the platform-level contract that binds security labels to hardware
partitions. Extends `PlatformBinding` with an optional partition contract.

**New file**: `SeLe4n/Kernel/HardwarePartition/Contract.lean`
**Modified file**: `SeLe4n/Platform/Contract.lean`

| ID | Ref | Description | Files | Est. |
|----|-----|-------------|-------|------|
| W2-A | CC-4 | **Define `PartitionBoundaryContract` data fields.** Create structure with 5 configuration fields: `partitionAssignment : PartitionAssignment`, `mpamConfig : PartitionId → MpamConfig`, `realmAssignment : RealmAssignment`, `cacheFlushOnSwitch : DomainId → DomainId → CacheFlushSpec`, `timerOffsetConfig : TimerOffsetConfig`. No proof fields yet — pure data. Derive `Repr`. ~20 lines | `Contract.lean` | Trivial |
| W2-B | CC-4 | **Add `partitionSeparation` proof field.** Extend `PartitionBoundaryContract` with: `partitionSeparation : ∀ (d₁ d₂ : DomainId), d₁ ≠ d₂ → ¬(policy.canFlow (domainOf d₁) (domainOf d₂)) → partitionAssignment.assign d₁ ≠ partitionAssignment.assign d₂`. This is the **core correctness obligation**: non-flowing domains must have distinct hardware partitions. Requires `DomainFlowPolicy` and a `domainOf` mapping as parameters. ~10 lines | `Contract.lean` | Small |
| W2-C | CC-4 | **Add `cacheWayDisjoint` proof field.** Extend `PartitionBoundaryContract` with: `cacheWayDisjoint : ∀ (p₁ p₂ : PartitionId), p₁ ≠ p₂ → CacheWayMask.disjoint (mpamConfig p₁).cacheWays (mpamConfig p₂).cacheWays = true`. Distinct partitions have non-overlapping cache way allocations. ~5 lines | `Contract.lean` | Trivial |
| W2-D | CC-4 | **Add `bandwidthBound` proof field.** Extend `PartitionBoundaryContract` with: `bandwidthBound : ∀ (ps : List PartitionId), (ps.map (fun p => (mpamConfig p).bandwidthLimit.val)).sum ≤ 100`. Total bandwidth across all active partitions must not exceed 100%. The `ps` parameter is the list of active partition IDs, supplied by the platform instantiator. ~5 lines | `Contract.lean` | Trivial |
| W2-E | CC-2 | **Add `timerOffsetDistinct` proof field.** Extend `PartitionBoundaryContract` with: `timerOffsetDistinct : ∀ (d₁ d₂ : DomainId), partitionAssignment.assign d₁ ≠ partitionAssignment.assign d₂ → timerOffsetConfig.offsets d₁ ≠ timerOffsetConfig.offsets d₂`. Domains in different partitions have distinct timer offsets (preventing cross-partition timer correlation). ~5 lines | `Contract.lean` | Trivial |
| W2-F | CC-1 | **Add `flushSpecCorrect` proof field.** Extend `PartitionBoundaryContract` with: `flushSpecCorrect : ∀ (d₁ d₂ : DomainId), partitionAssignment.assign d₁ ≠ partitionAssignment.assign d₂ → cacheFlushOnSwitch d₁ d₂ ≠ .none`. Cross-partition domain switches must specify a non-trivial cache flush. Same-partition switches may use `.none`. ~5 lines | `Contract.lean` | Trivial |
| W2-G | — | **Add Decidable instances to contract predicates.** For each proof field, add a corresponding `Decidable` field (matching the `RuntimeBoundaryContract` pattern which has `timerMonotonicDecidable`, etc.): `partitionSeparationDecidable`, `cacheWayDisjointDecidable`. This enables runtime `if` branching on contract predicates without manual instance threading. ~20 lines | `Contract.lean` | Small |
| W2-H | — | **Extend `PlatformBinding` with optional partition contract.** Add field `partitionContract : Option PartitionBoundaryContract := none` to the `PlatformBinding` class in `SeLe4n/Platform/Contract.lean`. The `:= none` default preserves backward compatibility — existing Sim, RPi5, and simulation instances compile unchanged without modification. ~5 lines | `SeLe4n/Platform/Contract.lean` | Trivial |
| W2-I | — | **Add `PlatformBinding.partition` accessor.** Following the existing `PlatformBinding.runtime`, `.boot`, `.interrupt`, `.config` accessor pattern, add `PlatformBinding.partition [PlatformBinding platform] : Option PartitionBoundaryContract`. ~5 lines | `SeLe4n/Platform/Contract.lean` | Trivial |
| W2-J | — | **Update re-export hub.** Add `import SeLe4n.Kernel.HardwarePartition.Contract` to `SeLe4n/Kernel/HardwarePartition.lean`. ~1 line | `HardwarePartition.lean` | Trivial |
| W2-K | — | **Verify backward compatibility.** Build all existing platform instances: `lake build SeLe4n.Platform.Sim.Contract`, `lake build SeLe4n.Platform.RPi5.Contract`. Both must compile without changes (the new `partitionContract` field defaults to `none`). This is a **verification-only** sub-task — no code changes. | — | Trivial |

**Intra-phase ordering constraints:**
- W2-A first (data fields before proof fields)
- W2-B, W2-C, W2-D, W2-E, W2-F are independent of each other (each adds one proof field)
- W2-B through W2-F all depend on W2-A
- W2-G depends on W2-B through W2-F (Decidable instances for all proof fields)
- W2-H depends on W2-A through W2-G (complete contract definition)
- W2-I depends on W2-H
- W2-J depends on W2-A (import availability)
- W2-K depends on W2-H and W2-I (must verify after PlatformBinding modification)

**Gate**: `lake build SeLe4n.Kernel.HardwarePartition.Contract`,
`lake build SeLe4n.Platform.Contract`,
`lake build SeLe4n.Platform.Sim.Contract`,
`lake build SeLe4n.Platform.RPi5.Contract`. Zero `sorry`/`axiom`.

---

### Phase W3: Partition Correctness Proofs (v0.22.2)

Prove that partition assignment correctly reflects the information flow policy.
The central formal contribution: hardware enforcement is sound with respect to
the NI model.

**New file**: `SeLe4n/Kernel/HardwarePartition/Correctness.lean`

| ID | Ref | Description | Files | Est. |
|----|-----|-------------|-------|------|
| W3-A | — | **Define `labelToDomain` bridge function.** Map the 2×2 `SecurityLabel` lattice into `SecurityDomain`: `publicLabel → domain 0`, `{low, trusted} → domain 1`, `{high, untrusted} → domain 2`, `kernelTrusted → domain 3`. Total function by case split on `Confidentiality × Integrity`. ~15 lines | `Correctness.lean` | Trivial |
| W3-B | — | **Prove `labelToDomain` roundtrip.** Prove `embedLegacyLabel_labelToDomain_roundtrip : ∀ l, embedLegacyLabel (labelToDomain ctx l) = l` (where `embedLegacyLabel` is the existing function in Policy.lean that maps 4 domains back to the 2×2 lattice). Proof by exhaustive case split on `l.confidentiality` and `l.integrity` (4 cases, each `rfl`). ~20 lines | `Correctness.lean` | Small |
| W3-C | — | **Define `domainOfObject` helper.** Given a `LabelingContext` and `PartitionBoundaryContract`, define `domainOfObject ctx oid : SecurityDomain := labelToDomain ctx (ctx.objectLabelOf oid)` and similarly `domainOfThread`, `partitionOfObject`, `partitionOfThread`. These compose the labeling context with the partition assignment. ~20 lines | `Correctness.lean` | Trivial |
| W3-D | CC-4 | **Prove `partitionCorrectness` (key lemma).** Statement: given `PartitionBoundaryContract` with `partitionSeparation`, if `securityFlowsTo l₁ l₂ = false ∧ securityFlowsTo l₂ l₁ = false` (mutual non-flow), then `partitionOfObject o₁ ≠ partitionOfObject o₂`. **Proof strategy**: by contrapositive. Assume `partitionOfObject o₁ = partitionOfObject o₂`. Then `partitionAssignment.assign d₁ = partitionAssignment.assign d₂`. By `partitionSeparation` contrapositive: either `d₁ = d₂` or `policy.canFlow d₁ d₂`. Case 1 (`d₁ = d₂`): same domain, so labels are related, contradicting mutual non-flow via `securityFlowsTo_refl`. Case 2: `canFlow d₁ d₂` maps back to `securityFlowsTo l₁ l₂ = true`, contradicting hypothesis. ~40 lines | `Correctness.lean` | Small |
| W3-E | CC-4 | **Prove `cacheIsolationCorollary`.** From W3-D + `cacheWayDisjoint` (W2-C): if two objects have mutually non-flowing labels, their cache way sets are disjoint. Statement: `mutualNonFlow l₁ l₂ → CacheWayMask.disjoint (cacheWaysOf o₁) (cacheWaysOf o₂) = true`. Proof: apply W3-D to get `p₁ ≠ p₂`, then apply `cacheWayDisjoint`. ~15 lines | `Correctness.lean` | Trivial |
| W3-F | CC-4 | **Prove `bandwidthIsolationCorollary`.** From W3-D + partition assignment: non-flowing objects map to distinct partitions with independent bandwidth groups. Statement: `mutualNonFlow l₁ l₂ → bandwidthGroupOf o₁ ≠ bandwidthGroupOf o₂`. Proof: apply W3-D, then unfold `bandwidthGroupOf` through `mpamConfig`. ~15 lines | `Correctness.lean` | Trivial |
| W3-G | — | **Prove `transitivityPreservation`.** If the `DomainFlowPolicy` is well-formed (reflexive + transitive, from `wellFormed` in Policy.lean), then partition assignment respects the transitive closure: `canFlow a b → canFlow b c → partitionOf a = partitionOf c → canFlow a c`. Proof: direct from `DomainFlowPolicy.isTransitive`. ~20 lines | `Correctness.lean` | Small |
| W3-H | — | **State `partitionAwareNonInterference` (forward declaration).** State the strengthened NI theorem: under a `PartitionBoundaryContract`, `partitionAwareLowEquivalent` (defined in W6-E) is preserved by all `NonInterferenceStep` constructors. The full proof requires W6 (projection strengthening). Mark with `sorry -- TPI-W3H: requires W6-F projection strengthening`. Register in `TRACKED_PROOF_ISSUES.md`. ~15 lines | `Correctness.lean` | Trivial |
| W3-I | — | **Prove `mutualNonFlow_decidable`.** `mutualNonFlow l₁ l₂` is `securityFlowsTo l₁ l₂ = false ∧ securityFlowsTo l₂ l₁ = false`. Provide a `Decidable` instance so it can be used in runtime branching. Proof: `instDecidableAnd` with `Bool.decEq`. ~10 lines | `Correctness.lean` | Trivial |
| W3-J | — | **Update re-export hub.** Add `import SeLe4n.Kernel.HardwarePartition.Correctness` to `HardwarePartition.lean`. ~1 line | `HardwarePartition.lean` | Trivial |

**Intra-phase ordering constraints:**
- W3-A first (bridge function needed by all subsequent tasks)
- W3-B depends on W3-A (roundtrip of `labelToDomain`)
- W3-C depends on W3-A (uses `labelToDomain`)
- W3-D depends on W3-A + W3-C (the key lemma using helpers)
- W3-E depends on W3-D (corollary)
- W3-F depends on W3-D (corollary)
- W3-G depends on W3-A (uses domain flow transitivity, independent of W3-D)
- W3-H depends on W3-D (references the correctness result, but proof is sorry)
- W3-I is independent (decidability instance for mutual non-flow)
- W3-J depends on all others
- **Parallel**: W3-E, W3-F, W3-G, W3-H, W3-I are all independent after W3-D

**Gate**: `lake build SeLe4n.Kernel.HardwarePartition.Correctness`. Exactly one
tracked `sorry` (W3-H). Zero `axiom`.

---

### Phase W4: CCA Realm Model (v0.22.3)

Model ARM Confidential Compute Architecture realm isolation. The RMM's
guarantees are modeled as one hardware axiom; the kernel's obligation to
configure the GPT correctly is a provable property.

**New file**: `SeLe4n/Kernel/HardwarePartition/Realm.lean`

| ID | Ref | Description | Files | Est. |
|----|-----|-------------|-------|------|
| W4-A | CC-4 | **Define `GranuleProtectionTable` type.** Define `GranuleProtectionTable` as `PAddr → GranuleState` (total function — every physical address has a granule state). Add `GranuleProtectionTable.default : GranuleProtectionTable := fun _ => .nonSecure` (all pages start non-secure before realm assignment). ~10 lines | `Realm.lean` | Trivial |
| W4-B | CC-4 | **Define `realmMemoryIsolation` axiom.** `axiom realmMemoryIsolation (gpt : GranuleProtectionTable) : ∀ (r₁ r₂ : RealmId) (pa : PAddr), r₁ ≠ r₂ → gpt pa = .realm r₁ → gpt pa ≠ .realm r₂`. A physical address cannot belong to two distinct realms simultaneously. This is a **hardware guarantee** enforced by the ARM RME granule protection check unit at the interconnect — the kernel cannot verify this. Documented in ARM DDI0487 §D8. This is the plan's sole axiom. ~10 lines | `Realm.lean` | Trivial |
| W4-C | CC-4 | **Define `domainOwnsPage` predicate.** `domainOwnsPage (ctx : LabelingContext) (d : DomainId) (pa : PAddr) : Prop`. When `ctx.memoryOwnership = some mdo`, checks `mdo.regionOwner pa = some d`. When `none`, vacuously false (no ownership model configured). This reuses the existing `MemoryDomainOwnership` from Policy.lean. ~15 lines | `Realm.lean` | Trivial |
| W4-D | CC-4 | **Define `realmDomainConsistent` proof obligation.** `realmDomainConsistent (contract : PartitionBoundaryContract) (ctx : LabelingContext) (gpt : GranuleProtectionTable) : Prop := ∀ (d : DomainId) (rid : RealmId), contract.realmAssignment.assign d = some rid → ∀ (pa : PAddr), domainOwnsPage ctx d pa → gpt pa = .realm rid`. The kernel must ensure that every page owned by a domain-with-realm is in that realm's GPT entry. This is a proof obligation on the kernel, not an axiom. ~15 lines | `Realm.lean` | Small |
| W4-E | CC-4 | **Define `realmCreate` transition.** `realmCreate (rid : RealmId) (pages : List PAddr) (gpt : GranuleProtectionTable) : GranuleProtectionTable`. Assigns each page in `pages` to `.realm rid`. Implemented as `pages.foldl (fun g pa => fun addr => if addr == pa then .realm rid else g addr) gpt`. ~15 lines | `Realm.lean` | Small |
| W4-F | CC-4 | **Prove `realmCreate_preserves_other_realms`.** Statement: `∀ pa, gpt pa = .realm r₂ → r₂ ≠ rid → pa ∉ pages → realmCreate rid pages gpt pa = .realm r₂`. Creating a new realm does not reassign pages belonging to other realms (provided those pages are not in the creation page list). Proof by induction on `pages`, using `if` branch elimination at each fold step. ~30 lines | `Realm.lean` | Small |
| W4-G | CC-4 | **Define `realmDestroy` transition.** `realmDestroy (rid : RealmId) (gpt : GranuleProtectionTable) : GranuleProtectionTable := fun pa => if gpt pa = .realm rid then .nonSecure else gpt pa`. Releases all pages belonging to the destroyed realm back to `.nonSecure`. ~10 lines | `Realm.lean` | Trivial |
| W4-H | CC-4 | **Prove `realmDestroy_preserves_other_realms`.** Statement: `∀ pa, gpt pa = .realm r₂ → r₂ ≠ rid → realmDestroy rid gpt pa = .realm r₂`. Destroying one realm does not affect pages belonging to other realms. Proof by unfolding `realmDestroy` and using `r₂ ≠ rid` to show the `if` takes the `else` branch. ~15 lines | `Realm.lean` | Trivial |
| W4-I | CC-4 | **Prove `realmPartitionBridge`.** Statement: if `realmAssignment d₁ = some r₁` and `realmAssignment d₂ = some r₂` and `r₁ ≠ r₂`, then for all `pa`, `domainOwnsPage d₁ pa → ¬domainOwnsPage d₂ pa`. Combined with `realmMemoryIsolation` (W4-B) and `realmDomainConsistent` (W4-D): `d₁`'s pages are in realm `r₁`, `d₂`'s would be in realm `r₂`, but a page can't be in both (axiom), so they're disjoint. **Proof strategy**: assume both `domainOwnsPage d₁ pa` and `domainOwnsPage d₂ pa`. By `realmDomainConsistent`, `gpt pa = .realm r₁` and `gpt pa = .realm r₂`. Then `r₁ = r₂` by function determinism, contradicting `r₁ ≠ r₂`. ~25 lines | `Realm.lean` | Small |
| W4-J | — | **Define `trivialRealmAssignment`.** `trivialRealmAssignment : RealmAssignment := ⟨fun _ => none⟩`. For platforms without CCA (including current RPi5). All realm proof obligations (`realmDomainConsistent`) become vacuously true because the `some rid` hypothesis in the ∀ is never satisfied. Prove `trivialRealmConsistent : realmDomainConsistent trivialContract ctx gpt` where `trivialContract.realmAssignment = trivialRealmAssignment`. Proof: intro, `simp [trivialRealmAssignment]` discharges the `some rid` case. ~10 lines | `Realm.lean` | Trivial |
| W4-K | — | **Update re-export hub.** Add `import SeLe4n.Kernel.HardwarePartition.Realm` to `HardwarePartition.lean`. ~1 line | `HardwarePartition.lean` | Trivial |

**Intra-phase ordering constraints:**
- W4-A first (GPT type used by everything)
- W4-B depends on W4-A (axiom about GPT)
- W4-C is independent (uses only LabelingContext)
- W4-D depends on W4-A + W4-C (references GPT + domainOwnsPage)
- W4-E depends on W4-A (transition over GPT)
- W4-F depends on W4-E (preservation proof for create)
- W4-G depends on W4-A (transition over GPT)
- W4-H depends on W4-G (preservation proof for destroy)
- W4-I depends on W4-B + W4-D (bridge uses axiom + consistency)
- W4-J is independent after W4-A (trivial assignment)
- **Parallel chains**: {W4-E→W4-F} and {W4-G→W4-H} are independent; W4-I depends on both chain outputs conceptually but only on W4-B + W4-D directly

**Gate**: `lake build SeLe4n.Kernel.HardwarePartition.Realm`. Zero `sorry`.
Exactly one `axiom` (`realmMemoryIsolation`). Axiom documented in
`CLAIM_EVIDENCE_INDEX.md` with ARM DDI0487 §D8 reference.

---

### Phase W5: Timer Isolation Model (v0.22.4)

Close the machine timer covert channel (CC-2) by modeling ARM's virtual counter
offset mechanism. Currently `st.machine.timer` is excluded from
`ObservableState` (Projection.lean:323–326). This phase models the hardware
mechanism that makes that exclusion physically enforceable.

**New file**: `SeLe4n/Kernel/HardwarePartition/TimerIsolation.lean`
**Modified file**: `SeLe4n/Kernel/Architecture/Assumptions.lean`

| ID | Ref | Description | Files | Est. |
|----|-----|-------------|-------|------|
| W5-A | CC-2 | **Define `VirtualCounter` structure.** Fields: `physicalCount : Nat` (hardware `CNTPCT_EL0`), `offset : Nat` (per-domain `CNTVOFF_EL2`). Add computed field `virtualCount : Nat := if physicalCount ≥ offset then physicalCount - offset else 0` (saturating subtraction, matching ARM spec). ~15 lines | `TimerIsolation.lean` | Trivial |
| W5-B | CC-2 | **Define `projectDomainTimer`.** `projectDomainTimer (config : TimerOffsetConfig) (d : DomainId) (physicalCount : Nat) : Nat := VirtualCounter.mk physicalCount (config.offsets d) |>.virtualCount`. Computes the domain-local virtual counter from the physical counter and the domain's offset. ~10 lines | `TimerIsolation.lean` | Trivial |
| W5-C | CC-2 | **Prove `timerIncrement_uniform`.** Statement: `∀ d Δ, projectDomainTimer config d (phys + Δ) = projectDomainTimer config d phys + Δ` (when `phys ≥ config.offsets d`, which holds in steady state). Incrementing the physical counter by `Δ` increments every domain's virtual counter by the same `Δ`. Proof by unfolding `projectDomainTimer` and `VirtualCounter.virtualCount`, then `omega`. ~15 lines | `TimerIsolation.lean` | Small |
| W5-D | CC-2 | **Prove `timerNonInterference`.** Statement: given `config.offsets d₁ ≠ config.offsets d₂`, the absolute values `projectDomainTimer config d₁ phys` and `projectDomainTimer config d₂ phys` differ by a constant (`config.offsets d₂ - config.offsets d₁`) regardless of `phys`. Therefore, observing one virtual counter reveals no information about the other domain's execution pattern beyond the public offset difference. Proof: unfold both, subtract, show the difference is independent of `phys`. ~20 lines | `TimerIsolation.lean` | Small |
| W5-E | CC-2 | **Prove `timerOffsetSeparation`.** Statement: given a `PartitionBoundaryContract` with `timerOffsetDistinct` (W2-E), non-flowing domains (via `partitionCorrectness` from W3-D) have distinct timer offsets. Proof: chain W3-D (mutual non-flow → distinct partitions) with `timerOffsetDistinct` (distinct partitions → distinct offsets). ~15 lines | `TimerIsolation.lean` | Trivial |
| W5-F | CC-2 | **Define `domainSwitchTimerUpdate`.** `domainSwitchTimerUpdate (config : TimerOffsetConfig) (oldDomain newDomain : DomainId) (ms : MachineState) : MachineState`. Models what happens on domain switch: the physical counter is unchanged, but the visible timer value becomes `projectDomainTimer config newDomain ms.timer`. In the abstract model, this is a no-op on `MachineState` (the offset is conceptual — the hardware applies it transparently). Return `ms` unchanged. ~10 lines | `TimerIsolation.lean` | Trivial |
| W5-G | CC-2 | **Prove `domainSwitchTimerUpdate_preserves_machineWordBounded`.** Statement: `machineWordBounded ms → machineWordBounded (domainSwitchTimerUpdate config old new ms)`. Since W5-F returns `ms` unchanged, proof is `id`. ~5 lines | `TimerIsolation.lean` | Trivial |
| W5-H | — | **Extend `RuntimeBoundaryContract` with optional timer isolation.** Add field `timerIsolation : Option TimerOffsetConfig := none` to `RuntimeBoundaryContract` in `Assumptions.lean`. When `some config`, the `timerMonotonic` predicate is understood to hold for virtual counters per-domain (documentation-level strengthening; the `Prop` signature is unchanged — monotonicity of `phys + offset` follows from monotonicity of `phys`). The `:= none` default preserves backward compatibility. ~5 lines | `SeLe4n/Kernel/Architecture/Assumptions.lean` | Trivial |
| W5-I | — | **Verify backward compatibility.** Build all existing platform contracts that reference `RuntimeBoundaryContract`: `lake build SeLe4n.Platform.RPi5.RuntimeContract`, `lake build SeLe4n.Platform.Sim.RuntimeContract`. Both must compile without changes. Verification-only — no code changes. | — | Trivial |
| W5-J | — | **Update re-export hub.** Add `import SeLe4n.Kernel.HardwarePartition.TimerIsolation` to `HardwarePartition.lean`. ~1 line | `HardwarePartition.lean` | Trivial |

**Intra-phase ordering constraints:**
- W5-A → W5-B (VirtualCounter used by projectDomainTimer)
- W5-B → W5-C → W5-D (projection function → uniform increment → NI)
- W5-B → W5-E (uses projectDomainTimer indirectly via W3-D chain)
- W5-F → W5-G (function → preservation proof)
- W5-F is independent of W5-C/D/E (domain switch update is separate from NI proofs)
- W5-H is independent of W5-A through W5-G (modifies a different file)
- W5-I depends on W5-H
- **Parallel chains**: {W5-A→W5-B→W5-C→W5-D, W5-E} and {W5-F→W5-G} and {W5-H→W5-I}

**Gate**: `lake build SeLe4n.Kernel.HardwarePartition.TimerIsolation`,
`lake build SeLe4n.Kernel.Architecture.Assumptions`. Zero `sorry`/`axiom`.

---

### Phase W6: Projection Strengthening (v0.22.5)

The central model-level change: extend `ObservableState` and `projectState` to
account for hardware partition boundaries, and close the W3-H sorry. This is the
highest-risk phase because it modifies the core information flow infrastructure.

**Modified files**: `SeLe4n/Kernel/InformationFlow/Projection.lean`,
`SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean`,
`SeLe4n/Kernel/HardwarePartition/Correctness.lean`

| ID | Ref | Description | Files | Est. |
|----|-----|-------------|-------|------|
| W6-A | CC-4 | **Add partition fields to `ObservableState`.** Add two `Option`-wrapped fields: `partitionId : Option PartitionId := none` (observer's own partition), `cachePartition : Option CacheWayMask := none` (observer's cache allocation). The `:= none` defaults ensure that all existing code constructing `ObservableState` compiles unchanged — they just get `none` for the new fields. ~5 lines added to structure | `Projection.lean` | Trivial |
| W6-B | — | **Define `partitionObservable` gate.** `partitionObservable (contract : Option PartitionBoundaryContract) (observer : IfObserver) (ctx : LabelingContext) (oid : ObjId) : Bool`. When `contract = none`, returns `true` (no partition filtering). When `some c`, returns `true` only if the object's domain maps to the same partition as the observer's domain. This is the partition-aware strengthening of the observability gate. ~15 lines | `Projection.lean` | Small |
| W6-C | CC-4 | **Strengthen `projectObjects` with partition gate.** Modify `projectObjects` to apply both `objectObservable` (label-based) AND `partitionObservable` (partition-based). An object is projected only if both gates pass. When `partitionContract = none`, `partitionObservable` returns `true` and the existing behavior is preserved. Modify: change `if objectObservable ctx observer oid then ...` to `if objectObservable ctx observer oid && partitionObservable contract observer ctx oid then ...`. ~5 lines changed | `Projection.lean` | Small |
| W6-D | CC-4 | **Strengthen `projectMemory` with partition gate.** Add partition filtering to `projectMemory`: when `contract = some c`, a memory address is observable only if its owning domain (via `ctx.memoryOwnership`) maps to the same partition as the observer. When `contract = none` or `memoryOwnership = none`, existing behavior preserved. ~10 lines changed | `Projection.lean` | Small |
| W6-E | CC-4 | **Strengthen `projectIrqHandlers` with partition gate.** IRQ handler targets are filtered by both label observability and partition observability. When `contract = none`, existing behavior preserved. ~5 lines changed | `Projection.lean` | Trivial |
| W6-F | CC-4 | **Strengthen `projectObjectIndex` with partition gate.** Object index entries filtered by `objectObservable && partitionObservable`. When `contract = none`, existing behavior preserved. ~3 lines changed | `Projection.lean` | Trivial |
| W6-G | — | **Thread `contract` parameter through `projectState`.** Add `(contract : Option PartitionBoundaryContract := none)` parameter to `projectState`. Pass it to `projectObjects`, `projectMemory`, `projectIrqHandlers`, `projectObjectIndex`. Fill in `partitionId` and `cachePartition` fields of the result from `contract`. When `none`, all partition fields are `none` and all sub-projections behave as before. ~15 lines changed | `Projection.lean` | Small |
| W6-H | — | **Prove `projectState_partition_none_eq` (backward compatibility).** Statement: `projectState none ctx observer st = projectState_original ctx observer st` (where `projectState_original` is the pre-W6 definition, or equivalently, `projectState none` computes the same result as the old function). **Proof strategy**: unfold `projectState`, show each sub-projection with `contract = none` matches the original via `simp [partitionObservable]` (the `none` branch returns `true`, so the `&&` collapses). This is the **critical safety theorem** — if it fails, all existing NI proofs break. ~40 lines | `Projection.lean` | Medium |
| W6-I | — | **Update `projectStateFast` to match.** Thread the same `contract` parameter through `projectStateFast` (the precomputed-observable-set variant). Update `projectObjectsFast` and `projectIrqHandlersFast` to accept and apply the partition gate. Prove `projectStateFast_eq` still holds (the fast path agrees with the slow path including partition filtering). ~30 lines | `Projection.lean` | Small |
| W6-J | — | **Define `partitionAwareLowEquivalent`.** `partitionAwareLowEquivalent (contract : PartitionBoundaryContract) (ctx : LabelingContext) (observer : IfObserver) (s₁ s₂ : SystemState) : Prop := projectState (some contract) ctx observer s₁ = projectState (some contract) ctx observer s₂`. This is strictly stronger than `lowEquivalent` (which uses `projectState none`). ~5 lines | `Projection.lean` | Trivial |
| W6-K | — | **Prove `partitionAwareLowEquivalent_implies_lowEquivalent`.** Statement: `partitionAwareLowEquivalent contract ctx observer s₁ s₂ → lowEquivalent ctx observer s₁ s₂`. **Proof strategy**: `partitionAwareLowEquivalent` means `projectState (some c)` agrees. Since `partitionObservable (some c)` is a *strengthening* (filters more), agreement on the strengthened projection implies agreement on the original. Formally: if the partition-filtered projection is equal, then applying the weaker filter (which makes more things visible) cannot introduce inequality because both states have the same underlying objects — the weaker filter just reveals more of what's already equal. This requires a monotonicity lemma: `partitionObservable (some c) oid = true → objectObservable ctx observer oid = true → ∃ the projected objects agree`. ~30 lines | `Projection.lean` | Medium |
| W6-L | — | **Close W3-H sorry: prove `partitionAwareNonInterference`.** Complete the proof in `Correctness.lean`. Under a `PartitionBoundaryContract`, `partitionAwareLowEquivalent` is preserved by all `NonInterferenceStep` constructors. **Proof strategy**: for each constructor, the existing per-operation NI proof already shows the operation's state changes are localized to non-observable targets (via `hEndpointHigh`, `hSenderHigh`, etc.). With partition-aware projection, these targets are *even more* filtered (by partition in addition to label). Since the existing proof shows the change is invisible under the weaker filter, it is a fortiori invisible under the stronger filter. Formally: compose each existing `_preserves_lowEquivalent` theorem with `partitionAwareLowEquivalent_implies_lowEquivalent` (W6-K). ~40 lines | `Correctness.lean` | Medium |
| W6-M | CC-1 | **Update covert channel documentation (scheduling).** Add structured doc comment to `projectActiveDomain` explaining that under hardware partitioning, while scheduling state is still visible (scheduling transparency is by design), the cache-timing amplification vector is eliminated: an observer in partition A cannot infer partition B's memory access patterns from cache pressure because MPAM isolates the cache ways. ~15 lines (doc comment only) | `Projection.lean` | Trivial |
| W6-N | — | **Update `computeObservableSet` to include partition gate.** The precomputed hash set (WS-G9) must also filter by `partitionObservable` when a contract is active. Thread `contract` parameter. Prove `foldl_observable_set_mem` still holds with the strengthened filter. ~20 lines | `Projection.lean` | Small |

**Intra-phase ordering constraints:**
- W6-A first (structure fields must exist before any projection function changes)
- W6-B depends on W6-A (uses new fields conceptually; references contract type)
- W6-C, W6-D, W6-E, W6-F are independent of each other (each modifies a different sub-projection)
- W6-C through W6-F all depend on W6-B (use `partitionObservable`)
- W6-G depends on W6-C through W6-F (threads parameter through to all sub-projections)
- W6-H depends on W6-G (backward compatibility proof over the threaded `projectState`)
- W6-I depends on W6-G (fast-path variant mirrors slow path)
- W6-J depends on W6-G (uses `projectState` with `some contract`)
- W6-K depends on W6-J + W6-H (strengthened equiv implies original equiv)
- W6-L depends on W6-K (uses `partitionAwareLowEquivalent_implies_lowEquivalent`)
- W6-M is independent (doc comment only)
- W6-N depends on W6-B (uses `partitionObservable`)
- **Critical path**: W6-A → W6-B → W6-C → W6-G → W6-H → W6-K → W6-L

**Gate**: `lake build SeLe4n.Kernel.InformationFlow.Projection`,
`lake build SeLe4n.Kernel.HardwarePartition.Correctness`,
`./scripts/test_full.sh`. Zero `sorry`/`axiom` (W3-H sorry is now closed).

---

### Phase W7: Platform Instantiation — Simulation (v0.22.6)

Instantiate the partition contract for the simulation platform. Enables
validation and test coverage without hardware. Follows the existing
Sim/RPi5 dual-instantiation pattern.

**New file**: `SeLe4n/Platform/Sim/PartitionContract.lean`
**Modified file**: `SeLe4n/Platform/Sim/Contract.lean`

| ID | Ref | Description | Files | Est. |
|----|-----|-------------|-------|------|
| W7-A | — | **Define `simPartitionAssignment`.** Map 4 domains to 4 partitions: `fun d => PartitionId.ofNat (d.val % 4)`. Domain 0 → partition 0, domain 1 → partition 1, domain 2 → partition 2, domain 3 → partition 3. Modular wrapping for domains ≥ 4 (matching the 4-element security label lattice). ~10 lines | `PartitionContract.lean` | Trivial |
| W7-B | — | **Define `simMpamConfig`.** 4 partitions, each with 4 simulated cache ways (16-way simulated cache): partition 0 gets `CacheWayMask.ofNat 0x000F` (ways 0–3), partition 1 gets `0x00F0` (ways 4–7), partition 2 gets `0x0F00` (ways 8–11), partition 3 gets `0xF000` (ways 12–15). Each gets `BandwidthPercent.ofNat 25`. ~20 lines | `PartitionContract.lean` | Small |
| W7-C | — | **Define `simRealmAssignment`.** `simRealmAssignment : RealmAssignment := ⟨fun _ => none⟩`. Simulation platform has no CCA — all realm obligations are vacuous. ~5 lines | `PartitionContract.lean` | Trivial |
| W7-D | — | **Define `simTimerOffsetConfig`.** `simTimerOffsetConfig : TimerOffsetConfig := ⟨fun d => d.val * 1_000_000⟩`. Domain 0 offset 0, domain 1 offset 1M, domain 2 offset 2M, domain 3 offset 3M. Distinct offsets for distinct domains. ~5 lines | `PartitionContract.lean` | Trivial |
| W7-E | — | **Define `simCacheFlushOnSwitch`.** `fun d₁ d₂ => if simPartitionAssignment.assign d₁ == simPartitionAssignment.assign d₂ then .none else .wayFlush ((simMpamConfig (simPartitionAssignment.assign d₁)).cacheWays)`. Same-partition switch: no flush. Cross-partition switch: flush outgoing partition's ways. ~10 lines | `PartitionContract.lean` | Trivial |
| W7-F | — | **Prove `simPartitionSeparation`.** Concrete proof over the 4-element lattice. Statement: `∀ d₁ d₂, d₁ ≠ d₂ → ¬(simPolicy.canFlow (simDomainOf d₁) (simDomainOf d₂)) → simPartitionAssignment.assign d₁ ≠ simPartitionAssignment.assign d₂`. Proof by exhaustive case analysis on `d₁.val % 4` and `d₂.val % 4` — each pair either flows (contradicting hypothesis) or has distinct partition assignments (satisfying conclusion). Use `decide` or `omega`. ~25 lines | `PartitionContract.lean` | Small |
| W7-G | — | **Prove `simCacheWayDisjoint`.** Statement: `∀ p₁ p₂, p₁ ≠ p₂ → CacheWayMask.disjoint (simMpamConfig p₁).cacheWays (simMpamConfig p₂).cacheWays = true`. Direct computation: `0x000F &&& 0x00F0 = 0`, etc. for all 6 pairs. Proof by case analysis on `p₁.val % 4` and `p₂.val % 4`, then `native_decide` on each case. ~20 lines | `PartitionContract.lean` | Small |
| W7-H | — | **Prove `simBandwidthBound`.** Statement: total bandwidth across 4 partitions is `4 × 25 = 100 ≤ 100`. Direct computation proof. ~10 lines | `PartitionContract.lean` | Trivial |
| W7-I | — | **Prove `simTimerOffsetDistinct`.** Statement: `∀ d₁ d₂, simPartitionAssignment.assign d₁ ≠ simPartitionAssignment.assign d₂ → simTimerOffsetConfig.offsets d₁ ≠ simTimerOffsetConfig.offsets d₂`. Proof: distinct partitions mean distinct domain groups (mod 4), so `d₁.val * 1_000_000 ≠ d₂.val * 1_000_000`. By `omega`. ~15 lines | `PartitionContract.lean` | Small |
| W7-J | — | **Prove `simFlushSpecCorrect`.** Statement: cross-partition switches have non-none flush specs. Proof: unfold `simCacheFlushOnSwitch`, the `else` branch returns `.wayFlush ...` which is `≠ .none`. ~10 lines | `PartitionContract.lean` | Trivial |
| W7-K | — | **Assemble `simPartitionBoundaryContract`.** Bundle W7-A through W7-J into the `PartitionBoundaryContract` structure, providing all data fields and proof fields. ~15 lines | `PartitionContract.lean` | Trivial |
| W7-L | — | **Wire into `simPlatformBinding`.** Modify `SeLe4n/Platform/Sim/Contract.lean`: set `partitionContract := some simPartitionBoundaryContract` in `simPlatformBinding` and `simRestrictivePlatformBinding`. Existing `runtimeContract`, `bootContract`, `interruptContract` fields unchanged. ~5 lines | `Contract.lean` | Trivial |

**Intra-phase ordering constraints:**
- W7-A, W7-B, W7-C, W7-D, W7-E are independent data definitions (can run in parallel)
- W7-F depends on W7-A (partition assignment used in proof)
- W7-G depends on W7-B (MPAM config used in proof)
- W7-H depends on W7-B (bandwidth sum)
- W7-I depends on W7-A + W7-D (partition assignment + timer config)
- W7-J depends on W7-A + W7-E (partition assignment + flush spec)
- W7-K depends on W7-F through W7-J (all proofs assembled)
- W7-L depends on W7-K

**Gate**: `lake build SeLe4n.Platform.Sim.PartitionContract`,
`lake build SeLe4n.Platform.Sim.Contract`,
`./scripts/test_smoke.sh`. Zero `sorry`/`axiom`.

---

### Phase W8: Platform Instantiation — ARMv9 Hardware (v0.22.7)

Concrete hardware contract for a BCM2712-successor SoC with ARMv9-A, MPAM, and
RME. This is the production-path instantiation. The ARMv9 platform is separate
from RPi5 — the current RPi5 (BCM2712, Cortex-A76, ARMv8.2) lacks MPAM/RME.

**New files**: `SeLe4n/Platform/ARMv9/Board.lean`,
`SeLe4n/Platform/ARMv9/PartitionContract.lean`,
`SeLe4n/Platform/ARMv9/RealmContract.lean`,
`SeLe4n/Platform/ARMv9/RuntimeContract.lean`,
`SeLe4n/Platform/ARMv9/BootContract.lean`,
`SeLe4n/Platform/ARMv9/Contract.lean`

| ID | Ref | Description | Files | Est. |
|----|-----|-------------|-------|------|
| W8-A | — | **Define ARMv9 SoC address constants.** MPAM MSC base address (implementation-defined; use placeholder `0x2000_0000` with `-- TODO: update from datasheet` comment). MPAM register offsets: `MPAMCFG_PART_SEL` (0x0100), `MPAMCFG_CPBM` (0x1000), `MPAMCFG_MBW_MAX` (0x0208), `MPAMCFG_MBW_PBM` (0x2000). GPT base address placeholder. Timer frequency (assume same 54 MHz crystal). ~30 lines | `Board.lean` | Small |
| W8-B | — | **Define ARMv9 memory map.** Extend RPi5 memory map pattern with MPAM MSC MMIO region and GPT control region. 8 GB RAM model (successor likely ships 8+ GB). Prove `armv9MemoryMap_wellFormed` (non-overlap) via `native_decide`. ~40 lines | `Board.lean` | Small |
| W8-C | — | **Define ARMv9 `MachineConfig`.** Extend existing `MachineConfig` pattern: `registerWidth := 64`, `virtualAddressWidth := 48`, `physicalAddressWidth := 48` (ARMv9 supports up to 52-bit, but 48 is standard), `pageSize := 4096`, `maxASID := 65536`, `memoryMap := armv9MemoryMap`, `registerCount := 32`. Prove `armv9MachineConfig_wellFormed` via `native_decide`. ~25 lines | `Board.lean` | Small |
| W8-D | — | **Define MPAM register types.** `MpamCpbm` (cache portion bitmap — `Nat` bitmask, same representation as `CacheWayMask`). `MpamMbwMax` (bandwidth maximum — 16-bit unsigned, percentage × 100 for finer granularity). `MpamPartSel` (partition selector — writes to this register select which PARTID's config is being modified). All derive `DecidableEq, Repr`. ~20 lines | `PartitionContract.lean` | Trivial |
| W8-E | — | **Define `configureMpamPartition` MMIO operation.** `configureMpamPartition (pid : PartitionId) (config : MpamConfig) : MmioAdapter Unit`. **Sub-steps**: (1) Write `pid.val` to `MPAMCFG_PART_SEL` via `mmioWrite32`, (2) write `config.cacheWays.val` to `MPAMCFG_CPBM` via `mmioWrite32`, (3) write `config.bandwidthLimit.val` to `MPAMCFG_MBW_MAX` via `mmioWrite32`. Uses existing `mmioWrite32` infrastructure from `RPi5/MmioAdapter.lean`. ~25 lines | `PartitionContract.lean` | Small |
| W8-F | — | **Prove `configureMpamPartition_frame`.** The MMIO writes only touch MPAM MSC addresses (not RAM, not GIC, not UART). Statement: `∀ addr, ¬inMpamMscRegion addr → configureMpamPartition pid config st |>.machine.memory addr = st.machine.memory addr`. Proof: unfold the 3 `mmioWrite32` calls, show each only modifies addresses within the MSC region. ~25 lines | `PartitionContract.lean` | Small |
| W8-G | — | **Define `armv9PartitionAssignment`.** Parameterized by `GenericLabelingContext` (supporting ≥3 domains via `DomainFlowPolicy`). Maps each domain to a distinct PARTID: `fun d => MpamPartId.ofNat (d.val % maxPartitions)` where `maxPartitions` is the hardware PARTID space (≥16 for ARMv9). ~10 lines | `PartitionContract.lean` | Trivial |
| W8-H | — | **Define `armv9MpamConfig`.** Maps each PARTID to a concrete MPAM configuration. For a 16-way L2 cache with `maxPartitions` partitions, divide ways equally: partition `p` gets `CacheWayMask.ofNat ((2^waysPerPartition - 1) <<< (p.val * waysPerPartition))`. Bandwidth divided equally: `100 / maxPartitions` per partition. ~20 lines | `PartitionContract.lean` | Small |
| W8-I | — | **Prove `armv9PartitionSeparation`.** Parameterized proof: given a well-formed `DomainFlowPolicy` and a `GenericLabelingContext`, non-flowing domains get distinct PARTIDs. Proof structure: similar to W7-F but general — uses `DomainFlowPolicy.wellFormed` (reflexivity + transitivity) rather than exhaustive case analysis. For the general case, delegates to `partitionSeparation` field obligation which the platform operator must satisfy at deployment time. ~30 lines | `PartitionContract.lean` | Medium |
| W8-J | — | **Prove `armv9CacheWayDisjoint`.** For the equal-division scheme in W8-H, distinct partitions have non-overlapping bitmasks. Proof: bit-shift arithmetic — if `p₁ ≠ p₂`, then `(mask <<< (p₁ * w)) &&& (mask <<< (p₂ * w)) = 0` when `w` divides the total way count evenly. ~25 lines | `PartitionContract.lean` | Small |
| W8-K | — | **Define ARMv9 realm configuration.** `armv9RealmAssignment : RealmAssignment`. Each domain maps to `some (RealmId.ofNat d.val)` when CCA is active, `none` otherwise. Add `armv9ConfigureRealm : RealmId → List PAddr → GranuleProtectionTable → GranuleProtectionTable` using the `realmCreate` function from W4-E. ~15 lines | `RealmContract.lean` | Small |
| W8-L | — | **Prove `armv9RealmConsistency`.** Instance of `realmDomainConsistent` (W4-D) for the ARMv9 platform. Statement: pages owned by a domain are in that domain's realm. This is an obligation on the boot sequence — the kernel must configure the GPT correctly at boot. For the abstract model, prove under the hypothesis that the boot sequence calls `realmCreate` for each domain's pages. ~20 lines | `RealmContract.lean` | Small |
| W8-M | — | **Define ARMv9 `RuntimeContract` and `BootContract`.** Follow RPi5 pattern. `armv9RuntimeContract`: timer monotonicity (same as RPi5 — ARM Generic Timer), register context stability (strengthened with partition ID tracking), memory access (RAM regions only). `armv9BootContract`: empty initial state. ~30 lines | `RuntimeContract.lean`, `BootContract.lean` | Small |
| W8-N | — | **Define `armv9CacheFlushOnSwitch`.** Same-partition switch: `.none`. Cross-partition switch: `.wayFlush` of the outgoing partition's cache ways. Add GIC-700 consideration: interrupt handling within a partition uses the partition's cache allocation. ~15 lines | `PartitionContract.lean` | Trivial |
| W8-O | — | **Assemble `armv9PartitionBoundaryContract`.** Bundle W8-G through W8-N into the contract structure. ~15 lines | `PartitionContract.lean` | Trivial |
| W8-P | — | **Assemble `armv9PlatformBinding`.** Create `SeLe4n/Platform/ARMv9/Contract.lean` with `instance : PlatformBinding ARMv9Platform`. Wire `runtimeContract`, `bootContract`, `interruptContract`, and `partitionContract := some armv9PartitionBoundaryContract`. ~20 lines | `Contract.lean` | Small |

**Intra-phase ordering constraints:**
- W8-A → W8-B → W8-C (board constants → memory map → MachineConfig)
- W8-D is independent (register types, no board dependency)
- W8-E depends on W8-A + W8-D (MMIO addresses + register types)
- W8-F depends on W8-E (frame proof over MMIO operation)
- W8-G depends on W8-A (max partitions from board definition)
- W8-H depends on W8-G (MPAM config uses partition assignment)
- W8-I depends on W8-G (separation proof over assignment)
- W8-J depends on W8-H (disjointness proof over config)
- W8-K depends on W8-A (realm assignment)
- W8-L depends on W8-K (realm consistency proof)
- W8-M depends on W8-B + W8-C (contracts reference memory map + config)
- W8-N depends on W8-G + W8-H (flush spec uses partition assignment + config)
- W8-O depends on W8-I + W8-J + W8-N (assembles all proofs)
- W8-P depends on W8-O + W8-M + W8-L (final assembly)
- **Parallel chains**: {W8-A→B→C, W8-M} and {W8-D→W8-E→W8-F} and {W8-G→W8-H→W8-I, W8-J, W8-N→W8-O} and {W8-K→W8-L}

**Gate**: `lake build SeLe4n.Platform.ARMv9.Contract`. Zero `sorry`/`axiom`.

---

### Phase W9: Cross-Subsystem Integration (v0.22.8)

Wire the hardware partition model into existing kernel subsystems. This is the
highest-risk phase for proof breakage because it modifies proven operations.
All modifications are `Option`-gated: when `partitionContract = none`, new code
branches are dead and existing proofs apply unchanged.

**Modified files**: `Scheduler/Operations/Core.lean`,
`Enforcement/Wrappers.lean`, `Lifecycle/Operations.lean`,
`CrossSubsystem.lean`, `Architecture/Invariant.lean`,
`Architecture/Adapter.lean`

| ID | Ref | Description | Files | Est. |
|----|-----|-------------|-------|------|
| W9-A | CC-1 | **Add `activeMpamPartId` field to `MachineState`.** Add `activeMpamPartId : Option PartitionId := none` to `MachineState` in `Machine.lean`. This tracks which MPAM PARTID is currently active in the hardware register. The `:= none` default preserves all existing `MachineState` construction sites. ~3 lines | `SeLe4n/Machine.lean` | Trivial |
| W9-B | CC-1 | **Prove `activeMpamPartId` is frame-transparent.** Prove that all existing `MachineState` operations (`advanceTimerState`, `writeRegisterState`, `readMemoryState`) preserve `activeMpamPartId` (they don't touch it). Statement: `(advanceTimerState ticks st).machine.activeMpamPartId = st.machine.activeMpamPartId`. Similar for write/read. Proof: unfold each operation, show the new field is not in the modified record fields. ~20 lines | `SeLe4n/Machine.lean` | Small |
| W9-C | — | **Define `adapterSwitchPartition`.** `adapterSwitchPartition (pid : PartitionId) (ms : MachineState) : MachineState := { ms with activeMpamPartId := some pid }`. Sets the active MPAM PARTID. ~5 lines | `SeLe4n/Kernel/Architecture/Adapter.lean` | Trivial |
| W9-D | — | **Define `adapterFlushCacheWays`.** `adapterFlushCacheWays (ways : CacheWayMask) (ms : MachineState) : MachineState := ms`. In the abstract model, cache flushing is a no-op on `MachineState` (the abstract model does not model cache contents — cache isolation is captured by the partition contract proofs, not by state mutation). The flush is modeled as a state annotation that the platform contract can reference. ~10 lines | `SeLe4n/Kernel/Architecture/Adapter.lean` | Trivial |
| W9-E | — | **Add partition hooks to `AdapterProofHooks`.** Add optional fields: `preserveSwitchPartition : Option (∀ pid st, proofLayerInvariantBundle st → proofLayerInvariantBundle (adapterSwitchPartition pid st).machine.toSystemState) := none`, `preserveFlushCacheWays : Option (∀ ways st, proofLayerInvariantBundle st → proofLayerInvariantBundle (adapterFlushCacheWays ways st).machine.toSystemState) := none`. Existing platform hooks (`simRestrictiveAdapterProofHooks`, `rpi5RestrictiveAdapterProofHooks`) pass `none` — unchanged. ~15 lines | `SeLe4n/Kernel/Architecture/Invariant.lean` | Small |
| W9-F | CC-1 | **Extend `schedule` with partition switch.** In `Scheduler/Operations/Core.lean`, after the domain switch logic (where `activeDomain` changes), add: `match partitionContract with | none => pure () | some c => let oldPart := c.partitionAssignment.assign oldDomain; let newPart := c.partitionAssignment.assign newDomain; if oldPart != newPart then do adapterFlushCacheWays (flushSpec oldDomain newDomain); adapterSwitchPartition newPart else pure ()`. **Sub-steps**: (1) Read lines around domain switch in `Core.lean` to identify insertion point. (2) Add `partitionContract` parameter (defaulting to `none`). (3) Add partition switch logic guarded by `match`. (4) Verify existing proofs compile. ~20 lines added | `Scheduler/Operations/Core.lean` | Medium |
| W9-G | CC-1 | **Prove `schedule` partition switch preserves `schedulerInvariantBundleFull`.** The partition switch modifies only `machine.activeMpamPartId` (via `adapterSwitchPartition`) and performs a conceptual cache flush (no-op in abstract model). Since `schedulerInvariantBundleFull` does not reference `activeMpamPartId` (it concerns run queues, current thread, domain time), the invariant is frame-preserved. **Proof strategy**: show `activeMpamPartId` is not in any field read by the scheduler invariant predicates, then apply W9-B (frame transparency). ~30 lines | `Scheduler/Operations/Preservation.lean` | Medium |
| W9-H | CC-4 | **Extend IPC enforcement with cross-partition flush.** In `Enforcement/Wrappers.lean`, for each of the 9 policy-gated wrappers, add after the `securityFlowsTo` check: if `partitionContract = some c` and sender and receiver are in different partitions, apply `adapterFlushCacheWays` before the IPC operation. This prevents cache-based data exfiltration during cross-partition IPC. Modification pattern: `if partitionCrossCheck c sender receiver then adapterFlushCacheWays ... >>= fun _ => uncheckedOp else uncheckedOp`. ~5 lines per wrapper × 9 = ~45 lines total, but each is mechanical | `Enforcement/Wrappers.lean` | Medium |
| W9-I | CC-4 | **Prove IPC flush preserves `coreIpcInvariantBundle`.** The cache flush is a no-op in the abstract model (`adapterFlushCacheWays` returns `ms`), so `coreIpcInvariantBundle` is trivially preserved. Statement: `coreIpcInvariantBundle st → coreIpcInvariantBundle (afterFlush st)` where `afterFlush st = st` (definitionally). Proof: `id`. The wrapper correctness theorems (e.g., `endpointSendDualChecked_eq_endpointSendDual_when_allowed`) need a new case for the partition-check branch; when `partitionContract = none`, they reduce to the existing proof. ~30 lines | `Enforcement/Soundness.lean` | Small |
| W9-J | CC-4 | **Extend `lifecycleRetypeObject` with partition binding.** When a new object is created via `retypeFromUntyped`, if `partitionContract = some c`, the new object's backing domain must match the creating thread's domain (and thus partition). Add a check: `if partitionContract matches some c then verify partitionOfThread caller = expected partition`. If CCA realms are active, assign the object's pages to the domain's realm via `realmCreate`. ~15 lines added | `Lifecycle/Operations.lean` | Small |
| W9-K | CC-4 | **Prove `lifecycleRetypeObject` partition binding preserves `lifecycleInvariantBundle`.** The partition check is a guard (returns error on failure, no state change). The realm page assignment modifies the GPT (which is not part of `SystemState` — it's a hardware-level structure). Therefore `lifecycleInvariantBundle` is frame-preserved. Proof: case split on partition check success/failure; failure is trivial; success delegates to existing preservation proof. ~25 lines | `Lifecycle/Invariant.lean` | Small |
| W9-L | — | **Define `partitionCrossSubsystemInvariant`.** Add to `CrossSubsystem.lean`: `partitionCrossSubsystemInvariant (contract : Option PartitionBoundaryContract) (st : SystemState) : Prop`. When `none`: `True` (vacuously satisfied). When `some c`: (1) `activeMpamPartId st.machine = some (c.partitionAssignment.assign st.scheduler.activeDomain)` — PARTID register matches active domain's partition, (2) `∀ oid obj, st.objects[oid]? = some obj → partitionOf oid = c.partitionAssignment.assign (domainOf oid)` — all objects are in their domain's partition. ~20 lines | `CrossSubsystem.lean` | Small |
| W9-M | — | **Prove `partitionCrossSubsystemInvariant_none`.** When `contract = none`, the invariant is `True`. Proof: `trivial`. This is the backward compatibility lemma — existing proofs that carry `crossSubsystemInvariant st` can discharge the new partition component by `exact True.intro`. ~5 lines | `CrossSubsystem.lean` | Trivial |
| W9-N | — | **Extend `proofLayerInvariantBundle` with partition invariant.** Add `partitionCrossSubsystemInvariant contract st` as the 10th conjunct in `proofLayerInvariantBundle`. The bundle signature gains a `(contract : Option PartitionBoundaryContract := none)` parameter. When `none`, the 10th conjunct is `True` (W9-M). ~5 lines modified | `Architecture/Invariant.lean` | Small |
| W9-O | — | **Prove existing `preserves_proofLayerInvariantBundle` theorems still hold.** Each existing preservation theorem (`adapterAdvanceTimer_ok_preserves_proofLayerInvariantBundle`, etc.) must discharge the new 10th conjunct. When `contract = none`: apply `partitionCrossSubsystemInvariant_none` (W9-M). When `some c`: the existing adapter operations don't modify `activeMpamPartId` (W9-B frame transparency), so the partition invariant is frame-preserved. **This is the critical backward compatibility proof.** ~40 lines total across 3 adapter theorems | `Architecture/Invariant.lean` | Medium |
| W9-P | — | **Run full regression.** Execute `./scripts/test_full.sh`. This is mandatory — W9 touches the proof core. If any Tier 3 invariant surface anchor fails, investigate and fix before proceeding. Verification-only — no code changes. | — | Small |

**Intra-phase ordering constraints:**
- W9-A first (MachineState field must exist before adapter operations)
- W9-B depends on W9-A (frame proofs for new field)
- W9-C + W9-D depend on W9-A (adapter operations use new field)
- W9-E depends on W9-C + W9-D (proof hooks reference adapter operations)
- W9-F depends on W9-C + W9-D (schedule uses adapters)
- W9-G depends on W9-F + W9-B (preservation proof uses frame transparency)
- W9-H depends on W9-D (IPC wrappers use cache flush)
- W9-I depends on W9-H (soundness proofs for modified wrappers)
- W9-J depends on W9-A (lifecycle uses partition check)
- W9-K depends on W9-J (preservation proof)
- W9-L depends on W9-A (references activeMpamPartId)
- W9-M depends on W9-L (backward compatibility lemma)
- W9-N depends on W9-L + W9-M (extends composed bundle)
- W9-O depends on W9-N + W9-B + W9-G (must reprove all adapter preservation)
- W9-P depends on all other W9 sub-tasks
- **Critical path**: W9-A → W9-B → W9-C → W9-F → W9-G → W9-N → W9-O → W9-P
- **Parallel chains**: {W9-H→W9-I} and {W9-J→W9-K} are independent of the scheduler chain

**Gate**: `./scripts/test_full.sh` passes (all tiers 0–3). All modified `.lean`
modules build individually. Zero `sorry`/`axiom`.

---

### Phase W10: Validation & Documentation (v0.22.9)

End-to-end validation, test coverage, documentation synchronization, and
closure report.

**New files**: `tests/PartitionSuite.lean`,
`docs/dev_history/audits/WS_W_CLOSURE_REPORT.md`
**Modified files**: Multiple documentation files.

| ID | Ref | Description | Files | Est. |
|----|-----|-------------|-------|------|
| W10-A | — | **Create `PartitionSuite.lean` scaffold.** Test file following existing `tests/NegativeStateSuite.lean` pattern. Import `SeLe4n.Kernel.HardwarePartition`, `SeLe4n.Platform.Sim.PartitionContract`. Define `partitionTestSuite : List TestCase`. ~30 lines | `tests/PartitionSuite.lean` | Trivial |
| W10-B | CC-4 | **Add partition assignment positive tests.** Verify: (1) 4 domains get 4 distinct partitions, (2) partition assignment is deterministic (same input → same output), (3) `simPartitionSeparation` holds for all non-flowing domain pairs. Use `#eval` or test harness assertions. ~25 lines | `tests/PartitionSuite.lean` | Small |
| W10-C | CC-4 | **Add cache disjointness positive tests.** Verify: (1) all 6 cache way mask pairs are disjoint, (2) union of all 4 masks equals the full 16-way mask (`0xFFFF`), (3) each mask has exactly 4 bits set (popcount). ~20 lines | `tests/PartitionSuite.lean` | Small |
| W10-D | CC-2 | **Add timer isolation positive tests.** Verify: (1) 4 domains get 4 distinct timer offsets, (2) `timerIncrement_uniform` holds for sample values, (3) `timerNonInterference` holds: virtual counter difference is constant across physical counter increments. ~20 lines | `tests/PartitionSuite.lean` | Small |
| W10-E | — | **Add partition assignment negative tests.** Verify: (1) attempting to assign two non-flowing domains to the same partition makes contract construction fail (the `partitionSeparation` proof field cannot be satisfied), (2) attempting to create overlapping cache way masks makes `cacheWayDisjoint` unsatisfiable. These are compile-time tests (the proof obligation cannot be discharged). ~15 lines + doc | `tests/PartitionSuite.lean` | Small |
| W10-F | — | **Add cross-partition IPC negative tests.** Verify: (1) IPC between domains in different partitions triggers cache flush (trace output shows flush), (2) IPC between domains in same partition does not trigger flush. Uses trace harness. ~20 lines | `tests/PartitionSuite.lean` | Small |
| W10-G | — | **Wire `PartitionSuite` into test infrastructure.** Add to `tests/` build target in `lakefile.lean`. Ensure `test_smoke.sh` runs the new suite. ~10 lines | `lakefile.lean`, `scripts/test_smoke.sh` | Trivial |
| W10-H | — | **Extend `MainTraceHarness.lean` with partition trace.** Add a partition-aware trace scenario: create 4 domains, assign partitions, perform domain switches, output partition IDs and flush specs. Update `tests/fixtures/main_trace_smoke.expected` with new expected output. ~30 lines | `SeLe4n/Testing/MainTraceHarness.lean`, `tests/fixtures/main_trace_smoke.expected` | Small |
| W10-I | — | **Sorry/axiom audit.** Scan all new `.lean` files for `sorry` and `axiom`. Expected result: zero `sorry`, exactly one `axiom` (`realmMemoryIsolation` in `Realm.lean`). Run: `grep -r 'sorry' SeLe4n/Kernel/HardwarePartition/` and `grep -r 'axiom' SeLe4n/Kernel/HardwarePartition/`. Document results. | — | Trivial |
| W10-J | CC-1,2,3,4 | **Update covert channel documentation.** Rewrite the accepted covert channel block in `Projection.lean:305–337`. Under a `PartitionBoundaryContract`: CC-2 (timer) **CLOSED** by `CNTVOFF_EL2` offset isolation (W5); CC-4 (object metadata) **CLOSED** by MPAM cache partitioning (W3-E); CC-1 (scheduling) **NARROWED** — schedule is still visible but cache amplification eliminated; CC-3 (TCB metadata) **NARROWED** — priority visible to label-observable threads but preemption-pattern inference bounded by partition isolation. Document residual bandwidth for CC-1 and CC-3. ~30 lines | `Projection.lean` | Small |
| W10-K | — | **Update `README.md`.** Add hardware partition isolation to the metrics section. Update the "Covert channel status" row. Add WS-W to the workstream table. Sync from `docs/codebase_map.json`. ~15 lines | `README.md` | Trivial |
| W10-L | — | **Update `docs/spec/SELE4N_SPEC.md`.** Add section "§X. Hardware Partition Isolation" covering: partition correctness theorem, MPAM integration, CCA realm model, timer isolation. Reference the new Lean modules. ~40 lines | `docs/spec/SELE4N_SPEC.md` | Small |
| W10-M | — | **Update `docs/DEVELOPMENT.md`.** Add WS-W to active workstream list. Update "Next workstreams" section. Add new module paths to source layout. ~15 lines | `docs/DEVELOPMENT.md` | Trivial |
| W10-N | — | **Update `docs/WORKSTREAM_HISTORY.md`.** Add WS-W entry with all 10 phases, sub-task counts, version numbers, and status. Follow existing format (WS-U entry is the template). ~30 lines | `docs/WORKSTREAM_HISTORY.md` | Small |
| W10-O | — | **Update `docs/CLAIM_EVIDENCE_INDEX.md`.** Add claims: (1) `partitionCorrectness` — partition assignment reflects flow policy, (2) `cacheIsolationCorollary` — non-flowing objects have disjoint caches, (3) `realmMemoryIsolation` (axiom) — hardware GPT isolation. Link each claim to the Lean source location. ~15 lines | `docs/CLAIM_EVIDENCE_INDEX.md` | Trivial |
| W10-P | — | **Regenerate `docs/codebase_map.json`.** Run the codebase map generator (if automated) or manually add entries for `SeLe4n/Kernel/HardwarePartition/*` and `SeLe4n/Platform/ARMv9/*`. ~20 lines | `docs/codebase_map.json` | Trivial |
| W10-Q | — | **Update `scripts/website_link_manifest.txt`.** Add any new paths referenced from the website. Run `scripts/check_website_links.sh` to verify all links resolve. ~5 lines | `scripts/website_link_manifest.txt` | Trivial |
| W10-R | — | **Write closure report.** `docs/dev_history/audits/WS_W_CLOSURE_REPORT.md` summarizing: phases delivered, sub-tasks completed, theorems proved (count), axioms introduced (1), covert channels closed (2) / narrowed (2), test coverage added, remaining limitations, hardware prerequisites for full deployment. Follow WS-U closure report format. ~60 lines | `WS_W_CLOSURE_REPORT.md` | Small |
| W10-S | — | **Run nightly validation.** Execute `NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh` (full Tier 0–4 suite). Verification-only — no code changes. | — | Small |

**Intra-phase ordering constraints:**
- W10-A first (test scaffold)
- W10-B, W10-C, W10-D, W10-E, W10-F are independent test additions (all depend on W10-A)
- W10-G depends on W10-A through W10-F (wires completed tests)
- W10-H is independent (trace harness, different file)
- W10-I is independent (audit scan, no code changes)
- W10-J is independent (doc comment in Projection.lean)
- W10-K through W10-Q are independent documentation updates (can run in parallel)
- W10-R depends on W10-I + W10-S (closure report references audit and validation results)
- W10-S depends on W10-G + W10-H (must run after tests are wired)
- **Parallel chains**: {W10-B,C,D,E,F} are 5 independent test sub-tasks; {W10-K through W10-Q} are 7 independent doc updates

**Gate**: `NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh` passes
(all tiers 0–4). Zero `sorry`. Exactly one tracked `axiom`. All documentation
synchronized.

---


## 5. Phase-Level Summary

| Phase | Version | Sub-tasks | Complexity | Nature |
|-------|---------|-----------|------------|--------|
| W1 — Foundation Types | v0.22.0 | 11 | Low | Type definitions only |
| W2 — Partition Contract | v0.22.1 | 11 | Low | Contract structure + PlatformBinding extension |
| W3 — Correctness Proofs | v0.22.2 | 10 | Medium | Core theorems (key lemma + corollaries) |
| W4 — CCA Realm Model | v0.22.3 | 11 | Medium | Hardware axiom + transition proofs |
| W5 — Timer Isolation | v0.22.4 | 10 | Medium | Timer model + NI proofs |
| W6 — Projection Strengthening | v0.22.5 | 14 | High | Core IF infrastructure modification |
| W7 — Sim Instantiation | v0.22.6 | 12 | Low | Concrete proofs by computation |
| W8 — ARMv9 Instantiation | v0.22.7 | 16 | Medium | Hardware platform definition |
| W9 — Cross-Subsystem Integration | v0.22.8 | 16 | High | Proof-core modifications |
| W10 — Validation & Documentation | v0.22.9 | 19 | Low | Tests + docs + closure |
| **Total** | | **130** | | |

## 6. Effort Distribution

| Estimate | W1 | W2 | W3 | W4 | W5 | W6 | W7 | W8 | W9 | W10 | Total |
|----------|----|----|----|----|----|----|----|----|----|----|-------|
| Trivial | 9 | 9 | 7 | 7 | 8 | 5 | 8 | 4 | 4 | 8 | **69** |
| Small | 2 | 2 | 3 | 4 | 2 | 6 | 4 | 11 | 8 | 11 | **53** |
| Medium | 0 | 0 | 0 | 0 | 0 | 3 | 0 | 1 | 4 | 0 | **8** |
| Large | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | **0** |
| **Total** | **11** | **11** | **10** | **11** | **10** | **14** | **12** | **16** | **16** | **19** | **130** |

No sub-task is rated Large — every original complex task has been decomposed
into Small or Medium atomic units.

## 7. File Inventory

### New files (17)

| File | Phase | Lines (est.) | Purpose |
|------|-------|-------------|---------|
| `SeLe4n/Kernel/HardwarePartition/Types.lean` | W1 | ~250 | Foundation types |
| `SeLe4n/Kernel/HardwarePartition/Contract.lean` | W2 | ~120 | Partition boundary contract |
| `SeLe4n/Kernel/HardwarePartition/Correctness.lean` | W3 | ~200 | Partition correctness proofs |
| `SeLe4n/Kernel/HardwarePartition/Realm.lean` | W4 | ~180 | CCA realm model |
| `SeLe4n/Kernel/HardwarePartition/TimerIsolation.lean` | W5 | ~120 | Timer isolation model |
| `SeLe4n/Kernel/HardwarePartition.lean` | W1 | ~10 | Re-export hub |
| `SeLe4n/Platform/Sim/PartitionContract.lean` | W7 | ~150 | Sim partition instance |
| `SeLe4n/Platform/ARMv9/Board.lean` | W8 | ~120 | ARMv9 board constants |
| `SeLe4n/Platform/ARMv9/PartitionContract.lean` | W8 | ~200 | ARMv9 MPAM contract |
| `SeLe4n/Platform/ARMv9/RealmContract.lean` | W8 | ~80 | ARMv9 CCA contract |
| `SeLe4n/Platform/ARMv9/RuntimeContract.lean` | W8 | ~60 | ARMv9 runtime contract |
| `SeLe4n/Platform/ARMv9/BootContract.lean` | W8 | ~40 | ARMv9 boot contract |
| `SeLe4n/Platform/ARMv9/Contract.lean` | W8 | ~30 | ARMv9 platform binding |
| `tests/PartitionSuite.lean` | W10 | ~160 | Partition test scenarios |
| `docs/dev_history/audits/WS_W_CLOSURE_REPORT.md` | W10 | ~60 | Closure report |

### Modified files (14)

| File | Phase | Change |
|------|-------|--------|
| `SeLe4n/Platform/Contract.lean` | W2 | Add `partitionContract` field + accessor |
| `SeLe4n/Platform/Sim/Contract.lean` | W7 | Wire `simPartitionBoundaryContract` |
| `SeLe4n/Machine.lean` | W9 | Add `activeMpamPartId` field + frame proofs |
| `SeLe4n/Kernel/Architecture/Assumptions.lean` | W5 | Add `timerIsolation` field |
| `SeLe4n/Kernel/Architecture/Adapter.lean` | W9 | Add partition adapter ops |
| `SeLe4n/Kernel/Architecture/Invariant.lean` | W9 | Extend proof bundle (10th conjunct) |
| `SeLe4n/Kernel/InformationFlow/Projection.lean` | W6 | Strengthen projection + doc update |
| `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean` | W6 | Thread partition contract |
| `SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean` | W9 | Cross-partition IPC flush |
| `SeLe4n/Kernel/InformationFlow/Enforcement/Soundness.lean` | W9 | Updated wrapper correctness |
| `SeLe4n/Kernel/Scheduler/Operations/Core.lean` | W9 | Partition switch on domain change |
| `SeLe4n/Kernel/Scheduler/Operations/Preservation.lean` | W9 | Partition switch preservation |
| `SeLe4n/Kernel/Lifecycle/Operations.lean` | W9 | Partition binding on retype |
| `SeLe4n/Kernel/CrossSubsystem.lean` | W9 | Partition cross-subsystem invariant |

### Shared file coordination

`SeLe4n/Platform/Contract.lean` is modified in W2 only (additive field).
`SeLe4n/Machine.lean` is modified in W9 only (additive field).
`SeLe4n/Kernel/Architecture/Invariant.lean` is modified in W9 only (additive conjunct).
`SeLe4n/Kernel/InformationFlow/Projection.lean` is modified in W6 (projection
strengthening) and W10 (doc comment update). W10-J must read W6's final state.
No conflicting modifications across phases — each phase's changes are additive
to a different region of the file.

## 8. Axiom Budget

| Axiom | Location | Justification |
|-------|----------|---------------|
| `realmMemoryIsolation` | `Realm.lean` (W4-B) | Hardware guarantee enforced by ARM RME granule protection check unit at the interconnect. The kernel cannot verify this — it is enforced by the physical address check at the bus level before memory access reaches the cache/DRAM controller. Analogous to trusting the MMU to enforce page table translations. Documented in ARM DDI0487 §D8. |

All other proof obligations are **theorems** derived from contract fields. The
contract fields are `Prop` values — the platform instantiator must provide
evidence (a proof term) when constructing the `PartitionBoundaryContract`.

## 9. Dependency Graph

```
W1 (Types)
 └──→ W2 (Contract)
       ├──→ W3 (Correctness) ──────────────────→ W6-L (close sorry)
       │     └── W3-H: sorry (needs W6)                ↑
       ├──→ W4 (Realm) ────────────────────────────────┤
       ├──→ W5 (Timer) ────────────────────────────────┤
       ├──→ W7 (Sim) ──────────────────→ W10           │
       └──→ W8 (ARMv9) ────────────────→ W10           │
                                           ↑            │
       W6 (Projection) ───────────────────┤←───────────┘
        └──→ W9 (Integration) ──────────→ W10
```

**Critical path**: W1 → W2 → W3 → W6 → W9 → W10

**Parallelizable after W2 completes**:
- W3, W4, W5, W7, W8 can all start simultaneously
- W4, W5, W7, W8 can complete independently of W3
- W6 requires W3 (for W6-L sorry closure), W4, W5 (for complete partition model)
- W9 requires W6 (for projection-aware integration)

**Optimal execution order with maximum parallelism**:
```
Time ──→
       W1 → W2 ┬→ W3 ──→ W6 ──→ W9 ──→ W10   (critical path)
                ├→ W4 ─────↗                     (parallel)
                ├→ W5 ─────↗                     (parallel)
                ├→ W7 ──────────────────→ W10    (parallel, early validation)
                └→ W8 ──────────────────→ W10    (parallel, hardware path)
```

## 10. Invariant Preservation Impact Map

| Invariant Bundle | W1–W5 | W6 | W7 | W8 | W9 | W10 |
|-----------------|-------|----|----|----|----|-----|
| `schedulerInvariantBundleFull` | — | — | — | — | W9-G: frame-preserved (activeMpamPartId not read) | — |
| `capabilityInvariantBundle` | — | — | — | — | Frame-preserved (no cap fields touched) | — |
| `coreIpcInvariantBundle` | — | — | — | — | W9-I: trivially preserved (flush is no-op) | — |
| `ipcSchedulerCouplingInvariantBundle` | — | — | — | — | Frame-preserved | — |
| `lifecycleInvariantBundle` | — | — | — | — | W9-K: case-split preservation | — |
| `serviceLifecycleCapabilityInvariantBundle` | — | — | — | — | Frame-preserved | — |
| `vspaceInvariantBundle` | — | — | — | — | Frame-preserved | — |
| `crossSubsystemInvariant` | — | — | — | — | W9-L: extended with partition predicate | — |
| `tlbConsistent` | — | — | — | — | Frame-preserved | — |
| `partitionCrossSubsystemInvariant` (**new**) | — | — | — | — | W9-L/M/N: defined + backward compat | — |
| `ObservableState` projection | — | W6-A through W6-N: strengthened | W7: instantiated | W8: instantiated | — | W10-J: doc update |
| `lowEquivalent` / NI | — | W6-K/L: strengthened variant | — | — | — | — |

## 11. Risk Assessment

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| W6-H backward compatibility proof fails | Low | Critical | `Option`-gating ensures `none` branch is syntactically identical. W6-H is prioritized early in W6 to detect issues before dependent work proceeds |
| W9-O reproof of adapter preservation fails | Medium | High | All W9 modifications are `Option`-gated. Frame transparency (W9-B) provides the key lemma. Run `test_full.sh` after every W9 sub-task |
| W6-L sorry closure is harder than expected | Medium | Medium | The proof structure delegates to existing per-operation NI proofs via W6-K (strengthened implies original). If delegation fails, fall back to per-constructor case analysis (more tedious but mechanically straightforward) |
| BCM2712 successor lacks MPAM support | Medium | Medium | W8 is the only phase affected. Simulation (W7), proofs (W3/W6), and all other phases are hardware-independent |
| MPAM specification complexity exceeds model | Low | Medium | Model only CPBM + MBW_MAX. Ignore monitoring counters, overflow interrupts, QoS priority levels |
| Lean 4.28.0 limitations for parameterized invariant bundle | Low | Low | `proofLayerInvariantBundle` gains one `Option` parameter. Lean handles optional parameters well; existing callers use the default `none` |
| CCA realm model too abstract | Medium | Low | Accepted: captures security-relevant properties (memory isolation per realm) without full RMM state machine. Full integration is WS-X scope |
| `projectStateFast_eq` proof breaks under partition threading | Low | Medium | W6-I is dedicated to this. The fast path mirrors the slow path structurally; threading the same `contract` parameter preserves the equivalence argument |

## 12. Success Criteria

At WS-W completion:

1. **Zero sorry** in all new `.lean` files
2. **Exactly one axiom** (`realmMemoryIsolation`) with ARM DDI0487 §D8 justification
3. **`partitionAwareNonInterference` proven**: under a valid
   `PartitionBoundaryContract`, the NI guarantee extends from functional-only
   to functional + cache-partition + timer isolation
4. **`partitionCorrectness` proven**: `securityFlowsTo` label separation implies
   distinct hardware partitions
5. **`cacheIsolationCorollary` proven**: non-flowing objects have disjoint cache
   way allocations
6. **Backward compatibility**: all existing tests pass with `partitionContract = none`;
   `projectState_partition_none_eq` proves projection equivalence
7. **Simulation validated**: end-to-end test with 4 simulated partitions
8. **ARMv9 platform defined**: complete `PlatformBinding` instance ready for
   hardware bring-up
9. **Covert channels**: CC-2 and CC-4 marked CLOSED; CC-1 and CC-3 marked
   NARROWED with residual bandwidth documented
10. **130/130 sub-tasks complete** with all gates passed
11. **All documentation synchronized**: README, spec, development guide,
    workstream history, claim evidence index, codebase map
