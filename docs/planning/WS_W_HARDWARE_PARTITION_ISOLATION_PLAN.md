# WS-W: Hardware Partition Isolation — ARM CCA + MPAM Integration Plan

**Status**: PLANNED
**Target versions**: v0.22.0–v0.22.12+
**Hardware target**: Raspberry Pi 5 successor SoCs (BCM2712 successor with ARMv9-A)
**Prerequisite**: WS-U complete (v0.21.7), RPi5 hardware binding foundation

## 1. Motivation

seLe4n's information flow model (Projection.lean, lines 305–337) documents four
accepted covert channels that are provably beyond the reach of software-only
mitigation:

1. **Scheduling state** — `activeDomain`, `domainSchedule`, `domainTimeRemaining`
   are unconditionally visible to all observers (scheduling transparency).
2. **Machine timer** — excluded from `ObservableState` but readable via
   `CNTVCT_EL0` on real hardware.
3. **TCB metadata** — thread priority and IPC state visible to any observer
   that can see the thread; priority is inferable from preemption patterns.
4. **Object store metadata** — cache-timing side channels during allocator
   operations leak object creation/deletion activity across domains.

The current NI guarantee covers **functional non-interference** only. This plan
extends the formal model to cover **microarchitectural non-interference** by
integrating ARM Confidential Compute Architecture (CCA) realm isolation and
Memory Partitioning and Monitoring (MPAM) cache/bandwidth partitioning, with
the kernel proving correct partition assignment.

## 2. Scope Boundary

**In scope:**
- Formal model of MPAM partition IDs, cache partition sets, and bandwidth groups
- Formal model of CCA realm boundaries and realm-domain correspondence
- Proof obligation: `securityFlowsTo` label separation implies hardware partition
  separation (partition correctness theorem)
- Extension of `PlatformBinding` with partition-aware contracts
- Extension of `ObservableState` with partition-aware projection strengthening
- Platform-specific instantiation for BCM2712-successor (ARMv9-A + MPAM + RME)
- Simulation platform instantiation for test/validation without hardware

**Out of scope:**
- Bare-metal device driver implementation (deferred to WS-X)
- EL3 firmware / TF-A integration (trust anchor, not kernel responsibility)
- Spectre/Meltdown-class transient execution mitigations (orthogonal)
- Physical side channels (power, EM emanation)

## 3. Architecture Overview

```
┌───────────────────────────────────────────────────────────┐
│                    Security Domain A                       │
│  SecurityLabel { confidentiality := .high, integrity := .trusted } │
│  PartitionId 1 ──→ MPAM PARTID 1 ──→ Cache Ways {0..3}  │
│                                   ──→ BW Group 1 (40%)   │
│  RealmId 1 ──→ CCA Realm Descriptor ──→ GPA isolation    │
├───────────────────────────────────────────────────────────┤
│                    Security Domain B                       │
│  SecurityLabel { confidentiality := .low, integrity := .untrusted } │
│  PartitionId 2 ──→ MPAM PARTID 2 ──→ Cache Ways {4..7}  │
│                                   ──→ BW Group 2 (30%)   │
│  RealmId 2 ──→ CCA Realm Descriptor ──→ GPA isolation    │
├───────────────────────────────────────────────────────────┤
│  seLe4n Kernel (EL1 / Realm EL1)                         │
│  ┌──────────────────────────────────────────────────────┐ │
│  │ PartitionContract : PlatformBinding extension        │ │
│  │ - assignPartition : DomainId → PartitionId           │ │
│  │ - partitionSeparation : ∀ d₁ d₂,                    │ │
│  │     ¬securityFlowsTo l₁ l₂ → partition d₁ ≠ d₂     │ │
│  │ - cacheFlush : DomainId → DomainId → CacheFlushSpec  │ │
│  └──────────────────────────────────────────────────────┘ │
├───────────────────────────────────────────────────────────┤
│  Hardware (ARMv9-A + MPAM + RME)                          │
│  - MPAM MSC: cache way partitioning per PARTID            │
│  - MPAM MBW: memory bandwidth allocation per PARTID       │
│  - RME: realm granule protection, GPA isolation            │
│  - CNTVOFF_EL2: per-realm virtual counter offset           │
└───────────────────────────────────────────────────────────┘
```

## 4. Phase Plan

### Phase W1: Foundation Types (v0.22.0)

Introduce the core typed identifiers and structures for hardware partitioning.
No behavioral changes — pure type definitions and basic decidability instances.

**New file**: `SeLe4n/Kernel/HardwarePartition/Types.lean`

| Sub-task | ID | Description | Deliverable |
|----------|----|-------------|-------------|
| W1-A | Partition identifier types | Define `PartitionId`, `MpamPartId`, `MpamPmg`, `CacheWaySet`, `BandwidthGroup` as typed wrappers following Prelude.lean conventions (`structure X where val : Nat deriving DecidableEq, Repr, Inhabited, Hashable`) | `Types.lean` type definitions |
| W1-B | MPAM configuration structure | Define `MpamConfig` recording per-partition cache way allocation, bandwidth limit (percentage), and monitoring group assignment | `Types.lean` struct |
| W1-C | CCA realm identifier | Define `RealmId`, `RealmDescriptor` (granule protection table entry abstraction), `RealmState` (active/inactive/destroying) | `Types.lean` struct |
| W1-D | Partition assignment map | Define `PartitionAssignment` as `DomainId → PartitionId` (total function), `RealmAssignment` as `DomainId → Option RealmId` | `Types.lean` struct |
| W1-E | Cache flush specification | Define `CacheFlushSpec` inductive: `.none`, `.fullFlush`, `.wayFlush (ways : CacheWaySet)`, `.asidFlush (asid : ASID)`. Models the microarchitectural cleanup required on domain switch | `Types.lean` inductive |
| W1-F | Timer offset specification | Define `TimerOffsetConfig` as `DomainId → Nat` (CNTVOFF_EL2 value per domain). Models per-domain virtual counter offset | `Types.lean` struct |

**Proof obligations**: None in W1 (pure type definitions). All types must derive
`DecidableEq` to enable decidable contract predicates (matching the existing
`RuntimeBoundaryContract` pattern where all predicates carry `Decidable` instances).

**Dependencies**: Prelude.lean (for `DomainId`, `ASID`), Machine.lean (for `PAddr`).

**Validation**: `lake build SeLe4n.Kernel.HardwarePartition.Types` must succeed.

---

### Phase W2: Partition Contract (v0.22.1)

Define the platform-level contract that binds security labels to hardware
partitions. Extends the existing `PlatformBinding` typeclass pattern.

**New file**: `SeLe4n/Kernel/HardwarePartition/Contract.lean`
**Modified file**: `SeLe4n/Platform/Contract.lean`

| Sub-task | ID | Description | Deliverable |
|----------|----|-------------|-------------|
| W2-A | Partition boundary contract | Define `PartitionBoundaryContract` structure with fields: `partitionAssignment : PartitionAssignment`, `mpamConfig : PartitionId → MpamConfig`, `realmAssignment : RealmAssignment`, `cacheFlushOnSwitch : DomainId → DomainId → CacheFlushSpec`, `timerOffsetConfig : TimerOffsetConfig` | `Contract.lean` struct |
| W2-B | Partition separation axiom field | Add to `PartitionBoundaryContract`: `partitionSeparation : ∀ (d₁ d₂ : DomainId), d₁ ≠ d₂ → ¬domainFlowsAllowed d₁ d₂ → partitionAssignment d₁ ≠ partitionAssignment d₂`. This is the **core correctness obligation** — non-flowing domains must have distinct hardware partitions | `Contract.lean` field |
| W2-C | Cache disjointness axiom field | Add to `PartitionBoundaryContract`: `cacheWayDisjoint : ∀ (p₁ p₂ : PartitionId), p₁ ≠ p₂ → (mpamConfig p₁).cacheWays ∩ (mpamConfig p₂).cacheWays = ∅`. Distinct partitions must have non-overlapping cache way allocations | `Contract.lean` field |
| W2-D | Bandwidth sum bound | Add: `bandwidthBound : (∑ p in activePartitions, (mpamConfig p).bandwidthPercent) ≤ 100`. Total bandwidth allocation must not exceed hardware capacity | `Contract.lean` field |
| W2-E | Extend PlatformBinding | Add optional field `partitionContract : Option PartitionBoundaryContract := none` to the `PlatformBinding` class. The `Option` wrapper preserves backward compatibility — existing Sim and RPi5 instances pass `none` and are unaffected | Modified `Contract.lean` |
| W2-F | Decidable instances | Provide `Decidable` instances for all contract predicates, matching the pattern in `RuntimeBoundaryContract` (which carries `timerMonotonicDecidable`, `registerContextStableDecidable`, `memoryAccessAllowedDecidable`) | `Contract.lean` instances |

**Design rationale for `Option` wrapping**: The partition contract is hardware-
dependent. Platforms without MPAM/CCA (including the current RPi5 BCM2712,
which is ARMv8.2 and lacks MPAM) must not be forced to provide partition proofs.
The `Option` wrapper lets the type system distinguish "platform supports hardware
partitioning" from "platform does not" at the contract level.

**Validation**: `lake build SeLe4n.Platform.Contract` and all existing platform
instances must compile unchanged.

---

### Phase W3: Partition Correctness Proofs (v0.22.2)

The central contribution: prove that the partition assignment correctly reflects
the information flow policy, so that the hardware enforcement is sound with
respect to the formal NI model.

**New file**: `SeLe4n/Kernel/HardwarePartition/Correctness.lean`

| Sub-task | ID | Description | Deliverable |
|----------|----|-------------|-------------|
| W3-A | Label-to-domain bridge | Define `labelToDomain : LabelingContext → SecurityLabel → SecurityDomain` that maps the 2×2 lattice into the `GenericLabelingContext`'s domain model. Prove roundtrip: `embedLegacyLabel` composed with `labelToDomain` is identity on the 4-element lattice | Bridge theorem |
| W3-B | Flow-implies-partition theorem | Prove `partitionCorrectness`: given a `PartitionBoundaryContract` with `partitionSeparation`, and two objects `o₁ o₂` with labels `l₁ l₂` such that `securityFlowsTo l₁ l₂ = false ∧ securityFlowsTo l₂ l₁ = false` (mutual non-flow), then `partitionOf o₁ ≠ partitionOf o₂` | `Correctness.lean` theorem |
| W3-C | Cache isolation corollary | From W3-B + W2-C (`cacheWayDisjoint`), derive: mutually non-flowing objects have disjoint cache way allocations. This is the theorem that bridges the gap between functional NI and cache-timing NI | `Correctness.lean` theorem |
| W3-D | Bandwidth isolation corollary | From W3-B + partition assignment, derive: non-flowing domains have independent bandwidth groups. An observer's bandwidth allocation is unaffected by non-observable domains' memory traffic | `Correctness.lean` theorem |
| W3-E | Transitivity preservation | Prove that if the `DomainFlowPolicy` is transitive (required by `wellFormed`), then partition assignment is consistent with the transitive closure: if `a` flows to `b` flows to `c`, then `a` and `c` share a partition only if `a` flows to `c` | `Correctness.lean` theorem |
| W3-F | Composition with existing NI | State (but do not fully prove) the **strengthened NI theorem**: `partitionAwareNonInterference` — under a `PartitionBoundaryContract`, the existing `composedNonInterference_step` extends from functional NI to functional + cache-partition NI. The full proof requires W6 (projection strengthening). Mark with structured `sorry` annotation `-- TPI-W3F: requires W6 projection` | `Correctness.lean` sorry-annotated theorem statement |

**Proof strategy**: W3-B is the key lemma. It follows by contrapositive from
`partitionSeparation`: assume `partitionOf o₁ = partitionOf o₂`, then by
`partitionSeparation`'s contrapositive, either `d₁ = d₂` or
`domainFlowsAllowed d₁ d₂`. The first case contradicts mutual non-flow (a
domain flows to itself by reflexivity). The second case directly contradicts
the hypothesis.

**Validation**: `lake build SeLe4n.Kernel.HardwarePartition.Correctness`.
The single `sorry` in W3-F must be tracked in `TRACKED_PROOF_ISSUES.md`.

---

### Phase W4: CCA Realm Model (v0.22.3)

Model ARM Confidential Compute Architecture realm isolation at the abstraction
level needed for kernel partition proofs. seLe4n runs at Realm EL1 (or EL1
under the Realm Management Monitor). This phase models the RMM's guarantees
as axioms the kernel can rely on.

**New file**: `SeLe4n/Kernel/HardwarePartition/Realm.lean`

| Sub-task | ID | Description | Deliverable |
|----------|----|-------------|-------------|
| W4-A | Granule Protection Table model | Define `GranuleState` inductive: `.realm (rid : RealmId)`, `.nonSecure`, `.secure`, `.root`. Define `GranuleProtectionTable` as `PAddr → GranuleState`. This models the GPT that RME hardware enforces — each physical page belongs to exactly one realm | `Realm.lean` types |
| W4-B | Realm memory isolation axiom | Define `realmMemoryIsolation : ∀ (r₁ r₂ : RealmId) (pa : PAddr), r₁ ≠ r₂ → gpt pa = .realm r₁ → gpt pa ≠ .realm r₂`. A physical address cannot belong to two realms simultaneously. This is a hardware guarantee, modeled as an axiom | `Realm.lean` axiom |
| W4-C | Realm-domain correspondence | Define `realmDomainConsistent : ∀ (d : DomainId), realmAssignment d = some rid → ∀ (pa : PAddr), domainOwnsPage d pa → gpt pa = .realm rid`. Every page owned by a domain with a realm assignment must be in that realm's GPT entry. This is the kernel's proof obligation — it must configure the GPT correctly | `Realm.lean` proof obligation |
| W4-D | Realm lifecycle transitions | Define `RealmTransition` inductive: `.create`, `.activate`, `.deactivate`, `.destroy`. Prove that realm transitions preserve GPT consistency: creating a realm does not reassign existing pages; destroying a realm releases all its pages to `.nonSecure` | `Realm.lean` transition proofs |
| W4-E | Realm-partition bridge | Prove that if `realmAssignment d₁ = some r₁` and `realmAssignment d₂ = some r₂` and `r₁ ≠ r₂`, then the domains have disjoint physical memory. Combined with W3-B, this gives: non-flowing domains have physically isolated memory when realms are active | `Realm.lean` bridge theorem |
| W4-F | Non-realm fallback | For platforms without CCA (including current RPi5), define `trivialRealmAssignment : DomainId → Option RealmId := fun _ => none`. All realm proof obligations become vacuously true. This preserves backward compatibility | `Realm.lean` default instance |

**Hardware reference**: ARM DEN0137 (Realm Management Monitor specification),
ARM DDI0487 (ARMv9-A Architecture Reference Manual, Part D: RME).

**Key design decision**: Realm isolation is modeled as a **hardware axiom**
(`realmMemoryIsolation`), not a proven theorem, because the kernel cannot
verify GPT enforcement — that is the responsibility of the RMM firmware and
hardware. The kernel's obligation is to configure the GPT correctly (W4-C),
which IS a provable property.

**Validation**: `lake build SeLe4n.Kernel.HardwarePartition.Realm`.

---

### Phase W5: Timer Isolation Model (v0.22.4)

Close the machine timer covert channel by modeling ARM's virtual counter offset
mechanism. Currently, `st.machine.timer` is excluded from `ObservableState`
(Projection.lean:323–326) to prevent the timing channel. This phase models the
hardware mechanism that makes exclusion physically enforceable.

**New file**: `SeLe4n/Kernel/HardwarePartition/TimerIsolation.lean`

| Sub-task | ID | Description | Deliverable |
|----------|----|-------------|-------------|
| W5-A | Virtual counter model | Define `VirtualCounter` structure: `physicalCount : Nat`, `offset : Nat`, `virtualCount := physicalCount - offset`. Each domain sees `virtualCount`, not `physicalCount`. The kernel sets `offset` via `CNTVOFF_EL2` on domain switch | `TimerIsolation.lean` struct |
| W5-B | Timer projection function | Define `projectDomainTimer : TimerOffsetConfig → DomainId → Nat → Nat` that computes the domain-local virtual counter from the physical counter and the domain's offset | `TimerIsolation.lean` function |
| W5-C | Timer non-interference | Prove `timerNonInterference`: if two domains `d₁ d₂` have different timer offsets, then incrementing the physical counter by any amount `Δ` changes both virtual counters by `Δ`, but the absolute values remain unrelated. An observer in `d₁` cannot determine `d₂`'s execution duration from timer reads | `TimerIsolation.lean` theorem |
| W5-D | Offset assignment correctness | Prove `timerOffsetSeparation`: given a `PartitionBoundaryContract`, non-flowing domains have distinct timer offsets iff the contract's `timerOffsetConfig` assigns distinct values. State the proof obligation that the platform must satisfy | `TimerIsolation.lean` theorem |
| W5-E | Domain-switch timer update | Define `domainSwitchTimerUpdate : DomainId → DomainId → MachineState → MachineState` that models what happens on domain switch: save current domain's virtual counter state, load new domain's offset into `CNTVOFF_EL2`, update `machine.timer` view. Prove it preserves `machineWordBounded` | `TimerIsolation.lean` function + proof |
| W5-F | Integration with RuntimeBoundaryContract | Extend `RuntimeBoundaryContract` with optional `timerIsolation : Option TimerOffsetConfig := none`. When present, the `timerMonotonic` predicate is strengthened: monotonicity holds for the **virtual** counter (per-domain), not just the physical counter. Existing contracts pass `none` and are unaffected | Modified `Assumptions.lean` |

**Design note**: W5-C is a weaker statement than "perfect timer isolation" — it
says that timer increments are uniform across domains (all see the same `Δ`),
but does not prevent inference from the *absence* of timer increments (i.e., a
domain that is not scheduled sees no increments). Full timer isolation requires
W1 scheduling partitioning + W5 offset isolation together. The combined
guarantee is stated in W9 (cross-subsystem integration).

**Validation**: `lake build SeLe4n.Kernel.HardwarePartition.TimerIsolation` and
`lake build SeLe4n.Kernel.Architecture.Assumptions` (backward compatibility).

---

### Phase W6: Projection Strengthening (v0.22.5)

The central model-level change: extend `ObservableState` and `projectState` to
account for hardware partition boundaries, and prove the strengthened NI theorem
that was forward-declared in W3-F.

**Modified files**: `SeLe4n/Kernel/InformationFlow/Projection.lean`,
`SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean`

| Sub-task | ID | Description | Deliverable |
|----------|----|-------------|-------------|
| W6-A | Extended ObservableState | Add optional fields to `ObservableState`: `partitionId : Option PartitionId` (observer's own partition), `cachePartition : Option CacheWaySet` (observer's cache allocation). These are `none` when no partition contract is active | Modified `Projection.lean` |
| W6-B | Partition-aware object projection | When a `PartitionBoundaryContract` is active, strengthen `projectObjects`: objects in a different partition are projected as `none` even if their label would pass `objectObservable`. This closes the cache-timing channel for object metadata — an observer cannot observe cache effects from objects in a different hardware partition | Modified `Projection.lean` |
| W6-C | Partition-aware memory projection | When a `PartitionBoundaryContract` is active, strengthen `projectMemory`: memory addresses whose owning domain maps to a different partition are projected as `none`. Combined with W4-E (realm memory isolation), this gives physical memory isolation | Modified `Projection.lean` |
| W6-D | Backward compatibility theorem | Prove `projectState_partition_none_eq`: when `partitionContract = none`, the extended `projectState` equals the original `projectState`. This ensures all existing NI proofs remain valid without modification | `Projection.lean` theorem |
| W6-E | Strengthened low-equivalence | Define `partitionAwareLowEquivalent`: two states are partition-aware low-equivalent iff their partition-strengthened projections are equal. Prove that `partitionAwareLowEquivalent` implies `lowEquivalent` (the strengthened notion is strictly stronger) | `Projection.lean` definition + theorem |
| W6-F | Close W3-F sorry | Complete the proof of `partitionAwareNonInterference` from W3-F. Under a `PartitionBoundaryContract`, `partitionAwareLowEquivalent` is preserved by all `NonInterferenceStep` constructors. The proof delegates to existing per-operation NI proofs (which already show state changes are localized to the operation's target objects) and then applies W3-C (cache isolation) to show that cache effects are also partition-local | `Correctness.lean` completed proof |
| W6-G | Scheduling channel documentation | Add a structured doc comment to `projectActiveDomain` explaining that under hardware partitioning, the scheduling channel's bandwidth is bounded: while scheduling state is still visible, the cache-timing amplification (where observing scheduling decisions leaks information about other domains' behavior via cache pressure) is eliminated by MPAM cache partitioning | Modified `Projection.lean` doc comment |

**Critical invariant**: W6-D is the single most important sub-task. If it
fails, the entire existing proof surface breaks. The implementation strategy
is: add the partition fields as `Option` types defaulting to `none`, and
use `if` branches that fall through to the existing projection logic when
`none`. The backward compatibility proof then follows by `simp` on the `none`
branch.

**Validation**: `lake build SeLe4n.Kernel.InformationFlow.Projection`,
`lake build SeLe4n.Kernel.InformationFlow.Invariant.Composition`,
`./scripts/test_full.sh` (full regression).

---

### Phase W7: Platform Instantiation — Simulation (v0.22.6)

Instantiate the partition contract for the simulation platform, enabling
validation and test coverage without hardware. Follows the existing
Sim/RPi5 dual-instantiation pattern.

**New file**: `SeLe4n/Platform/Sim/PartitionContract.lean`
**Modified file**: `SeLe4n/Platform/Sim/Contract.lean`

| Sub-task | ID | Description | Deliverable |
|----------|----|-------------|-------------|
| W7-A | Simulation MPAM config | Define `simMpamConfig` with 4 partitions (matching the 4-element security label lattice), each assigned 4 simulated cache ways (ways 0–3, 4–7, 8–11, 12–15 for a 16-way simulated cache) and 25% bandwidth | `PartitionContract.lean` |
| W7-B | Simulation partition assignment | Define `simPartitionAssignment : DomainId → PartitionId` mapping domain 0 → partition 0, domain 1 → partition 1, etc. For domains ≥4, wrap modularly (matching the 4-label lattice) | `PartitionContract.lean` |
| W7-C | Simulation realm assignment | Define `simRealmAssignment : DomainId → Option RealmId := fun _ => none`. Simulation platform has no CCA — all realm obligations are vacuous | `PartitionContract.lean` |
| W7-D | Prove simulation partition separation | Prove `simPartitionSeparation`: for the simulation's labeling context and partition assignment, non-flowing domains get distinct partitions. This is a concrete instantiation of W2-B over the 4-element lattice — provable by exhaustive case analysis (`decide` or `native_decide`) | `PartitionContract.lean` theorem |
| W7-E | Prove cache disjointness | Prove `simCacheWayDisjoint`: the 4 simulated cache way sets are pairwise disjoint. Direct computation proof | `PartitionContract.lean` theorem |
| W7-F | Assemble contract | Bundle W7-A through W7-E into `simPartitionBoundaryContract : PartitionBoundaryContract`. Wire into `simPlatformBinding` and `simRestrictivePlatformBinding` via `partitionContract := some simPartitionBoundaryContract` | Modified `Contract.lean` |
| W7-G | Timer offset config | Define `simTimerOffsetConfig : DomainId → Nat` assigning distinct offsets (e.g., domain `d` gets offset `d.val * 1000000`). Prove offsets are distinct for distinct domains | `PartitionContract.lean` |

**Validation**: `lake build SeLe4n.Platform.Sim.Contract`,
`./scripts/test_smoke.sh` (existing test suite passes with new contract).

---

### Phase W8: Platform Instantiation — ARMv9 Hardware (v0.22.7)

Define the concrete hardware contract for a BCM2712-successor SoC with ARMv9-A,
MPAM, and RME support. This is the production-path instantiation.

**New file**: `SeLe4n/Platform/ARMv9/Board.lean`
**New file**: `SeLe4n/Platform/ARMv9/PartitionContract.lean`
**New file**: `SeLe4n/Platform/ARMv9/RealmContract.lean`
**New file**: `SeLe4n/Platform/ARMv9/Contract.lean`

| Sub-task | ID | Description | Deliverable |
|----------|----|-------------|-------------|
| W8-A | ARMv9 board definition | Define BCM2712-successor constants: MPAM MSC base addresses, MPAM register offsets (`MPAMCFG_PART_SEL`, `MPAMCFG_CPBM`, `MPAMCFG_MBW_MAX`), GPT base address, number of MPAM partitions (implementation-defined, assume ≥16). Extend `MachineConfig` with `mpamPartitionCount : Nat` and `realmSupported : Bool` | `Board.lean` |
| W8-B | MPAM register model | Define `MpamRegister` structure modeling the MPAM MSC configuration registers: cache portion bitmap (`CPBM`), memory bandwidth maximum (`MBW_MAX`), monitoring counter select (`MON_SEL`). These are written via MMIO during partition setup | `PartitionContract.lean` types |
| W8-C | MPAM partition setup operation | Define `configureMpamPartition : PartitionId → MpamConfig → MmioAdapter Unit` that writes the correct MPAM registers for a partition. Model the MMIO writes using the existing `mmioWrite32` infrastructure from `RPi5/MmioAdapter.lean`. Prove the operation only touches MPAM MMIO regions (frame property) | `PartitionContract.lean` operation + proof |
| W8-D | Hardware partition assignment | Define the production `armv9PartitionAssignment` based on ARM MPAM's PARTID space. Prove `partitionSeparation` using the same strategy as W7-D but parameterized by the `GenericLabelingContext` (supporting ≥3 domains via `DomainFlowPolicy`) | `PartitionContract.lean` theorem |
| W8-E | Realm configuration | Define `configureRealm : RealmId → List PAddr → GranuleProtectionTable → GranuleProtectionTable` that assigns pages to a realm. Prove it preserves `realmMemoryIsolation` (W4-B): assigning pages to a new realm does not affect existing realms' pages | `RealmContract.lean` operation + proof |
| W8-F | GIC-700 interrupt partitioning | Model the GIC-700's MPAM-aware interrupt partitioning: interrupt handling within a partition's cache allocation. Define `gicPartitionConfig` ensuring interrupt handlers run in the correct partition context | `Board.lean` extension |
| W8-G | Cache flush on domain switch | Define `armv9CacheFlushOnSwitch` implementing the domain-switch cache cleanup policy: when switching between domains in the same MPAM partition, no flush needed (cache ways are shared); when switching between different partitions, flush the outgoing partition's cache ways via `DC CISW` | `PartitionContract.lean` |
| W8-H | Assemble platform binding | Bundle all components into `armv9PlatformBinding : PlatformBinding`. This extends the existing RPi5 binding pattern with partition and realm contracts | `Contract.lean` |

**Hardware references**:
- ARM IHI0086 (MPAM specification v1.1)
- ARM DEN0137 (RMM specification)
- ARM DDI0601 (Generic Interrupt Controller v4 with MPAM)

**Design decision**: The ARMv9 platform is a **separate platform** from RPi5,
not an extension. The current RPi5 (BCM2712, Cortex-A76, ARMv8.2) does not
support MPAM or RME. A future RPi6 or similar board with a Cortex-A720 or
later (ARMv9.2+) would use this platform definition. The RPi5 platform
continues to work with `partitionContract := none`.

**Validation**: `lake build SeLe4n.Platform.ARMv9.Contract`.

---

### Phase W9: Cross-Subsystem Integration (v0.22.8)

Wire the hardware partition model into the existing kernel subsystems:
scheduler (domain switch triggers partition switch), IPC (cross-partition
IPC requires cache flush), and lifecycle (retype in correct partition).

**Modified files**: Multiple existing kernel subsystem files.

| Sub-task | ID | Description | Deliverable |
|----------|----|-------------|-------------|
| W9-A | Scheduler partition switch | Extend `schedule` operation: when the active domain changes and a `PartitionBoundaryContract` is present, the scheduler must: (1) apply `cacheFlushOnSwitch` for the old→new domain pair, (2) update the MPAM PARTID register (modeled as a field in `MachineState`), (3) update the timer offset. Prove `schedulerInvariantBundleFull` preservation | Modified `Scheduler/Operations/Core.lean` |
| W9-B | Partition-aware IPC enforcement | Extend the 9 policy-gated wrappers in `Enforcement/Wrappers.lean`: when a `PartitionBoundaryContract` is present, cross-partition IPC additionally requires a cache flush of the sender's partition before the message is delivered (preventing cache-based data exfiltration). Define `crossPartitionIpcFlush` and prove it preserves `coreIpcInvariantBundle` | Modified `Enforcement/Wrappers.lean` |
| W9-C | Lifecycle partition binding | Extend `lifecycleRetypeObject`: when creating a new object, assign it to the creating domain's partition. If CCA realms are active, assign the object's backing pages to the domain's realm. Prove `lifecycleInvariantBundle` preservation | Modified `Lifecycle/Operations.lean` |
| W9-D | Cross-subsystem partition invariant | Define `partitionCrossSubsystemInvariant`: (1) all objects in a domain are in that domain's partition, (2) all pages backing objects in a domain are in that domain's realm, (3) the current MPAM PARTID register matches the active domain's partition. Add to `crossSubsystemInvariant` (with `Option` gating on partition contract presence) | Modified `CrossSubsystem.lean` |
| W9-E | Composed invariant extension | Extend `proofLayerInvariantBundle` with `partitionCrossSubsystemInvariant` (gated by partition contract). Prove all existing `preserves_proofLayerInvariantBundle` theorems still hold when `partitionContract = none` (backward compatibility) | Modified `Architecture/Invariant.lean` |
| W9-F | Adapter partition operations | Define `adapterSwitchPartition : PartitionId → MachineState → MachineState` and `adapterFlushCacheWays : CacheWaySet → MachineState → MachineState`. Add to `AdapterProofHooks` as optional fields: `preserveSwitchPartition` and `preserveFlushCacheWays`. Existing hooks pass vacuous proofs (operations are `none`-gated) | Modified `Architecture/Adapter.lean`, `Architecture/Invariant.lean` |

**Risk**: W9-A and W9-B are the highest-risk sub-tasks because they modify
existing proven operations. The mitigation is the `Option`-gating pattern:
when `partitionContract = none`, the new code branches are dead and existing
proofs apply unchanged. When `some contract`, new proofs are required but
are localized to the partition-specific state changes.

**Validation**: `./scripts/test_full.sh` (full regression including all
invariant surface anchors). This is mandatory — W9 touches the proof core.

---

### Phase W10: Validation & Documentation (v0.22.9)

End-to-end validation, test coverage, documentation synchronization, and
closure report.

| Sub-task | ID | Description | Deliverable |
|----------|----|-------------|-------------|
| W10-A | Simulation end-to-end test | Add test scenario in `tests/` that exercises the simulation partition contract: create 4 domains with distinct security labels, verify partition assignment, simulate domain switches with cache flushes, verify NI projection produces correct partition-aware results | New test file |
| W10-B | Negative test cases | Add negative tests: attempt to assign two non-flowing domains to the same partition (contract construction fails), attempt cross-partition IPC without flush (enforcement denies), attempt to create an object in the wrong partition (lifecycle rejects) | New test file |
| W10-C | Sorry/axiom audit | Verify zero `sorry` in all new files except tracked `axiom` for `realmMemoryIsolation` (W4-B, hardware axiom — not a sorry). All axioms must be documented in `CLAIM_EVIDENCE_INDEX.md` with rationale | Audit report |
| W10-D | Trace harness extension | Extend `MainTraceHarness.lean` with a partition-aware trace scenario. Update `tests/fixtures/main_trace_smoke.expected` if the new scenario produces trace output | Modified harness + fixture |
| W10-E | Documentation sync | Update: (1) `README.md` — add partition isolation metrics, (2) `docs/spec/SELE4N_SPEC.md` — add hardware partition section, (3) `docs/DEVELOPMENT.md` — add W-series to active workstream, (4) `docs/WORKSTREAM_HISTORY.md` — add WS-W entry, (5) `docs/CLAIM_EVIDENCE_INDEX.md` — add partition correctness claims, (6) Relevant GitBook chapters, (7) `docs/codebase_map.json` | Updated docs |
| W10-F | Covert channel reassessment | Update the accepted covert channel documentation in `Projection.lean:305–337`. Under a `PartitionBoundaryContract`, channels 2 (timer) and 4 (object store metadata) are **closed**. Channel 1 (scheduling state) is **narrowed** (cache amplification eliminated, but schedule visibility remains by design). Channel 3 (TCB metadata) is **narrowed** (priority inference via preemption patterns bounded by partition isolation). Document the residual channels | Modified `Projection.lean` doc comment |
| W10-G | Website link protection | Verify all new file paths added to `scripts/website_link_manifest.txt` if referenced from the website. Run `scripts/check_website_links.sh` | Updated manifest |
| W10-H | Closure report | Write `docs/dev_history/audits/WS_W_CLOSURE_REPORT.md` summarizing: phases delivered, theorems proved, axioms introduced, covert channels closed/narrowed, remaining limitations, hardware prerequisites | Closure report |

**Validation**: `./scripts/test_nightly.sh` with `NIGHTLY_ENABLE_EXPERIMENTAL=1`
(full nightly suite including Tier 4 experimental anchors).

---

## 5. File Inventory

### New files (13)

| File | Phase | Purpose |
|------|-------|---------|
| `SeLe4n/Kernel/HardwarePartition/Types.lean` | W1 | Foundation types |
| `SeLe4n/Kernel/HardwarePartition/Contract.lean` | W2 | Partition boundary contract |
| `SeLe4n/Kernel/HardwarePartition/Correctness.lean` | W3 | Partition correctness proofs |
| `SeLe4n/Kernel/HardwarePartition/Realm.lean` | W4 | CCA realm model |
| `SeLe4n/Kernel/HardwarePartition/TimerIsolation.lean` | W5 | Timer isolation model |
| `SeLe4n/Kernel/HardwarePartition.lean` | W2 | Re-export hub |
| `SeLe4n/Platform/Sim/PartitionContract.lean` | W7 | Sim partition instance |
| `SeLe4n/Platform/ARMv9/Board.lean` | W8 | ARMv9 board constants |
| `SeLe4n/Platform/ARMv9/PartitionContract.lean` | W8 | ARMv9 MPAM contract |
| `SeLe4n/Platform/ARMv9/RealmContract.lean` | W8 | ARMv9 CCA contract |
| `SeLe4n/Platform/ARMv9/Contract.lean` | W8 | ARMv9 platform binding |
| `tests/PartitionSuite.lean` | W10 | Partition test scenarios |
| `docs/dev_history/audits/WS_W_CLOSURE_REPORT.md` | W10 | Closure report |

### Modified files (10)

| File | Phase | Change |
|------|-------|--------|
| `SeLe4n/Platform/Contract.lean` | W2 | Add `partitionContract` field |
| `SeLe4n/Kernel/Architecture/Assumptions.lean` | W5 | Add `timerIsolation` field |
| `SeLe4n/Kernel/Architecture/Adapter.lean` | W9 | Add partition adapter ops |
| `SeLe4n/Kernel/Architecture/Invariant.lean` | W9 | Extend proof bundle |
| `SeLe4n/Kernel/InformationFlow/Projection.lean` | W6 | Strengthen projection |
| `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean` | W6 | Strengthen NI |
| `SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean` | W9 | Cross-partition flush |
| `SeLe4n/Kernel/Scheduler/Operations/Core.lean` | W9 | Partition switch |
| `SeLe4n/Kernel/Lifecycle/Operations.lean` | W9 | Partition binding |
| `SeLe4n/Kernel/CrossSubsystem.lean` | W9 | Partition cross-subsystem inv |

## 6. Axiom Budget

This plan introduces exactly **one** axiom:

| Axiom | Location | Justification |
|-------|----------|---------------|
| `realmMemoryIsolation` | `Realm.lean` (W4-B) | Hardware guarantee enforced by ARM RME granule protection check unit. The kernel cannot verify this — it is enforced by the physical address check at the interconnect level. Analogous to how the kernel trusts the MMU to enforce page table translations. Documented in ARM DDI0487 §D8 |

All other proof obligations are **theorems** derived from contract fields that
the platform instantiator must satisfy. The contract fields themselves are
`Prop` values — the platform must provide evidence (a proof term) at
instantiation time.

## 7. Dependency Graph

```
W1 (Types) ──→ W2 (Contract) ──→ W3 (Correctness) ──→ W6-F (Close sorry)
                    │                                         ↑
                    ├──→ W4 (Realm) ──────────────────────────┤
                    │                                         │
                    ├──→ W5 (Timer) ──────────────────────────┤
                    │                                         │
                    └──→ W7 (Sim) ─────→ W10 (Validation)    │
                                                ↑             │
W8 (ARMv9) ─────────────────────────────────────┤             │
                                                │             │
W9 (Integration) ──────────────────────────→ W10 ◄────────────┘
     ↑
     │
     ├── depends on W2, W3, W4, W5 (all contract + proof infrastructure)
     └── depends on W6 (projection strengthening)
```

**Critical path**: W1 → W2 → W3 → W6 → W9 → W10

**Parallelizable**: W4, W5, W7 can proceed in parallel after W2 completes.
W8 can proceed in parallel after W2 completes (hardware constants are
independent of proofs).

## 8. Risk Assessment

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| W6-D backward compatibility proof fails | Low | Critical | `Option`-gating pattern ensures `none` branch is syntactically identical to current code. If proof is non-trivial, add explicit `cast` lemma |
| W9 modifies proven operations and breaks existing proofs | Medium | High | All modifications are `Option`-gated. Existing proofs only need `simp [partitionContract, Option.none]` discharge. Run `test_full.sh` after every sub-task |
| BCM2712 successor lacks MPAM support | Medium | Medium | W8 is the only phase affected. The simulation platform (W7) and all proofs (W3, W6) are hardware-independent. The model remains valid; only instantiation is blocked |
| MPAM specification complexity exceeds model capacity | Low | Medium | Model only the subset of MPAM needed: CPBM (cache portion bitmap) and MBW_MAX (bandwidth). Ignore monitoring counters, overflow interrupts, and performance monitoring groups beyond basic PMG |
| Lean 4.28.0 limitations for complex axiom handling | Low | Low | Only one axiom (W4-B). Lean's `axiom` keyword is well-tested. All other obligations are theorems |
| CCA realm model too abstract for real-world deployment | Medium | Low | Accepted: the model captures the security-relevant properties (memory isolation per realm) without modeling the full RMM state machine. Full RMM integration is WS-X scope |

## 9. Success Criteria

At WS-W completion:

1. **Zero sorry** in all new `.lean` files (one tracked `axiom` for `realmMemoryIsolation`)
2. **`partitionAwareNonInterference`** theorem proven: under a valid
   `PartitionBoundaryContract`, the NI guarantee extends from functional-only
   to functional + cache-partition + timer isolation
3. **Backward compatibility**: all existing tests pass with `partitionContract = none`
4. **Simulation validated**: end-to-end test with 4 simulated partitions demonstrates
   correct partition assignment, cache disjointness, and strengthened projection
5. **ARMv9 platform defined**: complete `PlatformBinding` instance for ARMv9-A
   with MPAM + RME, ready for hardware bring-up when silicon is available
6. **Covert channel documentation updated**: channels 2 and 4 marked as closed
   under hardware partitioning; channels 1 and 3 marked as narrowed with
   precise residual bandwidth characterization
7. **All documentation synchronized**: README, spec, development guide,
   workstream history, claim evidence index, GitBook chapters, codebase map
