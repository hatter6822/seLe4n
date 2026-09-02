# SM0 — Foundations & Honesty Patches (WS-SM Phase 0)

> **Status**: CLOSED (v0.31.3) — all SM0 sub-tasks landed; the phase's
> theorem inventory is registered as SM0 in
> `SeLe4n/Kernel/Concurrency/PhaseTheoremManifest.lean`
> **Phase**: SM0 of WS-SM
> **Parent overview**: [`SMP_MULTICORE_COMPLETION_PLAN.md`](SMP_MULTICORE_COMPLETION_PLAN.md)
> **Audited cut**: `v0.31.2`
> **Target releases**: v0.31.3 (landed); SM1+ continues at v0.32.x (~18 small PRs)
> **Calendar estimate**: 4-6 weeks
> **Sub-task count**: 40-50

## 1. Phase goal

SM0 lays the **foundational types, build-time anchors, and
documentation-honesty patches** that the larger phases (SM1..SM10)
depend on. No runtime behavioral change yet; no SMP activation;
the v0.31.3 release boots single-core just as v0.31.2
does today.

Three substantive goals:

1. **Foundational typed identifiers** — `CoreId`, `LockKind`,
   `BklState`, `SgiKind`, `SharingDomain`, and the
   `PlatformBinding` extension fields they depend on. These are
   the type-level scaffolding the later phases build atop.
2. **Honesty patches** — close the documentation drift and dead-
   reference issues catalogued in SMP-M1..M7 + SMP-L1..L5. Make
   every claim in tree match what the code actually does.
3. **WS-RC merge** — recategorize WS-RC's R6..R14 phases into
   SM-prefixed sub-tasks per the maintainer decision; archive
   WS-RC sub-portfolio plans; update CLAUDE.md/AGENTS.md to
   reflect the unified workstream.

## 2. Dependencies

- WS-RC R0..R5 LANDED (true at v0.31.2). Confirmed via grep of
  CLAUDE.md.
- Lean 4.28.0 toolchain (current).
- elan/lake (current).
- No phase-level prerequisites — SM0 is the entry phase.

## 3. Mathematical foundations relevant to SM0

SM0's deliverables are mostly definitional, but several carry
mathematical content:

### 3.1 Core identifier and platform-parameterized core count

    namespace SeLe4n.Kernel.Concurrency

      /-- Number of cores on the kernel's target platform.
          PlatformBinding-supplied at v1.0.0; defaults to 4 for
          RPi5 BCM2712. -/
      def numCores : Nat := PlatformBinding.coreCount

      /-- Typed core identifier. `Fin numCores` makes every CoreId
          valid by construction; out-of-bounds access is a Lean
          type error, not a runtime check. -/
      abbrev CoreId : Type := Fin numCores

      def bootCoreId : CoreId := PlatformBinding.bootCoreId

      /-- All core ids enumerated via Lean Std `List.finRange`. -/
      def allCores : List CoreId := List.finRange numCores

      theorem numCores_pos : numCores > 0 :=
        PlatformBinding.coreCountPos

      theorem allCores_length : allCores.length = numCores :=
        List.length_finRange numCores

      theorem allCores_nodup : allCores.Nodup :=
        List.nodup_finRange numCores

      theorem bootCoreId_valid : bootCoreId.val < numCores :=
        bootCoreId.isLt

    end SeLe4n.Kernel.Concurrency

### 3.2 LockKind hierarchy (10-level total order)

    namespace SeLe4n.Kernel.Concurrency

      inductive LockKind where
        | objStore         -- the RobinHood hash table (level 0)
        | untyped          -- Untyped memory regions   (level 1)
        | cnode            -- Capability nodes         (level 2)
        | tcb              -- Thread control blocks    (level 3)
        | endpoint         -- IPC endpoints            (level 4)
        | notification     -- Notification objects     (level 5)
        | reply            -- Reply objects            (level 6)
        | schedContext     -- Scheduling contexts      (level 7)
        | vspaceRoot       -- VSpace roots / ASIDs     (level 8)
        | page             -- Page frames              (level 9)
        deriving DecidableEq, Repr

      def LockKind.level : LockKind → Nat
        | .objStore => 0  | .untyped => 1  | .cnode => 2
        | .tcb => 3       | .endpoint => 4 | .notification => 5
        | .reply => 6     | .schedContext => 7
        | .vspaceRoot => 8 | .page => 9

      /-- Strict-monotone: distinct kinds have distinct levels. -/
      theorem LockKind.level_strictMono :
          ∀ k₁ k₂ : LockKind, k₁ ≠ k₂ → k₁.level ≠ k₂.level := by
        intro k₁ k₂ h; cases k₁ <;> cases k₂ <;> simp_all <;> decide

      /-- Surjective: every level 0..9 is attained. -/
      theorem LockKind.level_surjective :
          ∀ n : Nat, n < 10 → ∃ k : LockKind, k.level = n := by
        intro n hn; interval_cases n <;>
          exact ⟨.objStore, rfl⟩ <;>
          -- (10 such existence proofs by case)
          sorry  -- expanded in SM0.I implementation

      /-- Bound: every level is < 10. -/
      theorem LockKind.level_bounded :
          ∀ k : LockKind, k.level < 10 := by
        intro k; cases k <;> decide

    end SeLe4n.Kernel.Concurrency

The `sorry` in `level_surjective` is a place-holder for the
SM0.I implementation; the actual proof is a 10-case `decide`.

### 3.3 LockId and total order

    namespace SeLe4n.Kernel.Concurrency

      structure LockId where
        kind  : LockKind
        objId : ObjId
        deriving DecidableEq, Repr

      /-- Lexicographic order: (kind.level, objId.val). -/
      instance : LE LockId where
        le l₁ l₂ :=
          l₁.kind.level < l₂.kind.level ∨
          (l₁.kind.level = l₂.kind.level ∧ l₁.objId.val ≤ l₂.objId.val)

      instance : LT LockId where
        lt l₁ l₂ := l₁ ≤ l₂ ∧ l₁ ≠ l₂

      /-- The le instance is decidable. -/
      instance (l₁ l₂ : LockId) : Decidable (l₁ ≤ l₂) := by
        unfold instLE; exact inferInstance

      /-- Totality: every pair of LockIds is comparable. -/
      theorem LockId.le_total : ∀ l₁ l₂ : LockId, l₁ ≤ l₂ ∨ l₂ ≤ l₁ := by
        intro l₁ l₂
        by_cases h₁ : l₁.kind.level < l₂.kind.level
        · exact Or.inl (Or.inl h₁)
        · by_cases h₂ : l₂.kind.level < l₁.kind.level
          · exact Or.inr (Or.inl h₂)
          · have hkind : l₁.kind.level = l₂.kind.level :=
              Nat.le_antisymm (Nat.le_of_not_lt h₂) (Nat.le_of_not_lt h₁)
            by_cases hobj : l₁.objId.val ≤ l₂.objId.val
            · exact Or.inl (Or.inr ⟨hkind, hobj⟩)
            · exact Or.inr (Or.inr ⟨hkind.symm, Nat.le_of_not_le hobj⟩)

      /-- Reflexivity. -/
      theorem LockId.le_refl : ∀ l : LockId, l ≤ l := by
        intro l; exact Or.inr ⟨rfl, Nat.le_refl _⟩

      /-- Transitivity. -/
      theorem LockId.le_trans :
          ∀ l₁ l₂ l₃ : LockId, l₁ ≤ l₂ → l₂ ≤ l₃ → l₁ ≤ l₃ := by
        intro l₁ l₂ l₃ h₁ h₂
        -- Case analysis on the disjuncts of each hypothesis (4 cases).
        sorry  -- expanded in SM0.I implementation

      /-- Antisymmetry. -/
      theorem LockId.le_antisymm :
          ∀ l₁ l₂ : LockId, l₁ ≤ l₂ → l₂ ≤ l₁ → l₁ = l₂ := by
        intro l₁ l₂ h₁ h₂
        sorry  -- expanded in SM0.I implementation

    end SeLe4n.Kernel.Concurrency

These four theorems (`le_total`, `le_refl`, `le_trans`,
`le_antisymm`) establish that LockId carries a decidable total
order — the prerequisite for SM3's deadlock-freedom proof
(Theorem 2.1.9).

### 3.4 BklState (legacy, retained as type-system anchor)

    namespace SeLe4n.Kernel.Concurrency

      /-- Big-Kernel-Lock state. Retained at v1.0.0 as a typed
          anchor that distinguishes "kernel is currently being
          entered by core c" (`.held c`) from "kernel is
          quiescent" (`.unheld`). With per-object fine locks
          (SM3), this becomes a coarser monitoring abstraction
          rather than the only atomicity mechanism. -/
      inductive BklState where
        | unheld
        | held (owner : CoreId)
        deriving DecidableEq, Repr, Inhabited

      def bklHeldBy (b : BklState) (c : CoreId) : Prop :=
        b = .held c

      instance (b : BklState) (c : CoreId) : Decidable (bklHeldBy b c) := by
        unfold bklHeldBy; exact inferInstance

      /-- BklState is well-formed iff at most one core holds it. -/
      theorem bklState_unique_owner :
          ∀ (b : BklState) (c₁ c₂ : CoreId),
            b = .held c₁ → b = .held c₂ → c₁ = c₂ := by
        intro b c₁ c₂ h₁ h₂; rw [h₁] at h₂; injection h₂

    end SeLe4n.Kernel.Concurrency

### 3.5 SgiKind

    namespace SeLe4n.Kernel.Concurrency

      /-- ARM GIC-400 SGI INTID allocation. INTIDs 0..15 are
          software-generated interrupts; the kernel reserves 5
          of them. The remaining 11 are available for
          application-layer use via a future capability
          operation (post-1.0). -/
      inductive SgiKind where
        | reschedule         -- INTID 0
        | tlbShootdownReq    -- INTID 1
        | tlbShootdownAck    -- INTID 2
        | cacheBroadcast     -- INTID 3
        | haltAll            -- INTID 4
        deriving DecidableEq, Repr

      def SgiKind.toIntid : SgiKind → Fin 16
        | .reschedule      => ⟨0, by decide⟩
        | .tlbShootdownReq => ⟨1, by decide⟩
        | .tlbShootdownAck => ⟨2, by decide⟩
        | .cacheBroadcast  => ⟨3, by decide⟩
        | .haltAll         => ⟨4, by decide⟩

      /-- Pairwise distinct INTIDs. C(5,2) = 10 inequalities. -/
      theorem SgiKind.toIntid_injective :
          ∀ k₁ k₂ : SgiKind, k₁ ≠ k₂ → k₁.toIntid ≠ k₂.toIntid := by
        intro k₁ k₂ h; cases k₁ <;> cases k₂ <;> simp_all <;> decide

      /-- All 5 INTIDs lie in the SGI range 0..15. -/
      theorem SgiKind.toIntid_in_range :
          ∀ k : SgiKind, k.toIntid.val < 16 := by
        intro k; exact k.toIntid.isLt

    end SeLe4n.Kernel.Concurrency

### 3.6 SharingDomain

    namespace SeLe4n.Kernel.Concurrency

      /-- ARMv8 memory-shareability domain. RPi5's BCM2712 is a
          single-cluster Cortex-A76 SoC: all cores share the
          inner-shareable domain. Cross-cluster (multi-CPU
          cluster) targets like big.LITTLE need the outer-
          shareable domain. PlatformBinding-parameterized. -/
      inductive SharingDomain where
        | inner    -- Inner-shareable (single cluster)
        | outer    -- Outer-shareable (multi-cluster)
        deriving DecidableEq, Repr

      /-- Selecting the right DSB barrier kind. -/
      def dsbForSharing (d : SharingDomain) : BarrierKind :=
        match d with
        | .inner => .dsbIsh
        | .outer => .dsbOsh

      /-- Selecting the right store-only DSB barrier kind. -/
      def dsbStForSharing (d : SharingDomain) : BarrierKind :=
        match d with
        | .inner => .dsbIshst
        | .outer => .dsbOshst

    end SeLe4n.Kernel.Concurrency

### 3.7 ArchAssumption extension (the SMP-H2 closure)

    namespace SeLe4n.Kernel.Architecture

      /-- Extended to 6 constructors at SM0. The new
          `singleCoreOperation` constructor anchors AN12-B's
          inventory entry #7 (which previously referred to a
          non-existent ArchAssumption case — SMP-H2). -/
      inductive ArchAssumption where
        | deterministicTimerProgress
        | deterministicRegisterContext
        | memoryAccessSafety
        | bootObjectTyping
        | irqRoutingTotality
        | singleCoreOperation    -- NEW: AN12-B inventory anchor
        deriving Repr, DecidableEq

      def assumptionInventory : List ArchAssumption :=
        [ .deterministicTimerProgress
        , .deterministicRegisterContext
        , .memoryAccessSafety
        , .bootObjectTyping
        , .irqRoutingTotality
        , .singleCoreOperation ]

      theorem assumptionInventory_count :
          assumptionInventory.length = 6 := by decide

      /-- Updated mapping: 6 architectures-assumptions to consumer theorems. -/
      def archAssumptionConsumer : ArchAssumption → Lean.Name
        | .deterministicTimerProgress =>
            `SeLe4n.Kernel.Architecture.deterministicTimerProgress_consumed_by_advanceTimer
        | .deterministicRegisterContext =>
            `SeLe4n.Kernel.Architecture.deterministicRegisterContext_consumed_by_writeRegister
        | .memoryAccessSafety =>
            `SeLe4n.Kernel.Architecture.memoryAccessSafety_consumed_by_readMemory
        | .bootObjectTyping =>
            `SeLe4n.Kernel.Architecture.default_system_state_proofLayerInvariantBundle
        | .irqRoutingTotality =>
            `SeLe4n.Platform.Boot.bootFromPlatformChecked_ok_implies_irqHandlersValid
        | .singleCoreOperation =>
            `SeLe4n.Kernel.bootFromPlatform_singleCore_witness

      theorem architecture_assumptions_index_total_6 :
          ∀ a : ArchAssumption, ∃ n : Lean.Name, archAssumptionConsumer a = n := by
        intro a; cases a <;> exact ⟨_, rfl⟩

      /-- C(6,2) = 15 pairwise inequalities. -/
      theorem archAssumptionConsumer_distinct_6 :
          (List.range 6).Pairwise (fun i j => i ≠ j →
            archAssumptionConsumer (Fin.mk i (by decide) : Fin 6).castSucc.toNat
            ≠ archAssumptionConsumer ...) := by
        sorry  -- expanded inline in SM0.B implementation

    end SeLe4n.Kernel.Architecture

The pairwise-distinctness theorem expands to 15 concrete
inequalities, all proven by `decide`.

## 4. Architectural choices for SM0

### 4.1 Why a separate `Concurrency/` namespace

CLAUDE.md's source layout already includes `SeLe4n/Kernel/Concurrency/`
with `Assumptions.lean` as the single existing module (AN12-B
inventory). SM0 populates the namespace with the typed primitives
that WS-SM relies on: `Types.lean` (CoreId, LockKind, LockId),
`Locks.lean` (BklState, lock-state primitives), `Sgi.lean`
(SgiKind), `Anchors.lean` (build-time inventory checks).

Keeping these in a dedicated namespace:
- Centralizes the SMP-specific types so future maintainers can
  find them without cross-subsystem grep.
- Lets the `Platform.Staged` build anchor sweep the whole
  namespace as one unit (already used by AN12-B inventory).
- Avoids polluting `Prelude.lean` (which is import-cheap and
  should stay so).

### 4.2 Why typeclass extension for PlatformBinding

The maintainer-decided parameterization (decision #5) requires
`numCores`, `bootCoreId`, `sharingDomain` to come from a
`PlatformBinding` instance. SM0 introduces the field schema:

    class PlatformBinding where
      ...                                       -- existing fields
      coreCount      : Nat
      coreCountPos   : coreCount > 0
      bootCoreId     : Fin coreCount
      sharingDomain  : SharingDomain

with RPi5 sets `coreCount := 4`, `bootCoreId := ⟨0, by decide⟩`,
`sharingDomain := .inner`; Sim instance(s) set similarly with
`coreCount := 1` (single-core simulator) or `coreCount := 4`
(SMP sim).

### 4.3 Spread-across-PRs discipline

Decision #9 ("spread across many small PRs") means SM0's ~21
sub-tasks landed in a single coherent cut at v0.31.3 (the maintainer redirected from the originally-planned ~18-PR spread once integration testing confirmed the SM0 closure was internally consistent). The
ordering is:
1. **Documentation honesty patches** first (low risk; no code
   change): SM0.J (dev_history refs), SM0.K (WS-V references),
   SM0.L (DEFERRED.md rewrite), SM0.P (CLAUDE.md/AGENTS.md),
   SM0.Q + Q.1 + Q.2 (WS-RC merge).
2. **Foundational types** next (small surface; pure additions):
   SM0.E (CoreId), SM0.F (SharingDomain), SM0.H (SgiKind),
   SM0.I (LockKind + LockId).
3. **AN12-B inventory hardening** third (builds on types): SM0.A
   (singleCoreOperation), SM0.B (inventory extension), SM0.C
   (Anchors), SM0.D (NoDup).
4. **PlatformBinding extension** fourth: SM0.G.
5. **Structural fixes** fifth: SM0.M (.smp_stacks zero), SM0.N
   (TPIDR_EL1 setup), SM0.O (MAX_SECONDARY_CORES param).
6. **Testing infrastructure** last: SM0.S (foundations suite),
   SM0.T (tier-4 SMP bootcheck stub), SM0.R (codebase_map),
   SM0.U (CHANGELOG per PR).

Each PR is independently reviewable, has its own acceptance
criteria, and can be reverted without affecting the rest.

## 5. Detailed sub-task breakdown

SM0 landed at `v0.31.3`. The sub-tasks it carried, in the groups it ran
them in; what each cut changed is in [`CHANGELOG.md`](../../CHANGELOG.md).

| Group | Sub | Scope |
|-------|-----|-------|
| Documentation honesty patches (Group 1) | SM0.J | Repoint dev_history cross-references |
| Documentation honesty patches (Group 1) | SM0.K | Update "deferred to WS-V" claims |
| Documentation honesty patches (Group 1) | SM0.L | Rewrite DEFERRED.md::DEF-R-HAL-L20 disposition |
| Documentation honesty patches (Group 1) | SM0.P | Update CLAUDE.md/AGENTS.md workstream context |
| Documentation honesty patches (Group 1) | SM0.Q | Merge WS-RC remainder into WS-SM |
| Documentation honesty patches (Group 1) | SM0.Q.1 | Per-phase absorption mapping |
| Documentation honesty patches (Group 1) | SM0.Q.2 | Archive WS-RC sub-portfolio plans |
| Foundational types (Group 2) | SM0.E | Define `CoreId := Fin numCores` + enumeration |
| Foundational types (Group 2) | SM0.F | Define `SharingDomain` |
| Foundational types (Group 2) | SM0.G | PlatformBinding extension |
| Foundational types (Group 2) | SM0.H | Define `SgiKind` |
| Foundational types (Group 2) | SM0.I | Define `LockKind` + `LockId` + total order |
| AN12-B inventory hardening (Group 3) | SM0.A | Add `singleCoreOperation` to ArchAssumption |
| AN12-B inventory hardening (Group 3) | SM0.B | Extend inventory + consumer map + distinctness |
| AN12-B inventory hardening (Group 3) | SM0.C | `Concurrency/Anchors.lean` with `@`-references |
| AN12-B inventory hardening (Group 3) | SM0.D | Inventory NoDup witness |
| Structural fixes (Group 4) | SM0.M | Zero `.smp_stacks` at boot |
| Structural fixes (Group 4) | SM0.N | Set TPIDR_EL1 in `secondary_entry` |
| Structural fixes (Group 4) | SM0.O | MAX_SECONDARY_CORES parameterization |
| Testing infrastructure (Group 5) | SM0.S | `tests/SmpFoundationsSuite.lean` |
| Testing infrastructure (Group 5) | SM0.T | Tier-4 SMP boot-check script stub |
| Testing infrastructure (Group 5) | SM0.R | Update `docs/codebase_map.json` |
| Testing infrastructure (Group 5) | SM0.U | CHANGELOG entries per SM0 PR |

## [v0.31.3] - 2026-05-15 — WS-SM Phase SM0 closure

Phase SM0 (Foundations & honesty patches) closes. 21 sub-tasks
landed in a single coherent cut at v0.31.3 (compressed from the
originally-planned v0.32.0..v0.32.x ~18-PR spread per maintainer
redirection):

- 5 honesty patches: dev_history cross-references repointed,
  WS-V deferral claims updated, DEF-R-HAL-L20 disposition
  rewritten, CLAUDE.md/AGENTS.md WS-SM context, WS-RC merge.
- 6 foundational types: CoreId, SharingDomain, PlatformBinding
  extension, SgiKind, LockKind + LockId.
- 4 AN12-B inventory hardening: singleCoreOperation
  constructor, inventory + consumer + distinctness extension,
  Anchors module, NoDup witness.
- 3 structural fixes: .smp_stacks zero, TPIDR_EL1 setup,
  MAX_SECONDARY_CORES param.
- 3 testing infrastructure: SmpFoundationsSuite, tier-4 stub,
  codebase_map regen.

Tier 0..3 green. AN12-B inventory now bound to actual
sourceTheorems via Anchors module (SMP-H3 closed). Single-core
boot path unchanged.

Refs: docs/planning/SMP_FOUNDATIONS_PLAN.md
```

**Acceptance**:
- Every PR has its own dated CHANGELOG entry.
- The aggregate SM0 closure entry summarizes the phase.

**Size**: T per PR; M for the aggregate.

## 6. Verification strategy for SM0

### 6.1 What SM0 proves

| Property | Theorem | Location |
|----------|---------|----------|
| numCores > 0 | `numCores_pos` | `Concurrency/Types.lean` |
| allCores enumerates all cores | `allCores_length`, `allCores_nodup` | `Concurrency/Types.lean` |
| bootCoreId is valid | `bootCoreId_valid` | `Concurrency/Types.lean` |
| LockKind levels are strict-mono | `level_strictMono` | `Concurrency/Locks/Kind.lean` |
| LockKind levels are surjective | `level_surjective` | `Concurrency/Locks/Kind.lean` |
| LockKind levels are bounded | `level_bounded` | `Concurrency/Locks/Kind.lean` |
| LockId order is total | `LockId.le_total` | `Concurrency/Locks/Kind.lean` |
| LockId order is transitive | `LockId.le_trans` | `Concurrency/Locks/Kind.lean` |
| LockId order is antisymmetric | `LockId.le_antisymm` | `Concurrency/Locks/Kind.lean` |
| SGI INTIDs are pairwise distinct | `SgiKind.toIntid_injective` | `Concurrency/Sgi.lean` |
| SGI INTIDs are in 0..15 | `SgiKind.toIntid_in_range` | `Concurrency/Sgi.lean` |
| ArchAssumption has 6 cases | `assumptionInventory_count` | `Architecture/Assumptions.lean` |
| ArchAssumption consumers are distinct | `archAssumptionConsumer_distinct_6` | `Architecture/Assumptions.lean` |
| AN12-B inventory IDs are NoDup | `smpLatentInventory_identifiers_nodup` | `Concurrency/Assumptions.lean` |
| AN12-B references resolve | (compile-time anchor) | `Concurrency/Anchors.lean` |
| BklState unique owner | `bklState_unique_owner` | `Concurrency/Locks.lean` |

Total: ~16 substantive theorems.

### 6.2 What SM0 assumes

- ARMv8-A MPIDR_EL1 layout (cited ARM ARM D17.2.98) — used by
  SM0.N's TPIDR_EL1 setup.
- Lean Std `List.finRange` length/Nodup theorems — used by
  SM0.E. These are themselves proven in Lean Std.

No new Lean axioms.

### 6.3 Testing

- **Tier 0 (hygiene)**: `scripts/test_tier0_hygiene.sh` runs
  unchanged; verifies SM0 doesn't introduce `sorry`, `axiom`,
  or `native_decide` (it shouldn't — all theorems are
  decidable).
- **Tier 1 (build)**: `lake build` on the SM0 modules.
- **Tier 2 (trace)**: SM0 doesn't change runtime behavior; the
  existing `main_trace_smoke.expected` fixture stays
  byte-identical.
- **Tier 3 (invariant)**: New `tests/SmpFoundationsSuite.lean`
  with `#check` of all SM0 public symbols + decidable examples.
- **Tier 4 (nightly)**: Stub script committed; populated
  starting in SM1.H.

## 7. Risk inventory for SM0

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| `level_surjective` proof has a missed case | LOW | LOW | `interval_cases` covers all 10 inductively |
| `LockId.le_trans` case analysis missed disjunct | LOW | MED (forces re-prove) | 4 cases; each verified independently |
| `Concurrency/Anchors.lean` import graph balloons | MED | LOW (longer build time) | Import surface is reviewed in PR; minimize transitive imports |
| `.smp_stacks` zero loop has off-by-one | LOW | HIGH (boot corruption) | QEMU smoke test post-zeroing |
| TPIDR_EL1 setup conflicts with boot core's own setup | LOW | HIGH (lost identity) | SM0.N sets TPIDR_EL1 on every core including boot |
| WS-RC absorption mapping incomplete | MED | MED | SM0.Q.1 review each R-phase against actual SM-phases |
| CHANGELOG entries inconsistent across many small PRs | MED | LOW | Aggregate SM0 closure entry captures the full story |
| Sim platform binding instances diverge | LOW | LOW | SM0.G updates all sim instances in one PR |

## 8. Cross-references

- **Master overview**:
  [`SMP_MULTICORE_COMPLETION_PLAN.md`](SMP_MULTICORE_COMPLETION_PLAN.md)
- **Next phase (Rust HAL)**:
  [`SMP_RUST_HAL_PLAN.md`](SMP_RUST_HAL_PLAN.md) — depends on
  SM0.G (PlatformBinding extension), SM0.N (TPIDR_EL1 setup).
- **Verified lock primitives**:
  [`SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md`](SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md)
  — depends on SM0.E (CoreId), SM0.I (LockKind, LockId).
- **Per-core state**:
  [`SMP_PER_CORE_STATE_PLAN.md`](SMP_PER_CORE_STATE_PLAN.md) —
  depends on SM0.E, SM0.G.

## 9. Acceptance gate for SM0

SM0 is complete when:

- [ ] All 21 sub-tasks landed across ~18 PRs.
- [ ] Tier 0..3 tests green at HEAD.
- [ ] No production-source `dev_history/` cross-references.
- [ ] No "deferred to WS-V" SMP-context claims remain.
- [ ] `ArchAssumption` has 6 constructors with full inventory
      machinery.
- [ ] `AN12-B inventory` build-anchored via `Concurrency/Anchors.lean`.
- [ ] `CoreId`, `LockKind`, `LockId`, `SgiKind`, `SharingDomain`,
      `BklState` types defined and theorem-bearing.
- [ ] `PlatformBinding` typeclass extended; RPi5 + Sim
      instances updated.
- [ ] `.smp_stacks` zeroed at boot; `TPIDR_EL1` set on
      `secondary_entry`.
- [ ] CLAUDE.md / AGENTS.md reflect WS-SM as active workstream.
- [ ] WS-RC R6..R14 absorption mapping documented in
      `AUDIT_v0.30.11_WORKSTREAM_PLAN.md` §15.
- [ ] WS-RC sub-portfolio plans (R4 closeout, R5 deferred)
      archived to `docs/dev_history/audits/`.
- [ ] `tests/SmpFoundationsSuite.lean` runs in tier-3.
- [ ] `scripts/test_tier4_smp_bootcheck.sh` stub committed.
- [ ] `docs/codebase_map.json` regenerated.
- [ ] CHANGELOG entries per PR + aggregate SM0 closure entry.
- [ ] `docs/spec/SELE4N_SPEC.md`, `docs/DEVELOPMENT.md`,
      `docs/gitbook/01-project-overview.md`,
      `docs/hardware_validation/speculation_barriers.md`
      updated for WS-SM context.

## 10. Theorem catalogue for SM0

The 16 substantive theorems SM0 introduces (consolidated for
the master-plan theorem-catalogue index):

| Theorem | Statement | File |
|---------|-----------|------|
| `numCores_pos` | `numCores > 0` | `Concurrency/Types.lean` |
| `allCores_length` | `allCores.length = numCores` | `Concurrency/Types.lean` |
| `allCores_nodup` | `allCores.Nodup` | `Concurrency/Types.lean` |
| `bootCoreId_valid` | `bootCoreId.val < numCores` | `Concurrency/Types.lean` |
| `LockKind.level_strictMono` | `∀ k₁ k₂, k₁ ≠ k₂ → k₁.level ≠ k₂.level` | `Concurrency/Locks/Kind.lean` |
| `LockKind.level_surjective` | `∀ n < 10, ∃ k, k.level = n` | `Concurrency/Locks/Kind.lean` |
| `LockKind.level_bounded` | `∀ k, k.level < 10` | `Concurrency/Locks/Kind.lean` |
| `LockId.le_total` | `∀ l₁ l₂, l₁ ≤ l₂ ∨ l₂ ≤ l₁` | `Concurrency/Locks/Kind.lean` |
| `LockId.le_refl` | `∀ l, l ≤ l` | `Concurrency/Locks/Kind.lean` |
| `LockId.le_trans` | `∀ l₁ l₂ l₃, l₁ ≤ l₂ → l₂ ≤ l₃ → l₁ ≤ l₃` | `Concurrency/Locks/Kind.lean` |
| `LockId.le_antisymm` | `∀ l₁ l₂, l₁ ≤ l₂ → l₂ ≤ l₁ → l₁ = l₂` | `Concurrency/Locks/Kind.lean` |
| `SgiKind.toIntid_injective` | Pairwise distinct INTIDs | `Concurrency/Sgi.lean` |
| `SgiKind.toIntid_in_range` | All INTIDs < 16 | `Concurrency/Sgi.lean` |
| `assumptionInventory_count` | Inventory has 6 entries | `Architecture/Assumptions.lean` |
| `architecture_assumptions_index_total_6` | Mapping is total over 6 cases | `Architecture/Assumptions.lean` |
| `archAssumptionConsumer_distinct_6` | 15 pairwise inequalities | `Architecture/Assumptions.lean` |
| `smpLatentInventory_identifiers_nodup` | AN12-B IDs are NoDup | `Concurrency/Assumptions.lean` |
| `bklState_unique_owner` | BklState has unique owner | `Concurrency/Locks.lean` |

(The `Concurrency/Anchors.lean` build-time `@`-references are not
theorems but build-time anchors; they appear in
`tests/SmpFoundationsSuite.lean` for tier-3 surface anchoring.)

## Appendix A — Verification commands

```bash
# Tier 0..3 (will be green post-SM0):
./scripts/test_tier0_hygiene.sh
./scripts/test_fast.sh
./scripts/test_smoke.sh
./scripts/test_full.sh

# Per-module build:
source ~/.elan/env
lake build SeLe4n.Kernel.Concurrency.Types
lake build SeLe4n.Kernel.Concurrency.Locks.Kind
lake build SeLe4n.Kernel.Concurrency.Sgi
lake build SeLe4n.Kernel.Concurrency.Anchors
lake build SmpFoundationsSuite

# Verify honesty patches:
grep -rn "dev_history" rust/sele4n-hal/src/ SeLe4n/Kernel/ || echo "OK: no dev_history refs"
grep -rn "deferred to WS-V" docs/spec/ docs/DEVELOPMENT.md docs/gitbook/ || echo "OK: no stale WS-V refs"

# Verify foundational types:
echo '#check @SeLe4n.Kernel.Concurrency.CoreId' | lake env lean --stdin
echo '#check @SeLe4n.Kernel.Concurrency.LockKind' | lake env lean --stdin

# Verify .smp_stacks zeroing (QEMU smoke test):
qemu-system-aarch64 -M virt -smp 4 -m 1G \
  -kernel target/aarch64-unknown-none/release/sele4n \
  -nographic -d guest_errors 2>&1 | grep -i "stack" || echo "OK: no stack errors"

# Verify TPIDR_EL1 setup (cargo test):
cargo test -p sele4n-hal --lib tpidr
```

## Appendix B — PR description template

Each SM0 PR uses the following template:

```
sm0(<letter>): <one-line summary>

<2-3 sentence motivation: what gap / finding / decision drives
this PR; reference SMP-Cx / SMP-Hx / SMP-Mx / SMP-Lx finding ID
or the maintainer decision number.>

<Specific changes:>
- <file:line>: <change>
- <file:line>: <change>
- ...

<Theorems added / migrated / retired:>
- `<theorem name>` — <one-line statement> — proven by <method>.

<Acceptance:>
- `lake build <module>` green.
- `<test suite>` runs and passes.
- <other concrete verification commands>.

Refs: docs/planning/SMP_FOUNDATIONS_PLAN.md SM0.<letter>
```

## Appendix C — Sub-task dependency graph

```
SM0.J (dev_history refs)     ⟶  independent
SM0.K (WS-V claims)          ⟶  independent
SM0.L (DEFERRED.md rewrite)  ⟶  independent
SM0.P (CLAUDE.md/AGENTS.md)  ⟶  independent
SM0.Q (WS-RC merge)          ⟶  needs SM0.P
SM0.Q.1 (absorption mapping) ⟶  needs SM0.Q
SM0.Q.2 (archive plans)      ⟶  needs SM0.Q.1

SM0.E (CoreId)               ⟶  needs SM0.G (for PlatformBinding.coreCount)
SM0.F (SharingDomain)        ⟶  needs SM0.G (for PlatformBinding.sharingDomain)
SM0.G (PlatformBinding ext)  ⟶  independent (can land first)
SM0.H (SgiKind)              ⟶  independent
SM0.I (LockKind, LockId)     ⟶  independent

SM0.A (singleCoreOp ctor)    ⟶  needs SM0.G (depends on platform binding fields no, actually independent)
SM0.B (inventory extension)  ⟶  needs SM0.A
SM0.C (Anchors)              ⟶  needs SM0.A, SM0.B
SM0.D (NoDup witness)        ⟶  independent (purely on existing inventory)

SM0.M (.smp_stacks zero)     ⟶  independent (assembly + linker)
SM0.N (TPIDR_EL1)            ⟶  needs SM0.M (linker symbol ordering)
SM0.O (MAX_SECONDARY param)  ⟶  independent

SM0.S (FoundationsSuite)     ⟶  needs SM0.E, SM0.F, SM0.H, SM0.I, SM0.A, SM0.C
SM0.T (tier-4 stub)          ⟶  independent
SM0.R (codebase_map)         ⟶  needs SM0.S (and any new modules)
SM0.U (CHANGELOG per PR)     ⟶  per-PR
```

Critical path: SM0.G → SM0.E → SM0.S → SM0.R.

The graph admits substantial parallelism — many sub-tasks
(SM0.J, SM0.K, SM0.L, SM0.D, SM0.H, SM0.I, SM0.M, SM0.O, SM0.T)
are independent and can land in any order.

## Appendix D — File-by-file impact

| File | Sub-tasks touching | Net LoC change |
|------|--------------------|----------------:|
| `SeLe4n/Kernel/Concurrency/Types.lean` (NEW) | SM0.E, SM0.F | +110 |
| `SeLe4n/Kernel/Concurrency/Locks/Kind.lean` (NEW) | SM0.I | +150 |
| `SeLe4n/Kernel/Concurrency/Sgi.lean` (NEW) | SM0.H | +50 |
| `SeLe4n/Kernel/Concurrency/Anchors.lean` (NEW) | SM0.C | +50 |
| `SeLe4n/Kernel/Concurrency/Assumptions.lean` (existing) | SM0.D | +15 |
| `SeLe4n/Kernel/Architecture/Assumptions.lean` (existing) | SM0.A, SM0.B, SM0.J | +80 / -10 |
| `SeLe4n/Kernel/CrossSubsystem.lean` (existing) | SM0.J | +5 / -5 |
| `SeLe4n/Platform/Contract.lean` (existing) | SM0.G | +20 |
| `SeLe4n/Platform/RPi5/Contract.lean` (existing) | SM0.G | +10 |
| `SeLe4n/Platform/Sim/*.lean` (existing) | SM0.G | +10 per instance |
| `SeLe4n/Platform/Staged.lean` (existing) | SM0.C | +1 |
| `rust/sele4n-hal/src/boot.S` (existing) | SM0.J, SM0.M, SM0.N | +30 / -5 |
| `rust/sele4n-hal/src/smp.rs` (existing) | SM0.N, SM0.O | +80 |
| `rust/sele4n-hal/link.ld` (existing) | SM0.M | +5 |
| `tests/SmpFoundationsSuite.lean` (NEW) | SM0.S | +150 |
| `scripts/test_tier4_smp_bootcheck.sh` (NEW) | SM0.T | +15 |
| `docs/spec/SELE4N_SPEC.md` (existing) | SM0.K | +20 / -10 |
| `docs/DEVELOPMENT.md` (existing) | SM0.K | +5 / -2 |
| `docs/gitbook/01-project-overview.md` (existing) | SM0.K | +5 / -2 |
| `docs/hardware_validation/speculation_barriers.md` (existing) | SM0.K | +5 / -3 |
| `docs/dev_history/audits/AUDIT_v0.29.0_DEFERRED.md` (existing) | SM0.L | +30 / -5 |
| `CLAUDE.md` (existing) | SM0.P | +100 / -200 (replaces WS-RC section) |
| `AGENTS.md` (existing) | SM0.P | mirror of CLAUDE.md |
| `docs/audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md` (existing) | SM0.Q, SM0.Q.1 | +300 / -50 |
| `docs/audits/WS_RC_R4_CLOSEOUT_PLAN.md` (move) | SM0.Q.2 | (move) |
| `docs/audits/WS_RC_R5_DEFERRED_COMPLETION_PLAN.md` (move) | SM0.Q.2 | (move) |
| `docs/codebase_map.json` (existing) | SM0.R | (regen) |
| `CHANGELOG.md` (existing) | SM0.U | +50 (per-PR entries + aggregate) |

**Total LoC change**: ~1,500 LoC added; ~500 LoC removed/moved.

---

*SM0 is the lightest WS-SM phase by LoC but the highest in
**organizational** weight: every WS-SM sub-task that follows
references the foundational types defined here, and the merge
of WS-RC into WS-SM happens here. The phase is intentionally
spread across ~18 small PRs (decision #9) so each landing is
independently reviewable.*
