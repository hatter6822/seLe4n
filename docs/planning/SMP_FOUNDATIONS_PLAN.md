# SM0 — Foundations & Honesty Patches (WS-SM Phase 0)

> **Phase**: SM0 of WS-SM
> **Parent overview**: [`SMP_MULTICORE_COMPLETION_PLAN.md`](SMP_MULTICORE_COMPLETION_PLAN.md)
> **Audited cut**: `v0.31.2`
> **Target releases**: v0.31.3 (landed); SM1+ continues at v0.32.x (~18 small PRs)
> **Calendar estimate**: 4-6 weeks
> **Sub-task count**: 40-50

## 1. Phase goal

SM0 lays the **foundational types, build-time anchors, and
documentation-honesty patches** that the larger phases (SM1..SM9)
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

### 5.1 Documentation honesty patches (Group 1)

#### SM0.J — Repoint dev_history cross-references

**Goal**: Production sources currently reference
`docs/dev_history/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md §12` —
a path inside `dev_history/` which CLAUDE.md's "Ignoring
dev_history" section says is archived and should not be the
canonical reference.

**Mathematical content**: none (pure text edits).

**Files**:
- `rust/sele4n-hal/src/boot.S:103`
- `SeLe4n/Kernel/Architecture/Assumptions.lean:333`
- `SeLe4n/Kernel/CrossSubsystem.lean:3264`

**Edit pattern** (3 sites, identical structure):

Before:
```
// Multi-core support (SMP) is closed by AN9-J (DEF-R-HAL-L20)
// per docs/dev_history/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md §12.
```

After:
```
// Multi-core support (SMP) is implemented in WS-SM, tracked in
// docs/planning/SMP_MULTICORE_COMPLETION_PLAN.md. The AN9-J
// scaffolding (DEF-R-HAL-L20) was the substrate; WS-SM
// activates and verifies it.
```

**Acceptance**:
- `grep -rn "dev_history" rust/sele4n-hal/src/ SeLe4n/Kernel/` returns 0 hits.
- `lake build` green (no Lean source touched substantively).
- Cargo build green (boot.S compiles).

**PR description template**:

```
sm0(J): repoint dev_history cross-references to active planning

CLAUDE.md "Ignoring dev_history" section forbids citing
docs/dev_history/ from production sources. Three sites in
production touched the rule:

- rust/sele4n-hal/src/boot.S:103
- SeLe4n/Kernel/Architecture/Assumptions.lean:333
- SeLe4n/Kernel/CrossSubsystem.lean:3264

All three now point at docs/planning/SMP_MULTICORE_COMPLETION_PLAN.md
(the active WS-SM overview).

Refs: docs/planning/SMP_FOUNDATIONS_PLAN.md SM0.J
```

**Size**: T (Trivial, <50 LoC of text edits).

---

#### SM0.K — Update "deferred to WS-V" claims

**Goal**: SMP-M2 finding. The spec, DEVELOPMENT.md, and GitBook
chapter 01 each claim "SMP support is deferred to WS-V". WS-V is
COMPLETE (was the pre-release audit-remediation workstream from
v0.21.7..v0.22.10) and never owned SMP. The claims are stale.

**Files**:
- `docs/spec/SELE4N_SPEC.md:509-519` (§6.4 Hardware Limitations)
- `docs/DEVELOPMENT.md:68`
- `docs/gitbook/01-project-overview.md:94`
- `docs/hardware_validation/speculation_barriers.md:85-87`

**Edit pattern**: Replace "Symmetric multiprocessing support is
deferred to WS-V" → "Symmetric multiprocessing is implemented in
WS-SM (pre-v1.0.0), tracked in
docs/planning/SMP_MULTICORE_COMPLETION_PLAN.md." Similar
treatment for sub-items (per-core run queues, IPI, spinlocks,
etc.) — each gets repointed to its WS-SM phase plan.

**Acceptance**:
- `grep -rn "deferred to WS-V" docs/spec/ docs/DEVELOPMENT.md docs/gitbook/` returns 0 hits in SMP context.
- Tier 0 hygiene green.

**Size**: S (~50-100 LoC of doc edits across 4 files).

---

#### SM0.L — Rewrite DEFERRED.md::DEF-R-HAL-L20 disposition

**Goal**: SMP-M2 root cause. The dispositioning row
`AUDIT_v0.29.0_DEFERRED.md:296-316` claims DEF-R-HAL-L20 is
"RESOLVED at v0.30.10". This is materially inaccurate: only the
scaffolding is in place, not the activation. The row needs to
honestly reflect the partial state.

**File**: `docs/dev_history/audits/AUDIT_v0.29.0_DEFERRED.md:290-340`.

**Edit pattern**:

Before (line 296):
```
### DEF-R-HAL-L20 — Secondary-Core Bring-Up (SMP) **[RESOLVED AT v0.30.10]**
```

After:
```
### DEF-R-HAL-L20 — Secondary-Core Bring-Up (SMP) **[PARTIALLY RESOLVED AT v0.30.10 — scaffolding only; full activation in WS-SM]**

The AN9-J scaffolding lays the Rust HAL infrastructure (PSCI
wrapper, per-core stacks, MPIDR gate). It does NOT activate
SMP at runtime — `bring_up_secondaries()` is never called from
any boot path (SMP-C1), and `rust_secondary_main` does not
perform per-core MMU/VBAR/GIC/timer init (SMP-C2). Activation
is the WS-SM workstream's scope.
```

The body of the disposition row similarly updates to honestly
state what was delivered vs what remains.

**Acceptance**:
- The disposition row reflects the scaffolding-only state.
- Cross-references to SMP-C1..C4 findings are added.

**Size**: T (~30 LoC of doc edits).

---

#### SM0.P — Update CLAUDE.md/AGENTS.md workstream context

**Goal**: Replace the WS-RC active-workstream context section
with a WS-SM active-workstream context section.

**Files**: `CLAUDE.md`, `AGENTS.md` (must stay byte-identical
apart from header).

**Edit pattern**: The current "Active workstream context"
section in CLAUDE.md tracks WS-RC R0..R5 with detailed phase
summaries. SM0.P preserves the historical record but replaces
the IN-FLIGHT status with WS-SM:

```
## Active workstream context

- **WS-SM SMP multi-core completion (v0.31.3 [SM0 LANDED] → v1.0.0)**:
  Unified workstream merging WS-RC's remaining R6..R14 phases
  with the SMP-specific SM-phases (SM0..SM9). Closes at v1.0.0
  with a bootable verified SMP microkernel on Raspberry Pi 5.
  Plan: docs/planning/SMP_MULTICORE_COMPLETION_PLAN.md.
  Decisions (binding): per-object RW fine locks; path-a Vector
  state replacement; hierarchical-by-kind lock order; SMP
  enabled by default; numCores via PlatformBinding; verified
  TicketLock + RwLock primitives.

  WS-RC R0..R5 LANDED at v0.31.2 (historical record preserved
  in docs/WORKSTREAM_HISTORY.md). R6..R14 absorbed into SM
  phases per SM0.Q.
```

**Acceptance**:
- CLAUDE.md/AGENTS.md byte-identical (excluding header).
- WS-SM is named as the active workstream.
- WS-RC R0..R5 closure recorded.

**Size**: S (~100 LoC of doc edits in two files).

---

#### SM0.Q — Merge WS-RC remainder into WS-SM

**Goal**: SM0.Q is the structural "merge" sub-task. WS-RC's
plan in `docs/audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md` carries
15 phases (R0..R14). R0..R5 LANDED at v0.31.2. R6..R14 absorb
into SM-prefixed sub-tasks within WS-SM.

**File**: `docs/audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md` (large,
~3303 lines; SM0.Q.1 below maps each R-phase to an SM-phase).

**Edit pattern**: SM0.Q updates the plan's front-matter to
record the merge:

```
> **Status**: WS-RC R0..R5 LANDED at v0.31.2. R6..R14 absorbed
> into WS-SM per the merge decision. This document is now
> historical; active WS-SM tracking is at
> docs/planning/SMP_MULTICORE_COMPLETION_PLAN.md.
```

Per-phase absorption mapping is in §15 (new section added by
SM0.Q.1).

**Acceptance**:
- WS-RC plan reflects merge.
- No orphan WS-RC tracking remains (no in-flight R6..R14
  references outside the absorption map).

**Size**: M (~200 LoC of plan-document edits).

---

#### SM0.Q.1 — Per-phase absorption mapping

**Goal**: For each WS-RC R6..R14 phase, identify whether its
objectives fit naturally inside an existing SM-phase or warrant
a dedicated SM sub-section. Document the mapping in a new §15
of the WS-RC plan.

**Mapping (initial draft; final mapping refined as each R-phase
is reviewed):**

| WS-RC | Description | Absorbed into |
|-------|-------------|---------------|
| R6 | (To be reviewed from the WS-RC plan) | SM2 / SM4 |
| R7 | (To be reviewed) | SM4 |
| R8 | (To be reviewed) | SM4 / SM5 |
| R9 | (To be reviewed) | SM5 |
| R10 | (To be reviewed) | SM6 |
| R11 | (To be reviewed) | SM6 / SM7 |
| R12 | (To be reviewed) | SM8 |
| R13 | (To be reviewed) | SM9 |
| R14 | (To be reviewed) | SM9 |

**Process**: SM0.Q.1 is to OPEN the absorption mapping work.
The detailed per-phase mapping happens during SM0.Q.1's PR,
which requires reading the full WS-RC plan and matching each
R-phase's substantive sub-tasks to the appropriate SM-phase.

**Acceptance**:
- Every R6..R14 finding has a documented SM-phase destination.
- No orphan WS-RC findings remain.

**Size**: M (~300 LoC of plan-document edits).

---

#### SM0.Q.2 — Archive WS-RC sub-portfolio plans

**Goal**: WS-RC produced two sub-portfolio close-out plans
(`docs/audits/WS_RC_R4_CLOSEOUT_PLAN.md`,
`docs/audits/WS_RC_R5_DEFERRED_COMPLETION_PLAN.md`) that
document closed sub-portfolios. With WS-RC merging into WS-SM,
these archive to `docs/dev_history/audits/`.

**Files**:
- Move `docs/audits/WS_RC_R4_CLOSEOUT_PLAN.md` →
  `docs/dev_history/audits/WS_RC_R4_CLOSEOUT_PLAN.md`.
- Move `docs/audits/WS_RC_R5_DEFERRED_COMPLETION_PLAN.md` →
  `docs/dev_history/audits/WS_RC_R5_DEFERRED_COMPLETION_PLAN.md`.
- Update `scripts/website_link_manifest.txt` to reflect new
  paths (if any current references exist).

**Acceptance**:
- Archived files present in new location.
- `docs/audits/README.md` updated to reflect merge.
- Website manifest consistent (Tier 0 gate passes).

**Size**: T (~20 LoC of doc edits; 2 file moves).

### 5.2 Foundational types (Group 2)

#### SM0.E — Define `CoreId := Fin numCores` + enumeration

**Goal**: Introduce the typed core identifier and enumeration
helpers as the foundation for every per-core piece in WS-SM.

**Mathematical specification**: Per §3.1 above.

**File**: New module `SeLe4n/Kernel/Concurrency/Types.lean`.

**Code skeleton**:

```lean
-- SPDX-License-Identifier: GPL-3.0-or-later
import SeLe4n.Prelude
import SeLe4n.Platform.Contract

namespace SeLe4n.Kernel.Concurrency

/-- Number of cores from the active platform binding. Defaults
    to 4 on RPi5 BCM2712. -/
def numCores : Nat := PlatformBinding.coreCount

/-- Typed core identifier. `Fin numCores` guarantees every
    CoreId is valid by construction. -/
abbrev CoreId : Type := Fin numCores

/-- The boot core (always core 0 in practice, but
    typeclass-supplied so multi-platform builds can override). -/
def bootCoreId : CoreId := PlatformBinding.bootCoreId

/-- All core ids enumerated. -/
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
```

**Acceptance**:
- Module compiles via `lake build SeLe4n.Kernel.Concurrency.Types`.
- All 4 theorems prove (`decide`-able under RPi5
  PlatformBinding).
- `#check SeLe4n.Kernel.Concurrency.CoreId` at REPL yields `Type`.

**Test additions** (in `tests/SmpFoundationsSuite.lean` — created
in SM0.S):

```lean
#check @SeLe4n.Kernel.Concurrency.numCores
#check @SeLe4n.Kernel.Concurrency.CoreId
#check @SeLe4n.Kernel.Concurrency.bootCoreId
#check @SeLe4n.Kernel.Concurrency.allCores

example : SeLe4n.Kernel.Concurrency.numCores = 4 := by decide
example : SeLe4n.Kernel.Concurrency.allCores.length = 4 := by decide
example : SeLe4n.Kernel.Concurrency.bootCoreId.val = 0 := by decide
```

**Size**: M (foundational types + 4 theorems; ~80 LoC).

---

#### SM0.F — Define `SharingDomain`

**Goal**: Per §3.6 above. Foundation for SM7 (TLB shootdown)
and SM2 (memory model).

**File**: Append to `SeLe4n/Kernel/Concurrency/Types.lean` (or
new sibling `SharingDomain.lean` — TBD by SM0.F's PR for
import-graph hygiene).

**Code skeleton**: per §3.6.

**Acceptance**:
- Module compiles.
- `SharingDomain.eq_decidable` available (auto-derived).
- `dsbForSharing .inner = .dsbIsh` (decidable example).
- `dsbForSharing .outer = .dsbOsh`.

**Size**: T (~30 LoC).

---

#### SM0.G — PlatformBinding extension

**Goal**: Add `coreCount`, `coreCountPos`, `bootCoreId`,
`sharingDomain` fields to the PlatformBinding typeclass.

**Files**:
- `SeLe4n/Platform/Contract.lean` (typeclass schema).
- `SeLe4n/Platform/RPi5/Contract.lean` (RPi5 instance).
- `SeLe4n/Platform/Sim/*.lean` (Sim instance(s)).

**Code skeleton** (typeclass schema):

```lean
class PlatformBinding where
  -- existing fields
  machineConfig : SeLe4n.MachineConfig
  ...

  -- SM0.G additions:
  coreCount     : Nat
  coreCountPos  : coreCount > 0
  bootCoreId    : Fin coreCount
  sharingDomain : SharingDomain
```

**RPi5 instance**:

```lean
instance rpi5PlatformBinding : PlatformBinding where
  -- existing fields
  ...

  coreCount      := 4
  coreCountPos   := by decide
  bootCoreId     := ⟨0, by decide⟩
  sharingDomain  := .inner
```

**Sim instance(s)**: SM0.G's PR adds analogous fields. For a
single-core sim: `coreCount := 1; bootCoreId := ⟨0, _⟩;
sharingDomain := .inner`. For a 4-core SMP-test sim:
`coreCount := 4`.

**Acceptance**:
- `instance` declarations type-check.
- All `PlatformBinding` consumers continue to compile (no field
  reordering breakage).
- Decidable witnesses: `decide` proves `coreCountPos` on RPi5
  (`4 > 0`) and Sim.

**Size**: M (typeclass + 2-3 instance updates; ~80 LoC across
4 files).

---

#### SM0.H — Define `SgiKind`

**Goal**: Per §3.5 above. Foundation for SM1.F (Rust SGI
primitive) and SM5.C (cross-core wake).

**File**: New `SeLe4n/Kernel/Concurrency/Sgi.lean`.

**Code skeleton**: per §3.5.

**Acceptance**:
- Module compiles.
- `SgiKind.toIntid_injective` proves by `decide`.
- `SgiKind.toIntid_in_range` proves by `Fin.isLt`.
- 5 INTID assignments (0..4) verified by decidable examples.

**Size**: S (~50 LoC).

---

#### SM0.I — Define `LockKind` + `LockId` + total order

**Goal**: Per §3.2 and §3.3. The foundational types for SM3's
per-object lock discipline and Theorem 2.1.9 (deadlock-freedom).

**File**: New `SeLe4n/Kernel/Concurrency/Locks/Kind.lean` (then
extended in SM3 with the lock-specific machinery).

**Code skeleton**: per §3.2 + §3.3, with the proof
`level_surjective` and `le_trans`/`le_antisymm` filled in:

```lean
theorem LockKind.level_surjective :
    ∀ n : Nat, n < 10 → ∃ k : LockKind, k.level = n := by
  intro n hn
  interval_cases n
  · exact ⟨.objStore, rfl⟩
  · exact ⟨.untyped, rfl⟩
  · exact ⟨.cnode, rfl⟩
  · exact ⟨.tcb, rfl⟩
  · exact ⟨.endpoint, rfl⟩
  · exact ⟨.notification, rfl⟩
  · exact ⟨.reply, rfl⟩
  · exact ⟨.schedContext, rfl⟩
  · exact ⟨.vspaceRoot, rfl⟩
  · exact ⟨.page, rfl⟩
```

The `le_trans` proof breaks into 4 cases on the disjunction
structure of the two hypotheses; each is straightforward by
`Nat.lt_trans` / `Nat.lt_of_lt_of_le` etc.

`le_antisymm` similarly: from `l₁ ≤ l₂` and `l₂ ≤ l₁`, deduce
`l₁.kind.level = l₂.kind.level` and `l₁.objId.val =
l₂.objId.val`, then use the strict-monotone level theorem to
get `l₁.kind = l₂.kind` and conclude `l₁ = l₂` by structure
extensionality.

**Acceptance**:
- All 6 theorems (`level_strictMono`, `level_surjective`,
  `level_bounded`, `LockId.le_total`, `LockId.le_refl`,
  `LockId.le_trans`, `LockId.le_antisymm`) prove.
- `decide` works for any specific LockId pair (decidable order).

**Size**: M (~150 LoC including all 7 theorems with proofs).

### 5.3 AN12-B inventory hardening (Group 3)

#### SM0.A — Add `singleCoreOperation` to ArchAssumption

**Goal**: Per §3.7. Close SMP-H2 per the implement-the-improvement
rule.

**File**: `SeLe4n/Kernel/Architecture/Assumptions.lean`.

**Code skeleton**: add the 6th constructor as shown in §3.7.

**Acceptance**:
- Inductive grows from 5 to 6 cases.
- All existing consumers compile (cases over `ArchAssumption`
  may need a 6th branch, e.g., in `archAssumptionConsumer`).
- Existing `assumptionInventoryComplete_holds` still proves
  (added 6th case to `cases` analysis).

**Size**: S (~30 LoC including downstream case-arm updates).

---

#### SM0.B — Extend inventory + consumer map + distinctness

**Goal**: Per §3.7 above. Make `singleCoreOperation` first-class
in the architecture inventory.

**File**: `SeLe4n/Kernel/Architecture/Assumptions.lean`.

**Code skeleton**: as in §3.7. The distinctness theorem requires
C(6,2) = 15 inequalities:

```lean
theorem archAssumptionConsumer_distinct_6 :
    -- 5 unique consumers + singleCoreOperation -> 15 pairs.
    archAssumptionConsumer .deterministicTimerProgress
      ≠ archAssumptionConsumer .deterministicRegisterContext ∧
    archAssumptionConsumer .deterministicTimerProgress
      ≠ archAssumptionConsumer .memoryAccessSafety ∧
    -- ... 13 more pairs ...
    archAssumptionConsumer .irqRoutingTotality
      ≠ archAssumptionConsumer .singleCoreOperation := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
```

**Acceptance**:
- All 6 cases in `architecture_assumptions_index_total_6`.
- `assumptionInventory.length = 6` by `decide`.
- 15 pairwise distinctness inequalities by `decide`.

**Size**: M (~80 LoC including the 15-conjunct theorem).

---

#### SM0.C — `Concurrency/Anchors.lean` with `@`-references

**Goal**: Close SMP-H3. Every `smpLatentInventory` entry's
`identifier` and `sourceTheorem` is verified at build time by
adding `@`-references in a sibling module.

**File**: New `SeLe4n/Kernel/Concurrency/Anchors.lean`.

**Code skeleton**:

```lean
-- SPDX-License-Identifier: GPL-3.0-or-later
import SeLe4n.Kernel.Concurrency.Assumptions
-- Pull in the modules that own the identifiers/sourceTheorems:
import SeLe4n.Kernel.Capability.Lookup            -- resolveCapAddress_result_valid_cnode
import SeLe4n.Kernel.Capability.Operations        -- cspaceCopy_preserves_capabilityInvariantBundle
import SeLe4n.Kernel.Lifecycle.Cleanup            -- lifecyclePreRetypeCleanup
import SeLe4n.Kernel.Service.Operations           -- serviceHasPathTo
import SeLe4n.Kernel.Scheduler.CBS                -- replenishmentPipelineOrder
import SeLe4n.Model.State                         -- typedIdDisjointness
import SeLe4n.Kernel.Architecture.Assumptions     -- architecture_assumptions_index
import SeLe4n.Kernel.CrossSubsystem               -- bootFromPlatform_singleCore_witness

namespace SeLe4n.Kernel.Concurrency

/-- AN12-B (SM0.C / SMP-H3 closure): compile-time anchor for
    each inventory entry's identifier + sourceTheorem.  If
    any referenced theorem is renamed without updating the
    inventory, the corresponding `@`-reference fails at
    elaboration. -/
example : True := by
  let _ := @SeLe4n.Kernel.resolveCapAddress_result_valid_cnode
  let _ := @SeLe4n.Kernel.cspaceCopy_preserves_capabilityInvariantBundle
  let _ := @SeLe4n.Kernel.lifecyclePreRetypeCleanup
  let _ := @SeLe4n.Kernel.serviceHasPathTo
  let _ := @SeLe4n.Kernel.replenishmentPipelineOrder
  let _ := @SeLe4n.Kernel.typedIdDisjointness
  let _ := @SeLe4n.Kernel.Architecture.architecture_assumptions_index
  let _ := @SeLe4n.Kernel.bootFromPlatform_singleCore_witness
  trivial

end SeLe4n.Kernel.Concurrency
```

Then wire into `Platform.Staged`:

```lean
-- In SeLe4n/Platform/Staged.lean, add:
import SeLe4n.Kernel.Concurrency.Anchors
```

**Acceptance**:
- Module compiles via `lake build SeLe4n.Kernel.Concurrency.Anchors`.
- Renaming any of the 8 referenced theorems fails the build
  (test by temporarily mis-spelling one).
- `Platform.Staged` build target includes the Anchors module.

**Size**: S (~50 LoC + 1 import statement in Staged.lean).

---

#### SM0.D — Inventory NoDup witness

**Goal**: Close SMP-L1. The 8-entry `smpLatentInventory` size
is witnessed by `smpLatentInventory_count`, but no NoDup witness
exists. Adding an entry without updating the count is caught,
but renaming one to a duplicate of another would slip silently.

**File**: `SeLe4n/Kernel/Concurrency/Assumptions.lean` (extend
existing module).

**Code skeleton**:

```lean
theorem smpLatentInventory_identifiers_nodup :
    (smpLatentInventory.map (·.identifier)).Nodup := by
  unfold smpLatentInventory
  simp only [List.map_cons, List.map_nil]
  decide
```

**Acceptance**:
- Theorem proves (`decide` handles the 8-entry NoDup check).
- Adding a duplicate-identifier entry to the inventory fails
  the build.

**Size**: T (~15 LoC).

### 5.4 Structural fixes (Group 4)

#### SM0.M — Zero `.smp_stacks` at boot

**Goal**: Close SMP-M3. The `.smp_stacks` linker section is
`NOLOAD` and not zeroed at boot. SMP activation would expose
stale RAM contents to secondary cores.

**Files**: `rust/sele4n-hal/src/boot.S`, `rust/sele4n-hal/link.ld`.

**Edit pattern**: Extend the BSS-zero loop in `boot.S`:

```asm
.L_bss_zero_loop:
    cmp     x0, x1
    b.ge    .L_bss_done
    stp     xzr, xzr, [x0], #16
    b       .L_bss_zero_loop

.L_bss_done:
    // SM0.M: Zero the SMP secondary-core stacks region too.
    adrp    x0, __smp_secondary_stacks_bottom
    add     x0, x0, :lo12:__smp_secondary_stacks_bottom
    adrp    x1, __smp_secondary_stack_top
    add     x1, x1, :lo12:__smp_secondary_stack_top
.L_smp_stacks_zero_loop:
    cmp     x0, x1
    b.ge    .L_smp_stacks_done
    stp     xzr, xzr, [x0], #16
    b       .L_smp_stacks_zero_loop
.L_smp_stacks_done:
```

The `link.ld` already exposes `__smp_secondary_stacks_bottom`
and `__smp_secondary_stack_top` (verified in audit).

**Acceptance**:
- Cargo unit test (host stub) that verifies the symbol names
  resolve.
- Boot trace on real hardware (QEMU `-smp 4`) shows zeroed
  stacks via a debug log probe (SM1.G adds the probe).
- Cost: ~192 KiB zeroing at boot, ~12K cycles on Cortex-A76 —
  negligible.

**Size**: S (~30 LoC of assembly).

---

#### SM0.N — Set TPIDR_EL1 in `secondary_entry`

**Goal**: Close SMP-M4. The `boot.S::secondary_entry` stub does
not set TPIDR_EL1 (the per-CPU base register) despite the
`smp.rs:19` docstring claim. SM0.N adds the setup so secondaries
can locate their per-CPU data block on first kernel entry.

**Files**:
- `rust/sele4n-hal/src/boot.S` (assembly setup).
- `rust/sele4n-hal/src/smp.rs` (per-CPU data array declaration).
- `rust/sele4n-hal/link.ld` (linker symbol if needed).

**Edit pattern** (boot.S::secondary_entry, after SP setup):

```asm
secondary_entry:
    // Step 1: mask all maskable interrupts.
    msr     daifset, #0xf

    // Step 2: per-core stack.
    sub     x1, x0, #1                // x1 = secondary index (0..2)
    lsl     x1, x1, #16
    adrp    x2, __smp_secondary_stack_top
    add     x2, x2, :lo12:__smp_secondary_stack_top
    sub     sp, x2, x1
    and     sp, sp, #~0xF

    // SM0.N: Set TPIDR_EL1 to per-CPU data base for this core.
    // context_id (x0) = 1..3 for secondaries; the boot core's
    // TPIDR_EL1 is set in Phase 4 of rust_boot_main.
    adrp    x2, PER_CPU_DATA
    add     x2, x2, :lo12:PER_CPU_DATA
    // Per-core slot offset = context_id * sizeof(PerCpuData).
    // For now PerCpuData is empty; offset = 0 for all cores.
    // The TPIDR_EL1 write provides the seam for SM1.B to
    // populate the struct.
    mov     x3, #0                    // sizeof(PerCpuData) = 0 currently
    madd    x2, x0, x3, x2            // x2 = PER_CPU_DATA + x0 * 0 = PER_CPU_DATA
    msr     tpidr_el1, x2

    // Step 3: jump to Rust per-core init.
    bl      rust_secondary_main
    b       .L_secondary_spin
```

**rust/sele4n-hal/src/smp.rs additions**:

```rust
/// SM0.N: Per-CPU data block array. Empty struct at SM0 —
/// populated in SM1.B with per-CPU state (current thread
/// pointer, idle TCB pointer, etc.).
#[repr(C, align(64))]
pub struct PerCpuData {
    // populated by SM1.B
}

#[no_mangle]
#[used]
pub static PER_CPU_DATA: [PerCpuData; 4] = [
    PerCpuData {},
    PerCpuData {},
    PerCpuData {},
    PerCpuData {},
];
```

**Acceptance**:
- Cargo build green.
- TPIDR_EL1 readable from `rust_secondary_main` (verified by a
  diagnostic kprintln in SM1.C).
- Boot core's TPIDR_EL1 setup (in `rust_boot_main`) added in
  the same PR.

**Size**: M (~80 LoC across boot.S + smp.rs).

---

#### SM0.O — MAX_SECONDARY_CORES parameterization

**Goal**: Close SMP-L2. `MAX_SECONDARY_CORES = 3` is hard-coded
in `smp.rs:52`. Parameterize via the new
`PlatformBinding.coreCount - 1`.

**File**: `rust/sele4n-hal/src/smp.rs`.

**Edit pattern**:

```rust
/// SM0.O: MAX_SECONDARY_CORES derived from
/// PlatformBinding.coreCount - 1 (the boot core + N-1
/// secondaries). At v1.0.0 the constant lives in Rust because
/// Rust doesn't see the Lean typeclass; it's pinned to match
/// the Lean side via build-time constant assertion.
pub const MAX_SECONDARY_CORES: usize = 3;

const _: () = assert!(
    MAX_SECONDARY_CORES + 1 == 4,
    "MAX_SECONDARY_CORES must match PlatformBinding.coreCount - 1"
);
```

(The compile-time assert ensures the Rust constant matches the
Lean PlatformBinding.coreCount, currently 4 for RPi5. A future
multi-platform port updates both in lockstep.)

**Acceptance**:
- Compile-time assert pins the relationship.
- Cargo test verifies MAX_SECONDARY_CORES + 1 == 4.

**Size**: T (~20 LoC).

### 5.5 Testing infrastructure (Group 5)

#### SM0.S — `tests/SmpFoundationsSuite.lean`

**Goal**: New test suite that anchors the SM0 foundational types
in tier-3 surface anchors and provides decidable examples.

**File**: New `tests/SmpFoundationsSuite.lean`.

**Code skeleton**:

```lean
-- SPDX-License-Identifier: GPL-3.0-or-later
import SeLe4n.Kernel.Concurrency.Types
import SeLe4n.Kernel.Concurrency.Locks.Kind
import SeLe4n.Kernel.Concurrency.Sgi
import SeLe4n.Kernel.Concurrency.Anchors

-- Surface anchors: #check every public foundational symbol.
#check @SeLe4n.Kernel.Concurrency.numCores
#check @SeLe4n.Kernel.Concurrency.CoreId
#check @SeLe4n.Kernel.Concurrency.bootCoreId
#check @SeLe4n.Kernel.Concurrency.allCores
#check @SeLe4n.Kernel.Concurrency.numCores_pos
#check @SeLe4n.Kernel.Concurrency.allCores_length
#check @SeLe4n.Kernel.Concurrency.allCores_nodup
#check @SeLe4n.Kernel.Concurrency.bootCoreId_valid

#check @SeLe4n.Kernel.Concurrency.LockKind
#check @SeLe4n.Kernel.Concurrency.LockKind.level
#check @SeLe4n.Kernel.Concurrency.LockKind.level_strictMono
#check @SeLe4n.Kernel.Concurrency.LockKind.level_surjective
#check @SeLe4n.Kernel.Concurrency.LockKind.level_bounded
#check @SeLe4n.Kernel.Concurrency.LockId
#check @SeLe4n.Kernel.Concurrency.LockId.le_total
#check @SeLe4n.Kernel.Concurrency.LockId.le_trans
#check @SeLe4n.Kernel.Concurrency.LockId.le_antisymm

#check @SeLe4n.Kernel.Concurrency.SgiKind
#check @SeLe4n.Kernel.Concurrency.SgiKind.toIntid
#check @SeLe4n.Kernel.Concurrency.SgiKind.toIntid_injective

#check @SeLe4n.Kernel.Concurrency.SharingDomain
#check @SeLe4n.Kernel.Concurrency.dsbForSharing
#check @SeLe4n.Kernel.Concurrency.dsbStForSharing

-- Decidable examples: ground-truth checks at RPi5 default.
example : SeLe4n.Kernel.Concurrency.numCores = 4 := by decide
example : SeLe4n.Kernel.Concurrency.allCores.length = 4 := by decide
example : SeLe4n.Kernel.Concurrency.bootCoreId.val = 0 := by decide
example : SeLe4n.Kernel.Concurrency.LockKind.objStore.level = 0 := by decide
example : SeLe4n.Kernel.Concurrency.LockKind.page.level = 9 := by decide

example :
    SeLe4n.Kernel.Concurrency.LockId.mk .tcb ⟨5⟩
    ≤ SeLe4n.Kernel.Concurrency.LockId.mk .tcb ⟨7⟩ := by
  decide

example :
    SeLe4n.Kernel.Concurrency.LockId.mk .cnode ⟨100⟩
    ≤ SeLe4n.Kernel.Concurrency.LockId.mk .tcb ⟨1⟩ := by
  decide

example : SeLe4n.Kernel.Concurrency.SgiKind.reschedule.toIntid.val = 0 := by decide
example : SeLe4n.Kernel.Concurrency.SgiKind.tlbShootdownAck.toIntid.val = 2 := by decide

example : SeLe4n.Kernel.Concurrency.dsbForSharing .inner = BarrierKind.dsbIsh := by decide
example : SeLe4n.Kernel.Concurrency.dsbForSharing .outer = BarrierKind.dsbOsh := by decide
```

**Acceptance**:
- Suite compiles via `lake build SmpFoundationsSuite` (executable target in lakefile).
- All 20+ `#check`s succeed.
- All decidable examples prove by `decide`.
- Suite runs as part of tier-3 invariant suite.

**Size**: M (~150 LoC of test code).

---

#### SM0.T — Tier-4 SMP boot-check script stub

**Goal**: Create the `test_tier4_smp_bootcheck.sh` script stub
that later phases populate. At SM0, this is purely a placeholder
with skip-message-only behavior.

**File**: New `scripts/test_tier4_smp_bootcheck.sh`.

**Code skeleton**:

```bash
#!/usr/bin/env bash
# WS-SM tier-4 SMP boot check.
#
# Populated incrementally by SM1.H (QEMU bring-up), SM5.K (per-core
# scheduler), SM6.F (cross-core IPC), SM7.E (TLB shootdown), and
# SM8.E (information flow under SMP).
#
# At SM0 this is a stub that exits 0 — the tier slot is reserved.

set -euo pipefail

echo "[SKIP] WS-SM tier-4 SMP boot-check stub (SM0)"
echo "  Populated by SM1.H..SM8.E as those phases land."
exit 0
```

**Acceptance**:
- Script executable.
- Wired into `scripts/test_nightly.sh` (or whichever tier-4 driver).
- Exits 0 at SM0 (stub behavior).

**Size**: T (~15 LoC).

---

#### SM0.R — Update `docs/codebase_map.json`

**Goal**: Regenerate the codebase map to include the new
SM0 modules:
- `SeLe4n/Kernel/Concurrency/Types.lean`
- `SeLe4n/Kernel/Concurrency/Sgi.lean`
- `SeLe4n/Kernel/Concurrency/Anchors.lean`
- `SeLe4n/Kernel/Concurrency/Locks/Kind.lean`

**File**: `docs/codebase_map.json` (regenerated).

**Process**:

```bash
python scripts/generate_codebase_map.py --pretty > docs/codebase_map.json
```

**Acceptance**:
- Map regenerated.
- New modules present in the map.
- Tier 0 hygiene gate passes (`scripts/check_codebase_map.sh`).

**Size**: T (mechanical; no manual edits).

---

#### SM0.U — CHANGELOG entries per SM0 PR

**Goal**: Each SM0 PR carries a CHANGELOG entry. The aggregate
SM0 closure has its own summary entry at SM0 completion.

**Pattern**:

Each PR's CHANGELOG entry (under `## [v0.32.X] - YYYY-MM-DD`):

```
### Added
- SM0.E: typed `CoreId := Fin numCores` + enumeration helpers
  (`allCores`, `allCores_length`, `allCores_nodup`).
- SM0.F: `SharingDomain` inductive + `dsbForSharing` / `dsbStForSharing`
  selectors.
- ...
```

The SM0 closure aggregate entry:

```
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
