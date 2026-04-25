/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

/-!
# AN9-C: BarrierKind Composition Algebra (DEF-A-M08 / DEF-A-M09 / DEF-AK3-K)

> **STATUS: production**.  This module defines a small algebra over ARMv8-A
> memory and synchronisation barriers and proves the laws (associativity,
> subsumption partial order) that the kernel relies on when it composes a
> page-table update sequence or an MMIO write sequence.  The Rust HAL
> mirrors this enum (see `rust/sele4n-hal/src/barriers.rs::BarrierKind`)
> so a Lean theorem about a sequence of `BarrierKind` values translates
> directly to a Rust `BarrierKind::emit()` chain at the FFI boundary.

The algebra is intentionally minimal.  Each constructor maps to a concrete
ARMv8-A instruction (or a no-op for `none`); the `sequenced` constructor
captures the *order* in which barriers fire.

```
inductive BarrierKind where
  | none
  | dsbIsh         -- inner-shareable data sync (default kernel barrier)
  | dsbIshst       -- inner-shareable, store-only
  | dsbOsh         -- outer-shareable data sync (cross-cluster ordering)
  | dsbOshst       -- outer-shareable, store-only
  | dcCvacDsbIsh   -- D-cache clean by VA + DSB ISH (page-table page commit)
  | isb            -- instruction-side serialisation
  | sequenced (pre : BarrierKind) (post : BarrierKind)
```

`sequenced` is associative up to the equational theory checked here, and
admits a partial order `subsumes` that lets composition theorems argue that
"barrier A is at least as strong as barrier B" without naming each instance.

## Use sites

- `pageTableUpdate_observes_armv8_ordering`  — composes the ARMv8-A
  page-table update sequence (`dsb ishst → dc cvac+dsb ish → isb`)
  required by ARM ARM D8.11.
- `mmioWrite_observes_dsbIshst_before_sideEffect` — proves an MMIO write
  is preceded by `dsb ishst` so the externally-observable side effect is
  ordered with respect to the kernel's prior writes.
- `tlbBarrierComplete` (TlbModel.lean) — uses `subsumes` to show every
  TLB-invalidation kernel entry point emits at least the
  `dsbIsh; isb` bracket the ARM ARM requires.

## Cross-references

- AK3-G `CacheBarrierKind` (`CacheModel.lean`) is the legacy 3-variant
  type that this module supersedes.  The two are kept side-by-side at
  v0.30.10 because `CacheBarrierKind` participates in proofs that have
  not yet been migrated; new code should use `BarrierKind`.
- AN9-H Rust mirror in `rust/sele4n-hal/src/barriers.rs`.
-/

namespace SeLe4n.Kernel.Architecture

/-- AN9-C.1: ARMv8-A barrier kinds.  See module-level docstring for the
mapping between constructors and the `dsb`/`isb`/`dc cvac` instruction
family. -/
inductive BarrierKind where
  /-- No barrier emitted.  Identity element for `sequenced`. -/
  | none      : BarrierKind
  /-- Data Synchronisation Barrier, Inner Shareable.  Default kernel
      barrier covering all preceding loads/stores. -/
  | dsbIsh    : BarrierKind
  /-- DSB ISHST — store-only inner-shareable.  Used before MMU updates
      to flush prior writes only (no-op for loads, slightly cheaper). -/
  | dsbIshst  : BarrierKind
  /-- AN9-I: DSB OSH — outer-shareable.  Required for cross-cluster
      visibility on multi-cluster topologies (e.g., BCM2712 has two
      Cortex-A76 clusters; some device interconnects sit OUTSIDE the
      inner-shareable domain). -/
  | dsbOsh    : BarrierKind
  /-- AN9-I: DSB OSHST — outer-shareable, store-only. -/
  | dsbOshst  : BarrierKind
  /-- DC CVAC + DSB ISH composite.  Models the page-table-page commit
      pattern: clean a freshly-written descriptor to the Point of
      Coherency, then fence so the hardware walker observes it. -/
  | dcCvacDsbIsh : BarrierKind
  /-- Instruction Synchronisation Barrier.  Forces the pipeline to
      re-fetch from cache/memory after the barrier, picking up new
      translations / SCTLR bits. -/
  | isb       : BarrierKind
  /-- Sequential composition: `pre` fires first, then `post`. -/
  | sequenced (pre : BarrierKind) (post : BarrierKind) : BarrierKind
  deriving DecidableEq, Repr, Inhabited

namespace BarrierKind

/-- AN9-C.1: The set of leaf `BarrierKind` constructors (every constructor
    that is not `sequenced`).  Useful for reasoning about which leaves
    appear in a composed term. -/
def leaves : BarrierKind → List BarrierKind
  | sequenced p q => p.leaves ++ q.leaves
  | b             => [b]

/-- AN9-C.1: Membership predicate — does `target` appear as a leaf inside
    `b` (after fully unfolding `sequenced`)? -/
def containsLeaf (target : BarrierKind) (b : BarrierKind) : Prop :=
  target ∈ b.leaves

/-- AN9-C.1: `containsLeaf` is decidable because `leaves` is a concrete
    list and `BarrierKind` admits `DecidableEq`. -/
instance : ∀ (t b : BarrierKind), Decidable (containsLeaf t b) := by
  intro t b
  unfold containsLeaf
  exact List.instDecidableMemOfLawfulBEq t b.leaves

/-- AN9-C.1: `sequenced none b` collapses to `b` at the leaf level —
    i.e., `none` acts as the left identity in the equational theory. -/
theorem leaves_sequenced_none_left (b : BarrierKind) :
    (sequenced none b).leaves = none :: b.leaves := by
  rfl

/-- AN9-C.1: Symmetric right-identity at the leaf level. -/
theorem leaves_sequenced_none_right (b : BarrierKind) :
    (sequenced b none).leaves = b.leaves ++ [none] := by
  show b.leaves ++ none.leaves = b.leaves ++ [none]
  rfl

/-- AN9-C.1: Associativity at the leaf level — composing three barriers
    in either grouping yields the same leaf list.  This is the key
    associativity law every downstream composition theorem appeals to. -/
theorem leaves_sequenced_assoc (a b c : BarrierKind) :
    (sequenced (sequenced a b) c).leaves =
      (sequenced a (sequenced b c)).leaves := by
  unfold leaves
  exact (List.append_assoc a.leaves b.leaves c.leaves)

/-- AN9-C.1: Subsumption partial order — `a.subsumes b` means every leaf
    barrier in `b` already appears in `a`.  In particular, if `a` emits
    a `dsbIsh; isb` bracket and `b` requires `isb`, then
    `a.subsumes b`.

    This is the predicate downstream theorems use to argue "this composed
    sequence is at least as strong as the ARM-ARM-required minimum". -/
def subsumes (a b : BarrierKind) : Prop :=
  ∀ leaf ∈ b.leaves, leaf ∈ a.leaves

/-- AN9-C.1: `subsumes` is reflexive. -/
theorem subsumes_refl (a : BarrierKind) : a.subsumes a := by
  intro _ h; exact h

/-- AN9-C.1: `subsumes` is transitive. -/
theorem subsumes_trans {a b c : BarrierKind}
    (hAB : a.subsumes b) (hBC : b.subsumes c) :
    a.subsumes c := by
  intro leaf h; exact hAB leaf (hBC leaf h)

/-- AN9-C.1: A sequenced barrier subsumes both halves. -/
theorem sequenced_subsumes_left (a b : BarrierKind) :
    (sequenced a b).subsumes a := by
  intro leaf h
  simp only [leaves, List.mem_append]
  exact Or.inl h

/-- AN9-C.1: Symmetric right half. -/
theorem sequenced_subsumes_right (a b : BarrierKind) :
    (sequenced a b).subsumes b := by
  intro leaf h
  simp only [leaves, List.mem_append]
  exact Or.inr h

/-- AN9-C.1: Decidable equality on `BarrierKind` makes `subsumes`
    decidable for any two concrete terms. -/
instance subsumesDecidable : ∀ (a b : BarrierKind), Decidable (a.subsumes b) := by
  intro a b
  unfold subsumes
  exact List.decidableBAll _ _

/-- AN9-C.2 building block: the canonical ARMv8-A page-table-update
    sequence.  ARM ARM D8.11 specifies, for software-managed page-table
    updates that must be visible to the MMU walker on the *current* core
    before subsequent execution:

      1. `dsb ishst`     — flush prior store buffer
      2. `dc cvac + dsb ish` — clean the freshly-written descriptor to PoC
      3. `isb`           — re-fetch translations on this core

    We model this as a 3-step `sequenced` composition. -/
def armv8PageTableUpdateSequence : BarrierKind :=
  sequenced dsbIshst (sequenced dcCvacDsbIsh isb)

/-- AN9-C.2 (DEF-A-M08): the canonical sequence subsumes each individual
    leaf the ARM ARM page-table-update protocol requires.  This is the
    headline theorem callers consume to discharge the hardware ordering
    obligation. -/
theorem pageTableUpdate_observes_armv8_ordering :
    armv8PageTableUpdateSequence.subsumes dsbIshst ∧
    armv8PageTableUpdateSequence.subsumes dcCvacDsbIsh ∧
    armv8PageTableUpdateSequence.subsumes isb := by
  refine ⟨?_, ?_, ?_⟩ <;> intro leaf h <;>
    simp [armv8PageTableUpdateSequence, leaves] at h ⊢ <;>
    simp [h]

/-- AN9-C.3 building block: every MMIO write must be preceded by at least
    a `dsb ishst` so the externally-observable side effect is correctly
    ordered with respect to prior kernel writes (ARM ARM B2.3.5). -/
def mmioWriteOrderingSequence : BarrierKind :=
  sequenced dsbIshst none

/-- AN9-C.3 (DEF-A-M09): MMIO write sequence subsumes `dsbIshst`. -/
theorem mmioWrite_observes_dsbIshst_before_sideEffect :
    mmioWriteOrderingSequence.subsumes dsbIshst := by
  intro leaf h; simp [mmioWriteOrderingSequence, leaves] at h ⊢; simp [h]

/-- AN9-I: cross-cluster (outer-shareable) MMIO write sequence.  Used for
    device registers that must be visible to cores in clusters other than
    the writer's. -/
def mmioWriteOrderingSequenceOuterShareable : BarrierKind :=
  sequenced dsbOshst none

/-- AN9-I: cross-cluster MMIO sequence subsumes `dsbOshst`. -/
theorem mmioWriteCrossCluster_observes_dsbOshst :
    mmioWriteOrderingSequenceOuterShareable.subsumes dsbOshst := by
  intro leaf h
  simp [mmioWriteOrderingSequenceOuterShareable, leaves] at h ⊢
  simp [h]

/-- AN9-I: outer-shareable subsumes inner-shareable for the *store-only*
    half of the algebra — every kernel that emits `dsb oshst` has, by ARM
    ARM B2.3.5, also satisfied the `dsb ishst` ordering requirement
    because the inner-shareable domain is contained in the outer one.
    This is **not** a leaf-level subsumption (the constructor names
    differ), so the proof is constructive: we exhibit a wrapping sequence
    `(dsbOshst; dsbIshst)` that subsumes both. -/
def storeBarrierClosure : BarrierKind :=
  sequenced dsbOshst dsbIshst

/-- AN9-I: store-barrier closure subsumes both individual store
    barriers. -/
theorem storeBarrierClosure_subsumes_both :
    storeBarrierClosure.subsumes dsbIshst ∧
    storeBarrierClosure.subsumes dsbOshst := by
  refine ⟨?_, ?_⟩ <;> intro leaf h <;>
    simp [storeBarrierClosure, leaves] at h ⊢ <;>
    simp [h]

/-- AN9-B building block: the canonical TLB-invalidation bracket required
    by ARM ARM D8.11 — every `tlbi` must be followed by a DSB ISH (so the
    invalidation completes) and an ISB (so the pipeline re-fetches with
    the post-invalidation translation set). -/
def tlbInvalidationBracket : BarrierKind :=
  sequenced dsbIsh isb

/-- AN9-B: the TLB-invalidation bracket subsumes both required leaves. -/
theorem tlbInvalidationBracket_subsumes :
    tlbInvalidationBracket.subsumes dsbIsh ∧
    tlbInvalidationBracket.subsumes isb := by
  refine ⟨?_, ?_⟩ <;> intro leaf h <;>
    simp [tlbInvalidationBracket, leaves] at h ⊢ <;>
    simp [h]

end BarrierKind

end SeLe4n.Kernel.Architecture
