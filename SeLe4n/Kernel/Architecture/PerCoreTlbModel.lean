-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Architecture.TlbModel
import SeLe4n.Kernel.Architecture.TlbShootdownProtocol

/-!
# WS-SM SM7.C — Per-core TLB model

The SMP generalisation of the single-core TLB model (`TlbModel.lean`).
`SystemState.tlb` is the boot core's abstract TLB view (WS-H11/M-17);
under SMP each PE caches translations in its own TLB, so an invalidation
issued on one core does not reach another core's TLB without the SM7.B
shootdown protocol.  SM7.C mounts a per-core `Vector TlbState numCores`
(`SystemState.perCoreTlb`, SM7.C.1) and defines the per-core model
operations over it:

* **SM7.C.2** `tlbInsertOnCore` — the hardware page-table walker filling
  one core's TLB with a fresh translation.
* **SM7.C.3** `tlbInvalidateOnCore` — a local (this-core) invalidation
  (`applyTlbInvalidation` on core `c`'s view only).
* **SM7.C.4** `tlbInvalidateOnAllCores` — the cross-core broadcast, which
  posts to the SM7.A `tlbShootdown` state **and** evolves every core's
  view exactly as Theorem 3.3.1's `shootdownRoundViews` prescribes, so
  the mounted field is a genuine consumer of the shootdown state machine.

The theorems:

* **SM7.C.5** `tlbInvalidationConsistent_perCore` — every core's view is
  consistent with the page tables (the per-core lift of `tlbConsistent`;
  the 13th `proofLayerInvariantBundle` conjunct — see `Invariant.lean`).
* **SM7.C.6** `tlbShootdown_invalidates_perCore` — the corollary of
  Theorem 3.3.1 mounted on `perCoreTlb`: after a covering
  `tlbInvalidateOnAllCores` no core retains a covered (stale) entry.
* **SM7.C.7** `tlbConsistency_cross_subsystem` — the cross-subsystem
  capstone tying the shootdown protocol, the per-core TLB model, and the
  VSpace page tables: a covering invalidation both removes every stale
  entry on every core (the SMP-C4 use-after-unmap closure) and preserves
  per-core consistency.

Design: the SM4.B **path-a** discipline — `tlbOnCore` / `setTlbOnCore`
accessors over the `Vector`, a `@[simp]` store/load algebra, per-core
`ext_perCoreTlb`, and a boot-quiescent default (`default_tlbOnCore`).  The
per-core view function the broadcast evolves is the protocol's
`shootdownRoundViews`, so Theorem 3.3.1
(`tlbShootdownBroadcast_invalidatesAllCores`) instantiates on the mounted
field mechanically.
-/

namespace SeLe4n.Kernel.Architecture

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- SM7.C.1 — Per-core TLB view accessors (SM4.B path-a discipline)
-- ============================================================================

/-- **WS-SM SM7.C.1**: read core `c`'s TLB view from the mounted per-core
vector.  The `Fin numCores`-indexed accessor of the SM4.B path-a
discipline. -/
def tlbOnCore (st : SystemState) (c : CoreId) : TlbState :=
  st.perCoreTlb.get c

/-- **WS-SM SM7.C.1**: write core `c`'s TLB view, leaving every other
core's slot and every non-`perCoreTlb` field unchanged (SM4.B path-a
setter). -/
def setTlbOnCore (st : SystemState) (c : CoreId) (t : TlbState) : SystemState :=
  { st with perCoreTlb := st.perCoreTlb.set c.val t c.isLt }

/-- **WS-SM SM7.C.1**: reading the slot just written returns the written
view. -/
@[simp] theorem setTlbOnCore_tlbOnCore_self (st : SystemState) (c : CoreId)
    (t : TlbState) :
    tlbOnCore (setTlbOnCore st c t) c = t := by
  simp [tlbOnCore, setTlbOnCore]

/-- **WS-SM SM7.C.1**: writing core `c`'s slot leaves every other core's
view unchanged — the per-core frame property. -/
theorem setTlbOnCore_tlbOnCore_ne (st : SystemState) {c c' : CoreId}
    (t : TlbState) (h : c ≠ c') :
    tlbOnCore (setTlbOnCore st c t) c' = tlbOnCore st c' := by
  simp only [tlbOnCore, setTlbOnCore]
  exact SeLe4n.PerCoreVector.get_set_ne st.perCoreTlb c c' t h

/-- **WS-SM SM7.C.1**: the setter touches only `perCoreTlb` — every other
`SystemState` field frames (all `rfl`, the record-update shape). -/
@[simp] theorem setTlbOnCore_objects (st : SystemState) (c : CoreId) (t : TlbState) :
    (setTlbOnCore st c t).objects = st.objects := rfl
@[simp] theorem setTlbOnCore_asidTable (st : SystemState) (c : CoreId) (t : TlbState) :
    (setTlbOnCore st c t).asidTable = st.asidTable := rfl
@[simp] theorem setTlbOnCore_scheduler (st : SystemState) (c : CoreId) (t : TlbState) :
    (setTlbOnCore st c t).scheduler = st.scheduler := rfl
@[simp] theorem setTlbOnCore_machine (st : SystemState) (c : CoreId) (t : TlbState) :
    (setTlbOnCore st c t).machine = st.machine := rfl
@[simp] theorem setTlbOnCore_tlb (st : SystemState) (c : CoreId) (t : TlbState) :
    (setTlbOnCore st c t).tlb = st.tlb := rfl
@[simp] theorem setTlbOnCore_tlbShootdown (st : SystemState) (c : CoreId) (t : TlbState) :
    (setTlbOnCore st c t).tlbShootdown = st.tlbShootdown := rfl

/-- **WS-SM SM7.C.1**: per-core view vectors are equal once they agree at
every core — the `PerCoreVector.ext` lever the per-core-model proofs use
to reduce whole-vector reasoning to a `∀ c` obligation. -/
theorem perCoreTlb_vector_ext {v w : _root_.Vector TlbState numCores}
    (h : ∀ c : CoreId, v.get c = w.get c) : v = w :=
  SeLe4n.PerCoreVector.ext h

/-- **WS-SM SM7.C.1**: at boot every core's TLB view is empty. -/
@[simp] theorem default_tlbOnCore (c : CoreId) :
    tlbOnCore (default : SystemState) c = TlbState.empty :=
  default_perCoreTlb c

-- ============================================================================
-- SM7.C.2 — tlbInsertOnCore (models the hardware translation walker)
-- ============================================================================

/-- **WS-SM SM7.C.2**: the hardware page-table walker's effect — core `c`
caches a fresh translation `entry` in its own TLB.  Models a TLB fill on
a walk that resolved `(entry.asid, entry.vaddr)`; the entry is prepended
to core `c`'s view (associative-cache membership, order-immaterial). -/
def tlbInsertOnCore (st : SystemState) (c : CoreId) (entry : TlbEntry) :
    SystemState :=
  setTlbOnCore st c { entries := entry :: (tlbOnCore st c).entries }

/-- **WS-SM SM7.C.2**: after a fill, core `c`'s view contains the inserted
entry. -/
theorem tlbInsertOnCore_mem (st : SystemState) (c : CoreId) (entry : TlbEntry) :
    entry ∈ (tlbOnCore (tlbInsertOnCore st c entry) c).entries := by
  simp [tlbInsertOnCore]

/-- **WS-SM SM7.C.2**: a fill on core `c` leaves every other core's view
unchanged — a hardware walk is a local event (the SMP asymmetry the
shootdown protocol later closes). -/
theorem tlbInsertOnCore_tlbOnCore_ne (st : SystemState) {c c' : CoreId}
    (entry : TlbEntry) (h : c ≠ c') :
    tlbOnCore (tlbInsertOnCore st c entry) c' = tlbOnCore st c' :=
  setTlbOnCore_tlbOnCore_ne st _ h

/-- **WS-SM SM7.C.2**: a fill touches only the TLB model — objects,
scheduler, machine, ASID table, and shootdown state all frame. -/
theorem tlbInsertOnCore_frame (st : SystemState) (c : CoreId) (entry : TlbEntry) :
    (tlbInsertOnCore st c entry).objects = st.objects ∧
    (tlbInsertOnCore st c entry).asidTable = st.asidTable ∧
    (tlbInsertOnCore st c entry).scheduler = st.scheduler ∧
    (tlbInsertOnCore st c entry).machine = st.machine ∧
    (tlbInsertOnCore st c entry).tlbShootdown = st.tlbShootdown :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- SM7.C.3 — tlbInvalidateOnCore (local, this-core invalidation)
-- ============================================================================

/-- **WS-SM SM7.C.3**: a local TLB invalidation on core `c` — retires the
operand `op` on core `c`'s view only (the non-broadcast `TLBI` a PE runs
against its own TLB).  Under SMP this reaches exactly one core; the
cross-core reach is `tlbInvalidateOnAllCores`. -/
def tlbInvalidateOnCore (st : SystemState) (c : CoreId) (op : TlbInvalidation) :
    SystemState :=
  setTlbOnCore st c (applyTlbInvalidation (tlbOnCore st c) op)

/-- **WS-SM SM7.C.3**: a local invalidation removes every covered entry
from core `c`'s view. -/
theorem tlbInvalidateOnCore_removes {op : TlbInvalidation} {e : TlbEntry}
    (h : tlbEntryMatches op e = true) (st : SystemState) (c : CoreId) :
    e ∉ (tlbOnCore (tlbInvalidateOnCore st c op) c).entries := by
  simp only [tlbInvalidateOnCore, setTlbOnCore_tlbOnCore_self]
  exact applyTlbInvalidation_removes h _

/-- **WS-SM SM7.C.3**: a local invalidation on core `c` leaves every other
core's view stale — the precise SMP hazard (`tlbInvalidateOnAllCores`
closes it). -/
theorem tlbInvalidateOnCore_tlbOnCore_ne (st : SystemState) {c c' : CoreId}
    (op : TlbInvalidation) (h : c ≠ c') :
    tlbOnCore (tlbInvalidateOnCore st c op) c' = tlbOnCore st c' :=
  setTlbOnCore_tlbOnCore_ne st _ h

/-- **WS-SM SM7.C.3**: a local invalidation never adds entries to core
`c`'s view — every surviving entry was already present.  The
consistency-monotonicity witness (SM7.C.5/C.7 use it). -/
theorem tlbInvalidateOnCore_subset (st : SystemState) (c : CoreId)
    (op : TlbInvalidation) {e : TlbEntry}
    (h : e ∈ (tlbOnCore (tlbInvalidateOnCore st c op) c).entries) :
    e ∈ (tlbOnCore st c).entries := by
  simp only [tlbInvalidateOnCore, setTlbOnCore_tlbOnCore_self] at h
  exact mem_of_mem_applyTlbInvalidation h

/-- **WS-SM SM7.C.3**: a local invalidation touches only the TLB model —
objects, scheduler, machine, ASID table, and shootdown state all frame. -/
theorem tlbInvalidateOnCore_frame (st : SystemState) (c : CoreId)
    (op : TlbInvalidation) :
    (tlbInvalidateOnCore st c op).objects = st.objects ∧
    (tlbInvalidateOnCore st c op).asidTable = st.asidTable ∧
    (tlbInvalidateOnCore st c op).scheduler = st.scheduler ∧
    (tlbInvalidateOnCore st c op).machine = st.machine ∧
    (tlbInvalidateOnCore st c op).tlbShootdown = st.tlbShootdown :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- SM7.C.4 — tlbInvalidateOnAllCores (cross-core broadcast via the protocol)
-- ============================================================================

/-- **WS-SM SM7.C.4** (broadcast frame): the SM7.B `tlbShootdownBroadcast`
posts only to the shootdown state — every core's TLB *view* frames (the
initiator's own invalidation and the targets' handler retirements are the
separate steps `tlbInvalidateOnAllCores` composes below). -/
theorem tlbShootdownBroadcast_perCoreTlb {st st' : SystemState}
    {initiator : CoreId} {targets : List CoreId} {op : TlbInvalidation}
    {sgis : List (CoreId × SgiKind)}
    (h : tlbShootdownBroadcast st initiator targets op = some (st', sgis)) :
    st'.perCoreTlb = st.perCoreTlb := by
  unfold tlbShootdownBroadcast at h
  cases hfold : targets.foldlM
      (fun s c => enqueueShootdown s c { op := op, initiator := initiator })
      (beginShootdownRoundFor st.tlbShootdown initiator targets) with
  | none => rw [hfold] at h; cases h
  | some posted =>
      rw [hfold] at h; injection h with h; rw [Prod.mk.injEq] at h
      obtain ⟨hst, _⟩ := h; subst hst; rfl

/-- **WS-SM SM7.C.4** (broadcast frame): the broadcast frames the ASID
table — page-table resolution (`resolveAsidRoot`) is unchanged, so TLB
consistency transports across a broadcast. -/
theorem tlbShootdownBroadcast_asidTable {st st' : SystemState}
    {initiator : CoreId} {targets : List CoreId} {op : TlbInvalidation}
    {sgis : List (CoreId × SgiKind)}
    (h : tlbShootdownBroadcast st initiator targets op = some (st', sgis)) :
    st'.asidTable = st.asidTable := by
  unfold tlbShootdownBroadcast at h
  cases hfold : targets.foldlM
      (fun s c => enqueueShootdown s c { op := op, initiator := initiator })
      (beginShootdownRoundFor st.tlbShootdown initiator targets) with
  | none => rw [hfold] at h; cases h
  | some posted =>
      rw [hfold] at h; injection h with h; rw [Prod.mk.injEq] at h
      obtain ⟨hst, _⟩ := h; subst hst; rfl

/-- **WS-SM SM7.C.4**: the cross-core TLB invalidation.  Runs the SM7.B
shootdown broadcast (opening a round on the SM7.A `tlbShootdown` state and
returning the exact `.tlbShootdownReq` SGI list) **and** evolves every
core's TLB view exactly as the protocol's per-core view function
`shootdownRoundViews` prescribes — the initiator applies the operand
locally (step 3), each target at its handler acknowledgment (step 4).

This is what wires the mounted `perCoreTlb` field into the shootdown
state machine: the same round both posts to `tlbShootdown` and retires
the operand on every reached core's view.  Fail-closed (`none`) exactly
when the broadcast's posting fold overflows — unreachable from a
quiescent state (`tlbInvalidateOnAllCores_isSome_of_quiescent`). -/
def tlbInvalidateOnAllCores (st : SystemState) (initiator : CoreId)
    (targets : List CoreId) (op : TlbInvalidation) :
    Option (SystemState × List (CoreId × SgiKind)) :=
  match tlbShootdownBroadcast st initiator targets op with
  | none => none
  | some (posted, sgis) =>
      some ({ posted with
        perCoreTlb := shootdownRoundViews posted.perCoreTlb initiator targets op },
        sgis)

/-- **WS-SM SM7.C.4** (decomposition): a successful cross-core invalidation
is exactly the broadcast's posted state with every core's view stepped by
`shootdownRoundViews` over the pre-state views. -/
theorem tlbInvalidateOnAllCores_spec {st st' : SystemState}
    {initiator : CoreId} {targets : List CoreId} {op : TlbInvalidation}
    {sgis : List (CoreId × SgiKind)}
    (h : tlbInvalidateOnAllCores st initiator targets op = some (st', sgis)) :
    ∃ posted, tlbShootdownBroadcast st initiator targets op = some (posted, sgis) ∧
      st' = { posted with
        perCoreTlb := shootdownRoundViews st.perCoreTlb initiator targets op } := by
  unfold tlbInvalidateOnAllCores at h
  cases hb : tlbShootdownBroadcast st initiator targets op with
  | none => rw [hb] at h; cases h
  | some pair =>
      obtain ⟨p, psgis⟩ := pair
      rw [hb] at h; injection h with h; rw [Prod.mk.injEq] at h
      obtain ⟨hst, hsgi⟩ := h
      refine ⟨p, ?_, ?_⟩
      · rw [hsgi]
      · rw [← hst, tlbShootdownBroadcast_perCoreTlb hb]

/-- **WS-SM SM7.C.4**: the post-state's per-core views are the round's
`shootdownRoundViews` over the pre-state views — the exact vector
Theorem 3.3.1 quantifies over, now mounted on the real field. -/
theorem tlbInvalidateOnAllCores_perCoreTlb {st st' : SystemState}
    {initiator : CoreId} {targets : List CoreId} {op : TlbInvalidation}
    {sgis : List (CoreId × SgiKind)}
    (h : tlbInvalidateOnAllCores st initiator targets op = some (st', sgis)) :
    st'.perCoreTlb = shootdownRoundViews st.perCoreTlb initiator targets op := by
  obtain ⟨posted, _, hst⟩ := tlbInvalidateOnAllCores_spec h
  rw [hst]

/-- **WS-SM SM7.C.4**: the emitted SGI list is exactly the broadcast's —
one `.tlbShootdownReq` per target, in target order. -/
theorem tlbInvalidateOnAllCores_sgis {st st' : SystemState}
    {initiator : CoreId} {targets : List CoreId} {op : TlbInvalidation}
    {sgis : List (CoreId × SgiKind)}
    (h : tlbInvalidateOnAllCores st initiator targets op = some (st', sgis)) :
    sgis = targets.map (fun c => (c, SgiKind.tlbShootdownReq)) := by
  obtain ⟨posted, hb, _⟩ := tlbInvalidateOnAllCores_spec h
  exact tlbShootdownBroadcast_sgis hb

/-- **WS-SM SM7.C.4**: the cross-core invalidation frames the page-table
subsystem — objects and the ASID table are unchanged, so `resolveAsidRoot`
is preserved (the coherence half of `tlbConsistency_cross_subsystem`). -/
theorem tlbInvalidateOnAllCores_objects {st st' : SystemState}
    {initiator : CoreId} {targets : List CoreId} {op : TlbInvalidation}
    {sgis : List (CoreId × SgiKind)}
    (h : tlbInvalidateOnAllCores st initiator targets op = some (st', sgis)) :
    st'.objects = st.objects := by
  obtain ⟨posted, hb, hst⟩ := tlbInvalidateOnAllCores_spec h
  rw [hst]
  show posted.objects = st.objects
  exact (tlbShootdownBroadcast_frame hb).1

theorem tlbInvalidateOnAllCores_asidTable {st st' : SystemState}
    {initiator : CoreId} {targets : List CoreId} {op : TlbInvalidation}
    {sgis : List (CoreId × SgiKind)}
    (h : tlbInvalidateOnAllCores st initiator targets op = some (st', sgis)) :
    st'.asidTable = st.asidTable := by
  obtain ⟨posted, hb, hst⟩ := tlbInvalidateOnAllCores_spec h
  rw [hst]
  show posted.asidTable = st.asidTable
  exact tlbShootdownBroadcast_asidTable hb

/-- **WS-SM SM7.C.4**: from a quiescent shootdown state the cross-core
invalidation always succeeds — the plan §4.1 capacity-sufficiency argument
lifted to the per-core model op (via
`tlbShootdownBroadcast_isSome_of_quiescent`). -/
theorem tlbInvalidateOnAllCores_isSome_of_quiescent {st : SystemState}
    (hq : shootdownQuiescent st.tlbShootdown) (initiator : CoreId)
    {targets : List CoreId} (hnd : targets.Nodup) (op : TlbInvalidation) :
    (tlbInvalidateOnAllCores st initiator targets op).isSome := by
  unfold tlbInvalidateOnAllCores
  have h := tlbShootdownBroadcast_isSome_of_quiescent hq initiator hnd op
  obtain ⟨pair, hpair⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨posted, psgis⟩ := pair
  rw [hpair]
  rfl

-- ============================================================================
-- SM7.C.5 — tlbInvalidationConsistent_perCore (the per-core TLB invariant)
-- ============================================================================

/-- **WS-SM SM7.C.5**: the per-core TLB consistency invariant — *every*
core's cached TLB view matches the current page tables.  The SMP
generalisation of the single-core `tlbConsistent st st.tlb` (the 9th
`proofLayerInvariantBundle` conjunct); this predicate is the 13th
conjunct (`Invariant.lean`), quantifying the *same* `tlbConsistent`
relation over every core's mounted view. -/
def tlbInvalidationConsistent_perCore (st : SystemState) : Prop :=
  ∀ c : CoreId, tlbConsistent st (tlbOnCore st c)

/-- **WS-SM SM7.C.5**: at boot the per-core TLB invariant holds
vacuously — every core's view is empty (`default_tlbOnCore`), and an
empty TLB is trivially consistent (`tlbConsistent_empty`).  The bundle
boot witness. -/
theorem default_tlbInvalidationConsistent_perCore :
    tlbInvalidationConsistent_perCore (default : SystemState) := by
  intro c
  rw [default_tlbOnCore]
  exact tlbConsistent_empty _

/-- **WS-SM SM7.C.5**: the per-core invariant projects to the boot core —
the bridge back to the single-core `tlbConsistent st st.tlb` conjunct's
subject at the boot-core slot. -/
theorem tlbInvalidationConsistent_perCore_bootCore {st : SystemState}
    (h : tlbInvalidationConsistent_perCore st) :
    tlbConsistent st (tlbOnCore st bootCoreId) :=
  h bootCoreId

/-- **WS-SM SM7.C.5** (consistency monotonicity + page-table frame): a TLB
view that is a subset of a consistent view, read against a state with the
*same* page tables (`objects` + `asidTable`, hence the same
`resolveAsidRoot`), is itself consistent.  This is the lever every
invalidation-preserves-consistency proof uses: invalidation only removes
entries and never touches the page tables. -/
theorem tlbConsistent_of_subset_of_state_frame {st st' : SystemState}
    {t t' : TlbState}
    (hObjects : st'.objects = st.objects)
    (hAsidTable : st'.asidTable = st.asidTable)
    (hSub : ∀ e ∈ t'.entries, e ∈ t.entries)
    (hConsist : tlbConsistent st t) :
    tlbConsistent st' t' := by
  intro entry hMem rootId root hResolve
  have hResolve' : resolveAsidRoot st entry.asid = some (rootId, root) := by
    unfold resolveAsidRoot at hResolve ⊢
    rw [hAsidTable, hObjects] at hResolve
    exact hResolve
  exact hConsist entry (hSub entry hMem) rootId root hResolve'

/-- **WS-SM SM7.C.5**: a local invalidation on core `c` preserves the
per-core invariant — retiring an operand only removes entries (never adds
one, never changes the page tables), so every core's view stays
consistent.  Invalidation is *always* safe. -/
theorem tlbInvalidateOnCore_preserves_tlbInvalidationConsistent_perCore
    (st : SystemState) (c : CoreId) (op : TlbInvalidation)
    (h : tlbInvalidationConsistent_perCore st) :
    tlbInvalidationConsistent_perCore (tlbInvalidateOnCore st c op) := by
  intro c'
  refine tlbConsistent_of_subset_of_state_frame
    (tlbInvalidateOnCore_frame st c op).1
    (tlbInvalidateOnCore_frame st c op).2.1 ?_ (h c')
  intro e he
  by_cases hcc : c = c'
  · subst hcc
    exact tlbInvalidateOnCore_subset st c op he
  · rw [tlbInvalidateOnCore_tlbOnCore_ne st op hcc] at he
    exact he

-- ============================================================================
-- SM7.C.6 — tlbShootdown_invalidates_perCore (Theorem 3.3.1, mounted)
-- ============================================================================

/-- **WS-SM SM7.C.6** (`tlbShootdown_invalidates_perCore`): the corollary
of Theorem 3.3.1 (`tlbShootdownBroadcast_invalidatesAllCores`) on the
mounted per-core field.  After a `tlbInvalidateOnAllCores` whose target
set covers every non-initiator core, **no core** retains any entry the
operand covers — the SMP-C4 use-after-unmap closure at the per-core TLB
model.  The proof is the mechanical instantiation the SM7.B design
promised: `tlbInvalidateOnAllCores`'s post-state per-core views are
exactly the `shootdownRoundViews` vector Theorem 3.3.1 quantifies over. -/
theorem tlbShootdown_invalidates_perCore
    (st : SystemState) (initiator : CoreId) {targets : List CoreId}
    (hcov : ∀ c : CoreId, c ≠ initiator → c ∈ targets)
    (op : TlbInvalidation) {st' : SystemState}
    {sgis : List (CoreId × SgiKind)}
    (h : tlbInvalidateOnAllCores st initiator targets op = some (st', sgis)) :
    ∀ (c : CoreId) {e : TlbEntry}, tlbEntryMatches op e = true →
      e ∉ (tlbOnCore st' c).entries := by
  intro c e he
  simp only [tlbOnCore, tlbInvalidateOnAllCores_perCoreTlb h]
  exact tlbShootdownBroadcast_invalidatesAllCores st.perCoreTlb initiator hcov op c he

-- ============================================================================
-- SM7.C.7 — tlbConsistency_cross_subsystem (the memory-subsystem capstone)
-- ============================================================================

/-- **WS-SM SM7.C.7** (`tlbConsistency_cross_subsystem`): the
cross-subsystem capstone tying the SM7.B **shootdown protocol**, the
SM7.C **per-core TLB model**, and the **VSpace page tables**.  A covering
cross-core invalidation, applied to a per-core-consistent state:

1. **removes every covered (stale) entry on every core** — the SMP-C4
   safety guarantee (no core caches a translation the operand retired);
2. **preserves per-core consistency** — the broadcast frames the page
   tables (`objects` + `asidTable` ⇒ `resolveAsidRoot` unchanged) and
   only removes entries, so every core's surviving view still matches the
   page tables.

Together: the shootdown subsystem keeps the per-core TLB model coherent
with the VSpace subsystem across cores.  This is the memory-subsystem
(protocol × TLB-model × page-table) analogue of the kernel-subsystem
`crossSubsystemInvariant` bridges. -/
theorem tlbConsistency_cross_subsystem
    (st : SystemState) (initiator : CoreId) {targets : List CoreId}
    (hcov : ∀ c : CoreId, c ≠ initiator → c ∈ targets)
    (op : TlbInvalidation)
    (hConsist : tlbInvalidationConsistent_perCore st)
    {st' : SystemState} {sgis : List (CoreId × SgiKind)}
    (h : tlbInvalidateOnAllCores st initiator targets op = some (st', sgis)) :
    (∀ (c : CoreId) {e : TlbEntry}, tlbEntryMatches op e = true →
        e ∉ (tlbOnCore st' c).entries) ∧
    tlbInvalidationConsistent_perCore st' := by
  refine ⟨tlbShootdown_invalidates_perCore st initiator hcov op h, ?_⟩
  intro c
  refine tlbConsistent_of_subset_of_state_frame
    (tlbInvalidateOnAllCores_objects h)
    (tlbInvalidateOnAllCores_asidTable h) ?_ (hConsist c)
  intro e he
  simp only [tlbOnCore] at he ⊢
  rw [tlbInvalidateOnAllCores_perCoreTlb h, shootdownRoundViews_get] at he
  split at he
  · exact mem_of_mem_applyTlbInvalidation he
  · exact he

end SeLe4n.Kernel.Architecture
