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
quiescent state (`tlbInvalidateOnAllCores_isSome_of_quiescent`).

**This is the eager _view-outcome abstraction_, NOT a completed round**
(PR #844 P2): it posts the round (leaving the targets' descriptors
pending and their acks down) while *eagerly* showing the resulting views,
so the post-state deliberately has the views ahead of the ack protocol —
it exists to state the SM7.C.6/C.7 *view* theorems (`tlbShootdown_invalidates_perCore`
/ `tlbConsistency_cross_subsystem`: "after a covering invalidation no core
retains a covered entry").  The **operative, drains-at-ack** round — the one
the live `completeShootdownRounds` seam realises, which evolves each target's
view *at* its handler acknowledgment and leaves the round quiescent — is
`shootdownRoundPerCore` (with `shootdownRoundPerCore_invalidates_perCore`
/ `_preserves_tlbInvalidationConsistent_perCore` / `shootdownRoundPerCore_cross_subsystem`
the faithful completed-round counterparts).  Do not read a `tlbInvalidateOnAllCores`
post-state as a real intermediate protocol state. -/
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

/-- **WS-SM SM7.C.5**: a single cached entry is consistent with the current
page tables — if its ASID resolves to a root, the cached mapping matches the
root's lookup.  The per-entry kernel of `tlbConsistent`. -/
def tlbEntryConsistent (st : SystemState) (e : TlbEntry) : Prop :=
  ∀ rootId root, resolveAsidRoot st e.asid = some (rootId, root) →
    VSpaceRoot.lookup root e.vaddr = some (e.paddr, e.perms)

/-- **WS-SM SM7.C.5**: a single cached entry is *allowed* on core `c` — it is
either consistent with the current page tables, or **covered by a pending
shootdown descriptor targeting `c`** (a stale entry is admissible exactly when
a shootdown is already scheduled to retire it).  This is the per-entry kernel
of the SM7.F.2 pending-aware invariant. -/
def tlbEntryOk (st : SystemState) (c : CoreId) (e : TlbEntry) : Prop :=
  tlbEntryConsistent st e ∨
    ∃ desc ∈ st.tlbShootdown.pendingOnCore c, tlbEntryMatches desc.op e = true

/-- **WS-SM SM7.C.5** (SM7.F.2 — the honest, pending-aware form): the per-core
TLB consistency invariant.  On *every* core, *every* cached entry is either
consistent with the current page tables or covered by a pending shootdown
descriptor for that core.  This is the invariant genuinely preserved once the
model holds real fills (SM7.F): `vspaceUnmapPageWithShootdown` makes an entry
stale **and** posts the covering descriptor in the same step (the pending
disjunct), and the `.tlbShootdownReq` handler drains a core's whole queue, so
survivors must be consistent (the consistent disjunct).  It weakens the
v0.32.80 unconditional `∀ c, tlbConsistent st (tlbOnCore st c)` — which was
only vacuously true (empty views) and false for a populated pending-round
state — to the form that holds across every reachable kernel state.  The 13th
`proofLayerInvariantBundle` conjunct (`Invariant.lean`). -/
def tlbInvalidationConsistent_perCore (st : SystemState) : Prop :=
  ∀ c : CoreId, ∀ e ∈ (tlbOnCore st c).entries, tlbEntryOk st c e

/-- **WS-SM SM7.C.5**: a fully page-table-consistent view satisfies the
pending-aware per-core predicate (every entry rides the *consistent* disjunct)
— the bridge from the old unconditional form to the honest one. -/
theorem tlbEntryOk_of_tlbConsistent {st : SystemState} {c : CoreId}
    {t : TlbState} (h : tlbConsistent st t) :
    ∀ e ∈ t.entries, tlbEntryOk st c e := by
  intro e he
  exact Or.inl (h e he)

/-- **WS-SM SM7.C.5** (the transport lever): `tlbEntryOk` carries across a
frame that preserves the page tables (`objects` + `asidTable` ⇒ the same
`resolveAsidRoot`) and does not *drop* any pending descriptor for `c`
(pending-superset).  Every preservation proof rides this: an invalidation
removes entries (survivors keep their witness) and never shrinks the page
tables or the pending set below what covers a stale survivor. -/
theorem tlbEntryOk_of_frame {st st' : SystemState} {c : CoreId} {e : TlbEntry}
    (hObjects : st'.objects = st.objects)
    (hAsidTable : st'.asidTable = st.asidTable)
    (hPend : ∀ d ∈ st.tlbShootdown.pendingOnCore c,
      d ∈ st'.tlbShootdown.pendingOnCore c)
    (h : tlbEntryOk st c e) : tlbEntryOk st' c e := by
  rcases h with hCon | ⟨desc, hmem, hmatch⟩
  · refine Or.inl ?_
    intro rootId root hResolve
    have hResolve' : resolveAsidRoot st e.asid = some (rootId, root) := by
      unfold resolveAsidRoot at hResolve ⊢
      rw [hAsidTable, hObjects] at hResolve; exact hResolve
    exact hCon rootId root hResolve'
  · exact Or.inr ⟨desc, hPend desc hmem, hmatch⟩

/-- **WS-SM SM7.C.5**: the common case of `tlbEntryOk_of_frame` — an op that
frames the page tables **and** the shootdown state entirely (equality) carries
`tlbEntryOk` unchanged. -/
theorem tlbEntryOk_of_frame_eq {st st' : SystemState} {c : CoreId} {e : TlbEntry}
    (hObjects : st'.objects = st.objects) (hAsidTable : st'.asidTable = st.asidTable)
    (hShoot : st'.tlbShootdown = st.tlbShootdown)
    (h : tlbEntryOk st c e) : tlbEntryOk st' c e :=
  tlbEntryOk_of_frame hObjects hAsidTable (fun d hd => by rw [hShoot]; exact hd) h

/-- **WS-SM SM7.C.5**: per-entry consistency carries across a page-table frame
(`objects` + `asidTable` ⇒ the same `resolveAsidRoot`). -/
theorem tlbEntryConsistent_of_frame {st st' : SystemState} {e : TlbEntry}
    (hObjects : st'.objects = st.objects) (hAsidTable : st'.asidTable = st.asidTable)
    (h : tlbEntryConsistent st e) : tlbEntryConsistent st' e := by
  intro rootId root hResolve
  have hResolve' : resolveAsidRoot st e.asid = some (rootId, root) := by
    unfold resolveAsidRoot at hResolve ⊢
    rw [hAsidTable, hObjects] at hResolve; exact hResolve
  exact h rootId root hResolve'

/-- **WS-SM SM7.F.2**: on a **quiescent** shootdown state (no pending
descriptors), the pending disjunct of `tlbEntryOk` is unavailable, so every
admissible entry is in fact consistent.  The bridge the round-level capstones
use: a covering invalidation from a quiescent consistent state keeps every
survivor consistent. -/
theorem tlbEntryConsistent_of_ok_of_quiescent {st : SystemState} {c : CoreId}
    {e : TlbEntry} (hq : shootdownQuiescent st.tlbShootdown) (h : tlbEntryOk st c e) :
    tlbEntryConsistent st e := by
  rcases h with hc | ⟨desc, hmem, _⟩
  · exact hc
  · rw [hq.1 c] at hmem; simp at hmem

/-- **WS-SM SM7.F.2** (the drain-survivor lever): an entry that *survives*
`applyTlbInvalidations t ops` is matched by **none** of the applied operands —
invalidation only removes, so a survivor was present after every operand's
application, hence never removed by any.  This is what proves the
`.tlbShootdownReq` handler's survivors consistent: a survivor cannot have been
covered by a (drained) pending descriptor, so it must ride the consistent
disjunct. -/
theorem applyTlbInvalidations_survivor_not_matched :
    ∀ (ops : List TlbInvalidation) (t : TlbState) (e : TlbEntry),
      e ∈ (applyTlbInvalidations t ops).entries →
      ∀ op ∈ ops, tlbEntryMatches op e = false := by
  intro ops
  induction ops with
  | nil => intro _ _ _ op hop; simp at hop
  | cons op' ops' ih =>
    intro t e he op hop
    rw [applyTlbInvalidations_cons] at he
    rcases List.mem_cons.mp hop with heq | hmem
    · subst heq
      have he1 : e ∈ (applyTlbInvalidation t op).entries := mem_of_mem_applyTlbInvalidations he
      cases hb : tlbEntryMatches op e with
      | false => rfl
      | true => exact absurd he1 (applyTlbInvalidation_removes hb t)
    · exact ih (applyTlbInvalidation t op') e he op hmem

/-- **WS-SM SM7.C.5**: at boot the per-core TLB invariant holds vacuously —
every core's view is empty (`default_tlbOnCore`), so there is no entry to
witness.  The bundle boot witness. -/
theorem default_tlbInvalidationConsistent_perCore :
    tlbInvalidationConsistent_perCore (default : SystemState) := by
  intro c e he
  rw [default_tlbOnCore] at he
  simp [TlbState.empty] at he

/-- **WS-SM SM7.C.5**: the per-core invariant projects to the boot core — each
of the boot core's cached entries is admissible (consistent or pending-covered). -/
theorem tlbInvalidationConsistent_perCore_bootCore {st : SystemState}
    (h : tlbInvalidationConsistent_perCore st) :
    ∀ e ∈ (tlbOnCore st bootCoreId).entries, tlbEntryOk st bootCoreId e :=
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
  intro c' e he
  have hpre : e ∈ (tlbOnCore st c').entries := by
    by_cases hcc : c = c'
    · subst hcc; exact tlbInvalidateOnCore_subset st c op he
    · rw [tlbInvalidateOnCore_tlbOnCore_ne st op hcc] at he; exact he
  exact tlbEntryOk_of_frame_eq
    (tlbInvalidateOnCore_frame st c op).1
    (tlbInvalidateOnCore_frame st c op).2.1
    (tlbInvalidateOnCore_frame st c op).2.2.2.2
    (h c' e hpre)

/-- **WS-SM SM7.C.5** (the insert half of the model's safety story): the
hardware translation walker preserves the per-core invariant **provided it
caches only a translation that matches the current page tables** — exactly
what a real page-table walk resolves.  Together with
`tlbInvalidateOnCore_preserves_…` this closes the model's consistency story:
the walker never caches a stale entry, and invalidation never breaks
consistency.  The `hEntry` hypothesis is the walker's contract (a walk that
resolved `(entry.asid, entry.vaddr)` to `(entry.paddr, entry.perms)`). -/
theorem tlbInsertOnCore_preserves_tlbInvalidationConsistent_perCore
    (st : SystemState) (c : CoreId) (entry : TlbEntry)
    (hConsist : tlbInvalidationConsistent_perCore st)
    (hEntry : ∀ rootId root, resolveAsidRoot st entry.asid = some (rootId, root) →
      VSpaceRoot.lookup root entry.vaddr = some (entry.paddr, entry.perms)) :
    tlbInvalidationConsistent_perCore (tlbInsertOnCore st c entry) := by
  have hObj : (tlbInsertOnCore st c entry).objects = st.objects :=
    (tlbInsertOnCore_frame st c entry).1
  have hAsid : (tlbInsertOnCore st c entry).asidTable = st.asidTable :=
    (tlbInsertOnCore_frame st c entry).2.1
  have hShoot : (tlbInsertOnCore st c entry).tlbShootdown = st.tlbShootdown :=
    (tlbInsertOnCore_frame st c entry).2.2.2.2
  intro c' e he
  by_cases hcc : c = c'
  · subst hcc
    simp only [tlbInsertOnCore, setTlbOnCore_tlbOnCore_self] at he
    rcases List.mem_cons.mp he with heq | hmemOld
    · -- the fresh entry: consistent by construction (hEntry + page-table frame).
      subst heq
      refine Or.inl ?_
      intro rootId root hResolve
      have hResolve' : resolveAsidRoot st e.asid = some (rootId, root) := by
        unfold resolveAsidRoot at hResolve ⊢; rw [hAsid, hObj] at hResolve; exact hResolve
      exact hEntry rootId root hResolve'
    · exact tlbEntryOk_of_frame_eq hObj hAsid hShoot (hConsist c e hmemOld)
  · have hpre : e ∈ (tlbOnCore st c').entries := by
      rw [tlbInsertOnCore_tlbOnCore_ne st entry hcc] at he; exact he
    exact tlbEntryOk_of_frame_eq hObj hAsid hShoot (hConsist c' e hpre)

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
    (hq : shootdownQuiescent st.tlbShootdown)
    (hcov : ∀ c : CoreId, c ≠ initiator → c ∈ targets)
    (op : TlbInvalidation)
    (hConsist : tlbInvalidationConsistent_perCore st)
    {st' : SystemState} {sgis : List (CoreId × SgiKind)}
    (h : tlbInvalidateOnAllCores st initiator targets op = some (st', sgis)) :
    (∀ (c : CoreId) {e : TlbEntry}, tlbEntryMatches op e = true →
        e ∉ (tlbOnCore st' c).entries) ∧
    tlbInvalidationConsistent_perCore st' := by
  refine ⟨tlbShootdown_invalidates_perCore st initiator hcov op h, ?_⟩
  intro c e he
  -- The op only removes; the broadcast frames the page tables.  From a
  -- quiescent state every pre-entry is consistent, so every survivor is too.
  have hpre : e ∈ (tlbOnCore st c).entries := by
    simp only [tlbOnCore] at he ⊢
    rw [tlbInvalidateOnAllCores_perCoreTlb h, shootdownRoundViews_get] at he
    split at he
    · exact mem_of_mem_applyTlbInvalidation he
    · exact he
  refine Or.inl (tlbEntryConsistent_of_frame
    (tlbInvalidateOnAllCores_objects h) (tlbInvalidateOnAllCores_asidTable h) ?_)
  exact tlbEntryConsistent_of_ok_of_quiescent hq (hConsist c e hpre)

-- ============================================================================
-- SM7.C.4 (total form) — tlbInvalidateOnAllCoresCoalescing
-- ============================================================================

/-- **WS-SM SM7.C.4** (total form): the coalescing cross-core invalidation
— the analogue of the SM7.B `tlbShootdownBroadcastCoalescing` for the
per-core model.  Unlike the strict `tlbInvalidateOnAllCores` (fail-closed
`none` on a full queue), this **never fails**: at capacity the posting
collapses to a covered full flush (`postShootdownRoundCoalescing`), so a
live caller that batches past `maxPendingPerCore` can never fail a syscall.
The per-core view evolution is identical (`shootdownRoundViews`), and the
two forms agree wherever the strict form succeeds
(`tlbInvalidateOnAllCoresCoalescing_eq_strict`). -/
def tlbInvalidateOnAllCoresCoalescing (st : SystemState) (initiator : CoreId)
    (targets : List CoreId) (op : TlbInvalidation) :
    SystemState × List (CoreId × SgiKind) :=
  ({ tlbShootdownBroadcastCoalescing st initiator targets op with
      perCoreTlb := shootdownRoundViews st.perCoreTlb initiator targets op },
    targets.map (fun c => (c, SgiKind.tlbShootdownReq)))

/-- **WS-SM SM7.C.4**: the coalescing form's per-core views are the same
`shootdownRoundViews` vector as the strict form's. -/
theorem tlbInvalidateOnAllCoresCoalescing_perCoreTlb (st : SystemState)
    (initiator : CoreId) (targets : List CoreId) (op : TlbInvalidation) :
    (tlbInvalidateOnAllCoresCoalescing st initiator targets op).1.perCoreTlb =
      shootdownRoundViews st.perCoreTlb initiator targets op := rfl

/-- **WS-SM SM7.C.4**: the coalescing form frames the page-table
subsystem — objects and the ASID table are unchanged (the coalescing
broadcast touches only `tlbShootdown`, and the view update only
`perCoreTlb`). -/
theorem tlbInvalidateOnAllCoresCoalescing_frame (st : SystemState)
    (initiator : CoreId) (targets : List CoreId) (op : TlbInvalidation) :
    (tlbInvalidateOnAllCoresCoalescing st initiator targets op).1.objects =
      st.objects ∧
    (tlbInvalidateOnAllCoresCoalescing st initiator targets op).1.asidTable =
      st.asidTable := ⟨rfl, rfl⟩

/-- **WS-SM SM7.C.4**: wherever the strict `tlbInvalidateOnAllCores`
succeeds (always from a quiescent state), the coalescing form commits the
identical state and SGI list — the theorems quantify over the strict form,
the runtime posts through the total form. -/
theorem tlbInvalidateOnAllCoresCoalescing_eq_strict {st st' : SystemState}
    {initiator : CoreId} {targets : List CoreId} {op : TlbInvalidation}
    {sgis : List (CoreId × SgiKind)}
    (h : tlbInvalidateOnAllCores st initiator targets op = some (st', sgis)) :
    tlbInvalidateOnAllCoresCoalescing st initiator targets op = (st', sgis) := by
  obtain ⟨posted, hb, hst⟩ := tlbInvalidateOnAllCores_spec h
  have hsgi := tlbInvalidateOnAllCores_sgis h
  unfold tlbInvalidateOnAllCoresCoalescing
  rw [tlbShootdownBroadcastCoalescing_eq_strict hb, hst, hsgi]

-- ============================================================================
-- SM7.C.5 (runtime checkability) — decidable per-core consistency
-- ============================================================================

/-- **WS-SM SM7.C.5**: an executable Boolean check of single-view TLB
consistency.  The `∀ rootId root, resolveAsidRoot … = some … → …` clause of
`tlbConsistent` is not `Fintype`-decidable (`ObjId`/`VSpaceRoot` are
infinite), so a `Decidable` instance needs this computable witness: for
each cached entry, if its ASID resolves to a root the cached mapping must
match the root's lookup; an entry whose ASID resolves to nothing is
vacuously consistent. -/
def tlbConsistentCheck (st : SystemState) (tlb : TlbState) : Bool :=
  tlb.entries.all (fun e =>
    match resolveAsidRoot st e.asid with
    | some (_, root) => VSpaceRoot.lookup root e.vaddr == some (e.paddr, e.perms)
    | none => true)

/-- **WS-SM SM7.C.5**: the executable check is sound *and* complete for
`tlbConsistent` — it decides it. -/
theorem tlbConsistentCheck_iff (st : SystemState) (tlb : TlbState) :
    tlbConsistentCheck st tlb = true ↔ tlbConsistent st tlb := by
  unfold tlbConsistentCheck tlbConsistent
  rw [List.all_eq_true]
  constructor
  · intro h e hMem rootId root hResolve
    have he := h e hMem
    rw [hResolve] at he
    simpa using he
  · intro h e hMem
    cases hR : resolveAsidRoot st e.asid with
    | none => rfl
    | some pair =>
        obtain ⟨rootId, root⟩ := pair
        simp only [beq_iff_eq]
        exact h e hMem rootId root hR

instance (st : SystemState) (tlb : TlbState) : Decidable (tlbConsistent st tlb) :=
  decidable_of_iff _ (tlbConsistentCheck_iff st tlb)

/-- **WS-SM SM7.C.5**: an executable Boolean check of single-entry
consistency (the per-entry kernel of `tlbConsistentCheck`). -/
def tlbEntryConsistentCheck (st : SystemState) (e : TlbEntry) : Bool :=
  match resolveAsidRoot st e.asid with
  | some (_, root) => VSpaceRoot.lookup root e.vaddr == some (e.paddr, e.perms)
  | none => true

/-- **WS-SM SM7.C.5**: the per-entry consistency check decides `tlbEntryConsistent`. -/
theorem tlbEntryConsistentCheck_iff (st : SystemState) (e : TlbEntry) :
    tlbEntryConsistentCheck st e = true ↔ tlbEntryConsistent st e := by
  unfold tlbEntryConsistentCheck tlbEntryConsistent
  constructor
  · intro h rootId root hResolve
    rw [hResolve] at h; simpa using h
  · intro h
    cases hR : resolveAsidRoot st e.asid with
    | none => rfl
    | some pair =>
        obtain ⟨rootId, root⟩ := pair
        simp only [beq_iff_eq]
        exact h rootId root hR

/-- **WS-SM SM7.C.5** (SM7.F.2): an executable Boolean check of the per-entry
*admissibility* predicate `tlbEntryOk` — consistent, or covered by a pending
descriptor for `c`. -/
def tlbEntryOkCheck (st : SystemState) (c : CoreId) (e : TlbEntry) : Bool :=
  tlbEntryConsistentCheck st e ||
    (st.tlbShootdown.pendingOnCore c).any (fun desc => tlbEntryMatches desc.op e)

/-- **WS-SM SM7.C.5**: the per-entry admissibility check decides `tlbEntryOk`. -/
theorem tlbEntryOkCheck_iff (st : SystemState) (c : CoreId) (e : TlbEntry) :
    tlbEntryOkCheck st c e = true ↔ tlbEntryOk st c e := by
  unfold tlbEntryOkCheck tlbEntryOk
  rw [Bool.or_eq_true, tlbEntryConsistentCheck_iff, List.any_eq_true]

/-- **WS-SM SM7.C.5** (SM7.F.2): an executable Boolean check of the pending-aware
per-core invariant — every core's every entry is admissible.  This is what
makes the **13th `proofLayerInvariantBundle` conjunct** runtime-verifiable,
exactly as the 12th (`pendingBounded`) is (`SmpTlbShootdownSuite` §5 probes it
on concrete states). -/
def tlbInvalidationConsistentCheck_perCore (st : SystemState) : Bool :=
  allCores.all (fun c => (tlbOnCore st c).entries.all (fun e => tlbEntryOkCheck st c e))

/-- **WS-SM SM7.C.5**: the per-core check decides the per-core invariant. -/
theorem tlbInvalidationConsistentCheck_perCore_iff (st : SystemState) :
    tlbInvalidationConsistentCheck_perCore st = true ↔
      tlbInvalidationConsistent_perCore st := by
  unfold tlbInvalidationConsistentCheck_perCore tlbInvalidationConsistent_perCore
  have hmem : ∀ c : CoreId, c ∈ allCores := by intro c; simp [allCores]
  constructor
  · intro h c e he
    rw [← tlbEntryOkCheck_iff]
    rw [List.all_eq_true] at h
    have hc := h c (hmem c)
    rw [List.all_eq_true] at hc
    exact hc e he
  · intro h
    rw [List.all_eq_true]
    intro c _
    rw [List.all_eq_true]
    intro e he
    rw [tlbEntryOkCheck_iff]
    exact h c e he

instance (st : SystemState) : Decidable (tlbInvalidationConsistent_perCore st) :=
  decidable_of_iff _ (tlbInvalidationConsistentCheck_perCore_iff st)

-- ============================================================================
-- SM7.C operational layer — the per-core drain the live seam runs
--
-- SM7.B's live shootdown handler (`handleTlbShootdownReqOnCore`) and its
-- round evolve the single boot-core view `SystemState.tlb`.  This layer is
-- the *per-core* generalisation: each core's handler drains *its own*
-- posted queue onto *its own* `perCoreTlb` view, so the mounted field
-- evolves by the REAL per-descriptor drain — not a parallel argument-driven
-- re-computation.  It is what the live `completeShootdownRounds` seam runs,
-- and its per-core view result is proven **equal** to the abstract
-- `shootdownRoundViews` vector Theorem 3.3.1 quantifies over.
-- ============================================================================

/-- **WS-SM SM7.C**: the SM7.B single-view handler frames the per-core TLB
model — it writes `st.tlb` and `st.tlbShootdown`, never `perCoreTlb`. -/
@[simp] theorem handleTlbShootdownReqOnCore_perCoreTlb_eq (st : SystemState)
    (c : CoreId) :
    (handleTlbShootdownReqOnCore st c).perCoreTlb = st.perCoreTlb := rfl

/-- **WS-SM SM7.C** (operational per-core handler): the `.tlbShootdownReq`
handler on the per-core model.  Runs the SM7.B single-view handler (drain
`c`'s queue, retire the drained operands on `st.tlb`, acknowledge `c`) AND
retires the *same* drained operands on core `c`'s own `perCoreTlb` view.
The two commit the identical `tlb` / `tlbShootdown` effect, so wiring it
into the live seam is trace-safe; the per-core drain is what makes
`perCoreTlb` operative. -/
def handleTlbShootdownReqOnCorePerCore (st : SystemState) (c : CoreId) :
    SystemState :=
  setTlbOnCore (handleTlbShootdownReqOnCore st c) c
    (applyTlbInvalidations (tlbOnCore st c)
      ((drainShootdowns st.tlbShootdown c).1.map (·.op)))

/-- **WS-SM SM7.C**: the per-core handler's `tlb` effect is exactly the
SM7.B single-view handler's (the trace-safety anchor). -/
@[simp] theorem handleTlbShootdownReqOnCorePerCore_tlb_eq (st : SystemState)
    (c : CoreId) :
    (handleTlbShootdownReqOnCorePerCore st c).tlb =
      (handleTlbShootdownReqOnCore st c).tlb := rfl

/-- **WS-SM SM7.C**: the per-core handler's shootdown-state effect is
exactly the SM7.B single-view handler's. -/
@[simp] theorem handleTlbShootdownReqOnCorePerCore_tlbShootdown_eq
    (st : SystemState) (c : CoreId) :
    (handleTlbShootdownReqOnCorePerCore st c).tlbShootdown =
      (handleTlbShootdownReqOnCore st c).tlbShootdown := rfl

/-- **WS-SM SM7.C**: the per-core handler retires `c`'s drained operands on
`c`'s own view. -/
theorem handleTlbShootdownReqOnCorePerCore_tlbOnCore_self (st : SystemState)
    (c : CoreId) :
    tlbOnCore (handleTlbShootdownReqOnCorePerCore st c) c =
      applyTlbInvalidations (tlbOnCore st c)
        ((drainShootdowns st.tlbShootdown c).1.map (·.op)) := by
  simp [handleTlbShootdownReqOnCorePerCore]

/-- **WS-SM SM7.C**: the per-core handler leaves every other core's view
untouched — a handler is a local (this-core) event. -/
theorem handleTlbShootdownReqOnCorePerCore_tlbOnCore_ne (st : SystemState)
    {c c' : CoreId} (h : c ≠ c') :
    tlbOnCore (handleTlbShootdownReqOnCorePerCore st c) c' = tlbOnCore st c' := by
  rw [handleTlbShootdownReqOnCorePerCore, setTlbOnCore_tlbOnCore_ne _ _ h]
  simp only [tlbOnCore, handleTlbShootdownReqOnCore_perCoreTlb_eq]

/-- **WS-SM SM7.C**: the per-core handler's `perCoreTlb` effect as a single
per-core-view write (the SM4.B path-a `set` form the fold reasons over). -/
theorem handleTlbShootdownReqOnCorePerCore_perCoreTlb (st : SystemState)
    (c : CoreId) :
    (handleTlbShootdownReqOnCorePerCore st c).perCoreTlb =
      setTlbViewOnCore st.perCoreTlb c
        (applyTlbInvalidations (tlbOnCore st c)
          ((drainShootdowns st.tlbShootdown c).1.map (·.op))) := by
  simp only [handleTlbShootdownReqOnCorePerCore, setTlbOnCore,
    handleTlbShootdownReqOnCore_perCoreTlb_eq, setTlbViewOnCore]

/-- **WS-SM SM7.C** (operational fidelity / non-vacuity bridge): on a state
whose queue at `c` is exactly the round's posted descriptor — what
`tlbShootdownBroadcast_posts_singleton` establishes — the per-core handler's
real drain retires exactly one application of the round's operand on `c`'s
view.  This ties the REAL per-core drain to the abstract `shootdownRoundViews`
step (`applyTlbInvalidation (view c) op`); it is *not* an axiomatised
re-computation. -/
theorem handleTlbShootdownReqOnCorePerCore_applies_posted_op {st : SystemState}
    {c : CoreId} {op : TlbInvalidation} {initiator : CoreId}
    (hpend : st.tlbShootdown.pendingOnCore c =
      [{ op := op, initiator := initiator }]) :
    tlbOnCore (handleTlbShootdownReqOnCorePerCore st c) c =
      applyTlbInvalidation (tlbOnCore st c) op := by
  rw [handleTlbShootdownReqOnCorePerCore_tlbOnCore_self, drainShootdowns_fst,
      hpend]
  rfl

/-- **WS-SM SM7.C**: the per-core handler never adds an entry to any core's
view — every core's post-view is a subset of its pre-view (invalidation
only removes).  The monotonicity the consistency-preservation proof rides. -/
theorem handleTlbShootdownReqOnCorePerCore_subset (st : SystemState)
    (c c' : CoreId) {e : TlbEntry}
    (h : e ∈ (tlbOnCore (handleTlbShootdownReqOnCorePerCore st c) c').entries) :
    e ∈ (tlbOnCore st c').entries := by
  by_cases hcc : c = c'
  · subst hcc
    rw [handleTlbShootdownReqOnCorePerCore_tlbOnCore_self] at h
    exact mem_of_mem_applyTlbInvalidations h
  · rw [handleTlbShootdownReqOnCorePerCore_tlbOnCore_ne st hcc] at h
    exact h

/-- **WS-SM SM7.C**: the per-core handler touches only the TLB model + the
shootdown state — objects, the ASID table, scheduler, and machine frame, so
`resolveAsidRoot` is preserved. -/
theorem handleTlbShootdownReqOnCorePerCore_frame (st : SystemState)
    (c : CoreId) :
    (handleTlbShootdownReqOnCorePerCore st c).objects = st.objects ∧
    (handleTlbShootdownReqOnCorePerCore st c).asidTable = st.asidTable :=
  ⟨rfl, rfl⟩

/-- **WS-SM SM7.C**: the per-core handler preserves the per-core invariant
— it only removes entries, and it frames the page tables. -/
theorem handleTlbShootdownReqOnCorePerCore_preserves_tlbInvalidationConsistent_perCore
    (st : SystemState) (c : CoreId)
    (h : tlbInvalidationConsistent_perCore st) :
    tlbInvalidationConsistent_perCore (handleTlbShootdownReqOnCorePerCore st c) := by
  have hObj := (handleTlbShootdownReqOnCorePerCore_frame st c).1
  have hAsid := (handleTlbShootdownReqOnCorePerCore_frame st c).2
  intro c' e he
  have hpre : e ∈ (tlbOnCore st c').entries :=
    handleTlbShootdownReqOnCorePerCore_subset st c c' he
  by_cases hcc : c = c'
  · -- Core `c`'s queue is drained to empty, so the pending disjunct is gone:
    -- a survivor of the drain must be *consistent* (it was not covered by any
    -- drained pending descriptor, or it would have been removed).
    subst hcc
    rw [handleTlbShootdownReqOnCorePerCore_tlbOnCore_self] at he
    rcases h c e hpre with hCon | ⟨desc, hmemDesc, hmatch⟩
    · exact Or.inl (tlbEntryConsistent_of_frame hObj hAsid hCon)
    · exfalso
      have hopmem : desc.op ∈ (drainShootdowns st.tlbShootdown c).1.map (·.op) := by
        rw [drainShootdowns_fst]; exact List.mem_map_of_mem hmemDesc
      have hnot := applyTlbInvalidations_survivor_not_matched _ _ _ he desc.op hopmem
      rw [hnot] at hmatch
      exact absurd hmatch (by decide)
  · -- Every other core's view and its pending queue are untouched.
    refine tlbEntryOk_of_frame hObj hAsid ?_ (h c' e hpre)
    intro d hd
    rw [handleTlbShootdownReqOnCorePerCore_tlbShootdown_eq,
        handleTlbShootdownReqOnCore_tlbShootdown_eq,
        completeShootdownOnCore_frame_pending _ (Ne.symm hcc)]
    exact hd

/-- **WS-SM SM7.C** (the initiator's local step, per-core): the SM7.B
initiator local invalidation (step 3) lifted to also retire the operand on
the *initiator's own* `perCoreTlb` view. -/
def tlbShootdownLocalPerCore (st : SystemState) (initiator : CoreId)
    (op : TlbInvalidation) : SystemState :=
  setTlbOnCore (tlbShootdownLocal st op) initiator
    (applyTlbInvalidation (tlbOnCore st initiator) op)

/-- **WS-SM SM7.C**: the per-core local step's `tlb` effect equals the
SM7.B single-view local step's. -/
@[simp] theorem tlbShootdownLocalPerCore_tlb_eq (st : SystemState)
    (initiator : CoreId) (op : TlbInvalidation) :
    (tlbShootdownLocalPerCore st initiator op).tlb =
      (tlbShootdownLocal st op).tlb := rfl

/-- **WS-SM SM7.C**: the per-core local step frames the shootdown state. -/
@[simp] theorem tlbShootdownLocalPerCore_tlbShootdown_eq (st : SystemState)
    (initiator : CoreId) (op : TlbInvalidation) :
    (tlbShootdownLocalPerCore st initiator op).tlbShootdown =
      st.tlbShootdown := rfl

/-- **WS-SM SM7.C**: the per-core local step's `perCoreTlb` effect as a
single per-core-view write. -/
theorem tlbShootdownLocalPerCore_perCoreTlb (st : SystemState)
    (initiator : CoreId) (op : TlbInvalidation) :
    (tlbShootdownLocalPerCore st initiator op).perCoreTlb =
      setTlbViewOnCore st.perCoreTlb initiator
        (applyTlbInvalidation (tlbOnCore st initiator) op) := by
  simp only [tlbShootdownLocalPerCore, setTlbOnCore, setTlbViewOnCore]
  rfl

/-- **WS-SM SM7.C** (the per-core fold's view result): folding the per-core
handler over targets — each of which holds exactly the round's posted
descriptor (`(pendingOnCore c).map (·.op) = [op]`) — evolves `perCoreTlb`
by the abstract `shootdownRoundViews` per-target step over the *real*
drain.  This is the operational-fidelity lemma: the live per-core drain and
the abstract view vector coincide, step for step (not by shared arguments). -/
theorem foldl_handleTlbShootdownReqOnCorePerCore_perCoreTlb {op : TlbInvalidation} :
    ∀ (targets : List CoreId), targets.Nodup →
    ∀ (st : SystemState),
      (∀ c ∈ targets, (st.tlbShootdown.pendingOnCore c).map (·.op) = [op]) →
      (targets.foldl handleTlbShootdownReqOnCorePerCore st).perCoreTlb =
        targets.foldl (fun vs c =>
          setTlbViewOnCore vs c (applyTlbInvalidation (vs.get c) op))
          st.perCoreTlb := by
  intro targets
  induction targets with
  | nil => intro _ st _; rfl
  | cons t ts ih =>
    intro hnd st hpost
    rw [List.nodup_cons] at hnd
    obtain ⟨htnotin, htsnd⟩ := hnd
    rw [List.foldl_cons, List.foldl_cons]
    have hpost' : ∀ c ∈ ts,
        ((handleTlbShootdownReqOnCorePerCore st t).tlbShootdown.pendingOnCore c).map
          (·.op) = [op] := by
      intro c hc
      have hct : c ≠ t := fun h => htnotin (h ▸ hc)
      rw [handleTlbShootdownReqOnCorePerCore_tlbShootdown_eq,
          handleTlbShootdownReqOnCore_tlbShootdown_eq,
          completeShootdownOnCore_frame_pending _ hct]
      exact hpost c (List.mem_cons_of_mem _ hc)
    rw [ih htsnd (handleTlbShootdownReqOnCorePerCore st t) hpost']
    have ht : (st.tlbShootdown.pendingOnCore t).map (·.op) = [op] :=
      hpost t (List.mem_cons_self ..)
    have hstep : (handleTlbShootdownReqOnCorePerCore st t).perCoreTlb =
        setTlbViewOnCore st.perCoreTlb t
          (applyTlbInvalidation (st.perCoreTlb.get t) op) := by
      rw [handleTlbShootdownReqOnCorePerCore_perCoreTlb, drainShootdowns_fst, ht]
      rfl
    rw [hstep]

/-- **WS-SM SM7.C** (the per-core fold's `tlb`/`tlbShootdown` bridge): the
per-core handler fold and the SM7.B single-view handler fold produce the
*same* `tlb` and `tlbShootdown` from states that agree on those two fields
— the per-core drain adds nothing observable to the single-view model.
This is what makes swapping the live catch-up fold to the per-core handler
trace-safe. -/
theorem foldl_handleTlbShootdownReqOnCorePerCore_agrees :
    ∀ (targets : List CoreId) (s1 s2 : SystemState),
      s1.tlb = s2.tlb → s1.tlbShootdown = s2.tlbShootdown →
      (targets.foldl handleTlbShootdownReqOnCorePerCore s1).tlb =
        (targets.foldl handleTlbShootdownReqOnCore s2).tlb ∧
      (targets.foldl handleTlbShootdownReqOnCorePerCore s1).tlbShootdown =
        (targets.foldl handleTlbShootdownReqOnCore s2).tlbShootdown := by
  intro targets
  induction targets with
  | nil => intro s1 s2 h1 h2; exact ⟨h1, h2⟩
  | cons t ts ih =>
    intro s1 s2 h1 h2
    rw [List.foldl_cons, List.foldl_cons]
    refine ih (handleTlbShootdownReqOnCorePerCore s1 t)
      (handleTlbShootdownReqOnCore s2 t) ?_ ?_
    · simp only [handleTlbShootdownReqOnCorePerCore_tlb_eq,
        handleTlbShootdownReqOnCore_tlb_eq, h1, h2]
    · simp only [handleTlbShootdownReqOnCorePerCore_tlbShootdown_eq,
        handleTlbShootdownReqOnCore_tlbShootdown_eq, h2]

/-- **WS-SM SM7.C** (the per-core fold frames the page tables): folding the
per-core handler over any target list leaves `objects` and `asidTable`
unchanged. -/
theorem foldl_handleTlbShootdownReqOnCorePerCore_frame :
    ∀ (targets : List CoreId) (st : SystemState),
      (targets.foldl handleTlbShootdownReqOnCorePerCore st).objects = st.objects ∧
      (targets.foldl handleTlbShootdownReqOnCorePerCore st).asidTable = st.asidTable := by
  intro targets
  induction targets with
  | nil => intro st; exact ⟨rfl, rfl⟩
  | cons t ts ih =>
    intro st
    rw [List.foldl_cons]
    obtain ⟨ho, ha⟩ := ih (handleTlbShootdownReqOnCorePerCore st t)
    exact ⟨ho.trans (handleTlbShootdownReqOnCorePerCore_frame st t).1,
           ha.trans (handleTlbShootdownReqOnCorePerCore_frame st t).2⟩

/-- **WS-SM SM7.C**: one complete shootdown round on the per-core model —
the SM7.B `shootdownRound` (broadcast → initiator local → target handlers)
with the initiator's local step and every target's handler evolving
`perCoreTlb` per-core.  This is the round the live `completeShootdownRounds`
seam runs; its `tlb`/`tlbShootdown` effect equals `shootdownRound`'s (the
bridge), and its `perCoreTlb` effect equals `shootdownRoundViews`. -/
def shootdownRoundPerCore (st : SystemState) (initiator : CoreId)
    (targets : List CoreId) (op : TlbInvalidation) : Option SystemState :=
  match tlbShootdownBroadcast st initiator targets op with
  | none => none
  | some (posted, _) =>
      some (targets.foldl handleTlbShootdownReqOnCorePerCore
        (tlbShootdownLocalPerCore posted initiator op))

/-- **WS-SM SM7.C** (decomposition): a successful per-core round is the
target-handler fold over the initiator's per-core local step on the
broadcast's posted state. -/
theorem shootdownRoundPerCore_spec {st final : SystemState}
    {initiator : CoreId} {targets : List CoreId} {op : TlbInvalidation}
    (h : shootdownRoundPerCore st initiator targets op = some final) :
    ∃ posted sgis, tlbShootdownBroadcast st initiator targets op = some (posted, sgis) ∧
      final = targets.foldl handleTlbShootdownReqOnCorePerCore
        (tlbShootdownLocalPerCore posted initiator op) := by
  unfold shootdownRoundPerCore at h
  cases hb : tlbShootdownBroadcast st initiator targets op with
  | none => rw [hb] at h; cases h
  | some pair =>
      obtain ⟨posted, psgis⟩ := pair
      rw [hb] at h; injection h with h
      exact ⟨posted, psgis, rfl, h.symm⟩

/-- **WS-SM SM7.C** (operative Theorem 3.3.1's view result): the per-core
round's `perCoreTlb` — evolved by the REAL per-descriptor drain — equals the
abstract `shootdownRoundViews` vector, so the mounted field's live evolution
IS the vector Theorem 3.3.1 quantifies over.  Requires the round to open
from quiescence with distinct targets (the SM7.B round-serialisation
regime). -/
theorem shootdownRoundPerCore_perCoreTlb {st final : SystemState}
    {initiator : CoreId} {targets : List CoreId} {op : TlbInvalidation}
    (hq : shootdownQuiescent st.tlbShootdown) (hnd : targets.Nodup)
    (h : shootdownRoundPerCore st initiator targets op = some final) :
    final.perCoreTlb = shootdownRoundViews st.perCoreTlb initiator targets op := by
  obtain ⟨posted, sgis, hb, hfinal⟩ := shootdownRoundPerCore_spec h
  subst hfinal
  -- Each target's queue in `posted` is exactly the round's descriptor.
  have hsingle : ∀ c ∈ targets,
      ((tlbShootdownLocalPerCore posted initiator op).tlbShootdown.pendingOnCore c).map
        (·.op) = [op] := by
    intro c hc
    rw [tlbShootdownLocalPerCore_tlbShootdown_eq,
        tlbShootdownBroadcast_posts_singleton hq hnd hb c hc]
    rfl
  rw [foldl_handleTlbShootdownReqOnCorePerCore_perCoreTlb targets hnd _ hsingle,
      tlbShootdownLocalPerCore_perCoreTlb]
  unfold shootdownRoundViews
  simp only [tlbOnCore, tlbShootdownBroadcast_perCoreTlb hb]

/-- **WS-SM SM7.C** (the bridge, A4): the per-core round's `tlb` effect is
exactly the SM7.B single-view `shootdownRound`'s — the two TLB models agree
on the boot-core-visible view for *every* round, not just at boot. -/
theorem shootdownRoundPerCore_tlb_eq {st : SystemState}
    {initiator : CoreId} {targets : List CoreId} {op : TlbInvalidation}
    {final finalSingle : SystemState}
    (h : shootdownRoundPerCore st initiator targets op = some final)
    (hs : shootdownRound st initiator targets op = some finalSingle) :
    final.tlb = finalSingle.tlb ∧ final.tlbShootdown = finalSingle.tlbShootdown := by
  obtain ⟨posted, sgis, hb, hfinal⟩ := shootdownRoundPerCore_spec h
  -- `shootdownRound` uses the same broadcast, so the same `posted`.
  have hs' : finalSingle = targets.foldl handleTlbShootdownReqOnCore
      (tlbShootdownLocal posted op) := by
    unfold shootdownRound at hs
    rw [hb] at hs; injection hs with hs; exact hs.symm
  subst hfinal; subst hs'
  exact foldl_handleTlbShootdownReqOnCorePerCore_agrees targets
    (tlbShootdownLocalPerCore posted initiator op) (tlbShootdownLocal posted op)
    rfl rfl

/-- **WS-SM SM7.C** (operative Theorem 3.3.1, `shootdownRoundPerCore`): after
a covering per-core round — the round the live seam runs — **no core**
retains any entry the operand covers.  This is Theorem 3.3.1 realised on the
mounted field by the real per-core drain: it composes
`shootdownRoundPerCore_perCoreTlb` (the drain equals the view vector) with
`tlbShootdownBroadcast_invalidatesAllCores` (the vector removes every
covered entry). -/
theorem shootdownRoundPerCore_invalidates_perCore {st final : SystemState}
    {initiator : CoreId} {targets : List CoreId} {op : TlbInvalidation}
    (hq : shootdownQuiescent st.tlbShootdown) (hnd : targets.Nodup)
    (hcov : ∀ c : CoreId, c ≠ initiator → c ∈ targets)
    (h : shootdownRoundPerCore st initiator targets op = some final) :
    ∀ (c : CoreId) {e : TlbEntry}, tlbEntryMatches op e = true →
      e ∉ (tlbOnCore final c).entries := by
  intro c e he
  simp only [tlbOnCore, shootdownRoundPerCore_perCoreTlb hq hnd h]
  exact tlbShootdownBroadcast_invalidatesAllCores st.perCoreTlb initiator hcov op c he

/-- **WS-SM SM7.C**: the per-core round frames the page tables. -/
theorem shootdownRoundPerCore_frame {st final : SystemState}
    {initiator : CoreId} {targets : List CoreId} {op : TlbInvalidation}
    (h : shootdownRoundPerCore st initiator targets op = some final) :
    final.objects = st.objects ∧ final.asidTable = st.asidTable := by
  obtain ⟨posted, sgis, hb, hfinal⟩ := shootdownRoundPerCore_spec h
  subst hfinal
  obtain ⟨ho, ha⟩ := foldl_handleTlbShootdownReqOnCorePerCore_frame targets
    (tlbShootdownLocalPerCore posted initiator op)
  refine ⟨ho.trans ?_, ha.trans ?_⟩
  · show posted.objects = st.objects; exact (tlbShootdownBroadcast_frame hb).1
  · show posted.asidTable = st.asidTable; exact tlbShootdownBroadcast_asidTable hb

/-- **WS-SM SM7.C**: the per-core round preserves the per-core invariant —
invalidation only removes entries and the round frames the page tables. -/
theorem shootdownRoundPerCore_preserves_tlbInvalidationConsistent_perCore
    {st final : SystemState} {initiator : CoreId} {targets : List CoreId}
    {op : TlbInvalidation}
    (hq : shootdownQuiescent st.tlbShootdown) (hnd : targets.Nodup)
    (hConsist : tlbInvalidationConsistent_perCore st)
    (h : shootdownRoundPerCore st initiator targets op = some final) :
    tlbInvalidationConsistent_perCore final := by
  intro c e he
  -- final.perCoreTlb.get c = shootdownRoundViews (st.perCoreTlb) …, which only removes.
  have hpre : e ∈ (tlbOnCore st c).entries := by
    simp only [tlbOnCore, shootdownRoundPerCore_perCoreTlb hq hnd h,
      shootdownRoundViews_get] at he
    split at he
    · exact mem_of_mem_applyTlbInvalidation he
    · exact he
  refine Or.inl (tlbEntryConsistent_of_frame
    (shootdownRoundPerCore_frame h).1 (shootdownRoundPerCore_frame h).2 ?_)
  exact tlbEntryConsistent_of_ok_of_quiescent hq (hConsist c e hpre)

-- ============================================================================
-- SM7.C live catch-up — the initiator's own per-core drain (PR #844 P1)
--
-- The live `completeShootdownRounds` fold drains every *non-initiator*
-- target's posted queue (`shootdownTargets execCore` excludes the initiator).
-- But the initiator's `tlbiForSharing` loop runs an inner-shareable broadcast,
-- which reaches the issuing PE too — so the initiator's own per-core view must
-- also retire the operands.  The scalar boot-core `st.tlb` was already retired
-- in the dispatch, so the initiator's per-core drain is `perCoreTlb`-only and
-- therefore trace-safe.  This closes the SM7.C.1 asymmetry the SM7.B single-view
-- model could not express (one `st.tlb` conflated all cores).
-- ============================================================================

/-- **WS-SM SM7.C** (initiator local drain, `perCoreTlb`-only): retire `ops` on
core `c`'s own per-core view.  The inner-shareable `tlbiForSharing` broadcast
reaches the issuing PE, so the initiator retires the operands on its own view;
the scalar `st.tlb` boot-core view was already retired in the dispatch, so this
touches `perCoreTlb` **only** (`st.tlb` / `st.tlbShootdown` frame — trace-safe). -/
def drainInitiatorPerCoreView (st : SystemState) (c : CoreId)
    (ops : List TlbInvalidation) : SystemState :=
  setTlbOnCore st c (applyTlbInvalidations (tlbOnCore st c) ops)

/-- **WS-SM SM7.C**: the initiator drain is `perCoreTlb`-only — `st.tlb` frames. -/
@[simp] theorem drainInitiatorPerCoreView_tlb (st : SystemState) (c : CoreId)
    (ops : List TlbInvalidation) :
    (drainInitiatorPerCoreView st c ops).tlb = st.tlb := rfl

/-- **WS-SM SM7.C**: the initiator drain frames the shootdown state. -/
@[simp] theorem drainInitiatorPerCoreView_tlbShootdown (st : SystemState)
    (c : CoreId) (ops : List TlbInvalidation) :
    (drainInitiatorPerCoreView st c ops).tlbShootdown = st.tlbShootdown := rfl

/-- **WS-SM SM7.C**: the initiator drain frames the page-table subsystem. -/
theorem drainInitiatorPerCoreView_frame (st : SystemState) (c : CoreId)
    (ops : List TlbInvalidation) :
    (drainInitiatorPerCoreView st c ops).objects = st.objects ∧
    (drainInitiatorPerCoreView st c ops).asidTable = st.asidTable := ⟨rfl, rfl⟩

/-- **WS-SM SM7.C**: after the initiator drain, the initiator's own view has
retired the operands. -/
theorem drainInitiatorPerCoreView_tlbOnCore_self (st : SystemState) (c : CoreId)
    (ops : List TlbInvalidation) :
    tlbOnCore (drainInitiatorPerCoreView st c ops) c =
      applyTlbInvalidations (tlbOnCore st c) ops := by
  simp [drainInitiatorPerCoreView]

/-- **WS-SM SM7.C**: the initiator drain leaves every other core's view
untouched. -/
theorem drainInitiatorPerCoreView_tlbOnCore_ne (st : SystemState)
    {c c' : CoreId} (ops : List TlbInvalidation) (h : c ≠ c') :
    tlbOnCore (drainInitiatorPerCoreView st c ops) c' = tlbOnCore st c' :=
  setTlbOnCore_tlbOnCore_ne st _ h

/-- **WS-SM SM7.C**: the initiator drain never adds an entry to any view. -/
theorem drainInitiatorPerCoreView_subset (st : SystemState) (c c' : CoreId)
    (ops : List TlbInvalidation) {e : TlbEntry}
    (h : e ∈ (tlbOnCore (drainInitiatorPerCoreView st c ops) c').entries) :
    e ∈ (tlbOnCore st c').entries := by
  by_cases hcc : c = c'
  · subst hcc
    rw [drainInitiatorPerCoreView_tlbOnCore_self] at h
    exact mem_of_mem_applyTlbInvalidations h
  · rw [drainInitiatorPerCoreView_tlbOnCore_ne st ops hcc] at h
    exact h

/-- **WS-SM SM7.C**: the initiator drain preserves the per-core invariant —
invalidation only removes entries and frames the page tables. -/
theorem drainInitiatorPerCoreView_preserves_tlbInvalidationConsistent_perCore
    (st : SystemState) (c : CoreId) (ops : List TlbInvalidation)
    (h : tlbInvalidationConsistent_perCore st) :
    tlbInvalidationConsistent_perCore (drainInitiatorPerCoreView st c ops) := by
  intro c' e he
  have hpre : e ∈ (tlbOnCore st c').entries :=
    drainInitiatorPerCoreView_subset st c c' ops he
  have hShoot : (drainInitiatorPerCoreView st c ops).tlbShootdown = st.tlbShootdown := rfl
  exact tlbEntryOk_of_frame_eq
    (drainInitiatorPerCoreView_frame st c ops).1
    (drainInitiatorPerCoreView_frame st c ops).2 hShoot (h c' e hpre)

/-- **WS-SM SM7.C**: folding the per-core handler over a target list leaves the
view of any core NOT in that list unchanged — a handler is a this-core event.
The initiator (excluded from `shootdownTargets`) is such a core. -/
theorem foldl_handleTlbShootdownReqOnCorePerCore_tlbOnCore_notMem :
    ∀ (cs : List CoreId) (st : SystemState) (c : CoreId), c ∉ cs →
      tlbOnCore (cs.foldl handleTlbShootdownReqOnCorePerCore st) c = tlbOnCore st c := by
  intro cs
  induction cs with
  | nil => intro st c _; rfl
  | cons t ts ih =>
    intro st c hnotin
    rw [List.mem_cons, not_or] at hnotin
    obtain ⟨hne, hnotin'⟩ := hnotin
    rw [List.foldl_cons, ih (handleTlbShootdownReqOnCorePerCore st t) c hnotin']
    exact handleTlbShootdownReqOnCorePerCore_tlbOnCore_ne st (Ne.symm hne)

/-- **WS-SM SM7.C**: folding the per-core handler over any target list preserves
the per-core invariant (every step does — `_preserves_…`). -/
theorem foldl_handleTlbShootdownReqOnCorePerCore_preserves_consistent :
    ∀ (cs : List CoreId) (st : SystemState),
      tlbInvalidationConsistent_perCore st →
      tlbInvalidationConsistent_perCore (cs.foldl handleTlbShootdownReqOnCorePerCore st) := by
  intro cs
  induction cs with
  | nil => intro st h; exact h
  | cons t ts ih =>
    intro st h
    rw [List.foldl_cons]
    exact ih _ (handleTlbShootdownReqOnCorePerCore_preserves_tlbInvalidationConsistent_perCore st t h)

/-- **WS-SM SM7.C** (the live per-core catch-up — PR #844 P1): the complete
per-core model effect of a live shootdown round's catch-up.  Drains every
non-initiator target's posted queue onto its own view
(`handleTlbShootdownReqOnCorePerCore`) **and** retires the round's operands on
the *initiator's* own view (`drainInitiatorPerCoreView` — the inner-shareable
broadcast reaches the issuing PE).  This is exactly what
`SyscallDispatchEntry.completeShootdownRounds` runs.  Its `tlb` / `tlbShootdown`
effect is definitionally the SM7.B single-view target-fold's (the initiator
drain is `perCoreTlb`-only), so wiring it into the live seam is trace-safe;
adding the initiator drain closes the SM7.C.1 asymmetry the single-view model
could not express. -/
def shootdownCatchUpPerCore (st : SystemState) (execCore : CoreId)
    (ops : List TlbInvalidation) : SystemState :=
  drainInitiatorPerCoreView
    ((shootdownTargets execCore).foldl handleTlbShootdownReqOnCorePerCore st)
    execCore ops

/-- **WS-SM SM7.C**: the live catch-up's `tlb` effect is the target fold's. -/
@[simp] theorem shootdownCatchUpPerCore_tlb (st : SystemState)
    (execCore : CoreId) (ops : List TlbInvalidation) :
    (shootdownCatchUpPerCore st execCore ops).tlb =
      ((shootdownTargets execCore).foldl handleTlbShootdownReqOnCorePerCore st).tlb := rfl

/-- **WS-SM SM7.C**: the live catch-up's shootdown-state effect is the target
fold's. -/
@[simp] theorem shootdownCatchUpPerCore_tlbShootdown (st : SystemState)
    (execCore : CoreId) (ops : List TlbInvalidation) :
    (shootdownCatchUpPerCore st execCore ops).tlbShootdown =
      ((shootdownTargets execCore).foldl handleTlbShootdownReqOnCorePerCore st).tlbShootdown := rfl

/-- **WS-SM SM7.C** (trace-safety — PR #844 P1): the live catch-up's `tlb` /
`tlbShootdown` effect equals the SM7.B **single-view** target fold's — the
initiator per-core drain adds nothing observable.  This is what keeps the
golden trace byte-identical after wiring the initiator drain into the live
seam: the field that additionally evolves (`perCoreTlb`) is projection-invisible
(`perCoreTlb_write_preserves_projection`). -/
theorem shootdownCatchUpPerCore_agrees_singleView (st : SystemState)
    (execCore : CoreId) (ops : List TlbInvalidation) :
    (shootdownCatchUpPerCore st execCore ops).tlb =
      ((shootdownTargets execCore).foldl handleTlbShootdownReqOnCore st).tlb ∧
    (shootdownCatchUpPerCore st execCore ops).tlbShootdown =
      ((shootdownTargets execCore).foldl handleTlbShootdownReqOnCore st).tlbShootdown := by
  rw [shootdownCatchUpPerCore_tlb, shootdownCatchUpPerCore_tlbShootdown]
  exact foldl_handleTlbShootdownReqOnCorePerCore_agrees (shootdownTargets execCore) st st rfl rfl

/-- **WS-SM SM7.C** (faithfulness — PR #844 P1): after the live catch-up the
*initiator's* own per-core view has retired the round's operands — the fix the
review asked for.  The target fold excludes the initiator
(`shootdownTargets` filters it out), so the drain reads the initiator's
pre-round view. -/
theorem shootdownCatchUpPerCore_initiator_view (st : SystemState)
    (execCore : CoreId) (ops : List TlbInvalidation) :
    tlbOnCore (shootdownCatchUpPerCore st execCore ops) execCore =
      applyTlbInvalidations (tlbOnCore st execCore) ops := by
  unfold shootdownCatchUpPerCore
  rw [drainInitiatorPerCoreView_tlbOnCore_self]
  have hnotin : execCore ∉ shootdownTargets execCore := by
    rw [mem_shootdownTargets_iff]; exact fun h => h rfl
  rw [foldl_handleTlbShootdownReqOnCorePerCore_tlbOnCore_notMem
    (shootdownTargets execCore) st execCore hnotin]

/-- **WS-SM SM7.C**: the live catch-up preserves the per-core invariant — both
the target fold and the initiator drain do. -/
theorem shootdownCatchUpPerCore_preserves_tlbInvalidationConsistent_perCore
    (st : SystemState) (execCore : CoreId) (ops : List TlbInvalidation)
    (h : tlbInvalidationConsistent_perCore st) :
    tlbInvalidationConsistent_perCore (shootdownCatchUpPerCore st execCore ops) := by
  unfold shootdownCatchUpPerCore
  exact drainInitiatorPerCoreView_preserves_tlbInvalidationConsistent_perCore _ _ _
    (foldl_handleTlbShootdownReqOnCorePerCore_preserves_consistent _ st h)

/-- **WS-SM SM7.C.7** (operative cross-subsystem capstone — PR #844 P2): the
memory-subsystem capstone on the **operative** round `shootdownRoundPerCore` —
the one the live seam realises, which drains each target's queue at its handler
acknowledgment (not the eager `tlbInvalidateOnAllCores` *view-outcome
abstraction*).  A covering round on a per-core-consistent state both removes
every covered entry on every core AND preserves per-core consistency — the
completed-round analogue of `tlbConsistency_cross_subsystem`. -/
theorem shootdownRoundPerCore_cross_subsystem {st final : SystemState}
    {initiator : CoreId} {targets : List CoreId} {op : TlbInvalidation}
    (hq : shootdownQuiescent st.tlbShootdown) (hnd : targets.Nodup)
    (hcov : ∀ c : CoreId, c ≠ initiator → c ∈ targets)
    (hConsist : tlbInvalidationConsistent_perCore st)
    (h : shootdownRoundPerCore st initiator targets op = some final) :
    (∀ (c : CoreId) {e : TlbEntry}, tlbEntryMatches op e = true →
        e ∉ (tlbOnCore final c).entries) ∧
    tlbInvalidationConsistent_perCore final :=
  ⟨shootdownRoundPerCore_invalidates_perCore hq hnd hcov h,
   shootdownRoundPerCore_preserves_tlbInvalidationConsistent_perCore hq hnd hConsist h⟩

-- ============================================================================
-- SM7.F.1 — Translation-walk fill seam (PR #844 review-2 P2, Comment 2)
--
-- The hardware TLB *fill*: on a memory access whose translation misses the
-- TLB, the page-table walker resolves the address and caches the translation.
-- The v0.32.80–83 model only ever *drained* `perCoreTlb` on the live path
-- (invalidations/shootdowns), never filled it, so a real cached translation
-- could not be represented.  `tlbFillOnCore` is the fill: it resolves
-- `(asid, vaddr)` through the CURRENT page tables and caches the
-- *consistent-by-construction* translation, so a walk can never install a
-- stale entry.  This is the operative primitive the live wiring (SM7.F.4) will
-- use; the honest pending-aware invariant it needs is SM7.F.2, and round-
-- generation-tagged catch-up is SM7.F.3 (see the plan §SM7.F).
-- ============================================================================

/-- **WS-SM SM7.F.1**: the translation a page-table walk resolves for
`(asid, vaddr)` against the current page tables — `some entry` iff the address
is mapped (`resolveAsidRoot` → `VSpaceRoot.lookup` both succeed), and the
resulting entry's `(paddr, perms)` are exactly the walked mapping (so it is
consistent by construction). -/
def tlbWalkEntry (st : SystemState) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) :
    Option TlbEntry :=
  match resolveAsidRoot st asid with
  | none => none
  | some p =>
    match p.2.lookup vaddr with
    | none => none
    | some q => some { asid := asid, vaddr := vaddr, paddr := q.1, perms := q.2 }

/-- **WS-SM SM7.F.1**: a walked entry satisfies the `tlbInsertOnCore` walker
contract — for its own `(asid, vaddr)`, the current page tables resolve to
exactly its `(paddr, perms)`.  This is what makes a fill consistency-safe. -/
theorem tlbWalkEntry_matches (st : SystemState) (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr) {entry : TlbEntry}
    (h : tlbWalkEntry st asid vaddr = some entry) :
    ∀ rootId root, resolveAsidRoot st entry.asid = some (rootId, root) →
      VSpaceRoot.lookup root entry.vaddr = some (entry.paddr, entry.perms) := by
  unfold tlbWalkEntry at h
  cases hres : resolveAsidRoot st asid with
  | none => simp [hres] at h
  | some p =>
    cases hlk : p.2.lookup vaddr with
    | none => simp [hres, hlk] at h
    | some q =>
      simp only [hres, hlk, Option.some.injEq] at h
      subst h
      intro rootId root hres2
      have hres2' : resolveAsidRoot st asid = some (rootId, root) := hres2
      rw [hres] at hres2'
      simp only [Option.some.injEq] at hres2'
      subst hres2'
      exact hlk

/-- **WS-SM SM7.F.1** (the fill): the hardware page-table walker fills core
`c`'s TLB with the translation it resolved for `(asid, vaddr)`.  On a mapped
address it caches the consistent-by-construction entry (`tlbWalkEntry`); on an
unmapped address it caches nothing.  Unlike the raw `tlbInsertOnCore` (which
accepts an arbitrary entry), a `tlbFillOnCore` result is always page-table
consistent, so it is the fill the live translation path can use soundly. -/
def tlbFillOnCore (st : SystemState) (c : CoreId) (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr) : SystemState :=
  match tlbWalkEntry st asid vaddr with
  | none => st
  | some entry => tlbInsertOnCore st c entry

/-- **WS-SM SM7.F.1**: a fill frames the page-table subsystem + the shootdown
state — it only touches `perCoreTlb`. -/
theorem tlbFillOnCore_frame (st : SystemState) (c : CoreId) (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr) :
    (tlbFillOnCore st c asid vaddr).objects = st.objects ∧
    (tlbFillOnCore st c asid vaddr).asidTable = st.asidTable ∧
    (tlbFillOnCore st c asid vaddr).tlbShootdown = st.tlbShootdown := by
  unfold tlbFillOnCore
  cases tlbWalkEntry st asid vaddr with
  | none => exact ⟨rfl, rfl, rfl⟩
  | some entry =>
    exact ⟨(tlbInsertOnCore_frame st c entry).1,
           (tlbInsertOnCore_frame st c entry).2.1,
           (tlbInsertOnCore_frame st c entry).2.2.2.2⟩

/-- **WS-SM SM7.F.1**: a fill on core `c` leaves every other core's view
unchanged — a hardware walk is a local event (the SMP asymmetry). -/
theorem tlbFillOnCore_tlbOnCore_ne (st : SystemState) {c c' : CoreId}
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (h : c ≠ c') :
    tlbOnCore (tlbFillOnCore st c asid vaddr) c' = tlbOnCore st c' := by
  unfold tlbFillOnCore
  cases tlbWalkEntry st asid vaddr with
  | none => rfl
  | some entry => exact tlbInsertOnCore_tlbOnCore_ne st entry h

/-- **WS-SM SM7.F.1** (the fill is consistency-safe): a translation-walk fill
preserves the per-core invariant — it caches only a mapping it resolved from
the current page tables, so the fresh entry is consistent by construction
(`tlbWalkEntry_matches` discharges the `tlbInsertOnCore_preserves_…` walker
contract).  Because the fill never installs a stale entry, wiring it into the
live path (SM7.F.4) will preserve consistency in the quiescent state — the
honest pending-aware form is SM7.F.2. -/
theorem tlbFillOnCore_preserves_tlbInvalidationConsistent_perCore
    (st : SystemState) (c : CoreId) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (h : tlbInvalidationConsistent_perCore st) :
    tlbInvalidationConsistent_perCore (tlbFillOnCore st c asid vaddr) := by
  unfold tlbFillOnCore
  cases hw : tlbWalkEntry st asid vaddr with
  | none => exact h
  | some entry =>
    exact tlbInsertOnCore_preserves_tlbInvalidationConsistent_perCore st c entry h
      (tlbWalkEntry_matches st asid vaddr hw)

end SeLe4n.Kernel.Architecture
