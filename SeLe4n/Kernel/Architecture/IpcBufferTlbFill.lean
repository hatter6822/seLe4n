-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Architecture.PerCoreTlbModel
import SeLe4n.Kernel.Architecture.IpcBufferRead
import SeLe4n.Kernel.Architecture.Invariant

/-!
# WS-SM SM7.F — Access-time TLB fills

SM7.F.1 gave the model a fill (`tlbFillOnCore`), and SM7.F.4 wired it at the
two VSpace seams: a core that **maps** a page caches the translation it just
established.  That left one site, and so left the per-core TLB model saying
only that a core caches translations it installed itself.

Hardware does not work that way.  A TLB entry is loaded when the PE *walks*
the page tables — on any access, whoever established the mapping.  A core that
merely reads memory another core mapped holds a cached translation, and that
translation is precisely what a shootdown exists to evict.  With fills only at
the mapping seam, a core in that position cached nothing, so Theorem 3.3.1 and
the 13th `proofLayerInvariantBundle` conjunct
(`tlbInvalidationConsistent_perCore`) were *vacuously* true for it — trivially
satisfied by an empty view rather than substantively by a maintained one.  No
theorem was false; they simply had nothing to say about the common case.

This module closes that gap at the translation the kernel genuinely performs
on a user address: the **IPC buffer walk**.  When a syscall carries more
message registers than the four the ABI passes in registers, the decode reads
the overflow slots out of the calling thread's IPC buffer
(`RegisterDecode.decodeSyscallArgsFromState` → `IpcBufferRead.ipcBufferReadMr`),
resolving a user virtual address through that thread's VSpace.  On hardware
that walk fills the executing core's TLB.  Here it fills `perCoreTlb`.

**Why the fill is keyed on a page.** `tlbEntryMatches` compares virtual
addresses for *equality*, not containment, so an entry keyed at a byte address
would not be matched by the page invalidation a later unmap posts — it would
survive the shootdown meant to evict it and leave the invariant reachably
false.  The fill therefore caches `IpcBufferRead.ipcBufferSlotPage`, the same
page base the read resolves through: one definition, two consumers, so the
"cache what the read walked" property holds by construction rather than by a
theorem that could rot.

**Why the entry is nonetheless not assumed correct.** The read resolves
through `tcb.vspaceRoot` while `tlbFillOnCore` resolves through
`resolveAsidRoot` — two genuinely different paths, which the ASID-rebind
hazard (SM7.F.4, v0.32.93) can drive apart.  Resolving through the ASID is the
faithful choice, because that is the tag hardware caches under and the one
`tlbEntryConsistent` is stated against; a fill is therefore always
consistent-by-construction.  That the two paths agree on the *physical* page
in the ordinary case is the content of
`tlbFillIpcBufferOnCore_caches_read_translation`, which relates the two rather
than restating either.
-/

namespace SeLe4n.Kernel.Architecture

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency
open SeLe4n.Kernel.Architecture.IpcBufferRead

-- ============================================================================
-- SM7.F.5 — the pages a decode's overflow read walks
-- ============================================================================

/-- The distinct pages a decode reading `overflowCount` overflow slots walks.

    Distinct, because `tlbInsertOnCore` prepends without deduplicating and a
    TLB caches one entry per page: the 116 slots of a page-aligned buffer all
    live on one page, and filling per-slot would stack 116 copies of a single
    translation into the modelled view. -/
def ipcBufferOverflowPages (ipcBuffer : VAddr) (overflowCount : Nat) :
    List VAddr :=
  ((List.range overflowCount).map (ipcBufferSlotPage ipcBuffer)).eraseDups

/-- Every page the fold visits is page-aligned, hence a legal mapping key and
    reachable by the page invalidation an unmap of it would post. -/
theorem ipcBufferOverflowPages_aligned
    (ipcBuffer : VAddr) (overflowCount : Nat) {page : VAddr}
    (h : page ∈ ipcBufferOverflowPages ipcBuffer overflowCount) :
    page.toNat % pageBytes = 0 := by
  unfold ipcBufferOverflowPages at h
  have hMap := mem_of_mem_eraseDups h
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hMap
  exact ipcBufferSlotPage_aligned ipcBuffer i

/-- A decode that read no overflow slot walks no page. -/
@[simp] theorem ipcBufferOverflowPages_zero (ipcBuffer : VAddr) :
    ipcBufferOverflowPages ipcBuffer 0 = [] := by
  simp [ipcBufferOverflowPages]

-- ============================================================================
-- SM7.F.5 — the fill
-- ============================================================================

/-- What a decode's IPC-buffer walk resolves, before any TLB is touched: the
ASID it resolves under and the distinct pages it walks.

Named separately because it is exactly the read's own resolution — the
caller's TCB, then that TCB's VSpace root — so the fill below demonstrably
caches what the read looked up rather than something reconstructed
independently.  `none` is the fail-closed case (no such thread, or a TCB whose
`vspaceRoot` does not resolve): a walk that resolves nothing caches nothing. -/
def ipcBufferWalkPlan (st : SystemState) (tid : ThreadId) (overflowCount : Nat) :
    Option (SeLe4n.ASID × List VAddr) :=
  match st.getTcb? tid with
  | none => none
  | some tcb =>
    match st.getVSpaceRoot? tcb.vspaceRoot with
    | none => none
    | some root =>
      some (root.asid, ipcBufferOverflowPages tcb.ipcBuffer overflowCount)

/-- A decode that read no overflow slot plans no page. -/
@[simp] theorem ipcBufferWalkPlan_zero_pages
    (st : SystemState) (tid : ThreadId) {plan : SeLe4n.ASID × List VAddr}
    (h : ipcBufferWalkPlan st tid 0 = some plan) : plan.2 = [] := by
  unfold ipcBufferWalkPlan at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · cases h; simp

/-- **WS-SM SM7.F.5**: the access-time fill.  Core `c` caches the translations
its own IPC-buffer walk resolved while decoding a syscall for thread `tid`
carrying `overflowCount` overflow message registers.

Resolution mirrors the read (`ipcBufferReadMr`): the caller's TCB, then that
TCB's VSpace root.  The entry itself is installed by `tlbFillOnCore`, so it is
consistent-by-construction and a walk that resolves nothing fills nothing. -/
def tlbFillIpcBufferOnCore (st : SystemState) (c : CoreId) (tid : ThreadId)
    (overflowCount : Nat) : SystemState :=
  match ipcBufferWalkPlan st tid overflowCount with
  | none => st
  | some plan =>
    plan.2.foldl (fun s page => tlbFillOnCore s c plan.1 page) st

/-- A decode that consulted no overflow slot leaves the state untouched — the
    fill is inert on the overwhelmingly common short-path syscall. -/
@[simp] theorem tlbFillIpcBufferOnCore_zero
    (st : SystemState) (c : CoreId) (tid : ThreadId) :
    tlbFillIpcBufferOnCore st c tid 0 = st := by
  unfold tlbFillIpcBufferOnCore
  cases hPlan : ipcBufferWalkPlan st tid 0 with
  | none => rfl
  | some plan =>
    obtain ⟨asid, pages⟩ := plan
    have hNil : pages = [] := ipcBufferWalkPlan_zero_pages st tid hPlan
    subst hNil
    rfl

-- ============================================================================
-- SM7.F.5 — frames
-- ============================================================================

/-- The fold's frame: filling touches only the TLB model. -/
private theorem foldl_tlbFillOnCore_frame
    (c : CoreId) (asid : SeLe4n.ASID) (pages : List VAddr) (st : SystemState) :
    (pages.foldl (fun s page => tlbFillOnCore s c asid page) st).objects
        = st.objects ∧
    (pages.foldl (fun s page => tlbFillOnCore s c asid page) st).asidTable
        = st.asidTable ∧
    (pages.foldl (fun s page => tlbFillOnCore s c asid page) st).tlbShootdown
        = st.tlbShootdown := by
  induction pages generalizing st with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons page rest ih =>
    have hStep := tlbFillOnCore_frame st c asid page
    have hRest := ih (tlbFillOnCore st c asid page)
    simp only [List.foldl_cons]
    exact ⟨hRest.1.trans hStep.1, hRest.2.1.trans hStep.2.1,
           hRest.2.2.trans hStep.2.2⟩

/-- **WS-SM SM7.F.5**: an access-time fill changes no object, no ASID binding
and no shootdown state — it is purely a TLB-model event, exactly as the
mapping-seam fill is. -/
theorem tlbFillIpcBufferOnCore_frame
    (st : SystemState) (c : CoreId) (tid : ThreadId) (overflowCount : Nat) :
    (tlbFillIpcBufferOnCore st c tid overflowCount).objects = st.objects ∧
    (tlbFillIpcBufferOnCore st c tid overflowCount).asidTable = st.asidTable ∧
    (tlbFillIpcBufferOnCore st c tid overflowCount).tlbShootdown
      = st.tlbShootdown := by
  unfold tlbFillIpcBufferOnCore
  cases hPlan : ipcBufferWalkPlan st tid overflowCount with
  | none => exact ⟨rfl, rfl, rfl⟩
  | some plan => exact foldl_tlbFillOnCore_frame c plan.1 plan.2 st

/-- The fold leaves every other core's view untouched. -/
private theorem foldl_tlbFillOnCore_tlbOnCore_ne
    {c c' : CoreId} (asid : SeLe4n.ASID) (pages : List VAddr)
    (st : SystemState) (h : c ≠ c') :
    tlbOnCore (pages.foldl (fun s page => tlbFillOnCore s c asid page) st) c'
      = tlbOnCore st c' := by
  induction pages generalizing st with
  | nil => rfl
  | cons page rest ih =>
    simp only [List.foldl_cons]
    rw [ih (tlbFillOnCore st c asid page), tlbFillOnCore_tlbOnCore_ne st asid page h]

/-- **WS-SM SM7.F.5**: a walk is a *local* event — the executing core caches
the translation and no other core's view moves.  This is the same SMP
asymmetry `tlbInsertOnCore_tlbOnCore_ne` states for the walker, now on the
live decode path: it is exactly why the other cores' stale entries need the
shootdown protocol rather than falling out of the access. -/
theorem tlbFillIpcBufferOnCore_tlbOnCore_ne
    (st : SystemState) {c c' : CoreId} (tid : ThreadId) (overflowCount : Nat)
    (h : c ≠ c') :
    tlbOnCore (tlbFillIpcBufferOnCore st c tid overflowCount) c'
      = tlbOnCore st c' := by
  unfold tlbFillIpcBufferOnCore
  cases hPlan : ipcBufferWalkPlan st tid overflowCount with
  | none => rfl
  | some plan => exact foldl_tlbFillOnCore_tlbOnCore_ne plan.1 plan.2 st h

-- ============================================================================
-- SM7.F.5 — the 13th bundle conjunct
-- ============================================================================

/-- The fold preserves per-core consistency, one `tlbFillOnCore` at a time. -/
private theorem foldl_tlbFillOnCore_preserves_tlbInvalidationConsistent_perCore
    (c : CoreId) (asid : SeLe4n.ASID) (pages : List VAddr) (st : SystemState)
    (h : tlbInvalidationConsistent_perCore st) :
    tlbInvalidationConsistent_perCore
      (pages.foldl (fun s page => tlbFillOnCore s c asid page) st) := by
  induction pages generalizing st with
  | nil => exact h
  | cons page rest ih =>
    simp only [List.foldl_cons]
    exact ih (tlbFillOnCore st c asid page)
      (tlbFillOnCore_preserves_tlbInvalidationConsistent_perCore st c asid page h)

/-- **WS-SM SM7.F.5**: the access-time fill preserves the 13th
`proofLayerInvariantBundle` conjunct.

Substantively rather than vacuously: the entries it adds are the ones a real
walk resolved, and each is consistent-by-construction because `tlbFillOnCore`
installs only what `tlbWalkEntry` returned. -/
theorem tlbFillIpcBufferOnCore_preserves_tlbInvalidationConsistent_perCore
    (st : SystemState) (c : CoreId) (tid : ThreadId) (overflowCount : Nat)
    (h : tlbInvalidationConsistent_perCore st) :
    tlbInvalidationConsistent_perCore
      (tlbFillIpcBufferOnCore st c tid overflowCount) := by
  unfold tlbFillIpcBufferOnCore
  cases hPlan : ipcBufferWalkPlan st tid overflowCount with
  | none => exact h
  | some plan =>
    exact foldl_tlbFillOnCore_preserves_tlbInvalidationConsistent_perCore
      c plan.1 plan.2 st h

-- ============================================================================
-- SM7.F.5 — the fill caches what the read walked
-- ============================================================================

/-- A fill only ever prepends, so an entry already cached stays cached. -/
private theorem tlbFillOnCore_entries_mono
    (st : SystemState) (c : CoreId) (asid : SeLe4n.ASID) (vaddr : VAddr)
    {e : TlbEntry} (h : e ∈ (tlbOnCore st c).entries) :
    e ∈ (tlbOnCore (tlbFillOnCore st c asid vaddr) c).entries := by
  unfold tlbFillOnCore
  cases hw : tlbWalkEntry st asid vaddr with
  | none => exact h
  | some entry =>
    unfold tlbInsertOnCore
    simp only [setTlbOnCore_tlbOnCore_self]
    exact List.mem_cons_of_mem _ h

private theorem foldl_tlbFillOnCore_entries_mono
    (c : CoreId) (asid : SeLe4n.ASID) :
    ∀ (pages : List VAddr) (st : SystemState) {e : TlbEntry},
      e ∈ (tlbOnCore st c).entries →
      e ∈ (tlbOnCore (pages.foldl (fun s p => tlbFillOnCore s c asid p) st) c).entries := by
  intro pages
  induction pages with
  | nil => intro st e h; exact h
  | cons p rest ih =>
    intro st e h
    simp only [List.foldl_cons]
    exact ih (tlbFillOnCore st c asid p) (tlbFillOnCore_entries_mono st c asid p h)

/-- A walk depends only on the objects and the ASID table, both of which a
    fill frames — so the translation a page resolves to is the same before and
    after any number of fills. -/
private theorem tlbWalkEntry_congr {st st' : SystemState}
    (hObj : st'.objects = st.objects) (hAsid : st'.asidTable = st.asidTable)
    (asid : SeLe4n.ASID) (vaddr : VAddr) :
    tlbWalkEntry st' asid vaddr = tlbWalkEntry st asid vaddr := by
  unfold tlbWalkEntry resolveAsidRoot
  rw [hObj, hAsid]

/-- **WS-SM SM7.F.5**: every page the walk resolves ends up cached. -/
private theorem foldl_tlbFillOnCore_mem
    (c : CoreId) (asid : SeLe4n.ASID) :
    ∀ (pages : List VAddr) (st : SystemState) {page : VAddr},
      page ∈ pages → ∀ {e : TlbEntry}, tlbWalkEntry st asid page = some e →
      e ∈ (tlbOnCore (pages.foldl (fun s p => tlbFillOnCore s c asid p) st) c).entries := by
  intro pages
  induction pages with
  | nil => intro _ _ hMem; simp at hMem
  | cons p rest ih =>
    intro st page hMem e hWalk
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hMem with rfl | hRest
    · -- the head is the page we care about: this step caches it, and every
      -- later step only prepends.
      refine foldl_tlbFillOnCore_entries_mono c asid rest _ ?_
      unfold tlbFillOnCore
      rw [hWalk]
      unfold tlbInsertOnCore
      simp only [setTlbOnCore_tlbOnCore_self]
      simp
    · -- a later page: the walk is unchanged by this step's fill (frame).
      refine ih (tlbFillOnCore st c asid p) hRest ?_
      have hFrame := tlbFillOnCore_frame st c asid p
      rw [tlbWalkEntry_congr hFrame.1 hFrame.2.1]
      exact hWalk

/-- A slot actually read is one of the pages the fill visits. -/
theorem mem_ipcBufferOverflowPages_of_lt
    (ipcBuffer : VAddr) {idx overflowCount : Nat} (h : idx < overflowCount) :
    ipcBufferSlotPage ipcBuffer idx
      ∈ ipcBufferOverflowPages ipcBuffer overflowCount := by
  unfold ipcBufferOverflowPages
  refine mem_eraseDups_of_mem ?_
  exact List.mem_map.mpr ⟨idx, List.mem_range.mpr h, rfl⟩

/-- **WS-SM SM7.F.5 — the correspondence.**  The entry the access-time fill
caches is the translation the decode's read actually used.

This is the theorem that makes the fill *this* fill rather than an unrelated
insertion, and it is load-bearing because the two sides resolve by different
routes: the read goes `tid → tcb.vspaceRoot → root`, while `tlbFillOnCore`
goes `asid → resolveAsidRoot`.  The hypothesis `hResolve` is exactly the
statement that those routes agree — which the ASID-rebind hazard can falsify,
so it is a real precondition and not bookkeeping.

The conclusion ties them: some cached entry is keyed at the slot's page under
the thread's ASID, and the read returns the word at *that entry's* physical
page plus the slot's offset within it. -/
theorem tlbFillIpcBufferOnCore_caches_read_translation
    (st : SystemState) (c : CoreId) (tid : ThreadId)
    (tcb : SeLe4n.Model.TCB) (root : SeLe4n.Model.VSpaceRoot)
    (idx overflowCount : Nat)
    (pa : SeLe4n.PAddr) (perms : SeLe4n.Model.PagePermissions)
    (hIdx : idx < overflowCount)
    (hBound : idx < maxOverflowSlots)
    (hTcb : st.getTcb? tid = some tcb)
    (hRoot : st.getVSpaceRoot? tcb.vspaceRoot = some root)
    (hResolve : resolveAsidRoot st root.asid = some (tcb.vspaceRoot, root))
    (hMapped : root.lookup (ipcBufferSlotPage tcb.ipcBuffer idx)
                 = some (pa, perms)) :
    ∃ e : TlbEntry,
      e ∈ (tlbOnCore (tlbFillIpcBufferOnCore st c tid overflowCount) c).entries ∧
      e.asid = root.asid ∧
      e.vaddr = ipcBufferSlotPage tcb.ipcBuffer idx ∧
      e.paddr = pa ∧
      ipcBufferReadMr st tid idx
        = .ok (readUInt64 st.machine.memory
                 (PAddr.ofNat
                   (e.paddr.toNat
                     + (ipcBufferSlotAddr tcb.ipcBuffer idx).pageOffset))) := by
  -- The walk resolves the slot's page to exactly the mapping the read used.
  have hWalk : tlbWalkEntry st root.asid (ipcBufferSlotPage tcb.ipcBuffer idx)
      = some { asid := root.asid,
               vaddr := ipcBufferSlotPage tcb.ipcBuffer idx,
               paddr := pa, perms := perms } := by
    unfold tlbWalkEntry
    rw [hResolve]
    dsimp only
    rw [hMapped]
  refine ⟨{ asid := root.asid,
            vaddr := ipcBufferSlotPage tcb.ipcBuffer idx,
            paddr := pa, perms := perms }, ?_, rfl, rfl, rfl,
          ipcBufferReadMr_ok_of_mapped st tid tcb root idx pa perms
            hBound hTcb hRoot hMapped⟩
  -- The plan resolves (same route as the read), and the slot's page is in it.
  have hPlan : ipcBufferWalkPlan st tid overflowCount
      = some (root.asid, ipcBufferOverflowPages tcb.ipcBuffer overflowCount) := by
    unfold ipcBufferWalkPlan
    simp only [hTcb, hRoot]
  simp only [tlbFillIpcBufferOnCore, hPlan]
  exact foldl_tlbFillOnCore_mem c root.asid _ st
    (mem_ipcBufferOverflowPages_of_lt tcb.ipcBuffer hIdx) hWalk

-- ============================================================================
-- SM7.F.5 — the fill touches only `perCoreTlb`, hence carries the bundle
-- ============================================================================

/-- A single fill is a `perCoreTlb`-only state update. -/
private theorem tlbFillOnCore_eq_setPerCoreTlb
    (st : SystemState) (c : CoreId) (asid : SeLe4n.ASID) (vaddr : VAddr) :
    ∃ t, tlbFillOnCore st c asid vaddr = { st with perCoreTlb := t } := by
  unfold tlbFillOnCore
  cases tlbWalkEntry st asid vaddr with
  | none => exact ⟨st.perCoreTlb, rfl⟩
  | some entry => exact ⟨_, rfl⟩

private theorem foldl_tlbFillOnCore_eq_setPerCoreTlb
    (c : CoreId) (asid : SeLe4n.ASID) :
    ∀ (pages : List VAddr) (st : SystemState),
      ∃ t, pages.foldl (fun s p => tlbFillOnCore s c asid p) st
             = { st with perCoreTlb := t } := by
  intro pages
  induction pages with
  | nil => intro st; exact ⟨st.perCoreTlb, rfl⟩
  | cons p rest ih =>
    intro st
    simp only [List.foldl_cons]
    obtain ⟨t1, h1⟩ := tlbFillOnCore_eq_setPerCoreTlb st c asid p
    rw [h1]
    obtain ⟨t2, h2⟩ := ih { st with perCoreTlb := t1 }
    exact ⟨t2, h2⟩

/-- **WS-SM SM7.F.5**: the access-time fill changes `perCoreTlb` and nothing
else.  This is what lets every invariant that does not read the per-core TLB
transport through the fill definitionally. -/
theorem tlbFillIpcBufferOnCore_eq_setPerCoreTlb
    (st : SystemState) (c : CoreId) (tid : ThreadId) (overflowCount : Nat) :
    ∃ t, tlbFillIpcBufferOnCore st c tid overflowCount
           = { st with perCoreTlb := t } := by
  unfold tlbFillIpcBufferOnCore
  cases hPlan : ipcBufferWalkPlan st tid overflowCount with
  | none => exact ⟨st.perCoreTlb, rfl⟩
  | some plan => exact foldl_tlbFillOnCore_eq_setPerCoreTlb c plan.1 plan.2 st

/-!
### Whole-bundle carriage

`tlbFillIpcBufferOnCore_eq_setPerCoreTlb` above pins that the fill writes
`perCoreTlb` and nothing else, so the whole bundle follows from the general
carriage lemma `proofLayerInvariantBundle_setPerCoreTlb` (`Invariant.lean`),
whose one remaining obligation is the thirteenth conjunct — the only one that
reads the field being written, and the one this module proves substantively.

Twelve of the other fourteen conjuncts transport definitionally; the two that
do not are blocked by a fuel-recursive `match` stuck on a symbolic `Nat` and by
an `inductive` family parameterised by the state.  Both are bridged by
congruence lemmas the codebase already carries — see the commentary on
`proofLayerInvariantBundle_setPerCoreTlb` for the full diagnosis. -/

/-- **WS-SM SM7.F.5**: the access-time fill preserves the whole
`proofLayerInvariantBundle`.

The fill writes only `perCoreTlb`, and the one conjunct that reads it is
preserved substantively — every entry the fill adds is one a real page-table
walk resolved, hence consistent by construction. -/
theorem tlbFillIpcBufferOnCore_preserves_proofLayerInvariantBundle
    (st : SystemState) (c : CoreId) (tid : ThreadId) (overflowCount : Nat)
    (h : proofLayerInvariantBundle st) :
    proofLayerInvariantBundle (tlbFillIpcBufferOnCore st c tid overflowCount) := by
  have hPerCoreTlbConsistent :=
    tlbFillIpcBufferOnCore_preserves_tlbInvalidationConsistent_perCore
    st c tid overflowCount
    (by unfold proofLayerInvariantBundle at h; exact h.2.2.2.2.2.2.2.2.2.2.2.2.1)
  obtain ⟨t, hEq⟩ := tlbFillIpcBufferOnCore_eq_setPerCoreTlb st c tid overflowCount
  rw [hEq] at hPerCoreTlbConsistent ⊢
  exact proofLayerInvariantBundle_setPerCoreTlb st t h hPerCoreTlbConsistent

end SeLe4n.Kernel.Architecture
