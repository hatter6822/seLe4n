-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Architecture.CacheModel
-- WS-SM SM7.D.2: the AN9-A.2 data-to-instruction barrier sequence, which the
-- kernel code-write sites' clean-to-PoU obligation is stated against.
import SeLe4n.Kernel.Architecture.TlbCacheComposition
import SeLe4n.Kernel.Architecture.CacheInvalidation
import SeLe4n.Kernel.Architecture.PerCoreTlbModel

/-!
# WS-SM SM7.D — Cache maintenance broadcast

The cache-side companion of SM7.C's per-core TLB model.  SM7.C closed the
*translation* half of SMP-C4 (a stale TLB entry on a remote core); SM7.D
closes the *cache* half, and the two halves are architecturally asymmetric
in a way that decides the whole design:

| structure | coherent across PEs? | kernel obligation |
|-----------|----------------------|-------------------|
| D-cache   | **yes** (hardware)   | none — `DC` by VA to PoC is architecturally visible to every agent in the domain |
| I-cache   | **no**               | issue the *broadcast* maintenance variant, or remote cores keep stale lines |
| TLB       | no                   | the SM7.B explicit-ack shootdown protocol |

So SM7.D delivers:

* **SM7.D.1** — the I-cache broadcast.  `IC IALLU` invalidates only the
  executing PE (`icInvalidateOnCore`, and `…_icacheOnCore_ne` proves the
  hazard: every other core keeps its lines).  `IC IALLUIS` / `IC IVAU`
  broadcast within the shareability domain (`icInvalidateBroadcast`), and
  `icInvalidateBroadcast_reaches_all_cores` is the cache analogue of the
  SM7.B Theorem 3.3.1: after a covering broadcast **no core** retains a
  covered line.  The per-core views are mounted as
  `SystemState.perCoreICache`.
* **SM7.D.2** — D-cache maintenance by VA to the Point of Coherency is
  system-wide.  Modelled, not assumed: `dcMaintenanceAllCores` applies the
  operation to *every* core's view with no `reach` parameter at all — the
  absence of a target set is the formal content of "at PoC, already
  system-wide" — and `dcMaintenanceByVA_reaches_all_cores` /
  `dcMaintenanceAllCores_establishes_dcacheCoherentAcrossCores` are the
  resulting guarantees.  `icInvalidateOnCore_vs_dcMaintenance_reach` states
  the contrast against the I-cache's PE-local variant as a theorem.
* **SM7.D.3** — cross-core D-cache maintenance for **DMA** buffers is out of
  scope for v1.0.0 (the kernel has no DMA driver, so no non-coherent agent
  exists).  This is a machine-checked scope boundary, not prose: the model
  enumerates its coherent agents (`modeledCoherentAgents`), proves the
  maintenance operation covers all of them
  (`dcMaintenance_covers_all_modeled_agents`), and proves the enumeration
  contains no non-coherent master (`modeledCoherentAgents_no_dma_master`).
  Introducing a DMA agent breaks the second theorem — a tripwire, so the
  obligation cannot be forgotten.
* **SM7.D.4** — the SMP cache-coherency invariant.
  `icacheCoherent_perCore` (every core's every cached line still has a live
  **executable** mapping) is the **14th `proofLayerInvariantBundle`
  conjunct**, and `cacheCoherency_cross_subsystem` is the memory-subsystem
  capstone (broadcast × cache-model × page-tables), mirroring SM7.C.7.

## Why provenance, not content

The model does not track instruction *bytes*: an `ICacheLine` records the
executable translation the fetch resolved through (`asid`, `vaddr`, `paddr`,
`perms`).  That is the hazard the **kernel** controls.  A line becomes
dangerous when the mapping that produced it goes away — the frame is then
free to be re-typed, scrubbed and handed to another subject, while a core
still holds the previous owner's instructions and could execute them through
a fresh executable mapping to the same physical page.  Keeping the field
shape identical to `TlbEntry` is deliberate: an I-cache line's provenance
*is* a translation plus "it was executable", so `ICacheLine.toTranslation`
lets the entire page-table frame algebra proven for `tlbEntryConsistent`
carry over unchanged.

Content coherency in the *other* direction — a thread writing new
instructions through the data side (self-modifying code, JIT) — is user
software's obligation on ARMv8-A (`DC CVAU` → `DSB` → `IC IVAU` → `DSB` →
`ISB`, the sequence `armv8DCacheToICacheSequence` in
`TlbCacheComposition.lean` models); seL4 exposes it as an explicit
`Page_Unify_Instruction` operation rather than performing it implicitly.
The kernel-side obligation SM7.D discharges is the mapping-lifetime one.

## Hardware references

* ARM ARM B2.7 / D7.4 — cache maintenance scope; `DC` by VA to the Point of
  Coherency affects all agents that can access the location.
* ARM ARM C6.2.88 — `IC IALLU` (PE-local) vs `IC IALLUIS` (Inner Shareable
  broadcast); `IC IVAU` (by VA to PoU, broadcast within the domain).
* ARM ARM D7.2 — instruction caches behave as PIPT to software, so a line's
  identity is its physical address.
-/

namespace SeLe4n.Kernel.Architecture

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- SM7.D.1 — The invalidation effect on one core's view
-- ============================================================================

/-- **WS-SM SM7.D.1**: does the operand cover this cached line?  The
hardware's comparison: `iallu` covers everything; `ivauPage p` covers exactly the
lines tagged with the physical address `p` (PIPT identity). -/
def icacheLineMatches (op : ICacheInvalidation) (l : ICacheLine) : Bool :=
  match op with
  | .iallu       => true
  | .ivauPage p  => p == l.paddr
  -- `unifyPage` removes the same lines as `ivauPage`; the difference is the
  -- emitted sequence (it additionally cleans the page's stores to the Point of
  -- Unification first).  Cf. `TlbInvalidation`'s `vae1` / `vale1`.
  | .unifyPage p => p == l.paddr

/-- **WS-SM SM7.D.1**: the effect of retiring one maintenance operand on one
core's instruction-cache view — every covered line is removed, nothing is
added.  The instruction-side twin of `applyTlbInvalidation`. -/
def applyICacheInvalidation (ic : ICacheState) (op : ICacheInvalidation) :
    ICacheState :=
  { lines := ic.lines.filter (fun l => !icacheLineMatches op l) }

/-- **WS-SM SM7.D.1**: membership after one invalidation — a line survives
iff it was present and the operand does not cover it. -/
theorem mem_applyICacheInvalidation_iff (ic : ICacheState)
    (op : ICacheInvalidation) (l : ICacheLine) :
    l ∈ (applyICacheInvalidation ic op).lines ↔
      l ∈ ic.lines ∧ icacheLineMatches op l = false := by
  simp [applyICacheInvalidation, List.mem_filter]

/-- **WS-SM SM7.D.1**: a covered line is gone after the invalidation — the
per-step removal half of the SM7.D.1 broadcast theorem. -/
theorem applyICacheInvalidation_removes {op : ICacheInvalidation}
    {l : ICacheLine} (h : icacheLineMatches op l = true) (ic : ICacheState) :
    l ∉ (applyICacheInvalidation ic op).lines := by
  rw [mem_applyICacheInvalidation_iff]
  intro ⟨_, hFalse⟩
  rw [h] at hFalse
  cases hFalse

/-- **WS-SM SM7.D.1**: an uncovered line is untouched — the selectivity half
(a targeted `IC IVAU` does not flush the whole cache). -/
theorem applyICacheInvalidation_preserves_other {op : ICacheInvalidation}
    {l : ICacheLine} (h : icacheLineMatches op l = false) (ic : ICacheState) :
    l ∈ (applyICacheInvalidation ic op).lines ↔ l ∈ ic.lines := by
  rw [mem_applyICacheInvalidation_iff]
  simp [h]

/-- **WS-SM SM7.D.1**: invalidation never adds lines — the monotonicity every
coherency-preservation proof rides. -/
theorem mem_of_mem_applyICacheInvalidation {ic : ICacheState}
    {op : ICacheInvalidation} {l : ICacheLine}
    (h : l ∈ (applyICacheInvalidation ic op).lines) : l ∈ ic.lines :=
  ((mem_applyICacheInvalidation_iff ic op l).mp h).1

/-- **WS-SM SM7.D.1**: retiring the same operand twice is retiring it once —
a duplicated broadcast (or a re-run handler) is harmless. -/
theorem applyICacheInvalidation_idempotent (ic : ICacheState)
    (op : ICacheInvalidation) :
    applyICacheInvalidation (applyICacheInvalidation ic op) op =
      applyICacheInvalidation ic op := by
  simp [applyICacheInvalidation, List.filter_filter]

/-- **WS-SM SM7.D.1**: `IC IALLU` empties the view — no line, in particular
none a targeted operand would have missed, survives a full invalidate. -/
theorem applyICacheInvalidation_iallu (ic : ICacheState) :
    (applyICacheInvalidation ic .iallu).lines = [] := by
  simp [applyICacheInvalidation, icacheLineMatches]

/-- **WS-SM SM7.D.1**: `ivauPage p` covers exactly the lines tagged `p`. -/
theorem icacheLineMatches_ivauPage {p : SeLe4n.PAddr} {l : ICacheLine}
    (h : l.paddr = p) : icacheLineMatches (.ivauPage p) l = true := by
  simp [icacheLineMatches, h]

/-- **WS-SM SM7.D.1**: `iallu` covers every line. -/
theorem icacheLineMatches_iallu (l : ICacheLine) :
    icacheLineMatches .iallu l = true := rfl

/-- **WS-SM SM7.D**: `unifyPage p` covers exactly the lines tagged `p` — the
same removal semantics as `ivauPage p`. -/
theorem icacheLineMatches_unifyPage {p : SeLe4n.PAddr} {l : ICacheLine}
    (h : l.paddr = p) : icacheLineMatches (.unifyPage p) l = true := by
  simp [icacheLineMatches, h]

/-- **WS-SM SM7.D.1**: a surviving line is *not* tagged with the `ivauPage`
operand — the contrapositive form the preservation proofs consume. -/
theorem applyICacheInvalidation_survivor_paddr_ne {p : SeLe4n.PAddr}
    {ic : ICacheState} {l : ICacheLine}
    (h : l ∈ (applyICacheInvalidation ic (.ivauPage p)).lines) : l.paddr ≠ p := by
  intro hEq
  exact absurd h (applyICacheInvalidation_removes (icacheLineMatches_ivauPage hEq) ic)

/-- **WS-SM SM7.D** (the semantic grounding of `ICacheInvalidation.covers`):
when `a` covers `b`, every line `b` would retire is also retired by `a`.

`covers` is defined as a table on constructors, which by itself proves nothing.
This theorem ties it to the model's own effect, so "drop the covered entry"
in `recordIcacheMaintenanceList` is a *justified* reduction rather than a
convention.  Note it is stated only for the invalidation dimension, which is
all the abstract state models — the `unifyPage`'s clean to the Point of
Unification has no counterpart in `ICacheState` (there is no modelled D-cache
content), and it is exactly that unmodelled dimension which makes `iallu`
*not* cover `unifyPage` (`ICacheInvalidation.iallu_not_covers_unifyPage`). -/
theorem icacheLineMatches_of_covers {a b : ICacheInvalidation} {l : ICacheLine}
    (hcov : a.covers b = true) (hb : icacheLineMatches b l = true) :
    icacheLineMatches a l = true := by
  cases a <;> cases b <;>
    simp_all [ICacheInvalidation.covers, icacheLineMatches]

/-- **WS-SM SM7.D**: the state-level form — applying the covering operand
retires at least the lines the covered one would, so the ledger's dedup never
leaves a line the dropped entry would have removed. -/
theorem applyICacheInvalidation_subset_of_covers {a b : ICacheInvalidation}
    (hcov : a.covers b = true) (ic : ICacheState) {l : ICacheLine}
    (h : l ∈ (applyICacheInvalidation ic a).lines) :
    l ∈ (applyICacheInvalidation ic b).lines := by
  rw [mem_applyICacheInvalidation_iff] at h ⊢
  refine ⟨h.1, ?_⟩
  cases hb : icacheLineMatches b l with
  | false => rfl
  | true => exact absurd (icacheLineMatches_of_covers hcov hb) (by simp [h.2])

-- ============================================================================
-- SM7.D.1 — Per-core instruction-cache view accessors (SM4.B path-a)
-- ============================================================================

/-- **WS-SM SM7.D.1**: read core `c`'s instruction-cache view from the mounted
per-core vector.  The `Fin numCores`-indexed accessor of the SM4.B path-a
discipline, mirroring `tlbOnCore`. -/
def icacheOnCore (st : SystemState) (c : CoreId) : ICacheState :=
  st.perCoreICache.get c

/-- **WS-SM SM7.D.1**: write core `c`'s instruction-cache view, leaving every
other core's slot and every non-`perCoreICache` field unchanged. -/
def setIcacheOnCore (st : SystemState) (c : CoreId) (ic : ICacheState) :
    SystemState :=
  { st with perCoreICache := st.perCoreICache.set c.val ic c.isLt }

/-- **WS-SM SM7.D.1**: reading the slot just written returns the written
view. -/
@[simp] theorem setIcacheOnCore_icacheOnCore_self (st : SystemState)
    (c : CoreId) (ic : ICacheState) :
    icacheOnCore (setIcacheOnCore st c ic) c = ic := by
  simp [icacheOnCore, setIcacheOnCore]

/-- **WS-SM SM7.D.1**: writing core `c`'s slot leaves every other core's view
unchanged — the per-core frame property. -/
theorem setIcacheOnCore_icacheOnCore_ne (st : SystemState) {c c' : CoreId}
    (ic : ICacheState) (h : c ≠ c') :
    icacheOnCore (setIcacheOnCore st c ic) c' = icacheOnCore st c' := by
  simp only [icacheOnCore, setIcacheOnCore]
  exact SeLe4n.PerCoreVector.get_set_ne st.perCoreICache c c' ic h

/-- **WS-SM SM7.D.1**: the setter touches only `perCoreICache` — every other
`SystemState` field frames (all `rfl`, the record-update shape). -/
@[simp] theorem setIcacheOnCore_objects (st : SystemState) (c : CoreId)
    (ic : ICacheState) : (setIcacheOnCore st c ic).objects = st.objects := rfl
@[simp] theorem setIcacheOnCore_asidTable (st : SystemState) (c : CoreId)
    (ic : ICacheState) : (setIcacheOnCore st c ic).asidTable = st.asidTable := rfl
@[simp] theorem setIcacheOnCore_scheduler (st : SystemState) (c : CoreId)
    (ic : ICacheState) : (setIcacheOnCore st c ic).scheduler = st.scheduler := rfl
@[simp] theorem setIcacheOnCore_machine (st : SystemState) (c : CoreId)
    (ic : ICacheState) : (setIcacheOnCore st c ic).machine = st.machine := rfl
@[simp] theorem setIcacheOnCore_tlb (st : SystemState) (c : CoreId)
    (ic : ICacheState) : (setIcacheOnCore st c ic).tlb = st.tlb := rfl
@[simp] theorem setIcacheOnCore_tlbShootdown (st : SystemState) (c : CoreId)
    (ic : ICacheState) :
    (setIcacheOnCore st c ic).tlbShootdown = st.tlbShootdown := rfl
@[simp] theorem setIcacheOnCore_perCoreTlb (st : SystemState) (c : CoreId)
    (ic : ICacheState) :
    (setIcacheOnCore st c ic).perCoreTlb = st.perCoreTlb := rfl

/-- **WS-SM SM7.D.1**: at boot every core's instruction cache is cold. -/
@[simp] theorem default_icacheOnCore (c : CoreId) :
    icacheOnCore (default : SystemState) c = ICacheState.empty :=
  default_perCoreICache c

-- ============================================================================
-- SM7.D.1 — Model operations: fetch, PE-local invalidate, domain broadcast
-- ============================================================================

/-- **WS-SM SM7.D.1**: the hardware instruction fetch's effect — core `c`
caches the line it just fetched.  This is an *environment* step, not a kernel
transition: the PE fills its own instruction cache whenever it executes
through an executable mapping, without the kernel's participation.  The
kernel's obligation is the dual one — invalidate before the mapping that
authorised the fetch goes away — and
`icFetchOnCore_preserves_icacheCoherent_perCore` states the environment's
side of the contract (a fetch only happens through a live executable
mapping). -/
def icFetchOnCore (st : SystemState) (c : CoreId) (l : ICacheLine) :
    SystemState :=
  setIcacheOnCore st c { lines := l :: (icacheOnCore st c).lines }

/-- **WS-SM SM7.D.1**: after a fetch, core `c`'s view holds the line. -/
theorem icFetchOnCore_mem (st : SystemState) (c : CoreId) (l : ICacheLine) :
    l ∈ (icacheOnCore (icFetchOnCore st c l) c).lines := by
  simp [icFetchOnCore]

/-- **WS-SM SM7.D.1**: a fetch on core `c` leaves every other core's view
unchanged — an instruction fetch is a local event. -/
theorem icFetchOnCore_icacheOnCore_ne (st : SystemState) {c c' : CoreId}
    (l : ICacheLine) (h : c ≠ c') :
    icacheOnCore (icFetchOnCore st c l) c' = icacheOnCore st c' :=
  setIcacheOnCore_icacheOnCore_ne st _ h

/-- **WS-SM SM7.D.1**: a fetch touches only the instruction-cache model. -/
theorem icFetchOnCore_frame (st : SystemState) (c : CoreId) (l : ICacheLine) :
    (icFetchOnCore st c l).objects = st.objects ∧
    (icFetchOnCore st c l).asidTable = st.asidTable ∧
    (icFetchOnCore st c l).scheduler = st.scheduler ∧
    (icFetchOnCore st c l).machine = st.machine ∧
    (icFetchOnCore st c l).tlbShootdown = st.tlbShootdown ∧
    (icFetchOnCore st c l).perCoreTlb = st.perCoreTlb :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **WS-SM SM7.D.1**: `IC IALLU` (or a PE-local `IC IVAU`) — retires the
operand on core `c`'s view **only**.  Under SMP this reaches exactly one PE;
`icInvalidateBroadcast` is the variant that reaches the domain. -/
def icInvalidateOnCore (st : SystemState) (c : CoreId)
    (op : ICacheInvalidation) : SystemState :=
  setIcacheOnCore st c (applyICacheInvalidation (icacheOnCore st c) op)

/-- **WS-SM SM7.D.1**: a local invalidation removes every covered line from
core `c`'s view. -/
theorem icInvalidateOnCore_removes {op : ICacheInvalidation} {l : ICacheLine}
    (h : icacheLineMatches op l = true) (st : SystemState) (c : CoreId) :
    l ∉ (icacheOnCore (icInvalidateOnCore st c op) c).lines := by
  simp only [icInvalidateOnCore, setIcacheOnCore_icacheOnCore_self]
  exact applyICacheInvalidation_removes h _

/-- **WS-SM SM7.D.1** (**the SMP hazard**): `IC IALLU` leaves every *other*
core's instruction cache untouched.  A kernel that used the PE-local variant
after tearing down an executable mapping would leave remote cores holding the
previous owner's instructions — the instruction-side twin of the SMP-C4
stale-TLB hazard.  `icInvalidateBroadcast` closes it. -/
theorem icInvalidateOnCore_icacheOnCore_ne (st : SystemState) {c c' : CoreId}
    (op : ICacheInvalidation) (h : c ≠ c') :
    icacheOnCore (icInvalidateOnCore st c op) c' = icacheOnCore st c' :=
  setIcacheOnCore_icacheOnCore_ne st _ h

/-- **WS-SM SM7.D.1**: a local invalidation never adds lines to core `c`'s
view — every survivor was already present. -/
theorem icInvalidateOnCore_subset (st : SystemState) (c : CoreId)
    (op : ICacheInvalidation) {l : ICacheLine}
    (h : l ∈ (icacheOnCore (icInvalidateOnCore st c op) c).lines) :
    l ∈ (icacheOnCore st c).lines := by
  simp only [icInvalidateOnCore, setIcacheOnCore_icacheOnCore_self] at h
  exact mem_of_mem_applyICacheInvalidation h

/-- **WS-SM SM7.D.1**: a local invalidation touches only the
instruction-cache model. -/
theorem icInvalidateOnCore_frame (st : SystemState) (c : CoreId)
    (op : ICacheInvalidation) :
    (icInvalidateOnCore st c op).objects = st.objects ∧
    (icInvalidateOnCore st c op).asidTable = st.asidTable ∧
    (icInvalidateOnCore st c op).scheduler = st.scheduler ∧
    (icInvalidateOnCore st c op).machine = st.machine ∧
    (icInvalidateOnCore st c op).tlbShootdown = st.tlbShootdown ∧
    (icInvalidateOnCore st c op).perCoreTlb = st.perCoreTlb :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- SM7.D.1 — The inner-shareable broadcast (`IC IALLUIS` / `IC IVAU`)
-- ============================================================================

/-- **WS-SM SM7.D.1**: write one core's slot of a free-standing per-core view
vector (the `shootdownRoundViews`-style helper, for the broadcast fold). -/
def setIcacheViewOnCore (views : _root_.Vector ICacheState numCores)
    (c : CoreId) (ic : ICacheState) : _root_.Vector ICacheState numCores :=
  views.set c.val ic c.isLt

@[simp] theorem setIcacheViewOnCore_get_self
    (views : _root_.Vector ICacheState numCores) (c : CoreId) (ic : ICacheState) :
    (setIcacheViewOnCore views c ic).get c = ic := by
  simp [setIcacheViewOnCore]

theorem setIcacheViewOnCore_get_ne (views : _root_.Vector ICacheState numCores)
    {c c' : CoreId} (h : c' ≠ c) (ic : ICacheState) :
    (setIcacheViewOnCore views c ic).get c' = views.get c' := by
  simp only [setIcacheViewOnCore]
  exact SeLe4n.PerCoreVector.get_set_ne views c c' ic (fun he => h he.symm)

/-- **WS-SM SM7.D.1**: the per-core view effect of one broadcast instruction —
the operand is retired on **every** core in `reach`.  Unlike the SM7.B TLB
shootdown there is no initiator special case and no acknowledgment protocol:
`IC IALLUIS` / `IC IVAU` are single instructions the hardware propagates to
every PE of the shareability domain, the issuing PE included (ARM ARM
C6.2.88).  `reach` is a parameter for exactly the SM7.B §3.4 reason the
shootdown's `targets` is: on a multi-cluster port the Inner Shareable domain
stops covering every core, and the missing cores would need the SGI-based
protocol instead. -/
def icBroadcastViews (views : _root_.Vector ICacheState numCores)
    (reach : List CoreId) (op : ICacheInvalidation) :
    _root_.Vector ICacheState numCores :=
  reach.foldl
    (fun vs c => setIcacheViewOnCore vs c (applyICacheInvalidation (vs.get c) op))
    views

/-- **WS-SM SM7.D.1** (fold closed form): a slot holds the invalidated view
iff the broadcast reached it; duplicates collapse by idempotence. -/
theorem icBroadcastViews_get (op : ICacheInvalidation) (reach : List CoreId) :
    ∀ (vs : _root_.Vector ICacheState numCores) (c : CoreId),
      (icBroadcastViews vs reach op).get c =
        if c ∈ reach then applyICacheInvalidation (vs.get c) op else vs.get c := by
  unfold icBroadcastViews
  induction reach with
  | nil => intro vs c; simp
  | cons t ts ih =>
    intro vs c
    rw [List.foldl_cons, ih]
    by_cases hct : c = t
    · subst hct
      by_cases hcts : c ∈ ts
      · rw [if_pos hcts, if_pos (List.mem_cons_self ..),
            setIcacheViewOnCore_get_self, applyICacheInvalidation_idempotent]
      · rw [if_neg hcts, if_pos (List.mem_cons_self ..),
            setIcacheViewOnCore_get_self]
    · by_cases hcts : c ∈ ts
      · rw [if_pos hcts, if_pos (List.mem_cons_of_mem _ hcts),
            setIcacheViewOnCore_get_ne _ hct]
      · rw [if_neg hcts, if_neg (by simp [hct, hcts]),
            setIcacheViewOnCore_get_ne _ hct]

/-- **WS-SM SM7.D.1**: the broadcast maintenance step on the kernel state —
`IC IALLUIS` (for `iallu`) or `IC IVAU` (for `ivauPage`), retiring the operand on
every core in `reach`.  Touches only `perCoreICache`. -/
def icInvalidateBroadcast (st : SystemState) (reach : List CoreId)
    (op : ICacheInvalidation) : SystemState :=
  { st with perCoreICache := icBroadcastViews st.perCoreICache reach op }

/-- **WS-SM SM7.D.1**: the broadcast's per-core view, in closed form. -/
theorem icInvalidateBroadcast_icacheOnCore (st : SystemState)
    (reach : List CoreId) (op : ICacheInvalidation) (c : CoreId) :
    icacheOnCore (icInvalidateBroadcast st reach op) c =
      if c ∈ reach then applyICacheInvalidation (icacheOnCore st c) op
      else icacheOnCore st c :=
  icBroadcastViews_get op reach st.perCoreICache c

/-- **WS-SM SM7.D.1**: the broadcast never adds lines on any core. -/
theorem icInvalidateBroadcast_subset (st : SystemState) (reach : List CoreId)
    (op : ICacheInvalidation) {c : CoreId} {l : ICacheLine}
    (h : l ∈ (icacheOnCore (icInvalidateBroadcast st reach op) c).lines) :
    l ∈ (icacheOnCore st c).lines := by
  rw [icInvalidateBroadcast_icacheOnCore] at h
  split at h
  · exact mem_of_mem_applyICacheInvalidation h
  · exact h

/-- **WS-SM SM7.D.1**: the broadcast touches only the instruction-cache
model — objects, ASID table, scheduler, machine, shootdown state and the
per-core TLB views all frame.  This is what makes it composable with (and
invisible to) every other subsystem's invariants, and what makes the live
wiring trace-safe. -/
theorem icInvalidateBroadcast_frame (st : SystemState) (reach : List CoreId)
    (op : ICacheInvalidation) :
    (icInvalidateBroadcast st reach op).objects = st.objects ∧
    (icInvalidateBroadcast st reach op).asidTable = st.asidTable ∧
    (icInvalidateBroadcast st reach op).scheduler = st.scheduler ∧
    (icInvalidateBroadcast st reach op).machine = st.machine ∧
    (icInvalidateBroadcast st reach op).tlbShootdown = st.tlbShootdown ∧
    (icInvalidateBroadcast st reach op).perCoreTlb = st.perCoreTlb ∧
    (icInvalidateBroadcast st reach op).tlb = st.tlb :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **WS-SM SM7.D.1**: the set of cores one broadcast instruction reaches —
every core of the platform's shareability domain.

On the first hardware target (BCM2712, one Cortex-A76 cluster) all
`numCores` PEs sit in a single Inner Shareable domain, so `IC IALLUIS`
reaches all of them; `icBroadcastReach_cover` pins that.  A multi-cluster
port must either narrow this list and add an SGI-based instruction-cache
protocol for the out-of-domain cores (the SM7.B shootdown shape), or run in
the Outer Shareable domain — the same portability seam SM7.B §3.4
documents for the TLB. -/
def icBroadcastReach : List CoreId := allCores

/-- **WS-SM SM7.D.1**: on this platform the broadcast reaches every core. -/
theorem icBroadcastReach_cover (c : CoreId) : c ∈ icBroadcastReach := by
  simp [icBroadcastReach, allCores]

/-- **WS-SM SM7.D.1**: the reach enumeration is duplicate-free (each PE is
reached once; idempotence makes duplicates harmless anyway). -/
theorem icBroadcastReach_nodup : icBroadcastReach.Nodup := allCores_nodup

/-- **WS-SM SM7.D.1** (the headline — the cache analogue of SM7.B's Theorem
3.3.1): after a broadcast whose reach covers every core, **no core** retains
a line the operand covers.

This is the instruction-side closure of the SMP-C4 hazard class: the kernel
retires an executable mapping and the maintenance reaches every PE, so no
core can afterwards fetch the previous owner's instructions from a stale
line. -/
theorem icInvalidateBroadcast_reaches_all_cores (st : SystemState)
    {reach : List CoreId} (hcov : ∀ c : CoreId, c ∈ reach)
    (op : ICacheInvalidation) :
    ∀ (c : CoreId) {l : ICacheLine}, icacheLineMatches op l = true →
      l ∉ (icacheOnCore (icInvalidateBroadcast st reach op) c).lines := by
  intro c l hmatch hmem
  rw [icInvalidateBroadcast_icacheOnCore, if_pos (hcov c)] at hmem
  exact applyICacheInvalidation_removes hmatch _ hmem

/-- **WS-SM SM7.D.1**: the platform instantiation of the headline — a
broadcast over `icBroadcastReach` reaches every core on BCM2712. -/
theorem icInvalidateBroadcast_platform_reaches_all_cores (st : SystemState)
    (op : ICacheInvalidation) :
    ∀ (c : CoreId) {l : ICacheLine}, icacheLineMatches op l = true →
      l ∉ (icacheOnCore (icInvalidateBroadcast st icBroadcastReach op) c).lines :=
  icInvalidateBroadcast_reaches_all_cores st icBroadcastReach_cover op

/-- **WS-SM SM7.D.1**: a full broadcast invalidate (`IC IALLUIS` over the
whole domain) leaves **every** core's instruction cache cold. -/
theorem icInvalidateBroadcast_iallu_empties (st : SystemState)
    {reach : List CoreId} (hcov : ∀ c : CoreId, c ∈ reach) (c : CoreId) :
    (icacheOnCore (icInvalidateBroadcast st reach .iallu) c).lines = [] := by
  rw [icInvalidateBroadcast_icacheOnCore, if_pos (hcov c)]
  exact applyICacheInvalidation_iallu _

-- ============================================================================
-- SM7.D.2 — D-cache maintenance by VA at the Point of Coherency is system-wide
-- ============================================================================

/-- **WS-SM SM7.D.2**: typed data-cache maintenance-by-VA selector.  The three
operations the HAL exposes (`rust/sele4n-hal/src/cache.rs`), all *to the Point
of Coherency*:

* `cleanByVA`           — `DC CVAC`: write dirty data back, keep the line.
* `invalidateByVA`      — `DC IVAC`: drop the line without writing back.
* `cleanInvalidateByVA` — `DC CIVAC`: write back, then drop.

Note what the type does **not** carry: a reach.  That absence is the formal
content of SM7.D.2 — a `DC` operation by VA to the PoC is architecturally
required to affect every agent that can access the location (ARM ARM B2.7 /
D7.4), so unlike the instruction side there is no local-versus-broadcast
choice for the kernel to get wrong. -/
inductive DCacheMaintenance where
  /-- `DC CVAC` — clean by VA to PoC. -/
  | cleanByVA (paddr : SeLe4n.PAddr)
  /-- `DC IVAC` — invalidate by VA to PoC. -/
  | invalidateByVA (paddr : SeLe4n.PAddr)
  /-- `DC CIVAC` — clean and invalidate by VA to PoC. -/
  | cleanInvalidateByVA (paddr : SeLe4n.PAddr)
  deriving DecidableEq, Repr, Inhabited

/-- **WS-SM SM7.D.2**: the effect of one data-cache maintenance operation on
one PE's view, routed to the AG8-B single-core operations. -/
def applyDCacheMaintenance (cs : CacheState) : DCacheMaintenance → CacheState
  | .cleanByVA p           => dcClean cs p
  | .invalidateByVA p      => dcInvalidate cs p
  | .cleanInvalidateByVA p => dcCleanInvalidate cs p

/-- **WS-SM SM7.D.2**: the per-core data-cache views.  Free-standing (not
mounted in `SystemState`, unlike `perCoreICache`) precisely because the kernel
carries **no obligation** here: the data caches are hardware-coherent, so
there is no per-core software state to maintain — only the *reach* property to
prove. -/
abbrev DCacheViews := _root_.Vector CacheState numCores

/-- **WS-SM SM7.D.2**: a data-cache maintenance operation by VA to the Point
of Coherency, applied to the per-core views.

There is **no `reach` parameter**: the operation is applied to every core's
view unconditionally.  That is not an over-approximation — it is the
architectural semantics of "to the Point of Coherency" (ARM ARM B2.7): the
PoC is by definition the point at which all agents that can access memory see
the same copy, so a by-VA maintenance operation that completes to the PoC has
taken effect for every one of them.  Contrast `icInvalidateBroadcast`, which
*does* take a reach, because instruction caches are not coherent and the
broadcast variant of the instruction must be selected explicitly. -/
def dcMaintenanceAllCores (views : DCacheViews) (op : DCacheMaintenance) :
    DCacheViews :=
  views.map (fun cs => applyDCacheMaintenance cs op)

/-- **WS-SM SM7.D.2**: every core's post-maintenance view is that core's
pre-state view with the operation applied — the "no core is skipped" reading
of `dcMaintenanceAllCores`. -/
@[simp] theorem dcMaintenanceAllCores_get (views : DCacheViews)
    (op : DCacheMaintenance) (c : CoreId) :
    (dcMaintenanceAllCores views op).get c =
      applyDCacheMaintenance (views.get c) op := by
  simp only [dcMaintenanceAllCores, SeLe4n.PerCoreVector.get_eq_getElem]
  exact _root_.Vector.getElem_map ..

/-- **WS-SM SM7.D.2** (the headline): a `DC IVAC` / `DC CIVAC` by VA to the
Point of Coherency leaves **no core** holding the line — no software broadcast
protocol required, in contrast with the TLB (SM7.B) and the instruction cache
(SM7.D.1).  The data-cache half of the SMP cache-maintenance story. -/
theorem dcMaintenanceByVA_reaches_all_cores (views : DCacheViews)
    (p : SeLe4n.PAddr) :
    (∀ c : CoreId,
        ((dcMaintenanceAllCores views (.invalidateByVA p)).get c).dcache p =
          .invalid) ∧
    (∀ c : CoreId,
        ((dcMaintenanceAllCores views (.cleanInvalidateByVA p)).get c).dcache p =
          .invalid) := by
  constructor <;> intro c <;>
    simp only [dcMaintenanceAllCores_get, applyDCacheMaintenance]
  · exact dcInvalidate_makes_line_invalid _ p
  · exact dcCleanInvalidate_makes_line_invalid _ p

/-- **WS-SM SM7.D.2**: the SMP data-cache coherency predicate — every core's
view is coherent (no un-written-back line).  Under ARMv8-A hardware coherency
this is maintained by the interconnect, not by kernel code; the model records
it so the maintenance operations can be shown to preserve it. -/
def dcacheCoherentAcrossCores (views : DCacheViews) : Prop :=
  ∀ c : CoreId, dcacheCoherent (views.get c)

/-- **WS-SM SM7.D.2**: cold caches on every core are coherent — the boot
witness. -/
theorem dcacheCoherentAcrossCores_cold :
    dcacheCoherentAcrossCores
      (_root_.Vector.replicate numCores CacheState.empty) := by
  intro c addr
  rw [SeLe4n.PerCoreVector.replicate_get]
  simp [CacheState.empty]

/-- **WS-SM SM7.D.2**: every data-cache maintenance-by-VA operation preserves
cross-core data-cache coherency — cleaning can only take a line `dirty →
clean`, and both invalidating forms produce `.invalid`; none of the three can
introduce a dirty line. -/
theorem dcMaintenanceAllCores_preserves_dcacheCoherentAcrossCores
    (views : DCacheViews) (op : DCacheMaintenance)
    (h : dcacheCoherentAcrossCores views) :
    dcacheCoherentAcrossCores (dcMaintenanceAllCores views op) := by
  intro c
  rw [dcMaintenanceAllCores_get]
  cases op with
  | cleanByVA p => exact dcClean_preserves_dcacheCoherent _ p (h c)
  | invalidateByVA p => exact dcInvalidate_preserves_dcacheCoherent _ p (h c)
  | cleanInvalidateByVA p =>
      exact dcCleanInvalidate_preserves_dcacheCoherent _ p (h c)

/-- **WS-SM SM7.D.1 / SM7.D.2** (the asymmetry, as a theorem): the
instruction-side PE-local maintenance leaves *every other* core's view
**bit-identically** unchanged, while the data-side by-VA maintenance applies
to *every* core's view.  This is the structural statement of why the kernel
must select `IC IALLUIS` (never `IC IALLU`) on the SMP path, and why no
corresponding choice exists on the data side. -/
theorem icInvalidateOnCore_vs_dcMaintenance_reach
    (st : SystemState) (views : DCacheViews) {c c' : CoreId} (h : c ≠ c')
    (op : ICacheInvalidation) (dop : DCacheMaintenance) :
    icacheOnCore (icInvalidateOnCore st c op) c' = icacheOnCore st c' ∧
    ∀ d : CoreId, (dcMaintenanceAllCores views dop).get d =
      applyDCacheMaintenance (views.get d) dop :=
  ⟨icInvalidateOnCore_icacheOnCore_ne st op h,
   fun d => dcMaintenanceAllCores_get views dop d⟩

/-- **WS-SM SM7.D.1** (non-vacuity of the hazard): a line cached on a remote
core genuinely **survives** a PE-local instruction-cache invalidation, even a
full `IC IALLU`.  Without this, `icInvalidateOnCore_icacheOnCore_ne` alone
would be compatible with the remote view having been empty all along; here the
line is present before and after. -/
theorem icInvalidateOnCore_remote_line_survives (st : SystemState)
    {c c' : CoreId} (h : c ≠ c') (l : ICacheLine)
    (hmem : l ∈ (icacheOnCore st c').lines) (op : ICacheInvalidation) :
    l ∈ (icacheOnCore (icInvalidateOnCore st c op) c').lines := by
  rw [icInvalidateOnCore_icacheOnCore_ne st op h]; exact hmem

-- ============================================================================
-- SM7.D.2 — The data-side dual: kernel-written memory that may be executed
-- ============================================================================

/-- **WS-SM SM7.D.2**: the kernel operations that *write* memory a subject may
later execute, and therefore owe a clean to the **Point of Unification** before
that memory can be fetched as instructions.

Instruction fetches read at the PoU; a store lands in the data cache.  Until a
`DC CVAU` pushes the store to the PoU, an instruction fetch of the same address
may observe the *old* content — even on the very PE that performed the store,
and regardless of any I-cache invalidation.  Two kernel paths write such
memory:

* `retypeScrub` — `scrubObjectMemory` zeroes the target's backing memory as
  part of a re-type, so a subject that later maps the frame executable must not
  fetch the previous owner's instructions from a stale PoU copy.  (seL4's
  `clearMemory` does exactly this: `memzero` followed by
  `cleanCacheRange_PoU`.)
* `bootImageLoad` — the boot pipeline materialises the initial task's objects,
  including its code, before the first fetch.

This enumeration exists so the obligation is a *checked* object rather than a
comment: `kernelCodeWriteSites_owe_pou_clean` states it, and
`kernelCodeWriteSites_complete` is the tripwire that fails if a site is added
without an entry. -/
inductive KernelCodeWriteSite where
  /-- `scrubObjectMemory` during a re-type. -/
  | retypeScrub
  /-- Object/code materialisation during boot. -/
  | bootImageLoad
  deriving DecidableEq, Repr, Inhabited

/-- **WS-SM SM7.D.2**: the enumeration of kernel code-write sites. -/
def kernelCodeWriteSites : List KernelCodeWriteSite :=
  [.retypeScrub, .bootImageLoad]

/-- **WS-SM SM7.D.2** (the tripwire): every constructor is listed.  Adding a
site to `KernelCodeWriteSite` without listing it breaks this `decide`, which is
the reminder that the new path owes the clean-to-PoU step below. -/
theorem kernelCodeWriteSites_complete (s : KernelCodeWriteSite) :
    s ∈ kernelCodeWriteSites := by
  cases s <;> decide

/-- **WS-SM SM7.D.2**: the barrier sequence a kernel code-write site owes
before the written memory may be fetched as instructions — the canonical
ARMv8-A data-to-instruction pipeline `DC CVAU → DSB ISH → IC IVAU → DSB ISH →
ISB`, already modelled as `armv8DCacheToICacheSequence`
(`TlbCacheComposition.lean`, AN9-A.2).

SM7.D lands the **ordering obligation**, not the range emission.  The emission
needs each written object's *physical extent*, and the model does not yet carry
one: only `UntypedObject` has `regionBase` / `regionSize`, while a re-typed
object is identified by `ObjId` alone.  Giving kernel objects PA extents (from
the owning untyped's region plus the re-type offset) is an object-model change
scoped to SM9.E hardware bring-up, which is also the first point at which the
memory is physically backed and the omission could bite.  Until then this
theorem is the registered obligation, `kernelCodeWriteSites_complete` is its
tripwire, and the instruction-side half — which *is* expressible today, because
mappings carry page addresses — is live (SM7.D.1). -/
def kernelCodeWriteOwesPoUClean (_site : KernelCodeWriteSite) : Prop :=
  armv8DCacheToICacheSequence.covers CacheBarrierKind.dsb_ish ∧
  armv8DCacheToICacheSequence.covers CacheBarrierKind.isb

/-- **WS-SM SM7.D.2**: every kernel code-write site owes the full
data-to-instruction barrier sequence.  Discharged from the AN9-A.2 coverage
theorem — the point is not the proof but the *statement*: the obligation is now
a named object every site is quantified over. -/
theorem kernelCodeWriteSites_owe_pou_clean :
    ∀ s ∈ kernelCodeWriteSites, kernelCodeWriteOwesPoUClean s := by
  intro s _
  exact ⟨armv8DCacheToICacheSequence_covers_required.2.1,
         armv8DCacheToICacheSequence_covers_required.2.2⟩

-- ============================================================================
-- SM7.D.3 — Modelled coherent agents (the DMA scope boundary, as a tripwire)
-- ============================================================================

/-- **WS-SM SM7.D.3**: the agents whose caches this model tracks.

For v1.0.0 the answer is "the PEs, and nothing else": seLe4n has no DMA
driver, so no non-coherent bus master exists that could observe stale memory
or write behind the caches' back.  Cross-core data-cache maintenance *for DMA
buffers* is therefore out of scope — the SM7 plan §4.3 scope statement, made
machine-checked here rather than left as prose.

**Tripwire**: introducing a DMA master means adding a constructor here and
listing it in `modeledCoherentAgents`, which immediately breaks
`modeledCoherentAgents_no_dma_master` below.  The compile error is the
reminder that the buffer-ownership protocol (`DC CIVAC` before a device read,
`DC IVAC` after a device write, plus non-cacheable or cache-coherent-interconnect
mappings) must be modelled and proven in the same cut. -/
inductive CoherentAgent where
  /-- A processing element of the platform. -/
  | core (c : CoreId)
  deriving DecidableEq, Repr

/-- **WS-SM SM7.D.3**: the modelled coherent agents — exactly the platform's
PEs. -/
def modeledCoherentAgents : List CoherentAgent := allCores.map .core

/-- **WS-SM SM7.D.3**: every core is a modelled agent. -/
theorem mem_modeledCoherentAgents (c : CoreId) :
    CoherentAgent.core c ∈ modeledCoherentAgents :=
  List.mem_map.mpr ⟨c, by simp [allCores], rfl⟩

/-- **WS-SM SM7.D.3** (the scope boundary, machine-checked): every modelled
coherent agent is a PE — the model contains **no** non-coherent bus master.
This is what makes "cross-core DC for DMA is out of scope" a checked claim
rather than a comment: were a DMA agent added to `CoherentAgent` and listed,
this theorem would no longer hold. -/
theorem modeledCoherentAgents_no_dma_master :
    ∀ a ∈ modeledCoherentAgents, ∃ c : CoreId, a = .core c := by
  intro a ha
  obtain ⟨c, _, hc⟩ := List.mem_map.mp ha
  exact ⟨c, hc.symm⟩

/-- **WS-SM SM7.D.3**: data-cache maintenance by VA at the PoC covers **every**
modelled coherent agent.  Together with `modeledCoherentAgents_no_dma_master`
this is the complete v1.0.0 data-cache story: the only agents that exist are
the PEs, and the maintenance reaches all of them. -/
theorem dcMaintenance_covers_all_modeled_agents (views : DCacheViews)
    (op : DCacheMaintenance) :
    ∀ a ∈ modeledCoherentAgents, ∀ c : CoreId, a = .core c →
      (dcMaintenanceAllCores views op).get c =
        applyDCacheMaintenance (views.get c) op :=
  fun _ _ c _ => dcMaintenanceAllCores_get views op c

-- ============================================================================
-- SM7.D.4 — The SMP cache-coherency invariant (the 14th bundle conjunct)
-- ============================================================================

/-- **WS-SM SM7.D.4**: a cached instruction line is *coherent with the page
tables* when the mapping it was fetched through is still live **and still
executable**.

Two conjuncts, and both are load-bearing:

* `tlbEntryConsistent st l.toTranslation` — the ASID still resolves to a root
  and that root still maps `l.vaddr` to `(l.paddr, l.perms)`.  This is the
  SM7.F post-review *conjunction* form, so a line whose address space was
  destroyed (`resolveAsidRoot = none` after a VSpaceRoot retype) is **stale**,
  not vacuously fine.
* `l.perms.execute = true` — the mapping is still executable.  A fetch can
  only occur through an executable translation, so a line whose mapping has
  lost execute permission has outlived its authorisation.

The kernel's obligation is to broadcast the maintenance *before* committing a
transition that would falsify either conjunct — which is exactly what the live
`.vspaceUnmap` and `.lifecycleRetype` wrappers do. -/
def icacheLineConsistent (st : SystemState) (l : ICacheLine) : Prop :=
  tlbEntryConsistent st l.toTranslation ∧ l.perms.execute = true

/-- **WS-SM SM7.D.4** (`icacheCoherent_perCore`): the SMP instruction-cache
coherency invariant — on **every** core, **every** cached line still has a
live executable mapping.

The **14th `proofLayerInvariantBundle` conjunct** (`Invariant.lean`), and the
instruction-side companion of the 13th
(`tlbInvalidationConsistent_perCore`).  Unlike the 13th it needs no
pending-allowance disjunct: instruction-cache maintenance is a *synchronous*
broadcast instruction (`IC IALLUIS` / `IC IVAU`), not a queued
request/acknowledge round, so there is no committed window in which a core's
line is stale-but-scheduled-for-retirement.  Every transition that can falsify
a line's witness performs the broadcast atomically with the state change. -/
def icacheCoherent_perCore (st : SystemState) : Prop :=
  ∀ c : CoreId, ∀ l ∈ (icacheOnCore st c).lines, icacheLineConsistent st l

/-- **WS-SM SM7.D.4** (the transport lever): line coherency carries across any
frame that preserves the page tables (`objects` + `asidTable`, hence the same
`resolveAsidRoot`).  Every preservation proof rides this — the cache
operations never touch a page table, and the page-table operations pair with a
broadcast. -/
theorem icacheLineConsistent_of_frame {st st' : SystemState} {l : ICacheLine}
    (hObjects : st'.objects = st.objects) (hAsidTable : st'.asidTable = st.asidTable)
    (h : icacheLineConsistent st l) : icacheLineConsistent st' l :=
  ⟨tlbEntryConsistent_of_frame hObjects hAsidTable h.1, h.2⟩

/-- **WS-SM SM7.D.4**: at boot the invariant holds vacuously — every core's
instruction cache is cold (`default_icacheOnCore`), so there is no line to
witness.  The bundle boot witness. -/
theorem default_icacheCoherent_perCore :
    icacheCoherent_perCore (default : SystemState) := by
  intro c l hl
  rw [default_icacheOnCore] at hl
  simp [ICacheState.empty] at hl

/-- **WS-SM SM7.D.4**: the invariant projects to the boot core. -/
theorem icacheCoherent_perCore_bootCore {st : SystemState}
    (h : icacheCoherent_perCore st) :
    ∀ l ∈ (icacheOnCore st bootCoreId).lines, icacheLineConsistent st l :=
  h bootCoreId

/-- **WS-SM SM7.D.4**: a PE-local instruction-cache invalidation preserves the
invariant — it only removes lines, and touches no page table.  Invalidation is
*always* safe; what is unsafe is invalidating too **narrowly** (the reach
hazard `icInvalidateOnCore_icacheOnCore_ne` names), which is a completeness
question, not a soundness one. -/
theorem icInvalidateOnCore_preserves_icacheCoherent_perCore
    (st : SystemState) (c : CoreId) (op : ICacheInvalidation)
    (h : icacheCoherent_perCore st) :
    icacheCoherent_perCore (icInvalidateOnCore st c op) := by
  intro c' l hl
  have hpre : l ∈ (icacheOnCore st c').lines := by
    by_cases hcc : c = c'
    · subst hcc; exact icInvalidateOnCore_subset st c op hl
    · rw [icInvalidateOnCore_icacheOnCore_ne st op hcc] at hl; exact hl
  exact icacheLineConsistent_of_frame
    (icInvalidateOnCore_frame st c op).1
    (icInvalidateOnCore_frame st c op).2.1
    (h c' l hpre)

/-- **WS-SM SM7.D.4**: the domain broadcast preserves the invariant — same
reasoning as the local form, applied on every reached core. -/
theorem icInvalidateBroadcast_preserves_icacheCoherent_perCore
    (st : SystemState) (reach : List CoreId) (op : ICacheInvalidation)
    (h : icacheCoherent_perCore st) :
    icacheCoherent_perCore (icInvalidateBroadcast st reach op) := by
  intro c l hl
  exact icacheLineConsistent_of_frame
    (icInvalidateBroadcast_frame st reach op).1
    (icInvalidateBroadcast_frame st reach op).2.1
    (h c l (icInvalidateBroadcast_subset st reach op hl))

/-- **WS-SM SM7.D.4** (the environment's side of the contract): the hardware
instruction fetch preserves the invariant **provided it caches a line whose
mapping is live and executable** — which is exactly what an instruction fetch
requires to have happened at all (a fetch through a non-executable or absent
mapping takes a permission/translation fault instead of filling a line).

Together with the two invalidation theorems above this closes the model's
coherency story: the environment never caches an incoherent line, and the
kernel never *makes* a cached line incoherent without broadcasting first. -/
theorem icFetchOnCore_preserves_icacheCoherent_perCore
    (st : SystemState) (c : CoreId) (l : ICacheLine)
    (hCoherent : icacheCoherent_perCore st)
    (hLine : icacheLineConsistent st l) :
    icacheCoherent_perCore (icFetchOnCore st c l) := by
  have hObj : (icFetchOnCore st c l).objects = st.objects :=
    (icFetchOnCore_frame st c l).1
  have hAsid : (icFetchOnCore st c l).asidTable = st.asidTable :=
    (icFetchOnCore_frame st c l).2.1
  intro c' l' hl'
  by_cases hcc : c = c'
  · subst hcc
    simp only [icFetchOnCore, setIcacheOnCore_icacheOnCore_self] at hl'
    rcases List.mem_cons.mp hl' with heq | hmemOld
    · subst heq; exact icacheLineConsistent_of_frame hObj hAsid hLine
    · exact icacheLineConsistent_of_frame hObj hAsid (hCoherent c l' hmemOld)
  · have hpre : l' ∈ (icacheOnCore st c').lines := by
      rw [icFetchOnCore_icacheOnCore_ne st l hcc] at hl'; exact hl'
    exact icacheLineConsistent_of_frame hObj hAsid (hCoherent c' l' hpre)

/-- **WS-SM SM7.D.4** (fetch contract, sanity direction): a fetch that would
cache an **incoherent** line is impossible in the model's own terms — the
hypothesis `icacheLineConsistent` is not decoration.  Stated as the
contrapositive so the obligation reads as the hardware precondition it is: if
core `c` holds a line after a fetch and the invariant holds, that line had a
live executable mapping. -/
theorem icFetchOnCore_line_was_authorised
    (st : SystemState) (c : CoreId) (l : ICacheLine)
    (hCoherent : icacheCoherent_perCore st)
    (hLine : icacheLineConsistent st l) :
    icacheLineConsistent (icFetchOnCore st c l) l :=
  icFetchOnCore_preserves_icacheCoherent_perCore st c l hCoherent hLine c l
    (icFetchOnCore_mem st c l)

-- ============================================================================
-- SM7.D.4 (runtime checkability) — decidable per-core cache coherency
-- ============================================================================

/-- **WS-SM SM7.D.4**: an executable Boolean check of single-line coherency,
composed from the SM7.C.5 translation checker and the execute-permission
test. -/
def icacheLineConsistentCheck (st : SystemState) (l : ICacheLine) : Bool :=
  tlbEntryConsistentCheck st l.toTranslation && l.perms.execute

/-- **WS-SM SM7.D.4**: the per-line check decides `icacheLineConsistent`. -/
theorem icacheLineConsistentCheck_iff (st : SystemState) (l : ICacheLine) :
    icacheLineConsistentCheck st l = true ↔ icacheLineConsistent st l := by
  unfold icacheLineConsistentCheck icacheLineConsistent
  rw [Bool.and_eq_true, tlbEntryConsistentCheck_iff]

/-- **WS-SM SM7.D.4**: an executable Boolean check of the whole per-core
invariant — what makes the **14th `proofLayerInvariantBundle` conjunct**
runtime-verifiable, exactly as the 12th (`pendingBounded`) and 13th
(`tlbInvalidationConsistent_perCore`) are. -/
def icacheCoherentCheck_perCore (st : SystemState) : Bool :=
  allCores.all (fun c =>
    (icacheOnCore st c).lines.all (fun l => icacheLineConsistentCheck st l))

/-- **WS-SM SM7.D.4**: the per-core check decides the per-core invariant. -/
theorem icacheCoherentCheck_perCore_iff (st : SystemState) :
    icacheCoherentCheck_perCore st = true ↔ icacheCoherent_perCore st := by
  unfold icacheCoherentCheck_perCore icacheCoherent_perCore
  have hmem : ∀ c : CoreId, c ∈ allCores := by intro c; simp [allCores]
  constructor
  · intro h c l hl
    rw [← icacheLineConsistentCheck_iff]
    rw [List.all_eq_true] at h
    have hc := h c (hmem c)
    rw [List.all_eq_true] at hc
    exact hc l hl
  · intro h
    rw [List.all_eq_true]
    intro c _
    rw [List.all_eq_true]
    intro l hl
    rw [icacheLineConsistentCheck_iff]
    exact h c l hl

instance (st : SystemState) : Decidable (icacheCoherent_perCore st) :=
  decidable_of_iff _ (icacheCoherentCheck_perCore_iff st)

-- ============================================================================
-- SM7.D.4 — cacheCoherency_cross_subsystem (the memory-subsystem capstone)
-- ============================================================================

/-- **WS-SM SM7.D.4** (`cacheCoherency_cross_subsystem`): the cache-side
capstone, mirroring SM7.C.7's `tlbConsistency_cross_subsystem`.  A covering
instruction-cache broadcast, applied to a per-core-coherent state:

1. **removes every covered line on every core** — the instruction-side SMP
   safety guarantee (no core retains a line the operand retired), and
2. **preserves per-core coherency** — the broadcast frames the page tables
   (`objects` + `asidTable` ⇒ `resolveAsidRoot` unchanged) and only removes
   lines, so every core's surviving view still has live executable mappings.

Together with `dcMaintenanceByVA_reaches_all_cores` (the data side, where
hardware coherency makes the reach unconditional) this is the complete SM7.D
statement: **every cache-maintenance operation the kernel issues reaches every
core**. -/
theorem cacheCoherency_cross_subsystem (st : SystemState)
    {reach : List CoreId} (hcov : ∀ c : CoreId, c ∈ reach)
    (op : ICacheInvalidation) (hCoherent : icacheCoherent_perCore st) :
    (∀ (c : CoreId) {l : ICacheLine}, icacheLineMatches op l = true →
        l ∉ (icacheOnCore (icInvalidateBroadcast st reach op) c).lines) ∧
    icacheCoherent_perCore (icInvalidateBroadcast st reach op) :=
  ⟨icInvalidateBroadcast_reaches_all_cores st hcov op,
   icInvalidateBroadcast_preserves_icacheCoherent_perCore st reach op hCoherent⟩

/-- **WS-SM SM7.D.4**: the instruction-cache broadcast preserves the SM7.C/F
**per-core TLB** invariant (the 13th conjunct) — it frames `perCoreTlb`, the
page tables and the shootdown state, so the whole 13th-conjunct witness
transports unchanged.  This is what makes the SM7.D maintenance composable
onto the SM7.F wrappers without re-proving their TLB obligations. -/
theorem icInvalidateBroadcast_preserves_tlbInvalidationConsistent_perCore
    (st : SystemState) (reach : List CoreId) (op : ICacheInvalidation)
    (hTlb : tlbInvalidationConsistent_perCore st) :
    tlbInvalidationConsistent_perCore (icInvalidateBroadcast st reach op) := by
  intro c e he
  have hview : tlbOnCore (icInvalidateBroadcast st reach op) c = tlbOnCore st c := by
    simp only [tlbOnCore, icInvalidateBroadcast]
  rw [hview] at he
  exact tlbEntryOk_of_frame_eq
    (icInvalidateBroadcast_frame st reach op).1
    (icInvalidateBroadcast_frame st reach op).2.1
    (icInvalidateBroadcast_frame st reach op).2.2.2.2.1
    (hTlb c e he)

/-- **WS-SM SM7.D.4**: the joint SMP memory-subsystem statement — one covering
instruction-cache broadcast leaves **both** per-core cached structures in
their invariant states.  The `perCoreTlb` half is untouched (the broadcast
frames it), so the 13th conjunct rides through unchanged while the 14th is
re-established; this is the composition every live wrapper's post-state
needs. -/
theorem icInvalidateBroadcast_preserves_perCore_memory_invariants
    (st : SystemState) (reach : List CoreId) (op : ICacheInvalidation)
    (hTlb : tlbInvalidationConsistent_perCore st)
    (hIcache : icacheCoherent_perCore st) :
    tlbInvalidationConsistent_perCore (icInvalidateBroadcast st reach op) ∧
    icacheCoherent_perCore (icInvalidateBroadcast st reach op) :=
  ⟨icInvalidateBroadcast_preserves_tlbInvalidationConsistent_perCore st reach op hTlb,
   icInvalidateBroadcast_preserves_icacheCoherent_perCore st reach op hIcache⟩

-- ============================================================================
-- SM7.D.1 — Live wiring: the instruction-cache broadcast combinator
-- ============================================================================

/-- **WS-SM SM7.D.1**: record one owed maintenance operand in the emission
ledger (`SystemState.pendingIcacheMaintenance`).

The model applies the operand to `perCoreICache` immediately — that is what
makes the SM7.D.4 invariant hold in the committed state — while the *hardware*
emission necessarily happens later, at the runtime seam, once the transition has
been committed.  This ledger is the bridge: it carries the exact operand the
model used across that gap, so the seam emits precisely it rather than the
strongest operand it could justify from the shootdown diff.

Accumulation appends (`recordIcacheMaintenanceList`), dropping only an operand
already **covered** by an entry the ledger holds, so a transition that owed two
incomparable operands keeps both rather than collapsing them.  Collapsing would
be unsound here: `iallu` is not a top element, since `IC IALLUIS` performs no
`DC CVAU` and therefore does not discharge a `unifyPage`'s clean to the Point of
Unification.  Every live seam owes at most one operand against a ledger the
runtime cleared on the previous syscall, so in practice the ledger is the
singleton holding the model's exact operand. -/
def recordIcacheMaintenance (st : SystemState) (op : ICacheInvalidation) :
    SystemState :=
  { st with pendingIcacheMaintenance :=
      recordIcacheMaintenanceList st.pendingIcacheMaintenance op }

/-- **WS-SM SM7.D.1**: recording touches only the ledger — every other
`SystemState` field frames (all `rfl`, the record-update shape), so it composes
onto any transition without disturbing a single other subsystem's invariant. -/
@[simp] theorem recordIcacheMaintenance_objects (st : SystemState)
    (op : ICacheInvalidation) :
    (recordIcacheMaintenance st op).objects = st.objects := rfl
@[simp] theorem recordIcacheMaintenance_asidTable (st : SystemState)
    (op : ICacheInvalidation) :
    (recordIcacheMaintenance st op).asidTable = st.asidTable := rfl
@[simp] theorem recordIcacheMaintenance_scheduler (st : SystemState)
    (op : ICacheInvalidation) :
    (recordIcacheMaintenance st op).scheduler = st.scheduler := rfl
@[simp] theorem recordIcacheMaintenance_machine (st : SystemState)
    (op : ICacheInvalidation) :
    (recordIcacheMaintenance st op).machine = st.machine := rfl
@[simp] theorem recordIcacheMaintenance_tlb (st : SystemState)
    (op : ICacheInvalidation) :
    (recordIcacheMaintenance st op).tlb = st.tlb := rfl
@[simp] theorem recordIcacheMaintenance_tlbShootdown (st : SystemState)
    (op : ICacheInvalidation) :
    (recordIcacheMaintenance st op).tlbShootdown = st.tlbShootdown := rfl
@[simp] theorem recordIcacheMaintenance_perCoreTlb (st : SystemState)
    (op : ICacheInvalidation) :
    (recordIcacheMaintenance st op).perCoreTlb = st.perCoreTlb := rfl
@[simp] theorem recordIcacheMaintenance_perCoreICache (st : SystemState)
    (op : ICacheInvalidation) :
    (recordIcacheMaintenance st op).perCoreICache = st.perCoreICache := rfl

/-- **WS-SM SM7.D.1**: recording an operand leaves the ledger non-empty — the
runtime seam is guaranteed to find work when the model performed a
broadcast. -/
theorem recordIcacheMaintenance_ne_nil (st : SystemState)
    (op : ICacheInvalidation) :
    (recordIcacheMaintenance st op).pendingIcacheMaintenance ≠ [] :=
  recordIcacheMaintenanceList_ne_nil _ op

/-- **WS-SM SM7.D**: after recording, the ledger holds an entry that **covers**
the recorded operand — so draining the ledger discharges every obligation the
transition incurred, with no appeal to a (non-existent) ordering under which
`iallu` would dominate a clean-to-PoU. -/
theorem recordIcacheMaintenance_covered (st : SystemState)
    (op : ICacheInvalidation) :
    ∃ a ∈ (recordIcacheMaintenance st op).pendingIcacheMaintenance,
      a.covers op = true :=
  recordIcacheMaintenanceList_covered _ op

/-- **WS-SM SM7.D.1** (the exactness property the closure rests on): recording
into an **empty** ledger stores the operand verbatim.  Every live seam runs at
most one broadcast per transition against a ledger the runtime cleared on the
previous syscall, so the runtime emits the model's *precise* operand — a
targeted page invalidate for an executable unmap, and nothing at all for a
non-executable one. -/
@[simp] theorem recordIcacheMaintenance_of_nil {st : SystemState}
    (h : st.pendingIcacheMaintenance = []) (op : ICacheInvalidation) :
    (recordIcacheMaintenance st op).pendingIcacheMaintenance = [op] := by
  simp [recordIcacheMaintenance, h]

/-- **WS-SM SM7.D.1**: drain the emission ledger — the runtime seam's clear,
performed in the *same* atomic step that commits the transition, so every state
observed at a syscall boundary owes nothing. -/
def clearIcacheMaintenance (st : SystemState) : SystemState :=
  { st with pendingIcacheMaintenance := [] }

/-- **WS-SM SM7.D.1**: the drain leaves the ledger empty. -/
@[simp] theorem clearIcacheMaintenance_pending (st : SystemState) :
    (clearIcacheMaintenance st).pendingIcacheMaintenance = [] := rfl

/-- **WS-SM SM7.D.1**: the drain touches only the ledger — in particular it
leaves `perCoreICache` (and hence the SM7.D.4 invariant) and every trace-visible
field untouched, which is what makes the runtime clear trace-safe. -/
theorem clearIcacheMaintenance_frame (st : SystemState) :
    (clearIcacheMaintenance st).objects = st.objects ∧
    (clearIcacheMaintenance st).asidTable = st.asidTable ∧
    (clearIcacheMaintenance st).scheduler = st.scheduler ∧
    (clearIcacheMaintenance st).machine = st.machine ∧
    (clearIcacheMaintenance st).tlb = st.tlb ∧
    (clearIcacheMaintenance st).tlbShootdown = st.tlbShootdown ∧
    (clearIcacheMaintenance st).perCoreTlb = st.perCoreTlb ∧
    (clearIcacheMaintenance st).perCoreICache = st.perCoreICache :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **WS-SM SM7.D.1**: the drain preserves the 14th conjunct — it removes no
line and changes no page table. -/
theorem clearIcacheMaintenance_preserves_icacheCoherent_perCore
    (st : SystemState) (h : icacheCoherent_perCore st) :
    icacheCoherent_perCore (clearIcacheMaintenance st) :=
  fun c l hl => icacheLineConsistent_of_frame rfl rfl (h c l hl)

/-- **WS-SM SM7.D.1**: the drain preserves the 13th conjunct too. -/
theorem clearIcacheMaintenance_preserves_tlbInvalidationConsistent_perCore
    (st : SystemState) (h : tlbInvalidationConsistent_perCore st) :
    tlbInvalidationConsistent_perCore (clearIcacheMaintenance st) :=
  fun c e he => tlbEntryOk_of_frame_eq rfl rfl rfl (h c e he)

/-- **WS-SM SM7.D.1**: run a kernel transition and, on success, broadcast the
instruction-cache maintenance the transition owes.

The operand is computed from the **pre**-state (`mkOp`), because what has to
be invalidated is decided by what the transition is about to destroy — after
the fact the mapping is gone.  `none` means "this transition owes no
instruction-cache work", and then the wrapper commits the base result exactly
(so a transition that cannot invalidate a cached line adds no cost and no
trace divergence).

Errors propagate unchanged: a failed transition changed nothing, so it owes no
maintenance.  This is the instruction-side analogue of SM7.B.9's
`withShootdownRound`, minus the round — `IC IALLUIS` / `IC IVAU` complete in
the issuing instruction, with no queue and no acknowledgment. -/
def withIcacheBroadcast (mkOp : SystemState → Option ICacheInvalidation)
    (k : Kernel Unit) : Kernel Unit :=
  fun st =>
    let op? := mkOp st
    match k st with
    | .error e => .error e
    | .ok ((), st') =>
        match op? with
        | none => .ok ((), st')
        | some op =>
            .ok ((), recordIcacheMaintenance
              (icInvalidateBroadcast st' icBroadcastReach op) op)

/-- **WS-SM SM7.D.1**: the wrapper is error-transparent — it fails exactly
when the wrapped transition fails, with the same error. -/
theorem withIcacheBroadcast_error_iff
    (mkOp : SystemState → Option ICacheInvalidation) (k : Kernel Unit)
    (st : SystemState) (e : SeLe4n.Model.KernelError) :
    withIcacheBroadcast mkOp k st = .error e ↔ k st = .error e := by
  unfold withIcacheBroadcast
  cases hk : k st with
  | error e' => cases e'  <;> simp_all
  | ok pair => obtain ⟨u, st'⟩ := pair; cases u; cases mkOp st <;> simp

/-- **WS-SM SM7.D.1**: a transition that owes no instruction-cache work
commits exactly the base transition's result. -/
theorem withIcacheBroadcast_none_inert
    {mkOp : SystemState → Option ICacheInvalidation} (k : Kernel Unit)
    (st : SystemState) (hNone : mkOp st = none) :
    withIcacheBroadcast mkOp k st = k st := by
  unfold withIcacheBroadcast
  rw [hNone]
  cases k st with
  | error e => rfl
  | ok pair => obtain ⟨u, st'⟩ := pair; cases u; rfl

/-- **WS-SM SM7.D.1**: on the broadcasting branch the wrapper commits the base
result with the domain-wide invalidation applied. -/
theorem withIcacheBroadcast_some_ok
    {mkOp : SystemState → Option ICacheInvalidation} {k : Kernel Unit}
    {st st' : SystemState} {op : ICacheInvalidation}
    (hOp : mkOp st = some op) (hk : k st = .ok ((), st')) :
    withIcacheBroadcast mkOp k st =
      .ok ((), recordIcacheMaintenance
        (icInvalidateBroadcast st' icBroadcastReach op) op) := by
  unfold withIcacheBroadcast
  rw [hOp, hk]

/-- **WS-SM SM7.D.1**: the broadcast wrapper frames every field the base
transition committed except the per-core instruction caches — so composing it
onto a live transition is trace-safe (`perCoreICache ∉ projectState`) and
leaves every other subsystem's invariants exactly as the base transition left
them. -/
theorem withIcacheBroadcast_frame
    {mkOp : SystemState → Option ICacheInvalidation} {k : Kernel Unit}
    {st stB st' : SystemState}
    (hk : k st = .ok ((), stB))
    (hStep : withIcacheBroadcast mkOp k st = .ok ((), st')) :
    st'.objects = stB.objects ∧ st'.asidTable = stB.asidTable ∧
    st'.scheduler = stB.scheduler ∧ st'.machine = stB.machine ∧
    st'.tlb = stB.tlb ∧ st'.tlbShootdown = stB.tlbShootdown ∧
    st'.perCoreTlb = stB.perCoreTlb := by
  unfold withIcacheBroadcast at hStep
  rw [hk] at hStep
  cases hOp : mkOp st with
  | none =>
      rw [hOp] at hStep
      simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
      subst hStep; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | some op =>
      rw [hOp] at hStep
      simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
      subst hStep; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- SM7.D.1 — Live wiring (a): the `.vspaceUnmap` instruction-cache broadcast
-- ============================================================================

/-- **WS-SM SM7.D.1**: the physical address an unmap is about to stop being
executable at, if any.

`some p` exactly when the pre-state maps `(asid, vaddr)` to `p` **with execute
permission** — the only case in which a cached instruction line can exist for
this mapping, hence the only case that owes maintenance.  Read from the
*pre*-state, before `vspaceUnmapPage` erases the descriptor. -/
def unmapExecutablePaddr (st : SystemState) (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr) : Option SeLe4n.PAddr :=
  (resolveAsidRoot st asid).bind fun rr =>
    (VSpaceRoot.lookup rr.2 vaddr).bind fun lk =>
      if lk.2.execute then some lk.1 else none

/-- **WS-SM SM7.D.1**: the instruction-cache operand an unmap owes — a
targeted `IC IVAU` at the unmapped page's physical address when the mapping
was executable, and nothing otherwise.

Targeted rather than a full `IC IALLUIS`: instruction caches are PIPT to
software, so the retired page's lines are exactly the ones tagged with its
physical address, and flushing the whole domain's instruction caches on every
unmap would be a large, avoidable cost. -/
def unmapIcacheOperand (st : SystemState) (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr) : Option ICacheInvalidation :=
  (unmapExecutablePaddr st asid vaddr).map ICacheInvalidation.ivauPage

/-- **WS-SM SM7.D.1**: an executable pre-state mapping *does* produce an
operand — the completeness direction (the kernel never silently skips the
maintenance it owes). -/
theorem unmapExecutablePaddr_of_executable {st : SystemState}
    {asid : SeLe4n.ASID} {vaddr : SeLe4n.VAddr} {rid : SeLe4n.ObjId}
    {root : VSpaceRoot} {p : SeLe4n.PAddr} {perms : PagePermissions}
    (hres : resolveAsidRoot st asid = some (rid, root))
    (hlk : VSpaceRoot.lookup root vaddr = some (p, perms))
    (hx : perms.execute = true) :
    unmapExecutablePaddr st asid vaddr = some p := by
  simp [unmapExecutablePaddr, hres, hlk, hx]

/-- **WS-SM SM7.D.1**: the operand's physical address is the one the pre-state
mapping resolved to — the soundness direction (the maintenance targets exactly
the page being retired). -/
theorem unmapExecutablePaddr_eq_some {st : SystemState} {asid : SeLe4n.ASID}
    {vaddr : SeLe4n.VAddr} {p : SeLe4n.PAddr}
    (h : unmapExecutablePaddr st asid vaddr = some p) :
    ∃ rid root perms, resolveAsidRoot st asid = some (rid, root) ∧
      VSpaceRoot.lookup root vaddr = some (p, perms) ∧ perms.execute = true := by
  simp only [unmapExecutablePaddr, Option.bind_eq_some_iff] at h
  obtain ⟨rr, hres, lk, hlk, hif⟩ := h
  by_cases hx : lk.2.execute = true
  · rw [if_pos hx, Option.some.injEq] at hif
    subst hif
    exact ⟨rr.1, rr.2, lk.2, by simpa using hres, by simpa using hlk, hx⟩
  · rw [if_neg hx] at hif; cases hif

/-- **WS-SM SM7.D.1**: `unmapIcacheOperand` produces `some (.ivauPage p)` exactly
when `unmapExecutablePaddr` produces `some p`. -/
theorem unmapIcacheOperand_eq_some_iff (st : SystemState) (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr) (p : SeLe4n.PAddr) :
    unmapIcacheOperand st asid vaddr = some (.ivauPage p) ↔
      unmapExecutablePaddr st asid vaddr = some p := by
  unfold unmapIcacheOperand
  cases unmapExecutablePaddr st asid vaddr <;> simp

/-- **WS-SM SM7.D.1**: no executable mapping ⇒ no operand. -/
theorem unmapIcacheOperand_eq_none_iff (st : SystemState) (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr) :
    unmapIcacheOperand st asid vaddr = none ↔
      unmapExecutablePaddr st asid vaddr = none := by
  unfold unmapIcacheOperand
  cases unmapExecutablePaddr st asid vaddr <;> simp

/-- **WS-SM SM7.D.1** (**the live `.vspaceUnmap` seam**): the production VSpace
unmap, complete across *both* per-core cached structures.

Layered on SM7.F's `vspaceUnmapPageWithShootdownPerCore` (page-table erase +
local TLB flush + cross-core `.vae1` shootdown round + the initiator's own
per-core TLB drain), it adds the instruction-side obligation the TLB layer
cannot discharge: when the retired mapping was **executable**, an `IC IVAU`
broadcast over the shareability domain, so no core — the initiator included —
keeps a line fetched through a mapping that no longer exists.

Without it, unmapping an executable page and re-typing its frame would leave
remote cores able to fetch the previous owner's instructions from their
instruction caches through any later executable mapping of the same physical
page.  The TLB shootdown does not help: it retires *translations*, while the
instruction cache is tagged by physical address.

Trace-safe: `perCoreICache ∉ projectState`, and the broadcast frames every
field the syscall's round diff-recovery reads. -/
def vspaceUnmapPageWithShootdownAndIcacheBroadcast (executingCore : CoreId)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) : Kernel Unit :=
  withIcacheBroadcast (fun st => unmapIcacheOperand st asid vaddr)
    (vspaceUnmapPageWithShootdownPerCore executingCore asid vaddr)

/-- **WS-SM SM7.D.1**: the seam is error-transparent — it fails exactly when
the SM7.F unmap wrapper fails, with the same error. -/
theorem vspaceUnmapPageWithShootdownAndIcacheBroadcast_error_iff
    (executingCore : CoreId) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (st : SystemState) (e : SeLe4n.Model.KernelError) :
    vspaceUnmapPageWithShootdownAndIcacheBroadcast executingCore asid vaddr st
        = .error e ↔
      vspaceUnmapPageWithShootdownPerCore executingCore asid vaddr st = .error e :=
  withIcacheBroadcast_error_iff _ _ st e

/-- **WS-SM SM7.D.1**: unmapping a **non-executable** mapping owes no
instruction-cache work — the seam commits exactly the SM7.F wrapper's result,
so the common data-page unmap pays nothing. -/
theorem vspaceUnmapPageWithShootdownAndIcacheBroadcast_non_executable_inert
    (executingCore : CoreId) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (st : SystemState)
    (hNone : unmapExecutablePaddr st asid vaddr = none) :
    vspaceUnmapPageWithShootdownAndIcacheBroadcast executingCore asid vaddr st =
      vspaceUnmapPageWithShootdownPerCore executingCore asid vaddr st :=
  withIcacheBroadcast_none_inert _ st
    ((unmapIcacheOperand_eq_none_iff st asid vaddr).mpr hNone)

/-- **WS-SM SM7.D.1**: the SM7.F unmap wrapper frames the per-core instruction
caches — page-table erase, scalar flush, shootdown posting and the initiator's
TLB drain all leave `perCoreICache` untouched.  This is what makes the
instruction-cache change come *exclusively* from the SM7.D broadcast step (and
what makes the `none` branch genuinely inert). -/
theorem vspaceUnmapPageWithShootdownPerCore_perCoreICache_eq
    {executingCore : CoreId} {asid : SeLe4n.ASID} {vaddr : SeLe4n.VAddr}
    {st st' : SystemState}
    (hStep : vspaceUnmapPageWithShootdownPerCore executingCore asid vaddr st =
      .ok ((), st')) :
    st'.perCoreICache = st.perCoreICache := by
  unfold vspaceUnmapPageWithShootdownPerCore at hStep
  cases hUF : vspaceUnmapPageWithFlush asid vaddr st with
  | error e =>
      rw [(vspaceUnmapPageWithShootdown_error_iff executingCore asid vaddr st e).mpr hUF]
        at hStep
      simp at hStep
  | ok pair =>
      have hUF' : vspaceUnmapPageWithFlush asid vaddr st = .ok ((), pair.2) := hUF
      rw [vspaceUnmapPageWithShootdown_ok executingCore asid vaddr hUF'] at hStep
      simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
      subst hStep
      show pair.2.perCoreICache = st.perCoreICache
      exact vspaceUnmapPageWithFlush_perCoreICache_eq asid vaddr st pair.2 hUF'

/-- **WS-SM SM7.D.4** (the seam's key step): a cached line that **survives** the
unmap's instruction-cache maintenance cannot be a line for the unmapped
`(asid, vaddr)` pair.

Two ways the maintenance can leave a line standing, and both are covered:
* the unmap owed **no** operand (`unmapExecutablePaddr = none`) — then the
  mapping was not executable, and an admissible line for it would have carried
  `perms.execute = true`, contradicting `VSpaceRoot.lookup`'s functionality;
* the unmap owed `IC IVAU p` and the line survived it — then `l.paddr ≠ p`,
  while a line for the unmapped pair would have had exactly that physical
  address.

This is what discharges the page-table frame lemma's `hNotMatch` side condition
for every survivor. -/
theorem unmapSurvivor_not_target {st : SystemState} {asid : SeLe4n.ASID}
    {vaddr : SeLe4n.VAddr} {l : ICacheLine}
    (hCon : icacheLineConsistent st l)
    (hSurv : ∀ p, unmapExecutablePaddr st asid vaddr = some p → l.paddr ≠ p) :
    ¬(l.toTranslation.asid = asid ∧ l.toTranslation.vaddr = vaddr) := by
  rintro ⟨hA, hV⟩
  obtain ⟨rid, root, hres, hlk⟩ := hCon.1
  rw [hA] at hres
  rw [hV] at hlk
  exact hSurv l.paddr
    (unmapExecutablePaddr_of_executable hres hlk hCon.2) rfl

/-- **WS-SM SM7.D.4** (**the live seam's coherency theorem**): the production
`.vspaceUnmap` path preserves the SMP instruction-cache coherency invariant.

Per core, every line still held after the transition is one the maintenance did
not cover, hence — by `unmapSurvivor_not_target` — not a line for the unmapped
page; its witness therefore rides the unmap's page-table frame
(`vspaceUnmapPageWithFlush_tlbEntryConsistent_frame`), and its execute
permission is unchanged.  Lines that *were* for the unmapped page are gone from
**every** core, because the operand was broadcast over the whole shareability
domain rather than executed on the initiator alone.

This is the theorem that makes the 14th `proofLayerInvariantBundle` conjunct
true across the live unmap — the instruction-side counterpart of SM7.F's
`vspaceUnmapPageWithShootdownPerCore_preserves_tlbInvalidationConsistent_perCore`. -/
theorem vspaceUnmapPageWithShootdownAndIcacheBroadcast_preserves_icacheCoherent_perCore
    {executingCore : CoreId} {asid : SeLe4n.ASID} {vaddr : SeLe4n.VAddr}
    {st st' : SystemState}
    (hCoherent : icacheCoherent_perCore st)
    (hObjK : st.objects.invExtK) (hAsidK : st.asidTable.invExtK)
    (hMappingsWF : ∀ (oid : SeLe4n.ObjId) (root : VSpaceRoot),
      st.objects[oid]? = some (.vspaceRoot root) → root.mappings.invExt)
    (hMappingsSize : ∀ (oid : SeLe4n.ObjId) (root : VSpaceRoot),
      st.objects[oid]? = some (.vspaceRoot root) →
        root.mappings.size < root.mappings.capacity)
    (hStep : vspaceUnmapPageWithShootdownAndIcacheBroadcast executingCore asid
      vaddr st = .ok ((), st')) :
    icacheCoherent_perCore st' := by
  unfold vspaceUnmapPageWithShootdownAndIcacheBroadcast at hStep
  -- Decompose the base (SM7.F) wrapper's result.
  cases hBase : vspaceUnmapPageWithShootdownPerCore executingCore asid vaddr st with
  | error e =>
      rw [(withIcacheBroadcast_error_iff (fun st => unmapIcacheOperand st asid vaddr)
        (vspaceUnmapPageWithShootdownPerCore executingCore asid vaddr) st e).mpr hBase]
        at hStep
      cases hStep
  | ok pair =>
      obtain ⟨u, stP⟩ := pair
      cases u
      have hBase' : vspaceUnmapPageWithShootdownPerCore executingCore asid vaddr st =
          .ok ((), stP) := hBase
      -- The base wrapper frames the instruction caches …
      have hIc : stP.perCoreICache = st.perCoreICache :=
        vspaceUnmapPageWithShootdownPerCore_perCoreICache_eq hBase'
      -- … and its page-table effect is the unmap-flush's.
      cases hUF : vspaceUnmapPageWithFlush asid vaddr st with
      | error e =>
          have hErr : vspaceUnmapPageWithShootdownPerCore executingCore asid vaddr st =
              .error e := by
            unfold vspaceUnmapPageWithShootdownPerCore
            rw [(vspaceUnmapPageWithShootdown_error_iff executingCore asid vaddr st e).mpr hUF]
          rw [hErr] at hBase'
          cases hBase'
      | ok pairF =>
          have hUF' : vspaceUnmapPageWithFlush asid vaddr st = .ok ((), pairF.2) := hUF
          have hstP : stP = drainInitiatorPerCoreView
              (tlbShootdownBroadcastCoalescing pairF.2 executingCore
                (shootdownTargets executingCore) (encodePageInvalidation asid vaddr))
              executingCore [encodePageInvalidation asid vaddr] := by
            unfold vspaceUnmapPageWithShootdownPerCore at hBase'
            rw [vspaceUnmapPageWithShootdown_ok executingCore asid vaddr hUF'] at hBase'
            simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hBase'
            exact hBase'.symm
          have hObjP : stP.objects = pairF.2.objects := by rw [hstP]; rfl
          have hAsidP : stP.asidTable = pairF.2.asidTable := by rw [hstP]; rfl
          -- The shared per-survivor argument, parameterised by the maintenance's
          -- guarantee about a survivor's physical address.
          have hsurv : ∀ (c : CoreId) (l : ICacheLine),
              l ∈ (icacheOnCore stP c).lines →
              (∀ p, unmapExecutablePaddr st asid vaddr = some p → l.paddr ≠ p) →
              icacheLineConsistent stP l := by
            intro c l hl hNe
            have hpre : l ∈ (icacheOnCore st c).lines := by
              simpa only [icacheOnCore, hIc] using hl
            have hCon := hCoherent c l hpre
            refine ⟨?_, hCon.2⟩
            refine tlbEntryConsistent_of_frame hObjP hAsidP ?_
            exact vspaceUnmapPageWithFlush_tlbEntryConsistent_frame asid vaddr hObjK
              hAsidK hMappingsWF hMappingsSize hUF'
              (unmapSurvivor_not_target hCon hNe) hCon.1
          -- Case on whether the unmap owes instruction-cache maintenance.
          cases hOp : unmapIcacheOperand st asid vaddr with
          | none =>
              rw [withIcacheBroadcast_none_inert _ st hOp, hBase'] at hStep
              simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
              subst hStep
              intro c l hl
              exact hsurv c l hl (fun p hp => by
                rw [(unmapIcacheOperand_eq_none_iff st asid vaddr).mp hOp] at hp; cases hp)
          | some op =>
              rw [withIcacheBroadcast_some_ok hOp hBase'] at hStep
              simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
              subst hStep
              -- The operand is always a targeted `IC IVAU`.
              obtain ⟨p, hp⟩ : ∃ p, op = .ivauPage p := by
                unfold unmapIcacheOperand at hOp
                cases hE : unmapExecutablePaddr st asid vaddr with
                | none => rw [hE] at hOp; cases hOp
                | some q => rw [hE] at hOp; exact ⟨q, by simpa using hOp.symm⟩
              subst hp
              have hpEq : unmapExecutablePaddr st asid vaddr = some p :=
                (unmapIcacheOperand_eq_some_iff st asid vaddr p).mp hOp
              intro c l hl
              -- The ledger record frames every core's view, so a surviving line
              -- is one the broadcast itself left standing.
              rw [show icacheOnCore (recordIcacheMaintenance
                  (icInvalidateBroadcast stP icBroadcastReach (.ivauPage p))
                  (.ivauPage p)) c
                = icacheOnCore (icInvalidateBroadcast stP icBroadcastReach
                    (.ivauPage p)) c from rfl] at hl
              have hlP : l ∈ (icacheOnCore stP c).lines :=
                icInvalidateBroadcast_subset stP icBroadcastReach _ hl
              have hNe : l.paddr ≠ p := by
                rw [icInvalidateBroadcast_icacheOnCore,
                    if_pos (icBroadcastReach_cover c)] at hl
                exact applyICacheInvalidation_survivor_paddr_ne hl
              exact icacheLineConsistent_of_frame rfl rfl
                (hsurv c l hlP (fun q hq => by rw [hpEq] at hq; cases hq; exact hNe))

/-- **WS-SM SM7.D.4**: the live `.vspaceUnmap` seam also preserves the **13th**
conjunct — the SM7.F per-core TLB invariant.  The instruction-cache broadcast
frames every field that conjunct reads, so the SM7.F theorem carries through
the added step unchanged.  Together with
`…_preserves_icacheCoherent_perCore` this is the complete memory-subsystem
statement for the production unmap path: both per-core cached structures stay
in their invariant states. -/
theorem vspaceUnmapPageWithShootdownAndIcacheBroadcast_preserves_tlbInvalidationConsistent_perCore
    {executingCore : CoreId} {asid : SeLe4n.ASID} {vaddr : SeLe4n.VAddr}
    {st st' : SystemState}
    (hq : shootdownQuiescent st.tlbShootdown)
    (hConsist : tlbInvalidationConsistent_perCore st)
    (hObjK : st.objects.invExtK) (hAsidK : st.asidTable.invExtK)
    (hMappingsWF : ∀ (oid : SeLe4n.ObjId) (root : VSpaceRoot),
      st.objects[oid]? = some (.vspaceRoot root) → root.mappings.invExt)
    (hMappingsSize : ∀ (oid : SeLe4n.ObjId) (root : VSpaceRoot),
      st.objects[oid]? = some (.vspaceRoot root) →
        root.mappings.size < root.mappings.capacity)
    (hStep : vspaceUnmapPageWithShootdownAndIcacheBroadcast executingCore asid
      vaddr st = .ok ((), st')) :
    tlbInvalidationConsistent_perCore st' := by
  unfold vspaceUnmapPageWithShootdownAndIcacheBroadcast at hStep
  cases hBase : vspaceUnmapPageWithShootdownPerCore executingCore asid vaddr st with
  | error e =>
      rw [(withIcacheBroadcast_error_iff (fun st => unmapIcacheOperand st asid vaddr)
        (vspaceUnmapPageWithShootdownPerCore executingCore asid vaddr) st e).mpr hBase]
        at hStep
      cases hStep
  | ok pair =>
      obtain ⟨u, stP⟩ := pair
      cases u
      have hBase' : vspaceUnmapPageWithShootdownPerCore executingCore asid vaddr st =
          .ok ((), stP) := hBase
      have hP : tlbInvalidationConsistent_perCore stP :=
        vspaceUnmapPageWithShootdownPerCore_preserves_tlbInvalidationConsistent_perCore
          hq hConsist hObjK hAsidK hMappingsWF hMappingsSize hBase'
      cases hOp : unmapIcacheOperand st asid vaddr with
      | none =>
          rw [withIcacheBroadcast_none_inert _ st hOp, hBase'] at hStep
          simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
          subst hStep; exact hP
      | some op =>
          rw [withIcacheBroadcast_some_ok hOp hBase'] at hStep
          simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
          subst hStep
          exact icInvalidateBroadcast_preserves_tlbInvalidationConsistent_perCore
            stP icBroadcastReach op hP

/-- **WS-SM SM7.D.4** (the production unmap capstone): the live `.vspaceUnmap`
path keeps **both** SMP per-core memory invariants — the 13th conjunct
(per-core TLB) and the 14th (per-core instruction cache) — from a quiescent
shootdown state.  Every per-PE cached view of a mapping the syscall destroys is
either retired or provably covered, on every core. -/
theorem vspaceUnmapPageWithShootdownAndIcacheBroadcast_preserves_perCore_memory_invariants
    {executingCore : CoreId} {asid : SeLe4n.ASID} {vaddr : SeLe4n.VAddr}
    {st st' : SystemState}
    (hq : shootdownQuiescent st.tlbShootdown)
    (hConsist : tlbInvalidationConsistent_perCore st)
    (hCoherent : icacheCoherent_perCore st)
    (hObjK : st.objects.invExtK) (hAsidK : st.asidTable.invExtK)
    (hMappingsWF : ∀ (oid : SeLe4n.ObjId) (root : VSpaceRoot),
      st.objects[oid]? = some (.vspaceRoot root) → root.mappings.invExt)
    (hMappingsSize : ∀ (oid : SeLe4n.ObjId) (root : VSpaceRoot),
      st.objects[oid]? = some (.vspaceRoot root) →
        root.mappings.size < root.mappings.capacity)
    (hStep : vspaceUnmapPageWithShootdownAndIcacheBroadcast executingCore asid
      vaddr st = .ok ((), st')) :
    tlbInvalidationConsistent_perCore st' ∧ icacheCoherent_perCore st' :=
  ⟨vspaceUnmapPageWithShootdownAndIcacheBroadcast_preserves_tlbInvalidationConsistent_perCore
      hq hConsist hObjK hAsidK hMappingsWF hMappingsSize hStep,
   vspaceUnmapPageWithShootdownAndIcacheBroadcast_preserves_icacheCoherent_perCore
      hCoherent hObjK hAsidK hMappingsWF hMappingsSize hStep⟩

-- ============================================================================
-- SM7.D — The user-facing code-publication path (`.vspaceUnifyInstruction`)
-- ============================================================================

/-- **WS-SM SM7.D**: the physical page a unify request names, if the caller's
address space currently maps it.

Deliberately **not** gated on execute permission.  The subject that must run
the sequence is the one whose *stores* need publishing — a loader or JIT writes
the code through a **writable** mapping and unifies it there, after which some
(possibly other) subject maps the frame executable and runs it.  Requiring the
mapping to already be executable would make the operation useless in exactly
the case it exists for.  Authority is enforced at the syscall boundary instead
(`.vspaceUnifyInstruction` requires the `.write` right — you may publish code
you were able to write). -/
def unifyTargetPaddr (st : SystemState) (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr) : Option SeLe4n.PAddr :=
  (resolveAsidRoot st asid).bind fun rr =>
    (VSpaceRoot.lookup rr.2 vaddr).map (fun lk => lk.1)

/-- **WS-SM SM7.D**: a live mapping yields its physical page. -/
theorem unifyTargetPaddr_of_mapped {st : SystemState} {asid : SeLe4n.ASID}
    {vaddr : SeLe4n.VAddr} {rid : SeLe4n.ObjId} {root : VSpaceRoot}
    {p : SeLe4n.PAddr} {perms : PagePermissions}
    (hres : resolveAsidRoot st asid = some (rid, root))
    (hlk : VSpaceRoot.lookup root vaddr = some (p, perms)) :
    unifyTargetPaddr st asid vaddr = some p := by
  simp [unifyTargetPaddr, hres, hlk]

/-- **WS-SM SM7.D** (**the user-facing code-publication transition**): unify the
instruction and data views of one mapped page.

seLe4n's equivalent of seL4's `Page_Unify_Instruction`, and the mechanism by
which user software discharges the obligation ARMv8-A places on it: after
writing instructions through a data mapping (a program loader, a JIT), the
stores sit in the data cache, while an instruction fetch reads at the Point of
Unification — so without an explicit `DC CVAU` → `DSB` → `IC IVAU` → `DSB` →
`ISB` over the region, the fetch may observe the *old* content, even on the very
PE that performed the stores.

The kernel cannot do this implicitly: it has no way to know when a writer has
finished emitting code, and a JIT patching an already-mapped page never
re-enters a mapping operation at all.  Hence an explicit operation, exactly as
seL4 concluded.

The maintenance is issued as a **domain-wide** operand
(`icInvalidateBroadcast … icBroadcastReach`), because a remote PE may hold
lines from a previous incarnation of the same physical page; and it is recorded
in the emission ledger so the runtime emits the full unify sequence rather than
a bare invalidate.  The page tables are not modified — this is a pure cache
operation. -/
def vspaceUnifyInstructionPage (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) :
    Kernel Unit :=
  fun st =>
    match resolveAsidRoot st asid with
    | none => .error .asidNotBound
    | some (_, root) =>
        match VSpaceRoot.lookup root vaddr with
        | none => .error .translationFault
        | some (paddr, _) =>
            .ok ((), recordIcacheMaintenance
              (icInvalidateBroadcast st icBroadcastReach (.unifyPage paddr))
              (.unifyPage paddr))

/-- **WS-SM SM7.D**: an unbound ASID is rejected — fail-closed, no maintenance
emitted for an address space the caller does not have. -/
theorem vspaceUnifyInstructionPage_asid_unbound (st : SystemState)
    {asid : SeLe4n.ASID} (vaddr : SeLe4n.VAddr)
    (h : resolveAsidRoot st asid = none) :
    vspaceUnifyInstructionPage asid vaddr st = .error .asidNotBound := by
  unfold vspaceUnifyInstructionPage; rw [h]

/-- **WS-SM SM7.D**: an unmapped address is rejected — a subject cannot use the
operation to probe or maintain memory it has no mapping for. -/
theorem vspaceUnifyInstructionPage_unmapped {st : SystemState}
    {asid : SeLe4n.ASID} {vaddr : SeLe4n.VAddr} {rid : SeLe4n.ObjId}
    {root : VSpaceRoot}
    (hres : resolveAsidRoot st asid = some (rid, root))
    (hlk : VSpaceRoot.lookup root vaddr = none) :
    vspaceUnifyInstructionPage asid vaddr st = .error .translationFault := by
  unfold vspaceUnifyInstructionPage; simp only [hres, hlk]

/-- **WS-SM SM7.D**: a successful unify commits the domain-wide maintenance for
the mapped page and records it for the runtime. -/
theorem vspaceUnifyInstructionPage_ok {st : SystemState} {asid : SeLe4n.ASID}
    {vaddr : SeLe4n.VAddr} {rid : SeLe4n.ObjId} {root : VSpaceRoot}
    {p : SeLe4n.PAddr} {perms : PagePermissions}
    (hres : resolveAsidRoot st asid = some (rid, root))
    (hlk : VSpaceRoot.lookup root vaddr = some (p, perms)) :
    vspaceUnifyInstructionPage asid vaddr st =
      .ok ((), recordIcacheMaintenance
        (icInvalidateBroadcast st icBroadcastReach (.unifyPage p))
        (.unifyPage p)) := by
  unfold vspaceUnifyInstructionPage; simp only [hres, hlk]

/-- **WS-SM SM7.D**: the transition modifies **no page table** — it is a pure
cache operation, so it cannot be used to alter a mapping, and every VSpace
invariant transports unchanged. -/
theorem vspaceUnifyInstructionPage_frame {st st' : SystemState}
    {asid : SeLe4n.ASID} {vaddr : SeLe4n.VAddr}
    (h : vspaceUnifyInstructionPage asid vaddr st = .ok ((), st')) :
    st'.objects = st.objects ∧ st'.asidTable = st.asidTable ∧
    st'.scheduler = st.scheduler ∧ st'.machine = st.machine ∧
    st'.tlb = st.tlb ∧ st'.tlbShootdown = st.tlbShootdown ∧
    st'.perCoreTlb = st.perCoreTlb := by
  cases hres : resolveAsidRoot st asid with
  | none => rw [vspaceUnifyInstructionPage_asid_unbound st vaddr hres] at h; cases h
  | some rr =>
      obtain ⟨rid, root⟩ := rr
      cases hlk : VSpaceRoot.lookup root vaddr with
      | none => rw [vspaceUnifyInstructionPage_unmapped hres hlk] at h; cases h
      | some lk =>
          obtain ⟨p, pm⟩ := lk
          rw [vspaceUnifyInstructionPage_ok hres hlk] at h
          simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h
          subst h
          exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **WS-SM SM7.D**: the unify records the *unify* operand — the runtime emits
the full data-to-instruction sequence, not a bare invalidate, so the caller's
stores are pushed to the Point of Unification before the instruction lines are
dropped.  Recording a mere `ivauPage` here would silently lose the clean, which
is the whole reason the operation exists. -/
theorem vspaceUnifyInstructionPage_records_unify {st st' : SystemState}
    {asid : SeLe4n.ASID} {vaddr : SeLe4n.VAddr} {rid : SeLe4n.ObjId}
    {root : VSpaceRoot} {p : SeLe4n.PAddr} {perms : PagePermissions}
    (hLedger : st.pendingIcacheMaintenance = [])
    (hres : resolveAsidRoot st asid = some (rid, root))
    (hlk : VSpaceRoot.lookup root vaddr = some (p, perms))
    (h : vspaceUnifyInstructionPage asid vaddr st = .ok ((), st')) :
    st'.pendingIcacheMaintenance = [ICacheInvalidation.unifyPage p] := by
  rw [vspaceUnifyInstructionPage_ok hres hlk] at h
  simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h
  subst h
  exact recordIcacheMaintenance_of_nil hLedger _

/-- **WS-SM SM7.D**: after the unify **no core** retains a line for the page —
the domain-wide reach, on the user-facing path.  This is what makes freshly
written code safe to execute on any PE, not just the writer's. -/
theorem vspaceUnifyInstructionPage_invalidates_all_cores {st st' : SystemState}
    {asid : SeLe4n.ASID} {vaddr : SeLe4n.VAddr} {rid : SeLe4n.ObjId}
    {root : VSpaceRoot} {p : SeLe4n.PAddr} {perms : PagePermissions}
    (hres : resolveAsidRoot st asid = some (rid, root))
    (hlk : VSpaceRoot.lookup root vaddr = some (p, perms))
    (h : vspaceUnifyInstructionPage asid vaddr st = .ok ((), st')) :
    ∀ (c : CoreId) (l : ICacheLine), l.paddr = p →
      l ∉ (icacheOnCore st' c).lines := by
  rw [vspaceUnifyInstructionPage_ok hres hlk] at h
  simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h
  subst h
  intro c l hp hmem
  exact icInvalidateBroadcast_reaches_all_cores st icBroadcastReach_cover
    (.unifyPage p) c (icacheLineMatches_unifyPage hp) hmem

/-- **WS-SM SM7.D**: the unify preserves the 14th `proofLayerInvariantBundle`
conjunct — it only removes lines and touches no page table. -/
theorem vspaceUnifyInstructionPage_preserves_icacheCoherent_perCore
    {st st' : SystemState} {asid : SeLe4n.ASID} {vaddr : SeLe4n.VAddr}
    (hCoherent : icacheCoherent_perCore st)
    (h : vspaceUnifyInstructionPage asid vaddr st = .ok ((), st')) :
    icacheCoherent_perCore st' := by
  cases hres : resolveAsidRoot st asid with
  | none => rw [vspaceUnifyInstructionPage_asid_unbound st vaddr hres] at h; cases h
  | some rr =>
      obtain ⟨rid, root⟩ := rr
      cases hlk : VSpaceRoot.lookup root vaddr with
      | none => rw [vspaceUnifyInstructionPage_unmapped hres hlk] at h; cases h
      | some lk =>
          obtain ⟨p, pm⟩ := lk
          rw [vspaceUnifyInstructionPage_ok hres hlk] at h
          simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h
          subst h
          intro c l hl
          exact icacheLineConsistent_of_frame rfl rfl
            (icInvalidateBroadcast_preserves_icacheCoherent_perCore st
              icBroadcastReach (.unifyPage p) hCoherent c l hl)

/-- **WS-SM SM7.D**: the unify preserves the 13th conjunct too — it frames
`perCoreTlb`, the page tables and the shootdown state. -/
theorem vspaceUnifyInstructionPage_preserves_tlbInvalidationConsistent_perCore
    {st st' : SystemState} {asid : SeLe4n.ASID} {vaddr : SeLe4n.VAddr}
    (hConsist : tlbInvalidationConsistent_perCore st)
    (h : vspaceUnifyInstructionPage asid vaddr st = .ok ((), st')) :
    tlbInvalidationConsistent_perCore st' := by
  cases hres : resolveAsidRoot st asid with
  | none => rw [vspaceUnifyInstructionPage_asid_unbound st vaddr hres] at h; cases h
  | some rr =>
      obtain ⟨rid, root⟩ := rr
      cases hlk : VSpaceRoot.lookup root vaddr with
      | none => rw [vspaceUnifyInstructionPage_unmapped hres hlk] at h; cases h
      | some lk =>
          obtain ⟨p, pm⟩ := lk
          rw [vspaceUnifyInstructionPage_ok hres hlk] at h
          simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h
          subst h
          exact fun c e he =>
            tlbEntryOk_of_frame_eq rfl rfl rfl
              (icInvalidateBroadcast_preserves_tlbInvalidationConsistent_perCore
                st icBroadcastReach (.unifyPage p) hConsist c e he)

end SeLe4n.Kernel.Architecture
