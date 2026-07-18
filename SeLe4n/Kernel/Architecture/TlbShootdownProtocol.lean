-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Architecture.VSpace
import SeLe4n.Kernel.Architecture.TlbShootdown
import SeLe4n.Kernel.Architecture.AsidManager
import SeLe4n.Kernel.Concurrency.Sgi

/-!
# WS-SM SM7.B — TLB shootdown protocol transitions

The protocol slice of the TLB/cache shootdown phase
(`docs/planning/SMP_TLB_SHOOTDOWN_PLAN.md` §3.2, §5 SM7.B): the
initiator's local invalidation (SM7.B.1), the cross-core broadcast
round (SM7.B.2), the `.tlbShootdownReq` SGI-handler state transition
(SM7.B.3), the round composition their correctness theorem quantifies
over, and Theorem 3.3.1 (`tlbShootdownBroadcast_invalidatesAllCores`,
SM7.B.8) — together with the caller-facing shootdown-aware kernel
operations that wire the unmap / ASID-retire / flush surfaces through
the round (SM7.B.9 / SM7.B.10).

## Protocol shape (plan §3.2)

A round for invalidation operand `op` initiated by core `c₀`:

  1. `beginShootdownRoundFor c₀ targets` — the SM7.A masked round
     open: every *target* flag drops, everyone else (the initiator,
     and any core outside the target set) is born-acknowledged.
  2. One `enqueueShootdown` per target (the posting fold), then one
     `.tlbShootdownReq` SGI per target — `tlbShootdownBroadcast`
     returns the exact SGI list for the runtime seam to fire.
  3. The initiator's own invalidation — `tlbShootdownLocal` (the
     model of its broadcast-variant TLBI + `dsb`).
  4. Each target's SGI handler — `handleTlbShootdownReqOnCore`:
     drain the whole queue, retire one invalidation per drained
     descriptor, acknowledge.  The pure model applies the drained
     operations to the TLB view at the *acknowledgment* step
     (`tlbShootdownAckOnCore`), so a set ack flag is constructively
     "my view no longer contains the drained operands" — the exact
     reading Theorem 3.3.1's remote case needs.
  5. The initiator's wait loop exits at `allAcked` (termination:
     `TlbShootdownWait.lean`, SM7.B.5).

## Invalidation-effect semantics

`tlbEntryMatches` compares the *FFI-encoded* operand fields
(`UInt16` ASID tag, `UInt64` VA operand) against the encoding of the
entry's own typed fields — exactly the comparison the hardware
performs on the TLBI operand register (ARM ARM C6.2.313: the ASID
comparison uses ASID[15:0]; the VA comparison uses the encoded
VA[55:12] operand).  Encoding both sides makes the caller-side
round trip (`encodePageInvalidation` / `encodeAsidInvalidation`)
unconditionally sound: the entry the caller wants gone always
matches its own encoded descriptor, with no side condition on the
model address width.  Two model-distinct entries whose encodings
collide are *both* removed — over-invalidation, which is always
safe (an absent TLB entry re-walks the page tables; a stale present
one is the SMP-C4 hazard).

## Per-core views (Theorem 3.3.1) before SM7.C

`SystemState.tlb` is a single (boot-core) view until SM7.C mounts
the per-core `Vector TlbState numCores`.  Theorem 3.3.1 is therefore
proven at the protocol level over an explicit per-core view vector
(`shootdownRoundViews`) whose per-target step is *proven equal* to
the real handler transition's TLB effect on the real state
(`handleTlbShootdownReqOnCore_applies_posted_op` — the non-vacuity
bridge), plus the end-to-end single-view corollary over the real
`shootdownRound` pipeline (`shootdownRound_tlb_no_matching_entry`).
SM7.C.6 instantiates the vector form per-core mechanically.

## Round serialisation (SM7.A audit contract)

Every theorem here about a *round* (quiescence restoration, exact
posting, exact drain) assumes the SM7.A round-serialisation
contract: rounds are serialised system-wide under the single global
`ShootdownRoundLockId` (SM7.B.7, `TlbShootdownLockSet.lean`).  The
caller-facing wrappers below post through the *total* coalescing
enqueue (`enqueueShootdownOrCoalesce`) so that queue accumulation
between a pure posting commit and the runtime round's exhaustive
drain can never fail a syscall: at the capacity bound the queue
collapses to a single full flush (over-invalidation, always safe;
`enqueueShootdownOrCoalesce_pending_covered`).
-/

namespace SeLe4n.Kernel.Architecture

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- SM7.B — Invalidation-effect semantics on a TLB view
-- ============================================================================

/-- **WS-SM SM7.B**: does invalidation operand `op` cover TLB entry `e`?

The comparison is performed on the *FFI-encoded* operand fields —
`UInt16` ASID tag, `UInt64` VA operand — against the encoding of the
entry's own typed fields, exactly as the hardware compares the TLBI
operand register against a TLB entry's tag (ARM ARM C6.2.311–316).
`.vmalle1` covers everything; `.aside1` covers by ASID tag;
`.vae1` / `.vale1` cover by (ASID, VA) tag pair.  (`.vale1` is
last-level-only at the page-walk level; at this view granularity —
one entry per cached translation — its coverage equals `.vae1`.)

Encoding collisions (two model-distinct entries with equal encodings)
make `op` cover both — over-invalidation, always safe. -/
def tlbEntryMatches (op : TlbInvalidation) (e : TlbEntry) : Bool :=
  match op with
  | .vmalle1 => true
  | .vae1 a v =>
      a == UInt16.ofNat e.asid.toNat && v == UInt64.ofNat e.vaddr.toNat
  | .aside1 a => a == UInt16.ofNat e.asid.toNat
  | .vale1 a v =>
      a == UInt16.ofNat e.asid.toNat && v == UInt64.ofNat e.vaddr.toNat

/-- **WS-SM SM7.B**: the effect of retiring one TLB invalidation on a
TLB view — every covered entry is removed, nothing is added.  This is
the per-descriptor step the `.tlbShootdownReq` handler retires
(plan §3.2 step 4b) and the initiator's local step 3. -/
def applyTlbInvalidation (tlb : TlbState) (op : TlbInvalidation) : TlbState :=
  { entries := tlb.entries.filter (fun e => !tlbEntryMatches op e) }

/-- **WS-SM SM7.B**: membership after one invalidation — an entry
survives iff it was present and the operand does not cover it. -/
theorem mem_applyTlbInvalidation_iff (tlb : TlbState) (op : TlbInvalidation)
    (e : TlbEntry) :
    e ∈ (applyTlbInvalidation tlb op).entries ↔
      e ∈ tlb.entries ∧ tlbEntryMatches op e = false := by
  simp [applyTlbInvalidation, List.mem_filter]

/-- **WS-SM SM7.B**: a covered entry is gone after the invalidation —
the per-step removal half of Theorem 3.3.1. -/
theorem applyTlbInvalidation_removes {op : TlbInvalidation} {e : TlbEntry}
    (h : tlbEntryMatches op e = true) (tlb : TlbState) :
    e ∉ (applyTlbInvalidation tlb op).entries := by
  rw [mem_applyTlbInvalidation_iff]
  intro ⟨_, hFalse⟩
  rw [h] at hFalse
  cases hFalse

/-- **WS-SM SM7.B**: an uncovered entry is untouched — the
selectivity half (only the requested operand is invalidated). -/
theorem applyTlbInvalidation_preserves_other {op : TlbInvalidation}
    {e : TlbEntry} (h : tlbEntryMatches op e = false) (tlb : TlbState) :
    e ∈ (applyTlbInvalidation tlb op).entries ↔ e ∈ tlb.entries := by
  rw [mem_applyTlbInvalidation_iff]
  simp [h]

/-- **WS-SM SM7.B**: invalidation never adds entries — the
monotonicity that lets round-composition proofs chain removals. -/
theorem mem_of_mem_applyTlbInvalidation {tlb : TlbState}
    {op : TlbInvalidation} {e : TlbEntry}
    (h : e ∈ (applyTlbInvalidation tlb op).entries) : e ∈ tlb.entries :=
  ((mem_applyTlbInvalidation_iff tlb op e).mp h).1

/-- **WS-SM SM7.B**: retiring the same operand twice equals retiring
it once — the idempotence that makes a duplicate `.tlbShootdownReq`
SGI (and the per-core-views closed form) harmless. -/
theorem applyTlbInvalidation_idempotent (tlb : TlbState)
    (op : TlbInvalidation) :
    applyTlbInvalidation (applyTlbInvalidation tlb op) op =
      applyTlbInvalidation tlb op := by
  simp [applyTlbInvalidation, List.filter_filter]

/-- **WS-SM SM7.B**: a full flush (`.vmalle1`) empties the view —
the coalescing escape hatch's semantic supersession witness: after a
`.vmalle1` retires, *no* entry (in particular none a dropped
descriptor would have removed) survives. -/
theorem applyTlbInvalidation_vmalle1 (tlb : TlbState) :
    (applyTlbInvalidation tlb .vmalle1).entries = [] := by
  simp [applyTlbInvalidation, tlbEntryMatches]

/-- **WS-SM SM7.B**: retiring a whole drained queue, FIFO order —
the handler's step 4b fold. -/
def applyTlbInvalidations (tlb : TlbState) (ops : List TlbInvalidation) :
    TlbState :=
  ops.foldl applyTlbInvalidation tlb

@[simp] theorem applyTlbInvalidations_nil (tlb : TlbState) :
    applyTlbInvalidations tlb [] = tlb := rfl

theorem applyTlbInvalidations_cons (tlb : TlbState) (op : TlbInvalidation)
    (ops : List TlbInvalidation) :
    applyTlbInvalidations tlb (op :: ops) =
      applyTlbInvalidations (applyTlbInvalidation tlb op) ops := rfl

/-- **WS-SM SM7.B**: the fold never adds entries. -/
theorem mem_of_mem_applyTlbInvalidations {ops : List TlbInvalidation} :
    ∀ {tlb : TlbState} {e : TlbEntry},
      e ∈ (applyTlbInvalidations tlb ops).entries → e ∈ tlb.entries := by
  induction ops with
  | nil => intro tlb e h; exact h
  | cons op ops ih =>
    intro tlb e h
    exact mem_of_mem_applyTlbInvalidation
      (ih (tlb := applyTlbInvalidation tlb op) h)

/-- **WS-SM SM7.B**: a full flush empties the view. -/
theorem applyTlbInvalidation_vmalle1_entries_nil (t : TlbState) :
    applyTlbInvalidation t TlbInvalidation.vmalle1 = { entries := [] } := by
  unfold applyTlbInvalidation
  congr 1
  exact List.filter_eq_nil_iff.mpr (fun e _ h => nomatch h)

/-- **WS-SM SM7.B**: retiring anything on an empty view stays empty. -/
theorem applyTlbInvalidations_entries_nil (ops : List TlbInvalidation) :
    applyTlbInvalidations { entries := [] } ops = { entries := [] } := by
  induction ops with
  | nil => rfl
  | cons o os ih =>
    rw [applyTlbInvalidations_cons]
    exact ih

/-- **WS-SM SM7.B**: an operand list containing a full flush empties
the view no matter what else it carries. -/
theorem applyTlbInvalidations_of_mem_vmalle1 {ops : List TlbInvalidation}
    (h : TlbInvalidation.vmalle1 ∈ ops) :
    ∀ t : TlbState, applyTlbInvalidations t ops = { entries := [] } := by
  induction ops with
  | nil => cases h
  | cons o os ih =>
    intro t
    rcases List.mem_cons.mp h with hEq | hMem
    · rw [applyTlbInvalidations_cons, ← hEq,
          applyTlbInvalidation_vmalle1_entries_nil]
      exact applyTlbInvalidations_entries_nil os
    · rw [applyTlbInvalidations_cons]
      exact ih hMem _

/-- **WS-SM SM7.B**: the initiator-side operand collapse — a posted-ops
list containing a full flush executes as the single full flush (the
runtime's step-3 TLBI loop need not issue operands a `vmalle1` already
covers). -/
def collapseShootdownOps (ops : List TlbInvalidation) : List TlbInvalidation :=
  if ops.any (fun op => match op with
      | TlbInvalidation.vmalle1 => true
      | _ => false) then
    [TlbInvalidation.vmalle1]
  else ops

/-- **WS-SM SM7.B**: the collapse is effect-exact — executing the
collapsed list computes the *same* TLB view as executing the full
list, for every starting view.  (With a `vmalle1` present both sides
are the empty view; without one the lists are identical.) -/
theorem collapseShootdownOps_effect_eq (ops : List TlbInvalidation)
    (t : TlbState) :
    applyTlbInvalidations t (collapseShootdownOps ops) =
      applyTlbInvalidations t ops := by
  unfold collapseShootdownOps
  split
  · next hAny =>
      obtain ⟨op, hmem, hop⟩ := List.any_eq_true.mp hAny
      have hvm : TlbInvalidation.vmalle1 ∈ ops := by
        cases op <;> simp_all
      rw [applyTlbInvalidations_of_mem_vmalle1 hvm t,
          applyTlbInvalidations_of_mem_vmalle1 (List.mem_singleton.mpr rfl) t]
  · rfl

/-- **WS-SM SM7.B**: a collapse-free list is returned unchanged. -/
theorem collapseShootdownOps_no_vmalle1 {ops : List TlbInvalidation}
    (h : TlbInvalidation.vmalle1 ∉ ops) :
    collapseShootdownOps ops = ops := by
  unfold collapseShootdownOps
  rw [if_neg]
  intro hAny
  obtain ⟨op, hmem, hop⟩ := List.any_eq_true.mp hAny
  cases op <;> simp_all

/-- **WS-SM SM7.B**: retiring a queue containing `op` removes every
entry `op` covers — the drained-descriptor completeness half of
Theorem 3.3.1's remote case (`drainShootdowns_fst` supplies "every
posted descriptor is drained"; this supplies "every drained
descriptor's coverage is gone"). -/
theorem applyTlbInvalidations_removes {ops : List TlbInvalidation}
    {op : TlbInvalidation} (hop : op ∈ ops) {e : TlbEntry}
    (he : tlbEntryMatches op e = true) :
    ∀ tlb : TlbState, e ∉ (applyTlbInvalidations tlb ops).entries := by
  induction ops with
  | nil => cases hop
  | cons o os ih =>
    intro tlb
    rcases List.mem_cons.mp hop with hEq | hMem
    · subst hEq
      rw [applyTlbInvalidations_cons]
      intro hmem
      exact applyTlbInvalidation_removes he tlb
        (mem_of_mem_applyTlbInvalidations hmem)
    · rw [applyTlbInvalidations_cons]
      exact ih hMem _

-- ============================================================================
-- SM7.B — Caller-side operand encoders (typed kernel state → FFI operand)
-- ============================================================================

/-- **WS-SM SM7.B.9**: the shootdown operand for a page unmap/remap at
`(asid, vaddr)` — a `.vae1` (all-levels, by VA + ASID) invalidation
carrying the FFI-encoded fields.  Matching is performed on encodings
(`tlbEntryMatches`), so the encoded operand covers the caller's own
`(asid, vaddr)` entry unconditionally
(`encodePageInvalidation_matches`). -/
def encodePageInvalidation (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) :
    TlbInvalidation :=
  .vae1 (UInt16.ofNat asid.toNat) (UInt64.ofNat vaddr.toNat)

/-- **WS-SM SM7.B.10**: the shootdown operand for an ASID retirement —
a `.aside1` (full-ASID) invalidation. -/
def encodeAsidInvalidation (asid : SeLe4n.ASID) : TlbInvalidation :=
  .aside1 (UInt16.ofNat asid.toNat)

/-- **WS-SM SM7.B.9**: the encoded page operand covers every entry at
the caller's `(asid, vaddr)` — no side condition: both sides of the
comparison are the same encoding. -/
theorem encodePageInvalidation_matches (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr) {e : TlbEntry}
    (hAsid : e.asid = asid) (hVaddr : e.vaddr = vaddr) :
    tlbEntryMatches (encodePageInvalidation asid vaddr) e = true := by
  subst hAsid; subst hVaddr
  simp [tlbEntryMatches, encodePageInvalidation]

/-- **WS-SM SM7.B.10**: the encoded ASID operand covers every entry of
the caller's `asid`. -/
theorem encodeAsidInvalidation_matches (asid : SeLe4n.ASID) {e : TlbEntry}
    (hAsid : e.asid = asid) :
    tlbEntryMatches (encodeAsidInvalidation asid) e = true := by
  subst hAsid
  simp [tlbEntryMatches, encodeAsidInvalidation]

/-- **WS-SM SM7.B** (typed-flush bridge, page form): the encoded
invalidation is at least as strong as the typed local flush — every
entry surviving `applyTlbInvalidation (encodePageInvalidation a v)`
also survives `adapterFlushTlbByVAddr t a v`.  Encoding collisions
only ever *widen* the removal (over-invalidation), never narrow it,
so composing the wrappers' typed local flush with the remote encoded
retirement can never leave a remote view strictly staler than the
local one for the flushed translation. -/
theorem mem_adapterFlushTlbByVAddr_of_mem_applyTlbInvalidation_encodePage
    (t : TlbState) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) {e : TlbEntry}
    (h : e ∈ (applyTlbInvalidation t
      (encodePageInvalidation asid vaddr)).entries) :
    e ∈ (adapterFlushTlbByVAddr t asid vaddr).entries := by
  obtain ⟨hmem, hnomatch⟩ := (mem_applyTlbInvalidation_iff t _ e).mp h
  unfold adapterFlushTlbByVAddr
  refine List.mem_filter.mpr ⟨hmem, ?_⟩
  cases htyped : (e.asid == asid && e.vaddr == vaddr) with
  | false => rfl
  | true =>
      rw [Bool.and_eq_true] at htyped
      have hA : e.asid = asid := eq_of_beq htyped.1
      have hV : e.vaddr = vaddr := eq_of_beq htyped.2
      rw [encodePageInvalidation_matches asid vaddr hA hV] at hnomatch
      cases hnomatch

/-- **WS-SM SM7.B.10** (typed-flush bridge, ASID form): the encoded
ASID invalidation is at least as strong as the typed per-ASID flush. -/
theorem mem_adapterFlushTlbByAsid_of_mem_applyTlbInvalidation_encodeAsid
    (t : TlbState) (asid : SeLe4n.ASID) {e : TlbEntry}
    (h : e ∈ (applyTlbInvalidation t
      (encodeAsidInvalidation asid)).entries) :
    e ∈ (adapterFlushTlbByAsid t asid).entries := by
  obtain ⟨hmem, hnomatch⟩ := (mem_applyTlbInvalidation_iff t _ e).mp h
  unfold adapterFlushTlbByAsid
  refine List.mem_filter.mpr ⟨hmem, ?_⟩
  cases htyped : (e.asid == asid) with
  | false => simp [bne, htyped]
  | true =>
      have hA : e.asid = asid := eq_of_beq htyped
      rw [encodeAsidInvalidation_matches asid hA] at hnomatch
      cases hnomatch

-- ============================================================================
-- SM7.B.2 — Target-set computation
-- ============================================================================

/-- **WS-SM SM7.B.2**: the broadcast target set — every core except the
initiator (plan §3.2 step 2, `allCores \ {c₀}`).

This is the *model-complete* target set: the pure round discharges the
invalidation obligation of every non-initiator core, so Theorem 3.3.1
quantifies over all of `allCores`.  The *runtime* seam masks delivery
to online cores only (the SM7.A PR #838 P1 obligation): the Rust
`reset_for_round` leaves offline cores born-acknowledged and the entry
fires SGIs only at online targets — safe because every secondary
bring-up runs `tlbi vmalle1` before enabling its MMU, so a core that
was offline during a round onlines with an empty TLB. -/
def shootdownTargets (initiator : CoreId) : List CoreId :=
  allCores.filter (fun c => c != initiator)

/-- **WS-SM SM7.B.2**: membership — exactly the non-initiator cores. -/
theorem mem_shootdownTargets_iff (initiator c : CoreId) :
    c ∈ shootdownTargets initiator ↔ c ≠ initiator := by
  simp [shootdownTargets, List.mem_filter, allCores]

/-- **WS-SM SM7.B.2**: the initiator never targets itself. -/
theorem initiator_not_mem_shootdownTargets (initiator : CoreId) :
    initiator ∉ shootdownTargets initiator := by
  rw [mem_shootdownTargets_iff]
  exact fun h => h rfl

/-- **WS-SM SM7.B.2**: the target set covers every non-initiator core —
the coverage hypothesis of the SM7.A round capstone and of
Theorem 3.3.1. -/
theorem shootdownTargets_cover (initiator : CoreId) :
    ∀ c : CoreId, c ≠ initiator → c ∈ shootdownTargets initiator :=
  fun c hc => (mem_shootdownTargets_iff initiator c).mpr hc

/-- **WS-SM SM7.B.2**: no duplicate targets — one descriptor and one
SGI per remote core. -/
theorem shootdownTargets_nodup (initiator : CoreId) :
    (shootdownTargets initiator).Nodup :=
  allCores_nodup.filter _

-- ============================================================================
-- SM7.B.1 — tlbShootdownLocal (the initiator's local invalidation, step 3)
-- ============================================================================

/-- **WS-SM SM7.B.1**: the initiator's local invalidation — the model
of its broadcast-variant TLBI + `dsb` + `isb` (plan §3.2 step 3),
applied to the mounted (boot-core) TLB view.

Until SM7.C splits `SystemState.tlb` into per-core views this is the
single view's transition; removal is always sound for any executing
core because the runtime instruction is the *broadcast* (IS/OS)
variant, which reaches the boot core's TLB from any PE in the sharing
domain (ARM ARM C6.2.311). -/
def tlbShootdownLocal (st : SystemState) (op : TlbInvalidation) :
    SystemState :=
  { st with tlb := applyTlbInvalidation st.tlb op }

/-- **WS-SM SM7.B.1**: the local step touches only the TLB view. -/
theorem tlbShootdownLocal_frame (st : SystemState) (op : TlbInvalidation) :
    (tlbShootdownLocal st op).objects = st.objects ∧
    (tlbShootdownLocal st op).scheduler = st.scheduler ∧
    (tlbShootdownLocal st op).machine = st.machine ∧
    (tlbShootdownLocal st op).tlbShootdown = st.tlbShootdown :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **WS-SM SM7.B.1**: the local step removes every covered entry —
Theorem 3.3.1's initiator case at the single-view granularity. -/
theorem tlbShootdownLocal_removes {op : TlbInvalidation} {e : TlbEntry}
    (h : tlbEntryMatches op e = true) (st : SystemState) :
    e ∉ (tlbShootdownLocal st op).tlb.entries :=
  applyTlbInvalidation_removes h st.tlb

-- ============================================================================
-- SM7.B.2 — tlbShootdownBroadcast (round open + posting + SGI emission)
-- ============================================================================

/-- **WS-SM SM7.B.2**: open a shootdown round and post one descriptor
per target (plan §3.2 steps 1–2), returning the exact
`.tlbShootdownReq` SGI list for the runtime seam to fire.

Fail-closed: `none` iff the posting fold hits a full queue — under
the round-serialisation contract this is unreachable from a quiescent
state (`tlbShootdownBroadcast_isSome_of_quiescent`); an unexpected
`none` is a protocol-invariant violation the caller must surface, not
swallow.  The caller-facing syscall wrappers post through the *total*
coalescing variant `tlbShootdownBroadcastCoalescing` instead, which
converts overflow into a full-flush collapse rather than an error.

The round open is the SM7.A masked form (`beginShootdownRoundFor`):
only the targets are waited on; non-targets (offline cores at the
runtime seam) are born-acknowledged. -/
def tlbShootdownBroadcast (st : SystemState) (initiator : CoreId)
    (targets : List CoreId) (op : TlbInvalidation) :
    Option (SystemState × List (CoreId × SgiKind)) :=
  match targets.foldlM
      (fun s c => enqueueShootdown s c { op := op, initiator := initiator })
      (beginShootdownRoundFor st.tlbShootdown initiator targets) with
  | none => none
  | some posted =>
      some ({ st with tlbShootdown := posted },
        targets.map (fun c => (c, SgiKind.tlbShootdownReq)))

/-- **WS-SM SM7.B.2**: from a quiescent shootdown state the broadcast
always succeeds — the plan §4.1 capacity-sufficiency argument at the
protocol level (lifts `beginRoundFor_foldlM_enqueueShootdown_isSome`). -/
theorem tlbShootdownBroadcast_isSome_of_quiescent {st : SystemState}
    (hq : shootdownQuiescent st.tlbShootdown) (initiator : CoreId)
    {targets : List CoreId} (hnd : targets.Nodup) (op : TlbInvalidation) :
    (tlbShootdownBroadcast st initiator targets op).isSome := by
  unfold tlbShootdownBroadcast
  have h := beginRoundFor_foldlM_enqueueShootdown_isSome hq initiator hnd
    { op := op, initiator := initiator }
  obtain ⟨posted, hposted⟩ := Option.isSome_iff_exists.mp h
  simp only [hposted]
  rfl

/-- **WS-SM SM7.B.2**: a successful broadcast emits exactly one
`.tlbShootdownReq` SGI per target, in target order — the runtime seam
fires precisely this list (plan §3.2 step 2's `sendSgi` loop). -/
theorem tlbShootdownBroadcast_sgis {st st' : SystemState}
    {initiator : CoreId} {targets : List CoreId} {op : TlbInvalidation}
    {sgis : List (CoreId × SgiKind)}
    (h : tlbShootdownBroadcast st initiator targets op = some (st', sgis)) :
    sgis = targets.map (fun c => (c, SgiKind.tlbShootdownReq)) := by
  unfold tlbShootdownBroadcast at h
  cases hfold : targets.foldlM
      (fun s c => enqueueShootdown s c { op := op, initiator := initiator })
      (beginShootdownRoundFor st.tlbShootdown initiator targets) with
  | none => rw [hfold] at h; cases h
  | some posted =>
      rw [hfold] at h
      injection h with h
      rw [Prod.mk.injEq] at h
      obtain ⟨hst, hsgi⟩ := h
      exact hsgi.symm

/-- **WS-SM SM7.B.2**: every emitted SGI is a `.tlbShootdownReq` —
the broadcast never emits a reschedule or any other kind. -/
theorem tlbShootdownBroadcast_sgis_kind {st st' : SystemState}
    {initiator : CoreId} {targets : List CoreId} {op : TlbInvalidation}
    {sgis : List (CoreId × SgiKind)}
    (h : tlbShootdownBroadcast st initiator targets op = some (st', sgis)) :
    ∀ p ∈ sgis, p.2 = SgiKind.tlbShootdownReq := by
  rw [tlbShootdownBroadcast_sgis h]
  intro p hp
  obtain ⟨c, _, hpc⟩ := List.mem_map.mp hp
  rw [← hpc]

/-- **WS-SM SM7.B.2**: the broadcast touches only the shootdown state —
objects, scheduler, machine, and the TLB view are all framed (the
initiator's own invalidation is the separate `tlbShootdownLocal`
step, plan §3.2 step 3). -/
theorem tlbShootdownBroadcast_frame {st st' : SystemState}
    {initiator : CoreId} {targets : List CoreId} {op : TlbInvalidation}
    {sgis : List (CoreId × SgiKind)}
    (h : tlbShootdownBroadcast st initiator targets op = some (st', sgis)) :
    st'.objects = st.objects ∧ st'.scheduler = st.scheduler ∧
    st'.machine = st.machine ∧ st'.tlb = st.tlb := by
  unfold tlbShootdownBroadcast at h
  cases hfold : targets.foldlM
      (fun s c => enqueueShootdown s c { op := op, initiator := initiator })
      (beginShootdownRoundFor st.tlbShootdown initiator targets) with
  | none => rw [hfold] at h; cases h
  | some posted =>
      rw [hfold] at h
      injection h with h
      rw [Prod.mk.injEq] at h
      obtain ⟨hst, hsgi⟩ := h
      subst hst
      exact ⟨rfl, rfl, rfl, rfl⟩

/-- **WS-SM SM7.B.2** (fold lemma): with duplicate-free targets, the
posting fold appends exactly one descriptor to each visited core's
queue — every other visit frames it. -/
theorem foldlM_enqueueShootdown_pending_visited {targets : List CoreId} :
    ∀ {sd posted : TlbShootdownState} {d : TlbShootdownDescriptor},
      targets.Nodup →
      targets.foldlM (fun s c => enqueueShootdown s c d) sd = some posted →
      ∀ c ∈ targets, posted.pendingOnCore c = sd.pendingOnCore c ++ [d] := by
  induction targets with
  | nil => intro sd posted d _ _ c hc; cases hc
  | cons t ts ih =>
    intro sd posted d hnd hfold c hc
    rw [List.foldlM_cons] at hfold
    cases henq : enqueueShootdown sd t d with
    | none => rw [henq] at hfold; simp at hfold
    | some sd' =>
      rw [henq] at hfold
      rcases List.mem_cons.mp hc with hEq | hMem
      · subst hEq
        have hframe := foldlM_enqueueShootdown_frame_pending hfold
          (c := c) (List.nodup_cons.mp hnd).1
        rw [hframe, enqueueShootdown_pending_target henq]
      · rw [ih (List.nodup_cons.mp hnd).2 hfold c hMem,
            enqueueShootdown_frame_pending henq
              (fun hEq => (List.nodup_cons.mp hnd).1 (hEq ▸ hMem))]

/-- **WS-SM SM7.B.2**: from a quiescent state, a successful broadcast
leaves exactly the round's descriptor pending on each target — the
posting-exactness half of the round-trip Theorem 3.3.1 composes with
`drainShootdowns_fst`. -/
theorem tlbShootdownBroadcast_posts_singleton {st st' : SystemState}
    {initiator : CoreId} {targets : List CoreId} {op : TlbInvalidation}
    {sgis : List (CoreId × SgiKind)}
    (hq : shootdownQuiescent st.tlbShootdown) (hnd : targets.Nodup)
    (h : tlbShootdownBroadcast st initiator targets op = some (st', sgis)) :
    ∀ c ∈ targets, st'.tlbShootdown.pendingOnCore c =
      [{ op := op, initiator := initiator }] := by
  unfold tlbShootdownBroadcast at h
  cases hfold : targets.foldlM
      (fun s c => enqueueShootdown s c { op := op, initiator := initiator })
      (beginShootdownRoundFor st.tlbShootdown initiator targets) with
  | none => rw [hfold] at h; cases h
  | some posted =>
      rw [hfold] at h
      injection h with h
      rw [Prod.mk.injEq] at h
      obtain ⟨hst, hsgi⟩ := h
      subst hst
      intro c hc
      have hpost := foldlM_enqueueShootdown_pending_visited hnd hfold c hc
      have hempty : (beginShootdownRoundFor st.tlbShootdown initiator
          targets).pendingOnCore c = [] := by
        rw [beginShootdownRoundFor_frame_pending]
        exact hq.1 c
      show posted.pendingOnCore c = _
      rw [hpost, hempty]
      rfl

/-- **WS-SM SM7.B.2**: after a successful broadcast a core is
acknowledged iff it is the initiator or outside the target set — the
initiator genuinely waits on every target, and only on targets. -/
theorem tlbShootdownBroadcast_ack_iff {st st' : SystemState}
    {initiator : CoreId} {targets : List CoreId} {op : TlbInvalidation}
    {sgis : List (CoreId × SgiKind)}
    (h : tlbShootdownBroadcast st initiator targets op = some (st', sgis))
    (c : CoreId) :
    st'.tlbShootdown.ackOnCore c = true ↔ (c = initiator ∨ c ∉ targets) := by
  unfold tlbShootdownBroadcast at h
  cases hfold : targets.foldlM
      (fun s c => enqueueShootdown s c { op := op, initiator := initiator })
      (beginShootdownRoundFor st.tlbShootdown initiator targets) with
  | none => rw [hfold] at h; cases h
  | some posted =>
      rw [hfold] at h
      injection h with h
      rw [Prod.mk.injEq] at h
      obtain ⟨hst, hsgi⟩ := h
      subst hst
      show posted.ackOnCore c = true ↔ _
      rw [foldlM_enqueueShootdown_frame_ack hfold c]
      exact beginShootdownRoundFor_ackOnCore_iff st.tlbShootdown initiator
        targets c

/-- **WS-SM SM7.B.2** (fold lemma): the posting fold preserves the
SM7.A capacity invariant. -/
theorem foldlM_enqueueShootdown_preserves_pendingBounded
    {targets : List CoreId} :
    ∀ {sd posted : TlbShootdownState} {d : TlbShootdownDescriptor},
      pendingBounded sd →
      targets.foldlM (fun s c => enqueueShootdown s c d) sd = some posted →
      pendingBounded posted := by
  induction targets with
  | nil =>
    intro sd posted d hB hfold
    injection hfold with hfold
    exact hfold ▸ hB
  | cons t ts ih =>
    intro sd posted d hB hfold
    rw [List.foldlM_cons] at hfold
    cases henq : enqueueShootdown sd t d with
    | none => rw [henq] at hfold; simp at hfold
    | some sd' =>
      rw [henq] at hfold
      exact ih (enqueueShootdown_preserves_pendingBounded hB henq) hfold

/-- **WS-SM SM7.B.2**: a successful broadcast preserves the capacity
invariant. -/
theorem tlbShootdownBroadcast_preserves_pendingBounded {st st' : SystemState}
    {initiator : CoreId} {targets : List CoreId} {op : TlbInvalidation}
    {sgis : List (CoreId × SgiKind)}
    (hB : pendingBounded st.tlbShootdown)
    (h : tlbShootdownBroadcast st initiator targets op = some (st', sgis)) :
    pendingBounded st'.tlbShootdown := by
  unfold tlbShootdownBroadcast at h
  cases hfold : targets.foldlM
      (fun s c => enqueueShootdown s c { op := op, initiator := initiator })
      (beginShootdownRoundFor st.tlbShootdown initiator targets) with
  | none => rw [hfold] at h; cases h
  | some posted =>
      rw [hfold] at h
      injection h with h
      rw [Prod.mk.injEq] at h
      obtain ⟨hst, hsgi⟩ := h
      subst hst
      exact foldlM_enqueueShootdown_preserves_pendingBounded
        (beginShootdownRoundFor_preserves_pendingBounded hB initiator targets)
        hfold

-- ============================================================================
-- SM7.B.3 — The .tlbShootdownReq handler's state transition
-- ============================================================================

/-- **WS-SM SM7.B.3**: the drain half of the `.tlbShootdownReq` handler
(plan §3.2 step 4a) — core `c`'s queue is emptied and returned for the
runtime to retire.  Deliberately does **not** touch the ack flag or the
TLB view: the runtime executes the hardware TLBIs *between* this
commit and the acknowledgment commit (the SM7.A drain/ack seam). -/
def tlbShootdownDrainOnCore (st : SystemState) (c : CoreId) :
    SystemState × List TlbShootdownDescriptor :=
  let (drained, sd') := drainShootdowns st.tlbShootdown c
  ({ st with tlbShootdown := sd' }, drained)

/-- **WS-SM SM7.B.3**: the acknowledgment half (plan §3.2 steps 4b+4c)
— the retired invalidations are applied to the TLB view *at the
acknowledgment*, so a set ack flag constructively means "my view no
longer contains the retired operands".  This is the model reading the
SM7.B.4 release-acquire pairing certifies against the hardware: the
Rust handler release-stores the flag only after its TLBIs have
`dsb`-completed. -/
def tlbShootdownAckOnCore (st : SystemState) (c : CoreId)
    (retired : List TlbShootdownDescriptor) : SystemState :=
  { st with
      tlb := applyTlbInvalidations st.tlb (retired.map (·.op)),
      tlbShootdown := acknowledgeShootdown st.tlbShootdown c }

/-- **WS-SM SM7.B.3**: the complete `.tlbShootdownReq` handler state
transition — drain, retire the drained operations, acknowledge.  The
runtime realises the same composition in two commits with the hardware
TLBIs between them; the composed form exists for round-level
reasoning, exactly like the SM7.A `completeShootdownOnCore` it
projects onto. -/
def handleTlbShootdownReqOnCore (st : SystemState) (c : CoreId) :
    SystemState :=
  let (st', drained) := tlbShootdownDrainOnCore st c
  tlbShootdownAckOnCore st' c drained

/-- **WS-SM SM7.B.3**: the handler's shootdown-state projection is
exactly the SM7.A round step — the SM7.A round capstones
(`shootdownRoundFor_restores_quiescent`) transport to the protocol
handler through this equation. -/
theorem handleTlbShootdownReqOnCore_tlbShootdown_eq (st : SystemState)
    (c : CoreId) :
    (handleTlbShootdownReqOnCore st c).tlbShootdown =
      completeShootdownOnCore st.tlbShootdown c := rfl

/-- **WS-SM SM7.B.3**: the handler's TLB effect is exactly the retire
fold over the drained queue. -/
theorem handleTlbShootdownReqOnCore_tlb_eq (st : SystemState) (c : CoreId) :
    (handleTlbShootdownReqOnCore st c).tlb =
      applyTlbInvalidations st.tlb
        ((drainShootdowns st.tlbShootdown c).1.map (·.op)) := rfl

/-- **WS-SM SM7.B.3**: the handler touches only the TLB view and the
shootdown state. -/
theorem handleTlbShootdownReqOnCore_frame (st : SystemState) (c : CoreId) :
    (handleTlbShootdownReqOnCore st c).objects = st.objects ∧
    (handleTlbShootdownReqOnCore st c).scheduler = st.scheduler ∧
    (handleTlbShootdownReqOnCore st c).machine = st.machine :=
  ⟨rfl, rfl, rfl⟩

/-- **WS-SM SM7.B.3** (non-vacuity bridge for Theorem 3.3.1): on a
state where core `c`'s queue holds exactly the round's descriptor —
what `tlbShootdownBroadcast_posts_singleton` establishes — the
handler's TLB effect is exactly one application of the round's
operand.  This equation is what ties the per-core view vector's step
function (`shootdownRoundViews`) to the real handler transition. -/
theorem handleTlbShootdownReqOnCore_applies_posted_op {st : SystemState}
    {c : CoreId} {op : TlbInvalidation} {initiator : CoreId}
    (hpend : st.tlbShootdown.pendingOnCore c =
      [{ op := op, initiator := initiator }]) :
    (handleTlbShootdownReqOnCore st c).tlb =
      applyTlbInvalidation st.tlb op := by
  rw [handleTlbShootdownReqOnCore_tlb_eq, drainShootdowns_fst, hpend]
  rfl

/-- **WS-SM SM7.B.3**: a duplicate `.tlbShootdownReq` SGI is harmless —
the handler is idempotent: the second run drains an empty queue
(retiring nothing) and re-sets an already-set flag. -/
theorem handleTlbShootdownReqOnCore_idempotent (st : SystemState)
    (c : CoreId) :
    handleTlbShootdownReqOnCore (handleTlbShootdownReqOnCore st c) c =
      handleTlbShootdownReqOnCore st c := by
  -- The general absorbing form: the handler is the identity on any
  -- state whose queue at `c` is already empty and flag already set —
  -- which is exactly what a first handler run leaves behind.
  have key : ∀ st₁ : SystemState,
      st₁.tlbShootdown.pendingOnCore c = [] →
      st₁.tlbShootdown.ackOnCore c = true →
      handleTlbShootdownReqOnCore st₁ c = st₁ := by
    intro st₁ hpend hack
    have hdrain : (drainShootdowns st₁.tlbShootdown c).1 = [] := by
      rw [drainShootdowns_fst]
      exact hpend
    have hsd : acknowledgeShootdown (drainShootdowns st₁.tlbShootdown c).2 c =
        st₁.tlbShootdown := by
      apply TlbShootdownState.ext_perCore
      · intro c'
        rw [acknowledgeShootdown_frame_pending]
        by_cases hc : c' = c
        · subst hc
          rw [drainShootdowns_pending_self]
          exact hpend.symm
        · rw [drainShootdowns_frame_pending _ hc]
      · intro c'
        by_cases hc : c' = c
        · subst hc
          rw [acknowledgeShootdown_ackOnCore_self]
          exact hack.symm
        · rw [acknowledgeShootdown_ackOnCore_ne _ hc,
              drainShootdowns_frame_ack]
    have hstep : handleTlbShootdownReqOnCore st₁ c =
        { st₁ with
            tlb := applyTlbInvalidations st₁.tlb
              ((drainShootdowns st₁.tlbShootdown c).1.map (·.op)),
            tlbShootdown := acknowledgeShootdown
              (drainShootdowns st₁.tlbShootdown c).2 c } := rfl
    rw [hstep, hdrain, hsd]
    rfl
  apply key
  · rw [handleTlbShootdownReqOnCore_tlbShootdown_eq]
    simp
  · rw [handleTlbShootdownReqOnCore_tlbShootdown_eq]
    simp


-- ============================================================================
-- SM7.B — Round composition (the pipeline Theorem 3.3.1 quantifies over)
-- ============================================================================

/-- **WS-SM SM7.B**: one complete shootdown round on the system state —
broadcast (steps 1–2), the initiator's local invalidation (step 3),
then every target's handler (step 4).  The sequential composition is
sound because the round-serialisation contract (`ShootdownRoundLockId`)
admits no interleaving with another round, and the SM7.B.4
release-acquire pairing orders each handler's effect before the
initiator's `allAcked` observation (step 5). -/
def shootdownRound (st : SystemState) (initiator : CoreId)
    (targets : List CoreId) (op : TlbInvalidation) : Option SystemState :=
  match tlbShootdownBroadcast st initiator targets op with
  | none => none
  | some (posted, _) =>
      some (targets.foldl handleTlbShootdownReqOnCore
        (tlbShootdownLocal posted op))

/-- **WS-SM SM7.B**: the handler fold's shootdown-state projection is
the SM7.A round-step fold — the bridge that transports the SM7.A round
capstones to the protocol pipeline. -/
theorem foldl_handleTlbShootdownReqOnCore_tlbShootdown
    (targets : List CoreId) :
    ∀ st : SystemState,
      (targets.foldl handleTlbShootdownReqOnCore st).tlbShootdown =
        targets.foldl completeShootdownOnCore st.tlbShootdown := by
  induction targets with
  | nil => intro st; rfl
  | cons t ts ih =>
    intro st
    rw [List.foldl_cons, List.foldl_cons, ih,
        handleTlbShootdownReqOnCore_tlbShootdown_eq]

/-- **WS-SM SM7.B**: the handler fold never adds TLB entries — every
handler only retires invalidations. -/
theorem mem_tlb_of_foldl_handleTlbShootdownReqOnCore (targets : List CoreId) :
    ∀ {st : SystemState} {e : TlbEntry},
      e ∈ ((targets.foldl handleTlbShootdownReqOnCore st).tlb).entries →
      e ∈ st.tlb.entries := by
  induction targets with
  | nil => intro st e h; exact h
  | cons t ts ih =>
    intro st e h
    have hmem := ih (st := handleTlbShootdownReqOnCore st t) h
    rw [handleTlbShootdownReqOnCore_tlb_eq] at hmem
    exact mem_of_mem_applyTlbInvalidations hmem

/-- **WS-SM SM7.B.5 (reachability half)**: from a quiescent state the
round pipeline always completes. -/
theorem shootdownRound_isSome_of_quiescent {st : SystemState}
    (hq : shootdownQuiescent st.tlbShootdown) (initiator : CoreId)
    {targets : List CoreId} (hnd : targets.Nodup) (op : TlbInvalidation) :
    (shootdownRound st initiator targets op).isSome := by
  unfold shootdownRound
  have h := tlbShootdownBroadcast_isSome_of_quiescent hq initiator hnd op
  obtain ⟨pair, hpair⟩ := Option.isSome_iff_exists.mp h
  rw [hpair]
  rfl

/-- **WS-SM SM7.B**: a completed round restores quiescence — every
queue drained, every flag acknowledged — so the *next* round's posting
succeeds too (the plan §4.1 capacity induction, now at the protocol
pipeline level).  Lifts the SM7.A masked capstone
`shootdownRoundFor_restores_quiescent` through the handler fold's
projection.  No `Nodup` hypothesis: a duplicated target is drained
twice and the second drain retires nothing
(`handleTlbShootdownReqOnCore_idempotent`). -/
theorem shootdownRound_quiescent {st final : SystemState}
    {initiator : CoreId} {targets : List CoreId} {op : TlbInvalidation}
    (hq : shootdownQuiescent st.tlbShootdown)
    (h : shootdownRound st initiator targets op = some final) :
    shootdownQuiescent final.tlbShootdown := by
  unfold shootdownRound tlbShootdownBroadcast at h
  cases hfold : targets.foldlM
      (fun s c => enqueueShootdown s c { op := op, initiator := initiator })
      (beginShootdownRoundFor st.tlbShootdown initiator targets) with
  | none => rw [hfold] at h; cases h
  | some posted =>
      rw [hfold] at h
      injection h with h
      rw [← h, foldl_handleTlbShootdownReqOnCore_tlbShootdown]
      have hproj : (tlbShootdownLocal
          { st with tlbShootdown := posted } op).tlbShootdown = posted := rfl
      rw [hproj]
      exact shootdownRoundFor_restores_quiescent hq initiator hfold

/-- **WS-SM SM7.B.5 (exit-condition half)**: a completed round reaches
`allAcked` — the initiator wait-loop's exit condition is realised by
the round itself. -/
theorem shootdownRound_allAcked {st final : SystemState}
    {initiator : CoreId} {targets : List CoreId} {op : TlbInvalidation}
    (hq : shootdownQuiescent st.tlbShootdown)
    (h : shootdownRound st initiator targets op = some final) :
    allAcked final.tlbShootdown :=
  (shootdownRound_quiescent hq h).2

/-- **WS-SM SM7.B.8** (single-view corollary, the real pipeline): after
a completed round no covered entry survives in the mounted TLB view —
the initiator's local step removed it and no handler re-adds entries.
This is Theorem 3.3.1 at today's single-view mounting; the ∀-core form
is `tlbShootdownBroadcast_invalidatesAllCores` below. -/
theorem shootdownRound_tlb_no_matching_entry {st final : SystemState}
    {initiator : CoreId} {targets : List CoreId} {op : TlbInvalidation}
    (h : shootdownRound st initiator targets op = some final)
    {e : TlbEntry} (he : tlbEntryMatches op e = true) :
    e ∉ final.tlb.entries := by
  unfold shootdownRound at h
  cases hb : tlbShootdownBroadcast st initiator targets op with
  | none => rw [hb] at h; cases h
  | some pair =>
      rw [hb] at h
      injection h with h
      rw [← h]
      intro hmem
      have hloc := mem_tlb_of_foldl_handleTlbShootdownReqOnCore targets hmem
      exact tlbShootdownLocal_removes he pair.1 hloc

-- ============================================================================
-- SM7.B.8 — Theorem 3.3.1: per-core views
-- ============================================================================

/-- **WS-SM SM7.B.8**: write one core's TLB view slot (SM4.B path-a
setter over the explicit per-core view vector Theorem 3.3.1 quantifies
over; SM7.C.1 mounts this vector in `SystemState`). -/
def setTlbViewOnCore (views : Vector TlbState numCores) (c : CoreId)
    (t : TlbState) : Vector TlbState numCores :=
  views.set c.val t c.isLt

@[simp] theorem setTlbViewOnCore_get_self (views : Vector TlbState numCores)
    (c : CoreId) (t : TlbState) :
    (setTlbViewOnCore views c t).get c = t := by
  simp [setTlbViewOnCore]

theorem setTlbViewOnCore_get_ne (views : Vector TlbState numCores)
    {c c' : CoreId} (h : c' ≠ c) (t : TlbState) :
    (setTlbViewOnCore views c t).get c' = views.get c' := by
  simp only [setTlbViewOnCore]
  exact SeLe4n.PerCoreVector.get_set_ne views c c' t (fun he => h he.symm)

/-- **WS-SM SM7.B.8**: the per-core view effect of one complete round —
the initiator applies the operand locally (step 3); each target applies
it at its handler's acknowledgment (step 4).  The per-target step is
exactly the real handler transition's TLB effect on the really-posted
state (`handleTlbShootdownReqOnCore_applies_posted_op` +
`tlbShootdownBroadcast_posts_singleton` — the non-vacuity bridge), so
this function is the ∀-core reading of the `shootdownRound` pipeline,
not an independent axiomatisation. -/
def shootdownRoundViews (views : Vector TlbState numCores)
    (initiator : CoreId) (targets : List CoreId) (op : TlbInvalidation) :
    Vector TlbState numCores :=
  targets.foldl
    (fun vs c => setTlbViewOnCore vs c (applyTlbInvalidation (vs.get c) op))
    (setTlbViewOnCore views initiator
      (applyTlbInvalidation (views.get initiator) op))

/-- **WS-SM SM7.B.8** (fold closed form): a slot holds the invalidated
view iff the fold visited it; duplicates collapse by idempotence. -/
theorem foldl_invalidateViewOnCore_get (op : TlbInvalidation)
    (l : List CoreId) :
    ∀ (vs : Vector TlbState numCores) (c : CoreId),
      (l.foldl (fun vs c =>
          setTlbViewOnCore vs c (applyTlbInvalidation (vs.get c) op))
        vs).get c =
        if c ∈ l then applyTlbInvalidation (vs.get c) op else vs.get c := by
  induction l with
  | nil => intro vs c; simp
  | cons t ts ih =>
    intro vs c
    rw [List.foldl_cons, ih]
    by_cases hct : c = t
    · subst hct
      by_cases hcts : c ∈ ts
      · rw [if_pos hcts, if_pos (List.mem_cons_self ..),
            setTlbViewOnCore_get_self, applyTlbInvalidation_idempotent]
      · rw [if_neg hcts, if_pos (List.mem_cons_self ..),
            setTlbViewOnCore_get_self]
    · by_cases hcts : c ∈ ts
      · rw [if_pos hcts, if_pos (List.mem_cons_of_mem _ hcts),
            setTlbViewOnCore_get_ne _ hct]
      · rw [if_neg hcts, if_neg (by simp [List.mem_cons, hct, hcts]),
            setTlbViewOnCore_get_ne _ hct]

/-- **WS-SM SM7.B.8** (closed form): after a round, a core's view is
the invalidated view iff the core participated (as target or as
initiator), and is untouched otherwise. -/
theorem shootdownRoundViews_get (views : Vector TlbState numCores)
    (initiator : CoreId) (targets : List CoreId) (op : TlbInvalidation)
    (c : CoreId) :
    (shootdownRoundViews views initiator targets op).get c =
      if c ∈ targets ∨ c = initiator
      then applyTlbInvalidation (views.get c) op
      else views.get c := by
  unfold shootdownRoundViews
  rw [foldl_invalidateViewOnCore_get]
  by_cases hct : c ∈ targets
  · rw [if_pos hct, if_pos (Or.inl hct)]
    by_cases hci : c = initiator
    · subst hci
      rw [setTlbViewOnCore_get_self, applyTlbInvalidation_idempotent]
    · rw [setTlbViewOnCore_get_ne _ hci]
  · rw [if_neg hct]
    by_cases hci : c = initiator
    · subst hci
      rw [if_pos (Or.inr rfl), setTlbViewOnCore_get_self]
    · rw [if_neg (by simp [hct, hci]), setTlbViewOnCore_get_ne _ hci]

/-- **WS-SM SM7.B.8 — Theorem 3.3.1**
(`tlbShootdownBroadcast_invalidatesAllCores`, plan §3.3): after a
complete shootdown round whose target set covers every non-initiator
core, **no core's TLB view retains any entry the operand covers**.

Proof, as plan §3.3 sketches: case analysis on `c`.  The initiator
executed the local invalidation at step 3; every other core is a
target (coverage), and its handler applied the posted operand before
acknowledging (step 4b/4c — `shootdownRoundViews`'s per-target step,
tied to the real handler by
`handleTlbShootdownReqOnCore_applies_posted_op`).  The release-acquire
pairing (`shootdownAck_release_acquire`, SM7.B.4) orders each
handler's TLBI retirement before the initiator's `allAcked`
observation, so the post-round state this theorem describes is the
one the initiator's step-6 `dsb` publishes. -/
theorem tlbShootdownBroadcast_invalidatesAllCores
    (views : Vector TlbState numCores) (initiator : CoreId)
    {targets : List CoreId}
    (hcov : ∀ c : CoreId, c ≠ initiator → c ∈ targets)
    (op : TlbInvalidation) :
    ∀ (c : CoreId) {e : TlbEntry}, tlbEntryMatches op e = true →
      e ∉ ((shootdownRoundViews views initiator targets op).get c).entries := by
  intro c e he
  rw [shootdownRoundViews_get]
  have hpart : c ∈ targets ∨ c = initiator := by
    by_cases hci : c = initiator
    · exact Or.inr hci
    · exact Or.inl (hcov c hci)
  rw [if_pos hpart]
  exact applyTlbInvalidation_removes he _

/-- **WS-SM SM7.B.8** (the unmap instantiation of Theorem 3.3.1): after
a page-unmap round no core retains a translation for the unmapped
`(asid, vaddr)` — the SMP-C4 use-after-unmap closure, stated on the
caller's typed operands via the unconditional encoding round trip. -/
theorem tlbShootdownBroadcast_invalidates_unmap_target
    (views : Vector TlbState numCores) (initiator : CoreId)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) :
    ∀ (c : CoreId) {e : TlbEntry}, e.asid = asid → e.vaddr = vaddr →
      e ∉ ((shootdownRoundViews views initiator
        (shootdownTargets initiator)
        (encodePageInvalidation asid vaddr)).get c).entries :=
  fun c _ hA hV =>
    tlbShootdownBroadcast_invalidatesAllCores views initiator
      (shootdownTargets_cover initiator) _ c
      (encodePageInvalidation_matches asid vaddr hA hV)



-- ============================================================================
-- SM7.B.12 — Cross-cluster path via `.outer` sharing
-- ============================================================================

/-- **WS-SM SM7.B.12**: the broadcast round tagged with the sharing
domain its runtime TLBIs are issued in.  The domain selects the IS
(`.inner`) or OS (`.outer`) instruction variant and barrier at the
`tlbiForSharing` dispatch (SM1.E.4); the *state* protocol — round
open, posting, drain, acknowledgment — is domain-independent, which
is exactly what makes the cross-cluster port a platform-binding
change (`PlatformBinding.sharingDomain`, WS-SM decision #6) rather
than a protocol change. -/
def tlbShootdownBroadcastIn (_domain : SharingDomain) (st : SystemState)
    (initiator : CoreId) (targets : List CoreId) (op : TlbInvalidation) :
    Option (SystemState × List (CoreId × SgiKind)) :=
  tlbShootdownBroadcast st initiator targets op

/-- **WS-SM SM7.B.12** (`tlbShootdown_outer_correct`): the `.outer`
(cross-cluster) round is state-identical to the `.inner` round — every
SM7.B round theorem (posting exactness, quiescence restoration,
Theorem 3.3.1) therefore holds verbatim on an outer-shareable
platform; only the instruction variant the runtime dispatcher emits
changes (`SharingDomain.toTag` `.outer` ↦ 1, routed to the Rust
`tlbi_*os` arms, whose operand encoding is range-checked by
`tlbiForSharing_ffi_args_in_range` for both domains). -/
theorem tlbShootdown_outer_correct (st : SystemState) (initiator : CoreId)
    (targets : List CoreId) (op : TlbInvalidation) :
    tlbShootdownBroadcastIn .outer st initiator targets op =
      tlbShootdownBroadcastIn .inner st initiator targets op := rfl

-- ============================================================================
-- SM7.B.9 / SM7.B.10 — Caller-facing shootdown posting (total, coalescing)
-- ============================================================================

/-- **WS-SM SM7.B.9** (fold lemma): the coalescing posting fold —
total, never fails.  Whenever the strict posting fold succeeds, the
coalescing fold commits the identical state. -/
theorem foldl_enqueueShootdownOrCoalesce_eq_foldlM {targets : List CoreId} :
    ∀ {sd posted : TlbShootdownState} {d : TlbShootdownDescriptor},
      targets.foldlM (fun s c => enqueueShootdown s c d) sd = some posted →
      targets.foldl (fun s c => enqueueShootdownOrCoalesce s c d) sd =
        posted := by
  induction targets with
  | nil =>
    intro sd posted d h
    exact Option.some.inj h
  | cons t ts ih =>
    intro sd posted d h
    rw [List.foldlM_cons] at h
    cases henq : enqueueShootdown sd t d with
    | none => rw [henq] at h; simp at h
    | some sd' =>
      rw [henq] at h
      rw [List.foldl_cons, enqueueShootdownOrCoalesce_eq_enqueue henq]
      exact ih h

/-- **WS-SM SM7.B.9**: the total round posting on the shootdown state —
round open (targets unacknowledged) + one coalescing enqueue per
target.  Unlike the strict posting fold it cannot fail: accumulated
postings (multiple rounds committed before the runtime seam's
exhaustive drain catches up) collapse to a full flush, which
supersedes every dropped descriptor
(`enqueueShootdownOrCoalesce_pending_covered`; over-invalidation is
always safe). -/
def postShootdownRoundCoalescing (sd : TlbShootdownState)
    (initiator : CoreId) (targets : List CoreId) (op : TlbInvalidation) :
    TlbShootdownState :=
  targets.foldl
    (fun s c => enqueueShootdownOrCoalesce s c
      { op := op, initiator := initiator })
    (beginShootdownRoundFor sd initiator targets)

/-- **WS-SM SM7.B.9**: the total caller-facing broadcast — what the
shootdown-aware kernel operations (`vspaceUnmapPageWithShootdown` and
friends) commit.  The runtime seam recovers the emitted SGI set from
the state diff (`shootdownChangedTargets`), so no SGI list is
returned here. -/
def tlbShootdownBroadcastCoalescing (st : SystemState) (initiator : CoreId)
    (targets : List CoreId) (op : TlbInvalidation) : SystemState :=
  { st with tlbShootdown :=
      postShootdownRoundCoalescing st.tlbShootdown initiator targets op }

/-- **WS-SM SM7.B.9**: whenever the strict broadcast succeeds — always
from quiescence — the coalescing broadcast commits the same state. -/
theorem tlbShootdownBroadcastCoalescing_eq_strict {st st' : SystemState}
    {initiator : CoreId} {targets : List CoreId} {op : TlbInvalidation}
    {sgis : List (CoreId × SgiKind)}
    (h : tlbShootdownBroadcast st initiator targets op = some (st', sgis)) :
    tlbShootdownBroadcastCoalescing st initiator targets op = st' := by
  unfold tlbShootdownBroadcast at h
  cases hfold : targets.foldlM
      (fun s c => enqueueShootdown s c { op := op, initiator := initiator })
      (beginShootdownRoundFor st.tlbShootdown initiator targets) with
  | none => rw [hfold] at h; cases h
  | some posted =>
      rw [hfold] at h
      injection h with h
      rw [Prod.mk.injEq] at h
      obtain ⟨hst, hsgi⟩ := h
      subst hst
      unfold tlbShootdownBroadcastCoalescing postShootdownRoundCoalescing
      rw [foldl_enqueueShootdownOrCoalesce_eq_foldlM hfold]

/-- **WS-SM SM7.B.9**: the coalescing broadcast touches only the
shootdown state. -/
theorem tlbShootdownBroadcastCoalescing_frame (st : SystemState)
    (initiator : CoreId) (targets : List CoreId) (op : TlbInvalidation) :
    (tlbShootdownBroadcastCoalescing st initiator targets op).objects =
      st.objects ∧
    (tlbShootdownBroadcastCoalescing st initiator targets op).scheduler =
      st.scheduler ∧
    (tlbShootdownBroadcastCoalescing st initiator targets op).machine =
      st.machine ∧
    (tlbShootdownBroadcastCoalescing st initiator targets op).tlb = st.tlb :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **WS-SM SM7.B.9** (fold lemma): the coalescing posting fold
preserves the capacity invariant unconditionally. -/
theorem foldl_enqueueShootdownOrCoalesce_preserves_pendingBounded
    {targets : List CoreId} :
    ∀ {sd : TlbShootdownState} {d : TlbShootdownDescriptor},
      pendingBounded sd →
      pendingBounded (targets.foldl
        (fun s c => enqueueShootdownOrCoalesce s c d) sd) := by
  induction targets with
  | nil => intro sd d hB; exact hB
  | cons t ts ih =>
    intro sd d hB
    rw [List.foldl_cons]
    exact ih (enqueueShootdownOrCoalesce_preserves_pendingBounded hB t d)

/-- **WS-SM SM7.B.9**: the total round posting preserves the capacity
invariant — with no hypothesis on queue occupancy at all. -/
theorem postShootdownRoundCoalescing_preserves_pendingBounded
    {sd : TlbShootdownState} (hB : pendingBounded sd) (initiator : CoreId)
    (targets : List CoreId) (op : TlbInvalidation) :
    pendingBounded (postShootdownRoundCoalescing sd initiator targets op) := by
  unfold postShootdownRoundCoalescing
  exact foldl_enqueueShootdownOrCoalesce_preserves_pendingBounded
    (beginShootdownRoundFor_preserves_pendingBounded hB initiator targets)

/-- **WS-SM SM7.B.9**: the coalescing broadcast preserves the capacity
invariant. -/
theorem tlbShootdownBroadcastCoalescing_preserves_pendingBounded
    {st : SystemState} (hB : pendingBounded st.tlbShootdown)
    (initiator : CoreId) (targets : List CoreId) (op : TlbInvalidation) :
    pendingBounded
      (tlbShootdownBroadcastCoalescing st initiator targets
        op).tlbShootdown :=
  postShootdownRoundCoalescing_preserves_pendingBounded hB initiator
    targets op

/-- **WS-SM SM7.B.9** (fold lemma): the coalescing posting fold frames
every unvisited core's queue. -/
theorem foldl_enqueueShootdownOrCoalesce_frame_pending (l : List CoreId) :
    ∀ (sd : TlbShootdownState) (d : TlbShootdownDescriptor) {c : CoreId},
      c ∉ l →
      (l.foldl (fun s c => enqueueShootdownOrCoalesce s c d)
        sd).pendingOnCore c = sd.pendingOnCore c := by
  induction l with
  | nil => intro sd d c _; rfl
  | cons t ts ih =>
    intro sd d c hc
    rw [List.foldl_cons, ih _ _ (fun hm => hc (List.mem_cons_of_mem _ hm)),
        enqueueShootdownOrCoalesce_frame_pending sd
          (fun hEq => hc (List.mem_cons.mpr (Or.inl hEq))) d]

/-- **WS-SM SM7.B.9** (fold lemma): the coalescing posting fold never
touches any ack flag. -/
theorem foldl_enqueueShootdownOrCoalesce_frame_ack (l : List CoreId) :
    ∀ (sd : TlbShootdownState) (d : TlbShootdownDescriptor) (c : CoreId),
      (l.foldl (fun s c => enqueueShootdownOrCoalesce s c d)
        sd).ackOnCore c = sd.ackOnCore c := by
  induction l with
  | nil => intro sd d c; rfl
  | cons t ts ih =>
    intro sd d c
    rw [List.foldl_cons, ih, enqueueShootdownOrCoalesce_frame_ack]

/-- **WS-SM SM7.B.9**: after the total round posting a core is
acknowledged iff it is the initiator or outside the target set —
identical to the strict broadcast's ack shape. -/
theorem postShootdownRoundCoalescing_ack_iff (sd : TlbShootdownState)
    (initiator : CoreId) (targets : List CoreId) (op : TlbInvalidation)
    (c : CoreId) :
    (postShootdownRoundCoalescing sd initiator targets op).ackOnCore c =
        true ↔
      (c = initiator ∨ c ∉ targets) := by
  unfold postShootdownRoundCoalescing
  rw [foldl_enqueueShootdownOrCoalesce_frame_ack]
  exact beginShootdownRoundFor_ackOnCore_iff sd initiator targets c

/-- **WS-SM SM7.B.9** (fold lemma): after the coalescing posting fold,
every visited core's queue holds the round's descriptor or a
full-flush descriptor that supersedes it — no invalidation request is
ever lost, even past the capacity bound. -/
theorem foldl_enqueueShootdownOrCoalesce_covered (targets : List CoreId) :
    ∀ (sd : TlbShootdownState) (d : TlbShootdownDescriptor),
      targets.Nodup →
      ∀ c ∈ targets,
        d ∈ (targets.foldl (fun s c => enqueueShootdownOrCoalesce s c d)
            sd).pendingOnCore c ∨
          ∃ d' ∈ (targets.foldl
              (fun s c => enqueueShootdownOrCoalesce s c d)
              sd).pendingOnCore c,
            d'.op = TlbInvalidation.vmalle1 := by
  induction targets with
  | nil => intro sd d _ c hc; cases hc
  | cons t ts ih =>
    intro sd d hnd c hc
    rcases List.mem_cons.mp hc with hEq | hMem
    · subst hEq
      rw [List.foldl_cons,
          foldl_enqueueShootdownOrCoalesce_frame_pending ts _ _
            (List.nodup_cons.mp hnd).1]
      exact enqueueShootdownOrCoalesce_request_covered sd c d
    · rw [List.foldl_cons]
      exact ih _ _ (List.nodup_cons.mp hnd).2 c hMem

/-- **WS-SM SM7.B.9**: the total round posting never loses the round's
request — every target holds the descriptor, or a full flush that
supersedes it. -/
theorem postShootdownRoundCoalescing_covered (sd : TlbShootdownState)
    (initiator : CoreId) {targets : List CoreId} (hnd : targets.Nodup)
    (op : TlbInvalidation) :
    ∀ c ∈ targets,
      ({ op := op, initiator := initiator } : TlbShootdownDescriptor) ∈
          (postShootdownRoundCoalescing sd initiator targets
            op).pendingOnCore c ∨
        ∃ d' ∈ (postShootdownRoundCoalescing sd initiator targets
            op).pendingOnCore c,
          d'.op = TlbInvalidation.vmalle1 := by
  unfold postShootdownRoundCoalescing
  exact foldl_enqueueShootdownOrCoalesce_covered targets _ _ hnd

-- ============================================================================
-- SM7.B.9 — Shootdown-aware kernel operations (the unmap-caller wiring)
-- ============================================================================

/-- **WS-SM SM7.B.9**: post a shootdown round for `op` from
`executingCore` to every other core — the total posting step every
shootdown-aware kernel operation composes after its local flush.

The runtime seam (`SyscallDispatchEntry.completeShootdownRounds`)
recovers the targets from the `(pre, post)` shootdown-state diff,
fires the `.tlbShootdownReq` SGIs at the *online* targets, executes
the initiator's broadcast TLBI, waits for `allAcked` (bounded,
fail-closed), and commits the handler catch-up. -/
def withShootdownRound (executingCore : CoreId) (op : TlbInvalidation) :
    Kernel Unit :=
  fun st =>
    .ok ((), tlbShootdownBroadcastCoalescing st executingCore
      (shootdownTargets executingCore) op)

/-- **WS-SM SM7.B.9**: the posting step is total — it never fails a
syscall. -/
theorem withShootdownRound_total (executingCore : CoreId)
    (op : TlbInvalidation) (st : SystemState) :
    withShootdownRound executingCore op st =
      .ok ((), tlbShootdownBroadcastCoalescing st executingCore
        (shootdownTargets executingCore) op) := rfl

/-- **WS-SM SM7.B.9**: **production entry point** — VSpace unmap with
targeted local TLB flush *and* cross-core shootdown round.

Composes the verified `vspaceUnmapPageWithFlush` (page-table erase +
local per-`(asid, vaddr)` flush — the initiator's local invalidation
in its established typed form) with the round posting for the same
operand.  This is the SM7.B.9 closure of the SMP-C4 use-after-unmap
hazard: without the round, a remote core could keep translating the
unmapped page through its stale TLB entry indefinitely. -/
def vspaceUnmapPageWithShootdown (executingCore : CoreId)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) : Kernel Unit :=
  fun st =>
    match vspaceUnmapPageWithFlush asid vaddr st with
    | .error e => .error e
    | .ok ((), st') =>
        withShootdownRound executingCore
          (encodePageInvalidation asid vaddr) st'

/-- **WS-SM SM7.B.9**: does the pre-state hold a live translation for
`(asid, vaddr)`?  The map wrapper's remap detector: only replacing a
*live* translation leaves a stale entry cached on remote cores.  A
fresh map owes no round — ARM64 TLBs cache no negative entries, so a
virtual address with no current translation cannot be cached anywhere
(every earlier transition that removed one ran its own round). -/
def vspaceHasTranslation (st : SystemState) (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr) : Bool :=
  match resolveAsidRoot st asid with
  | some (_, root) => (root.lookup vaddr).isSome
  | none => false

/-- **WS-SM SM7.B.9**: **production entry point** — state-aware
bounds-checked VSpace map with local flush and, on the *remap*
direction only, a shootdown round: replacing a live translation leaves
the *old* one cached on remote cores exactly like an unmap does, while
a fresh map (no prior translation, `vspaceHasTranslation` false on the
pre-state) has nothing stale to invalidate anywhere and commits the
base operation exactly (`…_fresh_inert`). -/
def vspaceMapPageCheckedWithShootdownFromState (executingCore : CoreId)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (perms : PagePermissions := PagePermissions.readOnly) : Kernel Unit :=
  fun st =>
    let hadPrior := vspaceHasTranslation st asid vaddr
    match vspaceMapPageCheckedWithFlushFromState asid vaddr paddr perms st with
    | .error e => .error e
    | .ok ((), st') =>
        if hadPrior then
          withShootdownRound executingCore
            (encodePageInvalidation asid vaddr) st'
        else
          .ok ((), st')

/-- **WS-SM SM7.B.9**: a fresh map posts no round — the wrapper commits
exactly the base operation's result (trace safety for every
first-mapping call, and no spurious cross-core traffic for the common
fresh-map case). -/
theorem vspaceMapPageCheckedWithShootdownFromState_fresh_inert
    (executingCore : CoreId) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr) (perms : PagePermissions) (st : SystemState)
    (hFresh : vspaceHasTranslation st asid vaddr = false) :
    vspaceMapPageCheckedWithShootdownFromState executingCore asid vaddr paddr
        perms st =
      vspaceMapPageCheckedWithFlushFromState asid vaddr paddr perms st := by
  unfold vspaceMapPageCheckedWithShootdownFromState
  simp only [hFresh]
  cases h : vspaceMapPageCheckedWithFlushFromState asid vaddr paddr perms st with
  | error e => rfl
  | ok pair =>
      obtain ⟨u, st'⟩ := pair
      cases u
      simp

/-- **WS-SM SM7.B.9** (model fact): a *successful* checked map is
always a fresh map — `VSpaceRoot.mapPage` rejects an occupied `vaddr`
with `.mappingConflict`, so replacing a live translation in one step
is unreachable; the kernel's remap discipline is unmap-then-map, and
the shootdown round rides the unmap.  This is why the map wrapper's
posting branch is dead code *today* (`…_never_posts` below) — it stays
as a defense-in-depth seam: if `mapPage` ever gains replace semantics,
the round posts automatically instead of silently going missing. -/
theorem vspaceMapPage_ok_fresh
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (perms : PagePermissions) {st st' : SystemState}
    (hOk : vspaceMapPage asid vaddr paddr perms st = .ok ((), st')) :
    vspaceHasTranslation st asid vaddr = false := by
  unfold vspaceMapPage at hOk
  revert hOk
  cases hRes : resolveAsidRoot st asid with
  | none => intro hOk; cases hOk
  | some pair =>
      simp only []
      split
      · intro hOk; cases hOk
      · cases hMap : pair.2.mapPage vaddr paddr perms with
        | none => intro hOk; cases hOk
        | some root' =>
            intro _
            show (match resolveAsidRoot st asid with
              | some (_, root) => (root.lookup vaddr).isSome
              | none => false) = false
            rw [hRes]
            show (pair.2.lookup vaddr).isSome = false
            unfold VSpaceRoot.mapPage at hMap
            revert hMap
            split
            · intro hMap; cases hMap
            · cases hLook : pair.2.mappings[vaddr]? with
              | some _ => intro hMap; cases hMap
              | none =>
                  intro _
                  simp only [VSpaceRoot.lookup, hLook, Option.isSome_none]

/-- **WS-SM SM7.B.9**: the checked map's `ok`-implies-fresh fact lifted
through the flush and bounds-check layers. -/
theorem vspaceMapPageCheckedWithFlushFromState_ok_fresh
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (perms : PagePermissions) {st st' : SystemState}
    (hOk : vspaceMapPageCheckedWithFlushFromState asid vaddr paddr perms st
      = .ok ((), st')) :
    vspaceHasTranslation st asid vaddr = false := by
  unfold vspaceMapPageCheckedWithFlushFromState at hOk
  revert hOk
  split
  · intro hOk; cases hOk
  · split
    · intro hOk; cases hOk
    · unfold vspaceMapPageWithFlush
      cases hBase : vspaceMapPage asid vaddr paddr perms st with
      | error e => intro hOk; cases hOk
      | ok pair =>
          intro _
          exact vspaceMapPage_ok_fresh asid vaddr paddr perms
            (st' := pair.2) (by rw [hBase])

/-- **WS-SM SM7.B.9** (today's-model corollary): the checked map
wrapper never posts a round — every success path is a fresh map, whose
shootdown state is exactly the pre-state's. -/
theorem vspaceMapPageCheckedWithShootdownFromState_never_posts
    (executingCore : CoreId) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr) (perms : PagePermissions) {st st' : SystemState}
    (hOk : vspaceMapPageCheckedWithShootdownFromState executingCore asid vaddr
      paddr perms st = .ok ((), st')) :
    st'.tlbShootdown = st.tlbShootdown := by
  cases hPrior : vspaceHasTranslation st asid vaddr with
  | false =>
      rw [vspaceMapPageCheckedWithShootdownFromState_fresh_inert executingCore
        asid vaddr paddr perms st hPrior] at hOk
      exact vspaceMapPageCheckedWithFlushFromState_tlbShootdown_eq asid vaddr
        paddr perms st st' hOk
  | true =>
      -- Unreachable: the posting branch requires a successful base map,
      -- which forces freshness.
      revert hOk
      unfold vspaceMapPageCheckedWithShootdownFromState
      simp only [hPrior]
      cases hBase : vspaceMapPageCheckedWithFlushFromState asid vaddr paddr
          perms st with
      | error e => intro hOk; cases hOk
      | ok pair =>
          have := vspaceMapPageCheckedWithFlushFromState_ok_fresh asid vaddr
            paddr perms (st' := pair.2)
            (by rw [hBase])
          rw [hPrior] at this
          cases this

/-- **WS-SM SM7.B.9** (defense-in-depth spec): *were* a prior
translation replaceable in one step, the wrapper would post the round
— the conditional's behaviour contract, independent of today's
`mapPage` conflict semantics (whose `ok`-implies-fresh fact makes the
hypotheses jointly unsatisfiable at present;
`vspaceMapPageCheckedWithFlushFromState_ok_fresh`). -/
theorem vspaceMapPageCheckedWithShootdownFromState_remap_posts
    (executingCore : CoreId) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr) (perms : PagePermissions)
    {st stFlush : SystemState}
    (hPrior : vspaceHasTranslation st asid vaddr = true)
    (h : vspaceMapPageCheckedWithFlushFromState asid vaddr paddr perms st
      = .ok ((), stFlush)) :
    vspaceMapPageCheckedWithShootdownFromState executingCore asid vaddr paddr
        perms st =
      .ok ((), tlbShootdownBroadcastCoalescing stFlush executingCore
        (shootdownTargets executingCore)
        (encodePageInvalidation asid vaddr)) := by
  unfold vspaceMapPageCheckedWithShootdownFromState
  simp only [hPrior, h]
  rfl

/-- **WS-SM SM7.B.10**: **production entry point** — per-ASID TLB flush
with shootdown round: the ASID-retire path.  Reusing a retired ASID
with any core still caching translations for it breaks address-space
isolation (the AsidManager `requiresFlush` contract); this operation
is that contract's kernel-level discharge — local `TLBI ASIDE1`
model + `.aside1` round to every other core. -/
def tlbFlushByASIDWithShootdown (executingCore : CoreId)
    (asid : SeLe4n.ASID) : Kernel Unit :=
  fun st =>
    match tlbFlushByASID asid st with
    | .error e => .error e
    | .ok ((), st') =>
        withShootdownRound executingCore (encodeAsidInvalidation asid) st'

/-- **WS-SM SM7.B.9**: **production entry point** — per-page TLB flush
with shootdown round. -/
def tlbFlushByPageWithShootdown (executingCore : CoreId)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) : Kernel Unit :=
  fun st =>
    match tlbFlushByPage asid vaddr st with
    | .error e => .error e
    | .ok ((), st') =>
        withShootdownRound executingCore
          (encodePageInvalidation asid vaddr) st'

/-- **WS-SM SM7.B.10**: allocate an ASID from a pool, discharging the
`requiresFlush` obligation through the shootdown round.

`AsidPool.allocate` marks reuse and rollover allocations
`requiresFlush := true` (stale TLB entries from the ASID's prior owner
may exist — on *any* core, under SMP); this transition is the missing
consumer the AsidManager TLB contract deferred to "HAL discipline":
when the pool demands a flush, the full `.aside1` round runs before
the allocation result is returned, so the reused ASID is clean
system-wide.  Pool exhaustion fails closed with
`.resourceExhausted`. -/
def asidAllocateWithShootdown (executingCore : CoreId) (pool : AsidPool) :
    Kernel AsidAllocResult :=
  fun st =>
    match pool.allocate with
    | none => .error .resourceExhausted
    | some result =>
        if result.requiresFlush then
          match tlbFlushByASIDWithShootdown executingCore result.asid st with
          | .error e => .error e
          | .ok ((), st') => .ok (result, st')
        else
          .ok (result, st)

/-- **WS-SM SM7.B.9**: the unmap wrapper fails exactly when the
verified flush op fails, with the same error — the shootdown posting
never introduces a failure mode. -/
theorem vspaceUnmapPageWithShootdown_error_iff (executingCore : CoreId)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (st : SystemState)
    (e : KernelError) :
    vspaceUnmapPageWithShootdown executingCore asid vaddr st = .error e ↔
      vspaceUnmapPageWithFlush asid vaddr st = .error e := by
  unfold vspaceUnmapPageWithShootdown
  cases h : vspaceUnmapPageWithFlush asid vaddr st with
  | error e' => exact Iff.rfl
  | ok pair =>
      obtain ⟨u, st'⟩ := pair
      cases u
      show withShootdownRound executingCore
          (encodePageInvalidation asid vaddr) st' = .error e ↔ _
      rw [withShootdownRound_total]
      simp

/-- **WS-SM SM7.B.9**: on success the unmap wrapper commits the
verified flush op's state with the round posted on top — the
page-table and local-TLB content are exactly
`vspaceUnmapPageWithFlush`'s (`tlbShootdownBroadcastCoalescing_frame`),
and every other core's queue carries the unmap's invalidation request
(`postShootdownRoundCoalescing_covered`). -/
theorem vspaceUnmapPageWithShootdown_ok (executingCore : CoreId)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) {st stFlush : SystemState}
    (h : vspaceUnmapPageWithFlush asid vaddr st = .ok ((), stFlush)) :
    vspaceUnmapPageWithShootdown executingCore asid vaddr st =
      .ok ((), tlbShootdownBroadcastCoalescing stFlush executingCore
        (shootdownTargets executingCore)
        (encodePageInvalidation asid vaddr)) := by
  unfold vspaceUnmapPageWithShootdown
  rw [h]
  rfl

/-- **WS-SM SM7.B.9**: a successful unmap-with-shootdown leaves the
unmap's invalidation request pending (or superseded by a full flush)
on **every** other core — the posting half of the SMP-C4 closure at
the caller level. -/
theorem vspaceUnmapPageWithShootdown_posts (executingCore : CoreId)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) {st stFlush : SystemState}
    (_h : vspaceUnmapPageWithFlush asid vaddr st = .ok ((), stFlush)) :
    ∀ c : CoreId, c ≠ executingCore →
      ({ op := encodePageInvalidation asid vaddr,
         initiator := executingCore } : TlbShootdownDescriptor) ∈
          (tlbShootdownBroadcastCoalescing stFlush executingCore
            (shootdownTargets executingCore)
            (encodePageInvalidation asid vaddr)).tlbShootdown.pendingOnCore
              c ∨
        ∃ d' ∈ (tlbShootdownBroadcastCoalescing stFlush executingCore
            (shootdownTargets executingCore)
            (encodePageInvalidation asid vaddr)).tlbShootdown.pendingOnCore
              c,
          d'.op = TlbInvalidation.vmalle1 := by
  intro c hc
  exact postShootdownRoundCoalescing_covered stFlush.tlbShootdown
    executingCore (shootdownTargets_nodup executingCore)
    (encodePageInvalidation asid vaddr) c
    ((mem_shootdownTargets_iff executingCore c).mpr hc)

/-- **WS-SM SM7.B.10**: a `requiresFlush` allocation flushes the reused
ASID locally and posts the `.aside1` round before returning — the
retired ASID cannot come back with stale translations anywhere. -/
theorem asidAllocateWithShootdown_requiresFlush (executingCore : CoreId)
    {pool : AsidPool} {result : AsidAllocResult}
    (hAlloc : pool.allocate = some result)
    (hFlush : result.requiresFlush = true) (st : SystemState) :
    asidAllocateWithShootdown executingCore pool st =
      .ok (result, tlbShootdownBroadcastCoalescing
        { st with tlb := adapterFlushTlbByAsid st.tlb result.asid }
        executingCore (shootdownTargets executingCore)
        (encodeAsidInvalidation result.asid)) := by
  unfold asidAllocateWithShootdown
  simp only [hAlloc, hFlush]
  rfl

/-- **WS-SM SM7.B.10**: a fresh (bump-allocator) allocation posts
nothing and leaves the state untouched — no flush obligation, no
round. -/
theorem asidAllocateWithShootdown_fresh_inert (executingCore : CoreId)
    {pool : AsidPool} {result : AsidAllocResult}
    (hAlloc : pool.allocate = some result)
    (hFlush : result.requiresFlush = false) (st : SystemState) :
    asidAllocateWithShootdown executingCore pool st = .ok (result, st) := by
  unfold asidAllocateWithShootdown
  simp only [hAlloc, hFlush]
  rfl

-- ============================================================================
-- SM7.B — Runtime-seam diff recovery (which cores must a commit poke?)
-- ============================================================================

/-- **WS-SM SM7.B**: the cores whose pending-shootdown queue a commit
changed — the diff the runtime seam fires `.tlbShootdownReq` SGIs at
(the shootdown analogue of the SM5.F.4 `computeCrossCoreSgis`
re-derivation: posting is data-driven in the pure model, and the entry
recovers the target set from the committed `(pre, post)` pair so the
dispatch signature stays unchanged). -/
def shootdownChangedTargets (pre post : SystemState) : List CoreId :=
  allCores.filter (fun c =>
    post.tlbShootdown.pendingOnCore c != pre.tlbShootdown.pendingOnCore c)

/-- **WS-SM SM7.B**: membership — exactly the cores with a changed
pending queue. -/
theorem mem_shootdownChangedTargets_iff (pre post : SystemState)
    (c : CoreId) :
    c ∈ shootdownChangedTargets pre post ↔
      post.tlbShootdown.pendingOnCore c ≠
        pre.tlbShootdown.pendingOnCore c := by
  simp [shootdownChangedTargets, List.mem_filter, allCores]

/-- **WS-SM SM7.B**: a commit that leaves the shootdown state alone
pokes nobody — the non-shootdown-syscall inertness of the runtime
seam (trace safety: no existing syscall's SGI behaviour changes). -/
theorem shootdownChangedTargets_nil_of_eq {pre post : SystemState}
    (h : post.tlbShootdown = pre.tlbShootdown) :
    shootdownChangedTargets pre post = [] := by
  unfold shootdownChangedTargets
  rw [List.filter_eq_nil_iff]
  intro c _
  rw [h]
  simp

/-- **WS-SM SM7.B**: the newly-posted invalidation operands of a
commit, deduplicated — the runtime seam executes one initiator-local
broadcast TLBI per distinct operand (plan §3.2 step 3). -/
def shootdownPostedOps (pre post : SystemState) : List TlbInvalidation :=
  ((shootdownChangedTargets pre post).flatMap (fun c =>
    (post.tlbShootdown.pendingOnCore c).map (·.op))).eraseDups

-- ============================================================================
-- SM7.B — Invariant-bundle carriage (`pendingBounded`, the 12th
-- `proofLayerInvariantBundle` conjunct)
-- ============================================================================
-- Every live shootdown-aware transition preserves the shootdown capacity
-- invariant: the posting side is total-by-coalescing
-- (`tlbShootdownBroadcastCoalescing_preserves_pendingBounded`), the
-- handler side only drains (`completeShootdownOnCore_preserves_pendingBounded`),
-- and every base operation frames `SystemState.tlbShootdown`
-- (`VSpace.lean` / `CleanupPreservation.lean` `…_tlbShootdown_eq` families).

/-- **WS-SM SM7.B**: the local shootdown step preserves the capacity
invariant — it touches only the TLB view (`tlbShootdownLocal_frame`). -/
theorem tlbShootdownLocal_preserves_pendingBounded {st : SystemState}
    (hB : pendingBounded st.tlbShootdown) (op : TlbInvalidation) :
    pendingBounded (tlbShootdownLocal st op).tlbShootdown :=
  (tlbShootdownLocal_frame st op).2.2.2 ▸ hB

/-- **WS-SM SM7.B**: the `.tlbShootdownReq` handler preserves the
capacity invariant — its shootdown projection is exactly the SM7.A
round step (`handleTlbShootdownReqOnCore_tlbShootdown_eq`). -/
theorem handleTlbShootdownReqOnCore_preserves_pendingBounded
    {st : SystemState} (hB : pendingBounded st.tlbShootdown) (c : CoreId) :
    pendingBounded (handleTlbShootdownReqOnCore st c).tlbShootdown := by
  rw [handleTlbShootdownReqOnCore_tlbShootdown_eq]
  exact completeShootdownOnCore_preserves_pendingBounded hB c

/-- **WS-SM SM7.B**: the round-posting combinator preserves the
capacity invariant (total — no failure path, no occupancy premise). -/
theorem withShootdownRound_preserves_pendingBounded
    {st st' : SystemState} {executingCore : CoreId} {op : TlbInvalidation}
    (hB : pendingBounded st.tlbShootdown)
    (hOk : withShootdownRound executingCore op st = .ok ((), st')) :
    pendingBounded st'.tlbShootdown := by
  unfold withShootdownRound at hOk
  simp only [Except.ok.injEq, Prod.mk.injEq] at hOk
  rw [← hOk.2]
  exact tlbShootdownBroadcastCoalescing_preserves_pendingBounded hB
    executingCore (shootdownTargets executingCore) op

/-- **WS-SM SM7.B.9**: the live unmap entry point preserves the
capacity invariant — the flush base op frames the shootdown state and
the posting step is total-by-coalescing. -/
theorem vspaceUnmapPageWithShootdown_preserves_pendingBounded
    {executingCore : CoreId} {asid : SeLe4n.ASID} {vaddr : SeLe4n.VAddr}
    {st st' : SystemState}
    (hB : pendingBounded st.tlbShootdown)
    (hOk : vspaceUnmapPageWithShootdown executingCore asid vaddr st
      = .ok ((), st')) :
    pendingBounded st'.tlbShootdown := by
  unfold vspaceUnmapPageWithShootdown at hOk
  revert hOk
  cases hBase : vspaceUnmapPageWithFlush asid vaddr st with
  | error e => intro hOk; cases hOk
  | ok pair =>
      intro hOk
      have hFrame : pair.2.tlbShootdown = st.tlbShootdown :=
        vspaceUnmapPageWithFlush_tlbShootdown_eq asid vaddr st pair.2 hBase
      exact withShootdownRound_preserves_pendingBounded (hFrame ▸ hB) hOk

/-- **WS-SM SM7.B.9**: the live map entry point preserves the capacity
invariant. -/
theorem vspaceMapPageCheckedWithShootdownFromState_preserves_pendingBounded
    {executingCore : CoreId} {asid : SeLe4n.ASID} {vaddr : SeLe4n.VAddr}
    {paddr : SeLe4n.PAddr} {perms : PagePermissions} {st st' : SystemState}
    (hB : pendingBounded st.tlbShootdown)
    (hOk : vspaceMapPageCheckedWithShootdownFromState executingCore asid vaddr
      paddr perms st = .ok ((), st')) :
    pendingBounded st'.tlbShootdown := by
  cases hPrior : vspaceHasTranslation st asid vaddr with
  | false =>
      rw [vspaceMapPageCheckedWithShootdownFromState_fresh_inert executingCore
        asid vaddr paddr perms st hPrior] at hOk
      rw [vspaceMapPageCheckedWithFlushFromState_tlbShootdown_eq
        asid vaddr paddr perms st st' hOk]
      exact hB
  | true =>
      revert hOk
      cases hBase : vspaceMapPageCheckedWithFlushFromState asid vaddr paddr
          perms st with
      | error e =>
          rw [show vspaceMapPageCheckedWithShootdownFromState executingCore
              asid vaddr paddr perms st = .error e from by
            unfold vspaceMapPageCheckedWithShootdownFromState
            simp only [hBase]]
          intro hOk; cases hOk
      | ok pair =>
          obtain ⟨u, stFlush⟩ := pair
          cases u
          rw [vspaceMapPageCheckedWithShootdownFromState_remap_posts
            executingCore asid vaddr paddr perms hPrior hBase]
          intro hOk
          simp only [Except.ok.injEq, Prod.mk.injEq] at hOk
          rw [← hOk.2]
          exact tlbShootdownBroadcastCoalescing_preserves_pendingBounded
            ((vspaceMapPageCheckedWithFlushFromState_tlbShootdown_eq asid vaddr
              paddr perms st stFlush hBase) ▸ hB) executingCore
            (shootdownTargets executingCore)
            (encodePageInvalidation asid vaddr)

/-- **WS-SM SM7.B.10**: the ASID-retire flush entry point preserves the
capacity invariant. -/
theorem tlbFlushByASIDWithShootdown_preserves_pendingBounded
    {executingCore : CoreId} {asid : SeLe4n.ASID} {st st' : SystemState}
    (hB : pendingBounded st.tlbShootdown)
    (hOk : tlbFlushByASIDWithShootdown executingCore asid st = .ok ((), st')) :
    pendingBounded st'.tlbShootdown := by
  unfold tlbFlushByASIDWithShootdown at hOk
  revert hOk
  cases hBase : tlbFlushByASID asid st with
  | error e => intro hOk; cases hOk
  | ok pair =>
      intro hOk
      have hFrame : pair.2.tlbShootdown = st.tlbShootdown :=
        tlbFlushByASID_tlbShootdown_eq asid st pair.2 hBase
      exact withShootdownRound_preserves_pendingBounded (hFrame ▸ hB) hOk

/-- **WS-SM SM7.B.9**: the per-page flush entry point preserves the
capacity invariant. -/
theorem tlbFlushByPageWithShootdown_preserves_pendingBounded
    {executingCore : CoreId} {asid : SeLe4n.ASID} {vaddr : SeLe4n.VAddr}
    {st st' : SystemState}
    (hB : pendingBounded st.tlbShootdown)
    (hOk : tlbFlushByPageWithShootdown executingCore asid vaddr st
      = .ok ((), st')) :
    pendingBounded st'.tlbShootdown := by
  unfold tlbFlushByPageWithShootdown at hOk
  revert hOk
  cases hBase : tlbFlushByPage asid vaddr st with
  | error e => intro hOk; cases hOk
  | ok pair =>
      intro hOk
      have hFrame : pair.2.tlbShootdown = st.tlbShootdown :=
        tlbFlushByPage_tlbShootdown_eq asid vaddr st pair.2 hBase
      exact withShootdownRound_preserves_pendingBounded (hFrame ▸ hB) hOk

/-- **WS-SM SM7.B.10**: the ASID-allocation entry point preserves the
capacity invariant — the flush arm delegates to
`tlbFlushByASIDWithShootdown`; the fresh arm commits the pre-state. -/
theorem asidAllocateWithShootdown_preserves_pendingBounded
    {executingCore : CoreId} {pool : AsidPool}
    {st st' : SystemState} {result : AsidAllocResult}
    (hB : pendingBounded st.tlbShootdown)
    (hOk : asidAllocateWithShootdown executingCore pool st
      = .ok (result, st')) :
    pendingBounded st'.tlbShootdown := by
  cases hAlloc : pool.allocate with
  | none =>
      rw [show asidAllocateWithShootdown executingCore pool st
          = .error .resourceExhausted from by
        unfold asidAllocateWithShootdown; simp only [hAlloc]] at hOk
      cases hOk
  | some r =>
      cases hFlushCase : r.requiresFlush with
      | true =>
          rw [asidAllocateWithShootdown_requiresFlush executingCore hAlloc
            hFlushCase st] at hOk
          simp only [Except.ok.injEq, Prod.mk.injEq] at hOk
          rw [← hOk.2]
          exact tlbShootdownBroadcastCoalescing_preserves_pendingBounded hB
            executingCore (shootdownTargets executingCore)
            (encodeAsidInvalidation r.asid)
      | false =>
          rw [asidAllocateWithShootdown_fresh_inert executingCore hAlloc
            hFlushCase st] at hOk
          simp only [Except.ok.injEq, Prod.mk.injEq] at hOk
          rw [← hOk.2]
          exact hB

-- ============================================================================
-- SM7.B — Handler commutativity (catch-up fold order-independence)
-- ============================================================================
-- The runtime's catch-up commit folds the handler over `shootdownTargets`;
-- the hardware retires each target's TLBIs in whatever order the SGIs land.
-- Distinct-core handler steps commute, so every visit order computes the
-- same state — the fold order in `completeShootdownRounds` is a
-- convention, not a correctness requirement.

/-- **WS-SM SM7.B**: single invalidation applications commute — each is
an entry filter, and filters intersect commutatively. -/
theorem applyTlbInvalidation_comm (t : TlbState) (op₁ op₂ : TlbInvalidation) :
    applyTlbInvalidation (applyTlbInvalidation t op₁) op₂ =
      applyTlbInvalidation (applyTlbInvalidation t op₂) op₁ := by
  unfold applyTlbInvalidation
  congr 1
  simp only [List.filter_filter]
  exact List.filter_congr (fun e _ => by rw [Bool.and_comm])

/-- **WS-SM SM7.B** (helper): a single application commutes past a
retire fold. -/
theorem applyTlbInvalidations_apply_comm (ops : List TlbInvalidation) :
    ∀ (t : TlbState) (op : TlbInvalidation),
      applyTlbInvalidations (applyTlbInvalidation t op) ops =
        applyTlbInvalidation (applyTlbInvalidations t ops) op := by
  induction ops with
  | nil => intro t op; rfl
  | cons o os ih =>
    intro t op
    rw [applyTlbInvalidations_cons, applyTlbInvalidation_comm t op o, ih,
        applyTlbInvalidations_cons]

/-- **WS-SM SM7.B**: retire folds of two operand lists commute. -/
theorem applyTlbInvalidations_comm (ops₁ ops₂ : List TlbInvalidation) :
    ∀ t : TlbState,
      applyTlbInvalidations (applyTlbInvalidations t ops₁) ops₂ =
        applyTlbInvalidations (applyTlbInvalidations t ops₂) ops₁ := by
  induction ops₁ with
  | nil => intro t; rfl
  | cons o os ih =>
    intro t
    rw [applyTlbInvalidations_cons, ih,
        applyTlbInvalidations_apply_comm ops₂ t o,
        applyTlbInvalidations_cons]

/-- **WS-SM SM7.B**: `.tlbShootdownReq` handler steps at *distinct*
cores commute — each drains only its own queue, acknowledges only its
own flag, and the TLB retire-filters intersect commutatively.  With
`foldl_handleTlbShootdownReqOnCore_swap` below this makes the catch-up
fold's visit order immaterial (any permutation of a `Nodup` target
list computes the same state, by induction on adjacent
transpositions). -/
theorem handleTlbShootdownReqOnCore_comm {c₁ c₂ : CoreId} (h : c₁ ≠ c₂)
    (st : SystemState) :
    handleTlbShootdownReqOnCore (handleTlbShootdownReqOnCore st c₁) c₂ =
      handleTlbShootdownReqOnCore (handleTlbShootdownReqOnCore st c₂) c₁ := by
  show ({ st with
      tlb := applyTlbInvalidations
        (applyTlbInvalidations st.tlb
          ((st.tlbShootdown.pendingOnCore c₁).map (·.op)))
        (((completeShootdownOnCore st.tlbShootdown c₁).pendingOnCore c₂).map
          (·.op)),
      tlbShootdown :=
        completeShootdownOnCore
          (completeShootdownOnCore st.tlbShootdown c₁) c₂ } : SystemState)
    = { st with
      tlb := applyTlbInvalidations
        (applyTlbInvalidations st.tlb
          ((st.tlbShootdown.pendingOnCore c₂).map (·.op)))
        (((completeShootdownOnCore st.tlbShootdown c₂).pendingOnCore c₁).map
          (·.op)),
      tlbShootdown :=
        completeShootdownOnCore
          (completeShootdownOnCore st.tlbShootdown c₂) c₁ }
  rw [completeShootdownOnCore_frame_pending st.tlbShootdown (Ne.symm h),
      completeShootdownOnCore_frame_pending st.tlbShootdown h,
      completeShootdownOnCore_comm h st.tlbShootdown,
      applyTlbInvalidations_comm]

/-- **WS-SM SM7.B**: adjacent-transposition form — swapping the first
two (distinct) targets of the handler fold changes nothing. -/
theorem foldl_handleTlbShootdownReqOnCore_swap {c₁ c₂ : CoreId}
    (h : c₁ ≠ c₂) (rest : List CoreId) (st : SystemState) :
    (c₁ :: c₂ :: rest).foldl handleTlbShootdownReqOnCore st =
      (c₂ :: c₁ :: rest).foldl handleTlbShootdownReqOnCore st := by
  simp only [List.foldl_cons]
  rw [handleTlbShootdownReqOnCore_comm h]

-- ============================================================================
-- SM7.B — Coalesced-round invalidation coverage (Theorem 3.3.1, total form)
-- ============================================================================

/-- **WS-SM SM7.B**: `.vmalle1` covers every entry — the coalescing
escape hatch's over-invalidation is total by construction. -/
@[simp] theorem tlbEntryMatches_vmalle1 (e : TlbEntry) :
    tlbEntryMatches TlbInvalidation.vmalle1 e = true := rfl

/-- **WS-SM SM7.B**: retiring a queue that *covers* a request (the
descriptor is pending, or a superseding full flush is) removes every
entry the request matches — the invalidation-effect reading of the
coalescing coverage disjunction
(`enqueueShootdownOrCoalesce_request_covered`): coalescing never loses
an invalidation, it only widens it. -/
theorem coveredQueueRetire_removes {queue : List TlbShootdownDescriptor}
    {d : TlbShootdownDescriptor}
    (hcov : d ∈ queue ∨ ∃ d' ∈ queue, d'.op = TlbInvalidation.vmalle1)
    {e : TlbEntry} (he : tlbEntryMatches d.op e = true) (t : TlbState) :
    e ∉ (applyTlbInvalidations t (queue.map (·.op))).entries := by
  rcases hcov with hmem | ⟨d', hd'mem, hd'op⟩
  · exact applyTlbInvalidations_removes (List.mem_map_of_mem hmem) he t
  · have hops : TlbInvalidation.vmalle1 ∈ queue.map (·.op) :=
      List.mem_map.mpr ⟨d', hd'mem, hd'op⟩
    exact applyTlbInvalidations_removes hops (tlbEntryMatches_vmalle1 e) t

/-- **WS-SM SM7.B** (Theorem 3.3.1, coalescing remote case): after a
live unmap commit, *whatever* the coalescing posting left on a remote
core's queue — the unmap's own descriptor or a superseding full flush
— retiring that queue removes the unmapped translation from that
core's view.  This closes the remote case for the **total** posting
path the production wrappers actually use (the strict-broadcast form
is `tlbShootdownBroadcast_invalidatesAllCores`). -/
theorem vspaceUnmapPageWithShootdown_remote_retire_removes
    (executingCore : CoreId) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    {st stFlush : SystemState}
    (h : vspaceUnmapPageWithFlush asid vaddr st = .ok ((), stFlush))
    {c : CoreId} (hc : c ≠ executingCore)
    {e : TlbEntry} (hA : e.asid = asid) (hV : e.vaddr = vaddr)
    (t : TlbState) :
    e ∉ (applyTlbInvalidations t
      (((tlbShootdownBroadcastCoalescing stFlush executingCore
          (shootdownTargets executingCore)
          (encodePageInvalidation asid vaddr)).tlbShootdown.pendingOnCore
            c).map (·.op))).entries :=
  coveredQueueRetire_removes
    (vspaceUnmapPageWithShootdown_posts executingCore asid vaddr h c hc)
    (encodePageInvalidation_matches asid vaddr hA hV) t

-- ============================================================================
-- SM7.B — Positive diff characterization + coalescing-round capstones
-- ============================================================================

/-- **WS-SM SM7.B**: positive diff characterization — a coalescing
posting from quiescence changes *exactly* the target queues, so the
runtime seam's diff recovery fires SGIs at exactly the round's
targets (the negative direction is
`shootdownChangedTargets_nil_of_eq`). -/
theorem shootdownChangedTargets_coalescing_of_quiescent
    {st : SystemState} (hq : shootdownQuiescent st.tlbShootdown)
    (initiator : CoreId) (op : TlbInvalidation) :
    shootdownChangedTargets st
      (tlbShootdownBroadcastCoalescing st initiator
        (shootdownTargets initiator) op) = shootdownTargets initiator := by
  have hpt : ∀ c ∈ allCores,
      ((tlbShootdownBroadcastCoalescing st initiator
          (shootdownTargets initiator) op).tlbShootdown.pendingOnCore c
        != st.tlbShootdown.pendingOnCore c) = (c != initiator) := by
    intro c _
    by_cases hc : c = initiator
    · subst hc
      have hframe : (tlbShootdownBroadcastCoalescing st c
          (shootdownTargets c) op).tlbShootdown.pendingOnCore c =
            st.tlbShootdown.pendingOnCore c := by
        show (postShootdownRoundCoalescing st.tlbShootdown c
          (shootdownTargets c) op).pendingOnCore c = _
        unfold postShootdownRoundCoalescing
        rw [foldl_enqueueShootdownOrCoalesce_frame_pending _ _ _
              (initiator_not_mem_shootdownTargets c),
            beginShootdownRoundFor_frame_pending]
      simp [hframe]
    · have hmem : c ∈ shootdownTargets initiator :=
        (mem_shootdownTargets_iff initiator c).mpr hc
      have hcov := postShootdownRoundCoalescing_covered st.tlbShootdown
        initiator (shootdownTargets_nodup initiator) op c hmem
      have hne : (tlbShootdownBroadcastCoalescing st initiator
          (shootdownTargets initiator) op).tlbShootdown.pendingOnCore c ≠
            st.tlbShootdown.pendingOnCore c := by
        rw [hq.1 c]
        rcases hcov with hmem' | ⟨d', hd'mem, _⟩
        · exact List.ne_nil_of_mem hmem'
        · exact List.ne_nil_of_mem hd'mem
      have h1 : ((tlbShootdownBroadcastCoalescing st initiator
          (shootdownTargets initiator) op).tlbShootdown.pendingOnCore c
            != st.tlbShootdown.pendingOnCore c) = true := by
        rw [bne_iff_ne]; exact hne
      have h2 : (c != initiator) = true := by
        rw [bne_iff_ne]; exact hc
      rw [h1, h2]
  exact List.filter_congr hpt

/-- **WS-SM SM7.B** (coalescing-round capstone, quiescence half): the
complete round the runtime actually executes — total coalescing
posting, initiator-local retirement, handler catch-up fold over the
targets — restores quiescence from quiescence.  This is the
`completeShootdownRounds` catch-up commit's discharge: after the fold,
every queue is empty and every flag acknowledged, so the *next* round
posts into empty queues (the §4.1 capacity-sufficiency induction,
closed for the coalescing path). -/
theorem coalescingRound_restores_quiescent {st : SystemState}
    (hq : shootdownQuiescent st.tlbShootdown) (initiator : CoreId)
    (op : TlbInvalidation) :
    shootdownQuiescent
      ((shootdownTargets initiator).foldl handleTlbShootdownReqOnCore
        (tlbShootdownLocal
          (tlbShootdownBroadcastCoalescing st initiator
            (shootdownTargets initiator) op) op)).tlbShootdown := by
  obtain ⟨⟨posted, sgis⟩, hb⟩ := Option.isSome_iff_exists.mp
    (tlbShootdownBroadcast_isSome_of_quiescent hq initiator
      (shootdownTargets_nodup initiator) op)
  rw [tlbShootdownBroadcastCoalescing_eq_strict hb]
  exact shootdownRound_quiescent hq
    (by unfold shootdownRound; rw [hb])

/-- **WS-SM SM7.B** (coalescing-round capstone, exit-condition half):
the complete coalescing round reaches `allAcked` — the bounded wait's
exit condition is realised by the round the runtime actually runs. -/
theorem coalescingRound_allAcked {st : SystemState}
    (hq : shootdownQuiescent st.tlbShootdown) (initiator : CoreId)
    (op : TlbInvalidation) :
    allAcked
      ((shootdownTargets initiator).foldl handleTlbShootdownReqOnCore
        (tlbShootdownLocal
          (tlbShootdownBroadcastCoalescing st initiator
            (shootdownTargets initiator) op) op)).tlbShootdown := by
  obtain ⟨⟨posted, sgis⟩, hb⟩ := Option.isSome_iff_exists.mp
    (tlbShootdownBroadcast_isSome_of_quiescent hq initiator
      (shootdownTargets_nodup initiator) op)
  rw [tlbShootdownBroadcastCoalescing_eq_strict hb]
  exact shootdownRound_allAcked hq
    (by unfold shootdownRound; rw [hb])
end SeLe4n.Kernel.Architecture
