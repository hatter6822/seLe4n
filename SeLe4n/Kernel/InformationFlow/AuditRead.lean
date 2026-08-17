/-
Copyright (c) 2025 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license.

WS-SM SM9.A: the declassification audit trail's **reader**.

SM8.C mounted a durable, bounded, fail-closed audit trail and shipped the live
`.declassify` syscall that writes it.  Nothing read it.  That is not merely an
absent convenience: the capacity bound is fail-closed, so a deployment that
performs `maxDeclassificationAuditEntries` authorized downgrades **stops being
able to declassify at all** until reboot.  A write-only trail with a hard cap is
a feature that disables itself.

This module is the read side, and everything in it is shaped by one question —
*what may a given reader learn?*

## The three gates, and why they are three

1. **A capability**, not a right.  `syscallLookupCap` checks
   `cap.hasRight gate.requiredRight` and **nothing about `cap.target`**, so a
   reader gated only on `.read` would be reachable by any thread holding any
   readable capability, which in practice is every thread (its own TCB
   suffices).  That is exactly the confused deputy closed at v0.32.97.  The
   authority is therefore a dedicated `CapTarget.auditTrail` capability
   (`API.extractAuditAuthority`), and an unconfigured deployment — one whose
   boot/CSpace layer mints none — has no audit reader at all.
2. **The reader's own clearance**, which selects *which entries* it sees.
   `auditLogVisibleTo` is a re-indexed filtered sublist, never a sparse global
   index, so the **count** of hidden entries cannot leak through index gaps.
3. **A configured monitor clearance**, which selects *what kind of identity*
   it gets and whether it may drain.  This is a deployment parameter
   (`LabelingContext.auditMonitorClearance`), deny-by-default, and deliberately
   **not** a predicate over the rows the trail currently holds — see
   `auditMonitorGate_records_derived_unsound`.

## Two classes of reader

|                        | Partial reader             | Fully-dominating monitor |
|------------------------|----------------------------|--------------------------|
| Entry identity         | **view-local index**       | **global timestamp**     |
| `status` generation    | none (always `0`)          | the global epoch         |
| Drain                  | refused                    | permitted                |
| Retry guarantee        | none promised              | `auditRead_stable_under_append` |

The split is forced.  A `DeclassificationEvent`'s timestamp is its *global*
position, so handing it to a partial reader tells that reader how many entries
preceded the one it can see — hidden ones included.  But exporting view-local
indices to *everyone* breaks the other side: a monitor correlating an event with
an archived predecessor needs an identity that survives a drain.  So the
protocol gives each reader the identity its clearance justifies.

## Why the reader chunks

Four exported fields are unbounded `Nat` in the model (`SecurityDomain.id`,
`ObjId.val`, the timestamp) and the fifth is a string, while a syscall returns
one word.  Each is therefore read through a fixed-width chunk protocol whose
theorem is **reconstruction** — folding the chunks recovers the value exactly —
rather than "each fragment fits", which says nothing about whether the record
can be rebuilt from the fragments.

The chunk *coordinates* are themselves single words, so "total for any `Nat`"
was never available: a value needing 2^64 chunks cannot have its own count
returned in one word.  The export is therefore **structurally bounded** and
**fails closed** above the bound (`.auditFieldTooLarge`), which makes
`auditReadField_reconstructs` a total theorem about a bounded domain rather than
a false theorem about an unbounded one.

## Why `status` is one call

A draft chunked `status` as well.  That trades *aliasing after ~2^55 drains* for
*tearing on the very first interleaved one*: a drain landing between two chunk
calls yields a generation assembled from two different states, corresponding to
no generation that ever existed.  So `status` returns in one call with both
components structurally bounded, and the retry theorem carries an explicit
`noGenerationWrap` premise rather than a silent assumption — a premise that is
written down is the honest form of a bound that cannot be made unconditional.

## What this module deliberately does not do

It adds **no kernel→user memory write path**.  A write mirror of `ipcBufferReadMr`
is feasible, but it would grow the trusted computing base — and note that
`ipcBufferReadMr` ignores `PagePermissions` entirely, which a write path must
not.  A monitor draining a 256-entry trail does not need the throughput.
Recorded as a deliberate non-goal, revisitable if throughput ever demands it.
-/
import SeLe4n.Kernel.InformationFlow.Declassification

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)

-- ============================================================================
-- §1  SM9.A.1 — the clearance-filtered, re-indexed visible view
-- ============================================================================

/-- WS-SM SM9.A.1: **what a reader at domain `reader` may see of a trail.**

An entry records a release *of* `srcDomain`'s information, so the clearance that
justifies reading it is the clearance to receive from `srcDomain`: the filter
keeps exactly the entries whose source the reader dominates.

`List.filter`, so the result is a genuine **sublist in the original order** and
is re-indexed from `0` — not a sparse view of the global trail.  That is the
whole no-gap-leak argument: a reader indexes its own view, so it cannot count
the entries between two visible ones, and `auditLogVisibleTo_hidden_insert` says
inserting an entry it cannot see leaves its view literally unchanged. -/
def auditLogVisibleTo (ctx : GenericLabelingContext) (reader : SecurityDomain)
    (log : DeclassificationAuditLog) : DeclassificationAuditLog :=
  log.filter (fun e => ctx.policy.canFlow e.srcDomain reader)

/-- WS-SM SM9.A.1: the empty trail is empty in every view. -/
@[simp] theorem auditLogVisibleTo_nil (ctx : GenericLabelingContext)
    (reader : SecurityDomain) :
    auditLogVisibleTo ctx reader [] = [] := rfl

/-- WS-SM SM9.A.1: the visible view is a sublist of the trail — order preserved,
nothing invented.  The template is `auditLogOnCore_sublist`. -/
theorem auditLogVisibleTo_sublist (ctx : GenericLabelingContext)
    (reader : SecurityDomain) (log : DeclassificationAuditLog) :
    (auditLogVisibleTo ctx reader log).Sublist log :=
  List.filter_sublist

/-- WS-SM SM9.A.1: a reader never sees more entries than the trail holds. -/
theorem auditLogVisibleTo_length_le (ctx : GenericLabelingContext)
    (reader : SecurityDomain) (log : DeclassificationAuditLog) :
    (auditLogVisibleTo ctx reader log).length ≤ log.length :=
  (auditLogVisibleTo_sublist ctx reader log).length_le

/-- WS-SM SM9.A.1: membership in the view is membership in the trail **and**
clearance — the characterisation every downstream proof travels along. -/
theorem mem_auditLogVisibleTo_iff (ctx : GenericLabelingContext)
    (reader : SecurityDomain) (log : DeclassificationAuditLog)
    (e : DeclassificationEvent) :
    e ∈ auditLogVisibleTo ctx reader log ↔
      e ∈ log ∧ ctx.policy.canFlow e.srcDomain reader = true := by
  simp [auditLogVisibleTo, List.mem_filter]

/-- WS-SM SM9.A.1: a visible entry is one the reader is cleared for. -/
theorem auditLogVisibleTo_cleared (ctx : GenericLabelingContext)
    (reader : SecurityDomain) (log : DeclassificationAuditLog)
    {e : DeclassificationEvent} (h : e ∈ auditLogVisibleTo ctx reader log) :
    ctx.policy.canFlow e.srcDomain reader = true :=
  ((mem_auditLogVisibleTo_iff ctx reader log e).mp h).2

/-- WS-SM SM9.A.1: the view distributes over append — the half
`auditRead_stable_under_append` (SM9.A.5) is built from. -/
theorem auditLogVisibleTo_append (ctx : GenericLabelingContext)
    (reader : SecurityDomain) (log extra : DeclassificationAuditLog) :
    auditLogVisibleTo ctx reader (log ++ extra) =
      auditLogVisibleTo ctx reader log ++ auditLogVisibleTo ctx reader extra := by
  simp [auditLogVisibleTo, List.filter_append]

/-- WS-SM SM9.A.1 (**the no-gap-leak theorem**): inserting an entry the reader
cannot see — *anywhere* in the trail — leaves that reader's view **literally
unchanged**.

This is the property a sparse global index would not have.  Under sparse
indexing the reader's own indices would shift, and the shift would tell it both
that a hidden entry exists and exactly where it sits; repeated observations
would enumerate the hidden layout.  Re-indexing removes the case rather than
mitigating it. -/
theorem auditLogVisibleTo_hidden_insert (ctx : GenericLabelingContext)
    (reader : SecurityDomain) (pre post : DeclassificationAuditLog)
    (e : DeclassificationEvent)
    (hHidden : ctx.policy.canFlow e.srcDomain reader = false) :
    auditLogVisibleTo ctx reader (pre ++ e :: post) =
      auditLogVisibleTo ctx reader (pre ++ post) := by
  simp [auditLogVisibleTo, List.filter_append, hHidden]

/-- WS-SM SM9.A.1: **the view is a function of the reader's clearance alone.**

Two readers the policy treats identically on the trail's sources see the same
entries — the view depends on no other property of the reader (not its identity,
not its core, not what it has read before).  The formal content of "the visible
view is a function of the reader's clearance". -/
theorem auditLogVisibleTo_determined_by_clearance (ctx : GenericLabelingContext)
    (r₁ r₂ : SecurityDomain) (log : DeclassificationAuditLog)
    (hAgree : ∀ e ∈ log, ctx.policy.canFlow e.srcDomain r₁ =
      ctx.policy.canFlow e.srcDomain r₂) :
    auditLogVisibleTo ctx r₁ log = auditLogVisibleTo ctx r₂ log := by
  unfold auditLogVisibleTo
  exact List.filter_congr (fun e he => by rw [hAgree e he])

/-- WS-SM SM9.A.1: filtering twice is filtering once — the view of a view is the
view, so a reader handed its own view learns nothing further. -/
@[simp] theorem auditLogVisibleTo_idempotent (ctx : GenericLabelingContext)
    (reader : SecurityDomain) (log : DeclassificationAuditLog) :
    auditLogVisibleTo ctx reader (auditLogVisibleTo ctx reader log) =
      auditLogVisibleTo ctx reader log := by
  simp [auditLogVisibleTo, List.filter_filter]

/-- WS-SM SM9.A.1: a reader dominating **every** source in the trail sees all of
it.  The bridge between the clearance filter and the drain's full-dominance
requirement (§5). -/
theorem auditLogVisibleTo_eq_self (ctx : GenericLabelingContext)
    (reader : SecurityDomain) (log : DeclassificationAuditLog)
    (hAll : ∀ e ∈ log, ctx.policy.canFlow e.srcDomain reader = true) :
    auditLogVisibleTo ctx reader log = log :=
  List.filter_eq_self.mpr hAll

/-- WS-SM SM9.A.1: the entry a reader's index `i` names, `none` past the end of
its own view.  Deliberately indexes the **view**, never the trail. -/
def auditVisibleEntry? (ctx : GenericLabelingContext) (reader : SecurityDomain)
    (log : DeclassificationAuditLog) (i : Nat) : Option DeclassificationEvent :=
  (auditLogVisibleTo ctx reader log)[i]?

/-- WS-SM SM9.A.1: an indexed entry is a visible one. -/
theorem auditVisibleEntry?_mem (ctx : GenericLabelingContext) (reader : SecurityDomain)
    (log : DeclassificationAuditLog) (i : Nat) {e : DeclassificationEvent}
    (h : auditVisibleEntry? ctx reader log i = some e) :
    e ∈ auditLogVisibleTo ctx reader log :=
  List.mem_of_getElem? h

-- ============================================================================
-- §2  SM9.A / plan §3.4 — the single privileged-reader gate
-- ============================================================================

/-! ## One gate, computed from configuration

Drain, global entry identity and (from SM9.B) the refusal ledger all need the
same question answered: *is this caller the deployment's audit monitor?*  There
is exactly **one** gate for all of them, and it is computed from a configured
deployment parameter rather than from the trail's current contents.

The tempting alternative — "the caller dominates every `srcDomain` currently
recorded" — is unsound, and unsound in the direction that matters.  Drain a
trail to `[]` and that predicate becomes **vacuously true**, so a low
audit-capability holder is classified as a fully-dominating monitor and reads
the global epoch, which counts precisely the entries the drain removed.  A
predicate over rows that drains delete cannot gate access to a quantity that
drains preserve.  `auditMonitorGate_records_derived_unsound` keeps that
counterexample refuted so a later cut cannot revert to the cheaper gate. -/

/-- WS-SM SM9.A (plan §3.4): **is `reader` the configured audit monitor?**

`monitorClearance` is the deployment's `LabelingContext.auditMonitorClearance`:
`none` when unset, which denies every caller — the same deny-by-default posture
`LabelingContext.declassificationPolicy` already has.  When set to `m`, a caller
qualifies iff it dominates `m`, i.e. information may flow `m → reader`.

The operator obligation that makes this a *full-dominance* gate rather than an
arbitrary one is `auditMonitorClearanceIsTop`: `m` must be a domain everything
flows to.  It is a property of the configuration, so unlike a records-derived
predicate it cannot be weakened by activity. -/
def auditMonitorAuthorized (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (reader : SecurityDomain) : Bool :=
  match monitorClearance with
  | none => false
  | some m => ctx.policy.canFlow m reader

/-- WS-SM SM9.A: **an unconfigured deployment has no audit monitor.**  Nothing
drains, nothing reads a global identity, and the 256-entry cliff stays — which
is the conservative default, not an oversight. -/
@[simp] theorem auditMonitorAuthorized_unconfigured (ctx : GenericLabelingContext)
    (reader : SecurityDomain) :
    auditMonitorAuthorized ctx none reader = false := rfl

/-- WS-SM SM9.A (the operator obligation): the configured monitor clearance is a
**top** of the flow policy — everything flows to it.

Stated as a property of the *configuration* rather than of the trail.  A
deployment that sets `auditMonitorClearance` to a domain some other domain does
not flow to has an audit monitor that cannot see everything, and this predicate
is what such a deployment fails. -/
def auditMonitorClearanceIsTop (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) : Prop :=
  ∃ m, monitorClearance = some m ∧ ∀ d : SecurityDomain, ctx.policy.canFlow d m = true

/-- WS-SM SM9.A: **a qualifying caller under a well-formed configuration
dominates every domain.**  Transitivity does the work: everything flows to the
configured clearance, and the clearance flows to the caller. -/
theorem auditMonitorAuthorized_dominates_all (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (reader : SecurityDomain)
    (hTop : auditMonitorClearanceIsTop ctx monitorClearance)
    (hTrans : ctx.policy.isTransitive)
    (hGate : auditMonitorAuthorized ctx monitorClearance reader = true) :
    ∀ d : SecurityDomain, ctx.policy.canFlow d reader = true := by
  obtain ⟨m, hm, hAll⟩ := hTop
  subst hm
  intro d
  exact hTrans d m reader (hAll d) hGate

/-- WS-SM SM9.A: the reader's own clearance — the domain of the subject the
executing core is running.  `none` on an idle core, which fails closed
everywhere it is consulted (the same posture as
`declassifyObjectFromCore_no_subject`). -/
def auditReaderDomain (ctx : GenericLabelingContext) (st : SystemState)
    (c : CoreId) : Option SecurityDomain :=
  (st.scheduler.currentOnCore c).map ctx.threadDomainOf

/-- WS-SM SM9.A: the state-level monitor gate the drain consults. -/
def auditMonitorGate (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (st : SystemState) (c : CoreId) : Bool :=
  match auditReaderDomain ctx st c with
  | none => false
  | some d => auditMonitorAuthorized ctx monitorClearance d

/-- WS-SM SM9.A: an idle core is not a monitor — there is no subject whose
clearance could qualify. -/
theorem auditMonitorGate_idle (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (st : SystemState) (c : CoreId)
    (hIdle : st.scheduler.currentOnCore c = none) :
    auditMonitorGate ctx monitorClearance st c = false := by
  simp [auditMonitorGate, auditReaderDomain, hIdle]

/-- WS-SM SM9.A (**the gate is configuration-derived**): moving the trail and
the epoch — by any amount, in either direction — does not move the gate's
verdict.

This is the property a records-derived gate lacks, stated over exactly the two
fields a drain writes.  It is what lets drain, the global identity export and
(from SM9.B) the refusal ledger share one gate without any of them inheriting a
predicate that ages out from under it. -/
theorem auditMonitorGate_is_configuration_derived (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (st : SystemState) (c : CoreId)
    (log : DeclassificationAuditLog) (epoch : Nat) :
    auditMonitorGate ctx monitorClearance
        { st with declassificationAuditLog := log, declassificationAuditEpoch := epoch } c =
      auditMonitorGate ctx monitorClearance st c := rfl

/-- WS-SM SM9.A (**the load-bearing negative**): a gate computed from the rows
the trail currently holds is **unsound**, and the drained-to-empty case is why.

The witness runs the whole story: a trail holding one `high`-sourced entry, a
`low` reader, and the linear-order policy.  Before the drain the rows-derived
predicate refuses the reader — there is an entry it cannot see.  After draining
that one entry the predicate is **vacuously true**, so the reader is
reclassified as a fully-dominating monitor and would be handed the global epoch
that counts the very entry just removed.  The configured gate refuses it
throughout, because it never looked at the rows.

Kept as a theorem rather than as prose so that a later cut cannot quietly revert
to the cheaper gate: doing so makes this statement unprovable. -/
theorem auditMonitorGate_records_derived_unsound :
    ∃ (ctx : GenericLabelingContext) (monitorClearance : Option SecurityDomain)
      (reader : SecurityDomain) (logBefore : DeclassificationAuditLog) (drained : Nat),
      (∃ e ∈ logBefore, ctx.policy.canFlow e.srcDomain reader = false) ∧
      (∀ e ∈ logBefore.drop drained, ctx.policy.canFlow e.srcDomain reader = true) ∧
      auditMonitorAuthorized ctx monitorClearance reader = false := by
  refine ⟨{ policy := DomainFlowPolicy.linearOrder
            objectDomainOf := fun _ => SecurityDomain.lowest
            threadDomainOf := fun _ => SecurityDomain.lowest
            endpointDomainOf := fun _ => SecurityDomain.lowest
            serviceDomainOf := fun _ => SecurityDomain.lowest },
          some ⟨3⟩, ⟨0⟩,
          [{ auditTimestampWitness 0 with srcDomain := ⟨3⟩ }], 1, ?_, ?_, ?_⟩
  · exact ⟨{ auditTimestampWitness 0 with srcDomain := ⟨3⟩ }, by simp, by decide⟩
  · decide
  · decide

-- ============================================================================
-- §3  SM9.A.2 — the chunk protocol
-- ============================================================================

/-! ## Exporting an unbounded value through a one-word channel

A syscall returns one word; four of the exported fields are unbounded `Nat` in
the model and the fifth is a string.  The protocol is positional base-2^32:
`fieldChunkCount` asks how many chunks a value needs, `field … chunk` returns
one of them, and `auditReadField_reconstructs` says folding them back recovers
the value **exactly**.

Two design points are load-bearing rather than incidental.

*The bound is structural.*  The chunk coordinates are themselves single words,
so a protocol claiming to export any `Nat` cannot be honest — a value needing
2^64 chunks has no representable count.  Chasing that with a cursor protocol
would need per-caller kernel state, which is not constructible (see
`observerScopedGeneration_not_mountable`).  So the export is capped at
`maxAuditFieldChunks` and **fails closed** above it.  `auditFieldBound_unreachable_in_kernel`
states the concrete inequality that makes the cap unreachable in practice, and
the reader still refuses rather than truncating, so the worst case is a refused
read and never a silently wrong value.

*A fixed low/high pair was drafted and is wrong.*  Two 32-bit chunks bound a
field at 2^64, so values differing above bit 63 produce identical chunks: it
moves the truncation point rather than removing it.  Proving each fragment
survives the boundary says nothing about whether the record can be rebuilt from
the fragments, and conflating the two is what made the two-chunk design look
adequate. -/

/-- WS-SM SM9.A.2: the chunk radix — 32 bits, so a chunk is a `UInt32`-sized
payload inside the 64-bit return word. -/
def auditFieldChunkModulus : Nat := 4294967296

/-- WS-SM SM9.A.2: the exported width, in chunks.  Four 32-bit chunks is 128
bits (`auditFieldExportBound`), which `auditFieldBound_unreachable_in_kernel`
shows no kernel-reachable value attains. -/
def maxAuditFieldChunks : Nat := 4

/-- WS-SM SM9.A.2: `2^128`, the first value the reader refuses to export. -/
theorem auditFieldExportBound :
    auditFieldChunkModulus ^ maxAuditFieldChunks = 2 ^ 128 := by decide

/-- WS-SM SM9.A.2: the radix is a genuine radix. -/
theorem auditFieldChunkModulus_gt_one : 1 < auditFieldChunkModulus := by decide

/-- WS-SM SM9.A.2: chunk `i` of `v`, little-endian in base `auditFieldChunkModulus`. -/
def auditFieldChunk (v i : Nat) : Nat :=
  (v / auditFieldChunkModulus ^ i) % auditFieldChunkModulus

/-- WS-SM SM9.A.2: how many chunks `v` needs, or `none` above the exported
width.  Structural on the fuel, so the cap is the fuel and there is no
well-founded recursion to discharge. -/
def auditChunkCountUpTo : Nat → Nat → Option Nat
  | 0, _ => none
  | k + 1, v =>
      if v < auditFieldChunkModulus then some 1
      else (auditChunkCountUpTo k (v / auditFieldChunkModulus)).map (· + 1)

/-- WS-SM SM9.A.2: the reader's chunk count — `none` is the fail-closed
`.auditFieldTooLarge` arm. -/
def auditFieldChunkCount? (v : Nat) : Option Nat :=
  auditChunkCountUpTo maxAuditFieldChunks v

/-- WS-SM SM9.A.2: fold `n` chunks back into a value, little-endian. -/
def auditFoldChunks : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => f 0 + auditFieldChunkModulus * auditFoldChunks n (fun i => f (i + 1))

/-- WS-SM SM9.A.2: a reported chunk count bounds the value it was computed
from — the invariant that makes the fold total. -/
theorem auditChunkCountUpTo_lt : ∀ (k v n : Nat),
    auditChunkCountUpTo k v = some n → v < auditFieldChunkModulus ^ n := by
  intro k
  induction k with
  | zero => intro v n h; simp [auditChunkCountUpTo] at h
  | succ k ih =>
    intro v n h
    unfold auditChunkCountUpTo at h
    split at h
    · rename_i hLt
      have : n = 1 := by simpa using h.symm
      subst this
      simpa using hLt
    · rename_i hGe
      obtain ⟨m, hm, hn⟩ := Option.map_eq_some_iff.mp h
      subst hn
      have hDiv := ih _ _ hm
      have hMod : 0 < auditFieldChunkModulus := by decide
      rw [Nat.pow_succ]
      exact (Nat.div_lt_iff_lt_mul hMod).mp hDiv

/-- WS-SM SM9.A.2: the chunk count exists exactly below the exported width —
the fail-closed characterisation, stated over the fuel so the cap is a
parameter. -/
theorem auditChunkCountUpTo_isSome_iff : ∀ (k v : Nat),
    (auditChunkCountUpTo k v).isSome = true ↔
      (0 < k ∧ v < auditFieldChunkModulus ^ k) := by
  intro k
  induction k with
  | zero => intro v; simp [auditChunkCountUpTo]
  | succ k ih =>
    intro v
    unfold auditChunkCountUpTo
    split
    · rename_i hLt
      have hle : auditFieldChunkModulus ^ 1 ≤ auditFieldChunkModulus ^ (k + 1) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      simp only [Option.isSome_some, true_iff]
      refine ⟨by omega, ?_⟩
      have : auditFieldChunkModulus ≤ auditFieldChunkModulus ^ (k + 1) := by
        simpa using hle
      omega
    · rename_i hGe
      have hGe' : auditFieldChunkModulus ≤ v := by omega
      have hMod : 0 < auditFieldChunkModulus := by decide
      simp only [Option.isSome_map, ih]
      constructor
      · rintro ⟨hk, hDiv⟩
        refine ⟨by omega, ?_⟩
        rw [Nat.pow_succ]
        exact (Nat.div_lt_iff_lt_mul hMod).mp hDiv
      · rintro ⟨-, hLt⟩
        rw [Nat.pow_succ] at hLt
        have hDiv : v / auditFieldChunkModulus < auditFieldChunkModulus ^ k :=
          (Nat.div_lt_iff_lt_mul hMod).mpr hLt
        refine ⟨?_, hDiv⟩
        rcases Nat.eq_zero_or_pos k with hk | hk
        · subst hk
          rw [Nat.pow_zero] at hDiv
          have hOne : 1 ≤ v / auditFieldChunkModulus :=
            (Nat.one_le_div_iff hMod).mpr hGe'
          omega
        · exact hk

/-- WS-SM SM9.A.2: the reader accepts exactly the values below `2^128`. -/
theorem auditFieldChunkCount?_isSome_iff (v : Nat) :
    (auditFieldChunkCount? v).isSome = true ↔ v < 2 ^ 128 := by
  rw [auditFieldChunkCount?, auditChunkCountUpTo_isSome_iff, ← auditFieldExportBound]
  simp [maxAuditFieldChunks]

/-- WS-SM SM9.A.2 (**fail-closed above the width**): a value at or above `2^128`
is **refused**, not truncated. -/
theorem auditFieldChunkCount?_none_iff (v : Nat) :
    auditFieldChunkCount? v = none ↔ 2 ^ 128 ≤ v := by
  rw [← Nat.not_lt, ← auditFieldChunkCount?_isSome_iff]
  cases h : auditFieldChunkCount? v <;> simp

/-- WS-SM SM9.A.2 (**the losslessness theorem**): folding a value's chunks
recovers the value **exactly**, over the whole domain the reader accepts.

Unconditional on that domain — which is the honest shape.  A theorem quantified
over every `Nat` would be false (the count is not representable); a theorem
about "each chunk fits a word" would be true and useless.  This one says the
record can be *rebuilt*. -/
theorem auditFoldChunks_auditFieldChunk : ∀ (n v : Nat),
    v < auditFieldChunkModulus ^ n →
    auditFoldChunks n (fun i => auditFieldChunk v i) = v := by
  intro n
  induction n with
  | zero =>
    intro v h
    rw [Nat.pow_zero] at h
    simp only [auditFoldChunks]
    omega
  | succ n ih =>
    intro v h
    have hMod : 0 < auditFieldChunkModulus := by decide
    have hShift : (fun i => auditFieldChunk v (i + 1))
        = (fun i => auditFieldChunk (v / auditFieldChunkModulus) i) := by
      funext i
      unfold auditFieldChunk
      rw [Nat.pow_succ,
        Nat.mul_comm (auditFieldChunkModulus ^ i) auditFieldChunkModulus,
        ← Nat.div_div_eq_div_mul]
    have hDiv : v / auditFieldChunkModulus < auditFieldChunkModulus ^ n := by
      rw [Nat.pow_succ] at h
      exact (Nat.div_lt_iff_lt_mul hMod).mpr h
    simp only [auditFoldChunks, hShift, ih _ hDiv]
    have h0 : auditFieldChunk v 0 = v % auditFieldChunkModulus := by
      simp [auditFieldChunk]
    rw [h0]
    exact Nat.mod_add_div v auditFieldChunkModulus

/-- WS-SM SM9.A.2: the consumer-facing form — whatever chunk count the reader
reports, folding that many chunks recovers the value. -/
theorem auditReadField_reconstructs (v n : Nat)
    (hCount : auditFieldChunkCount? v = some n) :
    auditFoldChunks n (fun i => auditFieldChunk v i) = v :=
  auditFoldChunks_auditFieldChunk n v
    (auditChunkCountUpTo_lt maxAuditFieldChunks v n hCount)

/-- WS-SM SM9.A.2: **the exported width is unreachable in the kernel.**

The cap is arithmetic, not a hope — and this matters most for the timestamp,
which is `epoch + index` over an epoch every drain advances, so "bounded in
practice" is not available the way it is for object ids.  Reaching the cap would
need `2^128` recorded downgrades; at one per nanosecond that is on the order of
`10^22` years.  The reader still fails closed above it, so the worst case is a
refused read rather than a silently truncated identity. -/
theorem auditFieldBound_unreachable_in_kernel (epoch : Nat)
    (hEpoch : epoch + maxDeclassificationAuditEntries < 2 ^ 128) :
    ∀ i < maxDeclassificationAuditEntries,
      (auditFieldChunkCount? (epoch + i)).isSome = true := by
  intro i hi
  rw [auditFieldChunkCount?_isSome_iff]
  omega

-- ============================================================================
-- §3b  SM9.A.2 — the authorization basis's designation
-- ============================================================================

/-! ## Why the designation is exported at all

`DeclassificationBasis` is a designation paired with a trust bit, and
`renderTagged_injective` is why the pair rather than either half is what an
audit consumer should read.  Exporting the **bit alone** would collapse every
`integratorOverride` to one externally-readable value, leaving a monitor unable
to say *which* out-of-band authority permitted an event — the question that
record exists to answer.  Structurally excluding integrator-authored entries
from readable trails was the alternative and is worse: those are exactly the
entries a monitor most needs to see.

So the designation is a chunked field like the others, four UTF-8 bytes per
32-bit chunk, with its own cap (`maxAuditDesignationBytes`) because a
designation is a string rather than a counter and the numeric cap would be
absurd for it.  `auditReadBasis_reconstructs_designation` is the reconstruction
theorem, and it is a genuine one: it relates two *different* functions (the
packer and the extractor), so it fails if either moves. -/

/-- WS-SM SM9.A.2: the bytes of an event's authorization-basis designation. -/
def auditBasisBytes (e : DeclassificationEvent) : List UInt8 :=
  e.authorizationBasis.render.toUTF8.toList

/-- WS-SM SM9.A.2: the exported designation width, in bytes. -/
def maxAuditDesignationBytes : Nat := 256

/-- WS-SM SM9.A.2: bytes per exported chunk. -/
def auditDesignationBytesPerChunk : Nat := 4

/-- WS-SM SM9.A.2: chunk `i` of a byte list, four bytes little-endian.  Bytes
past the end read as `0`, which is why the byte **count** is exported
separately: a trailing NUL is a legal `String` character, so chunk padding is
not self-delimiting. -/
def auditBasisChunkValue (bs : List UInt8) (i : Nat) : Nat :=
  (bs.getD (4 * i) 0).toNat
    + 256 * (bs.getD (4 * i + 1) 0).toNat
    + 65536 * (bs.getD (4 * i + 2) 0).toNat
    + 16777216 * (bs.getD (4 * i + 3) 0).toNat

/-- WS-SM SM9.A.2: byte `k` of a chunk value, `k < 4`. -/
def auditBasisByteOfChunk (chunkValue k : Nat) : Nat :=
  (chunkValue / 256 ^ k) % 256

/-- WS-SM SM9.A.2: how many chunks a designation of `n` bytes occupies. -/
def auditBasisChunkCount (n : Nat) : Nat := (n + 3) / 4

/-- WS-SM SM9.A.2 (**the designation's losslessness theorem**): extracting byte
`j % 4` from chunk `j / 4` returns byte `j` of the designation, for every byte
the reader is told exists.

Relates the packer to the extractor rather than restating either — the failure
mode `retypeIcacheOp_cleans_scrub_extent` hit at v0.32.101 and the splice arm hit
again at v0.33.16.  Move either function and this stops elaborating. -/
theorem auditReadBasis_reconstructs_designation (bs : List UInt8) (j : Nat) :
    auditBasisByteOfChunk (auditBasisChunkValue bs (j / 4)) (j % 4) =
      (bs.getD j 0).toNat := by
  have hb : ∀ i : Nat, (bs.getD i 0).toNat < 256 := fun i => (bs.getD i 0).toNat_lt_size
  obtain ⟨q, r, hr, hjq⟩ : ∃ q r, r < 4 ∧ j = 4 * q + r :=
    ⟨j / 4, j % 4, by omega, by omega⟩
  subst hjq
  have hq : (4 * q + r) / 4 = q := by omega
  have hrr : (4 * q + r) % 4 = r := by omega
  rw [hq, hrr]
  unfold auditBasisByteOfChunk auditBasisChunkValue
  have h0 := hb (4 * q)
  have h1 := hb (4 * q + 1)
  have h2 := hb (4 * q + 2)
  have h3 := hb (4 * q + 3)
  have hr4 : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases hr4 with rfl | rfl | rfl | rfl
  · simp only [Nat.add_zero, Nat.pow_zero]; omega
  · simp only [Nat.pow_one]; omega
  · simp only [show (256 : Nat) ^ 2 = 65536 from rfl]; omega
  · simp only [show (256 : Nat) ^ 3 = 16777216 from rfl]; omega

-- ============================================================================
-- §3c  SM9.A.2 — the status word
-- ============================================================================

/-! ## One call, because chunking `status` tears

A draft packed the visible length and the drain generation into one word and
noted the aliasing once the generation grows past the payload.  The obvious
repair — chunk `status` too — is **worse**: a multi-call read is not atomic, so a
drain landing between two chunk calls yields a generation assembled from two
different states, corresponding to no generation that ever existed.  Chunking
traded *aliasing after ~2^55 drains* for *tearing on the very first one*
(`auditStatusSplitRead_tears`).

So `status` returns in one call with both components structurally bounded: the
visible length by `maxDeclassificationAuditEntries`, and the generation by an
explicitly **stated** `noGenerationWrap` premise on the retry theorem.  A premise
that is written down is the honest form of a bound that cannot be made
unconditional. -/

/-- WS-SM SM9.A.2: the low field of the status word — nine bits, which holds
`maxDeclassificationAuditEntries` with room to spare. -/
def auditStatusLengthSlots : Nat := 512

/-- WS-SM SM9.A.2: the visible length fits the low field with room to spare. -/
theorem auditStatusLengthSlots_bounds_capacity :
    maxDeclassificationAuditEntries < auditStatusLengthSlots := by decide

/-- WS-SM SM9.A.2: the status word — visible length in the low field, the drain
generation above it. -/
def auditStatusWord (visibleLength generation : Nat) : Nat :=
  visibleLength + generation * auditStatusLengthSlots

/-- WS-SM SM9.A.2: decode the visible length. -/
def auditStatusVisibleLength (w : Nat) : Nat := w % auditStatusLengthSlots

/-- WS-SM SM9.A.2: decode the drain generation. -/
def auditStatusGeneration (w : Nat) : Nat := w / auditStatusLengthSlots

/-- WS-SM SM9.A.2: the status word determines both components — one word, one
state. -/
theorem auditStatusWord_roundtrip (visibleLength generation : Nat)
    (hLen : visibleLength < auditStatusLengthSlots) :
    auditStatusVisibleLength (auditStatusWord visibleLength generation) = visibleLength ∧
    auditStatusGeneration (auditStatusWord visibleLength generation) = generation := by
  unfold auditStatusVisibleLength auditStatusGeneration auditStatusWord auditStatusLengthSlots
  unfold auditStatusLengthSlots at hLen
  omega

/-- WS-SM SM9.A.2 (**the stated bound**): with the visible length within capacity
and the generation below `2^55`, the status word fits the 64-bit return
register.  `noGenerationWrap` is this premise, and it is a premise rather than a
theorem because the epoch is an unbounded monotone counter. -/
theorem auditStatusWord_fits (visibleLength generation : Nat)
    (hLen : visibleLength ≤ maxDeclassificationAuditEntries)
    (hGen : generation < 2 ^ 55) :
    auditStatusWord visibleLength generation < 2 ^ 64 := by
  unfold auditStatusWord auditStatusLengthSlots
  unfold maxDeclassificationAuditEntries at hLen
  omega

-- ============================================================================
-- §4  SM9.A.2 / plan §3.7 — read operations, fused with the structure they read
-- ============================================================================

/-! ## The completeness gate a new readable structure cannot decline to join

The obvious mechanisation of the reader-visibility discipline is a
`ReadableStructure.all` list with `mem_all`, in the `CovertChannelId.all` /
`KernelOperation.all` idiom.  It is weaker than it looks, and in precisely the
way SM8.E's own finding was weaker than it looked: `mem_all` proves every
constructor of a **hand-maintained** type appears in `all`, and nothing forces a
newly mounted readable field to add a constructor at all.  With the read
operations kept as a *separate* taxonomy, a future structure can be mounted,
exposed through a new read operation, and given neither a `ReadableStructure`
constructor nor an equivalence clause, while `mem_all` keeps compiling
(`readableStructure_list_gate_insufficient`).

So the two taxonomies are **fused**: every `AuditReadOp` names the
`ReadableStructure` it reads, so a read operation cannot exist without one, and
SM9.A.4a's equivalence clauses are a **total function** on `ReadableStructure`
rather than a list to append to.  A new readable structure is then a new
constructor — forced by the read operation that motivated it — and a new
constructor is a missing case in a total function, which is a compile error. -/

/-- WS-SM SM9.A.2 (plan §3.7): a kernel structure a clearance-filtered reader
can observe.

Each one owes both halves of the discipline: **(a)** it appears in the reader's
observation relation (`auditObservationalEquivalence`, SM9.A.4a), and **(b)** a
write the reader cannot see does not change what that reader sees.

SM9.A mounts one.  SM9.B's refusal ledger and any later readable structure join
by adding a constructor here, which is exactly what makes them impossible to
forget: the clause function on this type is total. -/
inductive ReadableStructure where
  /-- The declassification audit trail (`SystemState.declassificationAuditLog`)
      together with the epoch that gives its entries global identities. -/
  | declassificationAuditTrail
  deriving Repr, DecidableEq, Inhabited

namespace ReadableStructure

/-- WS-SM SM9.A.2: the enumeration. -/
def all : List ReadableStructure := [.declassificationAuditTrail]

/-- WS-SM SM9.A.2: every structure is enumerated. -/
theorem mem_all (s : ReadableStructure) : s ∈ all := by cases s <;> decide

/-- WS-SM SM9.A.2: no duplicates. -/
theorem all_nodup : all.Nodup := by decide

end ReadableStructure

/-- WS-SM SM9.A.2: the four numeric fields of a `DeclassificationEvent` the
reader exports through the chunk protocol.

`originatingCore` and the basis's trust bit are **not** here: both are
structurally bounded (`CoreId` is a `Fin numCores`, the bit is a `Bool`), so
they ride one word together (`AuditReadOp.coreAndTrust`).  The basis's
designation is not here either — it is a string, and gets the byte protocol of
§3b. -/
inductive AuditReadField where
  | srcDomain
  | dstDomain
  | targetObject
  | timestamp
  deriving Repr, DecidableEq, Inhabited

namespace AuditReadField

/-- WS-SM SM9.A.2: the enumeration. -/
def all : List AuditReadField := [.srcDomain, .dstDomain, .targetObject, .timestamp]

/-- WS-SM SM9.A.2: every field is enumerated. -/
theorem mem_all (f : AuditReadField) : f ∈ all := by cases f <;> decide

/-- WS-SM SM9.A.2: no duplicates. -/
theorem all_nodup : all.Nodup := by decide

end AuditReadField

/-- WS-SM SM9.A.2: the reader's sub-operations.  Every index is an index into
the **caller's own view**, never into the global trail. -/
inductive AuditReadOp where
  /-- Visible length, and — for the configured monitor only — the drain
      generation.  One call, because chunking it tears (§3c). -/
  | status
  /-- How many chunks numeric field `field` of visible entry `index` needs. -/
  | fieldChunkCount (index : Nat) (field : AuditReadField)
  /-- Chunk `chunk` of numeric field `field` of visible entry `index`. -/
  | field (index : Nat) (field : AuditReadField) (chunk : Nat)
  /-- Visible entry `index`'s originating core, packed with the kernel-issued
      trust bit.  Both components are structurally bounded, so one word. -/
  | coreAndTrust (index : Nat)
  /-- The byte length of visible entry `index`'s basis designation. -/
  | basisByteCount (index : Nat)
  /-- Chunk `chunk` (four bytes) of visible entry `index`'s basis designation. -/
  | basisChunk (index : Nat) (chunk : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- WS-SM SM9.A.2 (plan §3.7, **the fusion**): every read operation names the
structure it reads.

Total with no wildcard, so a read operation added for a newly mounted structure
does not elaborate until that structure has a `ReadableStructure` constructor —
and the constructor then forces an equivalence clause, because SM9.A.4a's clause
set is a total function on this type. -/
def AuditReadOp.readsStructure : AuditReadOp → ReadableStructure
  | .status => .declassificationAuditTrail
  | .fieldChunkCount _ _ => .declassificationAuditTrail
  | .field _ _ _ => .declassificationAuditTrail
  | .coreAndTrust _ => .declassificationAuditTrail
  | .basisByteCount _ => .declassificationAuditTrail
  | .basisChunk _ _ => .declassificationAuditTrail

/-- WS-SM SM9.A.2: the totality anchor.  The *mechanism* is the definition
itself — an exhaustive match with no wildcard; this theorem is the named surface
for that fact, in the shape `syscallReturnShape_total` established. -/
theorem auditReadOp_structure_total (op : AuditReadOp) :
    ∃ s, op.readsStructure = s := ⟨_, rfl⟩

/-- WS-SM SM9.A.2 (plan §3.7, **the refuted design, kept refuted**): a
hand-maintained list of readable structures plus a "everything listed is
readable" gate stays satisfied by a list that **misses** a readable structure —
membership cannot force a new member to join.

Witness: the empty list passes the gate vacuously while
`.declassificationAuditTrail` is readable and absent.  Contrast the fused
design, where a read operation cannot exist without naming a structure and a
structure cannot exist without a clause. -/
theorem readableStructure_list_gate_insufficient :
    ∃ l : List ReadableStructure,
      (∀ s ∈ l, ∃ op : AuditReadOp, op.readsStructure = s) ∧
      ∃ s : ReadableStructure, (∃ op : AuditReadOp, op.readsStructure = s) ∧ s ∉ l := by
  exact ⟨[], by simp, .declassificationAuditTrail, ⟨.status, rfl⟩, by simp⟩

-- ============================================================================
-- §4b  SM9.A.2 — the two reader classes
-- ============================================================================

/-- WS-SM SM9.A.2: **the value of a numeric field, as this reader may see it.**

Three of the four are the entry's own content and are exported verbatim.  The
**timestamp** is not: it is the entry's *global* position, so handing it to a
partial reader would tell that reader how many entries preceded the one it can
see — hidden ones included, which is exactly what the re-indexed view exists to
hide.  A partial reader therefore gets its own view-local index, which carries
no information it did not already supply.

A fully-dominating monitor gets the global timestamp, and needs it: the identity
must survive a drain for an archived predecessor to be correlatable at all.  The
two-class rule lives here, in one place, rather than being spread across the
read arms. -/
def auditExportedFieldValue (isMonitor : Bool) (index : Nat)
    (e : DeclassificationEvent) : AuditReadField → Nat
  | .srcDomain => e.srcDomain.id
  | .dstDomain => e.dstDomain.id
  | .targetObject => e.targetObject.val
  | .timestamp => if isMonitor then e.timestamp else index

/-- WS-SM SM9.A.2: **a partial reader's entry identity is its own index.**  It
learns nothing about the trail's global shape from it. -/
theorem auditReadIndex_is_view_local (index : Nat) (e : DeclassificationEvent) :
    auditExportedFieldValue false index e .timestamp = index := rfl

/-- WS-SM SM9.A.2: **a monitor's entry identity is the global timestamp** — the
identity that survives a drain, so an archived predecessor stays correlatable. -/
theorem dominatingReader_sees_global_identity (index : Nat) (e : DeclassificationEvent) :
    auditExportedFieldValue true index e .timestamp = e.timestamp := rfl

/-- WS-SM SM9.A.2: the core and the kernel-issued trust bit in one word.  Both
components are structurally bounded, so this needs no chunk protocol. -/
def auditCoreAndTrustWord (e : DeclassificationEvent) : Nat :=
  e.originatingCore.val +
    auditFieldChunkModulus * (if e.authorizationBasis.kernelVerifiable then 1 else 0)

/-- WS-SM SM9.A.2: the core fits the low field with room to spare, so the
packing is injective on the values the kernel produces. -/
theorem auditCoreAndTrustWord_core_fits (e : DeclassificationEvent) :
    e.originatingCore.val < auditFieldChunkModulus := by
  have h := e.originatingCore.isLt
  have : SeLe4n.Kernel.Concurrency.numCores < auditFieldChunkModulus := by decide
  omega

/-- WS-SM SM9.A.2: both components decode — the packing is lossless. -/
theorem auditCoreAndTrustWord_roundtrip (e : DeclassificationEvent) :
    auditCoreAndTrustWord e % auditFieldChunkModulus = e.originatingCore.val ∧
    auditCoreAndTrustWord e / auditFieldChunkModulus =
      (if e.authorizationBasis.kernelVerifiable then 1 else 0) := by
  have hFits := auditCoreAndTrustWord_core_fits e
  unfold auditCoreAndTrustWord auditFieldChunkModulus at *
  split <;> omega

/-- WS-SM SM9.A.2: **the trust bit is the kernel's own verdict**, carried as
data rather than left for a consumer to infer from the designation — which
`DeclassificationBasis.render_not_injective` shows is forgeable. -/
theorem auditCoreAndTrustWord_trust_bit (e : DeclassificationEvent) :
    (auditCoreAndTrustWord e / auditFieldChunkModulus = 1) ↔
      e.authorizationBasis = .policyRule := by
  rw [(auditCoreAndTrustWord_roundtrip e).2]
  rw [← DeclassificationBasis.kernelVerifiable_iff_policyRule]
  cases h : e.authorizationBasis.kernelVerifiable <;> simp

-- ============================================================================
-- §4c  SM9.A.2 — the reader
-- ============================================================================

/-- WS-SM SM9.A.2: **the audit read.**  A pure function of the reader's
clearance, the configured monitor clearance, the state and the requested
sub-operation, returning one word or a fail-closed error.

Every arm resolves its index through `auditVisibleEntry?`, so an index past the
end of the caller's own view is `.invalidArgument` and an entry the caller
cannot see is indistinguishable from one that does not exist.  A value too wide
to export is `.auditFieldTooLarge` — a refusal, never a truncation. -/
def auditReadWord (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (reader : SecurityDomain)
    (st : SystemState) (op : AuditReadOp) : Except KernelError Nat :=
  let isMonitor := auditMonitorAuthorized ctx monitorClearance reader
  let view := auditLogVisibleTo ctx reader st.declassificationAuditLog
  match op with
  | .status =>
      .ok (auditStatusWord view.length (if isMonitor then st.declassificationAuditEpoch else 0))
  | .fieldChunkCount index f =>
      match view[index]? with
      | none => .error .invalidArgument
      | some e =>
          match auditFieldChunkCount? (auditExportedFieldValue isMonitor index e f) with
          | none => .error .auditFieldTooLarge
          | some n => .ok n
  | .field index f chunk =>
      match view[index]? with
      | none => .error .invalidArgument
      | some e =>
          let v := auditExportedFieldValue isMonitor index e f
          match auditFieldChunkCount? v with
          | none => .error .auditFieldTooLarge
          | some n => if chunk < n then .ok (auditFieldChunk v chunk) else .error .invalidArgument
  | .coreAndTrust index =>
      match view[index]? with
      | none => .error .invalidArgument
      | some e => .ok (auditCoreAndTrustWord e)
  | .basisByteCount index =>
      match view[index]? with
      | none => .error .invalidArgument
      | some e =>
          let n := (auditBasisBytes e).length
          if n ≤ maxAuditDesignationBytes then .ok n else .error .auditFieldTooLarge
  | .basisChunk index chunk =>
      match view[index]? with
      | none => .error .invalidArgument
      | some e =>
          let bs := auditBasisBytes e
          if bs.length ≤ maxAuditDesignationBytes then
            (if chunk < auditBasisChunkCount bs.length then .ok (auditBasisChunkValue bs chunk)
             else .error .invalidArgument)
          else .error .auditFieldTooLarge

/-- WS-SM SM9.A.2: **the reader is a function of the visible view and the
exported generation alone.**

The keystone the flow argument (SM9.A.4b) is built on, and the reason the
reader can be shown to open no channel without inspecting each arm: two states
whose visible views agree, and whose epochs agree *when the caller is entitled
to the epoch at all*, are indistinguishable to this reader. -/
theorem auditRead_determined_by_view (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (reader : SecurityDomain)
    (st₁ st₂ : SystemState) (op : AuditReadOp)
    (hView : auditLogVisibleTo ctx reader st₁.declassificationAuditLog
      = auditLogVisibleTo ctx reader st₂.declassificationAuditLog)
    (hEpoch : auditMonitorAuthorized ctx monitorClearance reader = true →
      st₁.declassificationAuditEpoch = st₂.declassificationAuditEpoch) :
    auditReadWord ctx monitorClearance reader st₁ op =
      auditReadWord ctx monitorClearance reader st₂ op := by
  unfold auditReadWord
  cases hMon : auditMonitorAuthorized ctx monitorClearance reader with
  | false => cases op <;> simp only [hView, Bool.false_eq_true, if_false]
  | true =>
    rw [hEpoch hMon]
    cases op <;> simp only [hView]

/-- WS-SM SM9.A.2 (**a partial reader cannot count hidden entries**): its every
read is determined by its visible view — the epoch, which counts entries it may
not see, reaches it through no arm.

Stated over an arbitrary pair of states, so the two may differ by any number of
hidden entries and by any epoch whatsoever. -/
theorem auditRead_hides_global_position (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (reader : SecurityDomain)
    (st₁ st₂ : SystemState) (op : AuditReadOp)
    (hPartial : auditMonitorAuthorized ctx monitorClearance reader = false)
    (hView : auditLogVisibleTo ctx reader st₁.declassificationAuditLog
      = auditLogVisibleTo ctx reader st₂.declassificationAuditLog) :
    auditReadWord ctx monitorClearance reader st₁ op =
      auditReadWord ctx monitorClearance reader st₂ op :=
  auditRead_determined_by_view ctx monitorClearance reader st₁ st₂ op hView
    (fun h => absurd h (by simp [hPartial]))

/-- WS-SM SM9.A.2: **`status` is atomic** — one call, and both components come
from the same state.

The property chunking cannot have.  With a chunked `status` a drain landing
between two calls yields a generation assembled from two different states
(`auditStatusSplitRead_tears`); here the pair is a function of one `st`. -/
theorem auditReadStatus_atomic (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (reader : SecurityDomain)
    (st : SystemState)
    (hBounded : auditLogBounded st.declassificationAuditLog) :
    ∃ w, auditReadWord ctx monitorClearance reader st .status = .ok w ∧
      auditStatusVisibleLength w =
        (auditLogVisibleTo ctx reader st.declassificationAuditLog).length ∧
      auditStatusGeneration w =
        (if auditMonitorAuthorized ctx monitorClearance reader then
          st.declassificationAuditEpoch else 0) := by
  have hLen : (auditLogVisibleTo ctx reader st.declassificationAuditLog).length
      < auditStatusLengthSlots := by
    have h1 := auditLogVisibleTo_length_le ctx reader st.declassificationAuditLog
    unfold auditLogBounded at hBounded
    unfold auditStatusLengthSlots
    unfold maxDeclassificationAuditEntries at hBounded
    omega
  obtain ⟨hL, hG⟩ := auditStatusWord_roundtrip
    (auditLogVisibleTo ctx reader st.declassificationAuditLog).length
    (if auditMonitorAuthorized ctx monitorClearance reader then
      st.declassificationAuditEpoch else 0) hLen
  exact ⟨_, rfl, hL, hG⟩

/-- WS-SM SM9.A.2 (**a partial reader gets no generation at all**): its status
word is independent of the epoch — strictly stronger than scoping a drain
counter per observer, and the reason no per-observer state is needed.

A *global* drain counter returned to every reader would be a one-bit signal per
drain from the dominating monitor to every subject in the system, out of exactly
the boundary this phase polices.  `auditReadStatus_global_generation_leaks` is
the negative that keeps that design refuted. -/
theorem auditReadStatus_partial_hides_generation (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (reader : SecurityDomain)
    (st : SystemState) (epoch : Nat)
    (hPartial : auditMonitorAuthorized ctx monitorClearance reader = false) :
    auditReadWord ctx monitorClearance reader
        { st with declassificationAuditEpoch := epoch } .status =
      auditReadWord ctx monitorClearance reader st .status :=
  auditRead_hides_global_position ctx monitorClearance reader _ _ .status hPartial rfl

/-- WS-SM SM9.A.2 (**the refuted design**): a status that returned the global
drain generation to *every* reader would be observable — two states differing
only in the epoch would be distinguishable to a caller that can see no entry at
all.

Stated as the refutation of the naive design rather than as a property of this
one: `auditStatusGeneration` applied to a hypothetical global-generation status
separates the two states, and `auditReadStatus_partial_hides_generation` says
the shipped reader does not. -/
theorem auditReadStatus_global_generation_leaks :
    ∃ (visibleLength g₁ g₂ : Nat),
      visibleLength < auditStatusLengthSlots ∧ g₁ ≠ g₂ ∧
      auditStatusWord visibleLength g₁ ≠ auditStatusWord visibleLength g₂ := by
  refine ⟨0, 0, 1, by decide, by decide, ?_⟩
  unfold auditStatusWord auditStatusLengthSlots
  decide

/-- WS-SM SM9.A.2 (**why the per-observer drain token was not merely unbuilt but
unbuildable**): there is no finite family of security domains to key per-observer
state by.

`SecurityDomain.id` is an unbounded `Nat`, so for any list of domains a
deployment might enumerate there is a domain outside it — hence no `Vector`
indexed by reader, and no place to put an observer-scoped generation counter.
The two-class rule of §4b is what replaces it: the generation a caller may see
is the *global* epoch, and the gate decides whether it sees one at all. -/
theorem observerScopedGeneration_not_mountable (domains : List SecurityDomain) :
    ∃ d : SecurityDomain, d ∉ domains := by
  refine ⟨⟨(domains.map (fun x => x.id)).foldr max 0 + 1⟩, ?_⟩
  intro hMem
  have hLe : ∀ (l : List SecurityDomain) (x : SecurityDomain), x ∈ l →
      x.id ≤ (l.map (fun y => y.id)).foldr max 0 := by
    intro l
    induction l with
    | nil => intro x hx; simp at hx
    | cons a rest ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · simp only [List.map_cons, List.foldr_cons]
        exact Nat.le_max_left _ _
      · have hRest := ih x hx'
        simp only [List.map_cons, List.foldr_cons]
        exact Nat.le_trans hRest (Nat.le_max_right _ _)
  have := hLe domains _ hMem
  simp only at this
  omega

-- ============================================================================
-- §5  SM9.A.3 — the drain
-- ============================================================================

/-! ## Why drain requires full dominance

An earlier design let any reader drain "the longest prefix all of whose entries
it can see".  That leaks: on a trail `[A, H, B]` where the reader sees `A` and
`B` but not `H`, the drain stops after one entry and the reader learns that
entry 2 is invisible — the *position* of a hidden entry, which is precisely what
re-indexing exists to hide.  Worse, the visible length after the drain then
depends on how many hidden entries sit between the visible ones, so repeated
drains enumerate the hidden layout.

Requiring full dominance removes the case rather than mitigating it: either the
caller sees the whole trail and drains all of it, or it drains nothing.

**And "dominates every recorded domain" must not be computed from the records**
— §2's `auditMonitorGate_records_derived_unsound` is why.  The gate is the
configured monitor clearance; `auditDrain_requires_full_dominance` is the bridge
that turns a configuration obligation into the visibility fact the leak argument
needs.

**The operator consequence, recorded rather than buried.**  A deployment whose
monitor clearance is not a top of its flow policy cannot drain, and the
256-entry cliff returns for it.  That is the correct conservative default — a
leaky drain is worse than an un-drainable trail — but it is a real constraint,
and it belongs in the shipped documentation. -/

/-- WS-SM SM9.A.3: **drain a prefix of the trail.**

Gated on the configured monitor clearance (§2).  Removes `min count length`
entries and advances the epoch by exactly that many, so surviving timestamps
keep their identities and the next append cannot reuse one
(`auditDrain_next_timestamp_fresh`).  Returns the new trail length, which for a
qualifying caller *is* its new visible length
(`auditDrain_requires_full_dominance`). -/
def auditDrainVisiblePrefix (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (c : CoreId) (count : Nat) : Kernel Nat :=
  fun st =>
    if auditMonitorGate ctx monitorClearance st c then
      let removed := min count st.declassificationAuditLog.length
      .ok (st.declassificationAuditLog.length - removed,
           { st with
             declassificationAuditLog := st.declassificationAuditLog.drop removed,
             declassificationAuditEpoch := st.declassificationAuditEpoch + removed })
    else
      .error .illegalAuthority

/-- WS-SM SM9.A.3 (**fail-closed**): a caller that is not the configured monitor
drains nothing, and the state is untouched. -/
theorem auditDrain_denied_for_unauthorized (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (c : CoreId) (count : Nat)
    (st : SystemState)
    (hGate : auditMonitorGate ctx monitorClearance st c = false) :
    auditDrainVisiblePrefix ctx monitorClearance c count st = .error .illegalAuthority := by
  simp [auditDrainVisiblePrefix, hGate]

/-- WS-SM SM9.A.3: an unconfigured deployment cannot drain at all — the
deny-by-default posture, at the transition. -/
theorem auditDrain_unconfigured_denied (ctx : GenericLabelingContext)
    (c : CoreId) (count : Nat) (st : SystemState) :
    auditDrainVisiblePrefix ctx none c count st = .error .illegalAuthority := by
  refine auditDrain_denied_for_unauthorized ctx none c count st ?_
  unfold auditMonitorGate
  cases auditReaderDomain ctx st c <;> rfl

/-- WS-SM SM9.A.3 (**the frame**): a successful drain writes the trail and the
epoch and **nothing else** — not the object store, not the scheduler, not a
single SM7 memory-model field. -/
theorem auditDrain_frame (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (c : CoreId) (count : Nat)
    (st : SystemState) (n : Nat) (st' : SystemState)
    (hStep : auditDrainVisiblePrefix ctx monitorClearance c count st = .ok (n, st')) :
    st' = { st with
      declassificationAuditLog :=
        st.declassificationAuditLog.drop (min count st.declassificationAuditLog.length),
      declassificationAuditEpoch :=
        st.declassificationAuditEpoch + min count st.declassificationAuditLog.length } ∧
    n = st.declassificationAuditLog.length - min count st.declassificationAuditLog.length ∧
    auditMonitorGate ctx monitorClearance st c = true := by
  unfold auditDrainVisiblePrefix at hStep
  split at hStep
  · rename_i hGate
    simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
    exact ⟨hStep.2.symm, hStep.1.symm, hGate⟩
  · exact absurd hStep (by simp)

/-- WS-SM SM9.A.3: **a qualifying caller sees the whole trail.**

The bridge from the configuration obligation to the visibility fact: under a
well-formed configuration (the monitor clearance is a top of the flow policy) a
caller that passes the gate dominates every domain, hence every recorded
`srcDomain`, hence its visible view *is* the trail.  This is what makes the
drain positionally blind — there is no partial-visibility prefix to probe. -/
theorem auditDrain_requires_full_dominance (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (reader : SecurityDomain)
    (log : DeclassificationAuditLog)
    (hTop : auditMonitorClearanceIsTop ctx monitorClearance)
    (hTrans : ctx.policy.isTransitive)
    (hGate : auditMonitorAuthorized ctx monitorClearance reader = true) :
    auditLogVisibleTo ctx reader log = log :=
  auditLogVisibleTo_eq_self ctx reader log
    (fun e _ => auditMonitorAuthorized_dominates_all ctx monitorClearance reader hTop hTrans
      hGate e.srcDomain)

/-- WS-SM SM9.A.3: **every entry's source is a domain the labeling assigns to
some subject.**

A property of kernel-produced trails rather than a gate: the audited producer
records `srcDomain := ctx.threadDomainOf tid` for the subject the executing core
is running, so every entry it writes satisfies this by construction.

It is *not* the visibility gate, and it does not age the way a records-derived
gate would.  A records-derived gate becomes **more permissive** as entries
vanish, which is the failure §2 refutes; this predicate becomes *more* true, and
it is a soundness hypothesis on the trail rather than the thing that decides who
may drain. -/
def auditTrailSourcesFromLabeling (ctx : GenericLabelingContext)
    (log : DeclassificationAuditLog) : Prop :=
  ∀ e ∈ log, ∃ tid : SeLe4n.ThreadId, e.srcDomain = ctx.threadDomainOf tid

/-- WS-SM SM9.A.3: removing entries preserves it — the direction that matters,
since a drain is the operation this is used to justify. -/
theorem auditTrailSourcesFromLabeling_drop (ctx : GenericLabelingContext)
    (log : DeclassificationAuditLog) (d : Nat)
    (h : auditTrailSourcesFromLabeling ctx log) :
    auditTrailSourcesFromLabeling ctx (log.drop d) :=
  fun e hMem => h e (List.mem_of_mem_drop hMem)

/-- WS-SM SM9.A.3: the empty trail satisfies it — the boot witness. -/
@[simp] theorem auditTrailSourcesFromLabeling_nil (ctx : GenericLabelingContext) :
    auditTrailSourcesFromLabeling ctx [] := by
  intro e hMem; simp at hMem

/-- WS-SM SM9.A.3: **the live declassification establishes it.**

The producer records `srcDomain := ctx.threadDomainOf tid` for the subject the
executing core is running (`declassifyObjectFromCore_never_unaudited`), so every
entry it writes is sourced at a subject domain by construction.  Together with
the boot witness and the drop lemma this makes the hypothesis of
`auditDrain_requires_full_dominance_of_subjects` an invariant of any trail a
running system can reach, rather than a condition an operator has to check. -/
theorem declassifyObjectFromCore_preserves_trailSources
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (targetId : SeLe4n.ObjId) (st st' : SystemState)
    (hSources : auditTrailSourcesFromLabeling ctx st.declassificationAuditLog)
    (hStep : declassifyObjectFromCore ctx declPolicy c targetId st = .ok ((), st')) :
    auditTrailSourcesFromLabeling ctx st'.declassificationAuditLog := by
  obtain ⟨tid, -, hSt'⟩ :=
    declassifyObjectFromCore_frame_of_ok ctx declPolicy c targetId st st' hStep
  subst hSt'
  intro e hMem
  have hMem' : e ∈ st.declassificationAuditLog ++
      [declassifyStoreEvent c (ctx.threadDomainOf tid) (ctx.objectDomainOf targetId)
        targetId st] := hMem
  rcases List.mem_append.mp hMem' with hOld | hNew
  · exact hSources e hOld
  · rcases List.mem_singleton.mp hNew with rfl
    exact ⟨tid, rfl⟩

/-- WS-SM SM9.A.3 (**the practically satisfiable dominance obligation**): the
configured monitor clearance dominates every domain the *labeling* can assign to
a subject.

Weaker than `auditMonitorClearanceIsTop` and, crucially, **satisfiable by the
contexts the live path uses**: `liftLegacyContext` embeds the 2×2 lattice into
domains 0–3 with `{high, trusted}` above all four, but its policy denies flows
from ids outside the embedding's image, so no domain is a top of the whole
abstract space.

Configuration-derived exactly as the stronger form is: the policy, the labeling
and the clearance are all fixed deployment parameters.  None of them moves when
entries are recorded or removed. -/
def auditMonitorDominatesSubjects (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) : Prop :=
  ∃ m, monitorClearance = some m ∧
    ∀ tid : SeLe4n.ThreadId, ctx.policy.canFlow (ctx.threadDomainOf tid) m = true

/-- WS-SM SM9.A.3: a caller that passes the gate dominates every subject
domain. -/
theorem auditMonitorAuthorized_dominates_subjects (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (reader : SecurityDomain)
    (hDom : auditMonitorDominatesSubjects ctx monitorClearance)
    (hTrans : ctx.policy.isTransitive)
    (hGate : auditMonitorAuthorized ctx monitorClearance reader = true) :
    ∀ tid : SeLe4n.ThreadId, ctx.policy.canFlow (ctx.threadDomainOf tid) reader = true := by
  obtain ⟨m, hm, hAll⟩ := hDom
  subst hm
  intro tid
  exact hTrans _ m reader (hAll tid) hGate

/-- WS-SM SM9.A.3 (**the form a real deployment uses**): under the
subject-relative obligation, a caller that passes the gate sees **the whole
trail** — every entry, because every entry's source is a subject domain the
monitor dominates.

This is what makes the drain positionally blind on the contexts the live path
actually carries: there is no partial-visibility prefix to probe. -/
theorem auditDrain_requires_full_dominance_of_subjects (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (reader : SecurityDomain)
    (log : DeclassificationAuditLog)
    (hDom : auditMonitorDominatesSubjects ctx monitorClearance)
    (hTrans : ctx.policy.isTransitive)
    (hSources : auditTrailSourcesFromLabeling ctx log)
    (hGate : auditMonitorAuthorized ctx monitorClearance reader = true) :
    auditLogVisibleTo ctx reader log = log := by
  refine auditLogVisibleTo_eq_self ctx reader log (fun e hMem => ?_)
  obtain ⟨tid, hTid⟩ := hSources e hMem
  rw [hTid]
  exact auditMonitorAuthorized_dominates_subjects ctx monitorClearance reader hDom hTrans
    hGate tid

/-- WS-SM SM9.A.3: a drain never grows the trail, so the capacity bound rides
it unconditionally. -/
theorem auditDrain_preserves_auditLogBounded (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (c : CoreId) (count : Nat)
    (st : SystemState) (n : Nat) (st' : SystemState)
    (hBounded : auditLogBounded st.declassificationAuditLog)
    (hStep : auditDrainVisiblePrefix ctx monitorClearance c count st = .ok (n, st')) :
    auditLogBounded st'.declassificationAuditLog := by
  obtain ⟨hSt', -, -⟩ := auditDrain_frame ctx monitorClearance c count st n st' hStep
  subst hSt'
  unfold auditLogBounded at hBounded ⊢
  simp only [List.length_drop]
  omega

/-- WS-SM SM9.A.3 (**the timestamp discipline survives the drain**): removing
`d` entries and advancing the epoch by `d` leaves a trail well-formed at its new
epoch.

The half `auditTimestampsFrom_drop` exists for, and the reason the epoch
advances by the number removed rather than by one: the anchor has to move
exactly as far as the prefix that was cut. -/
theorem auditDrain_preserves_wellFormed_at_epoch (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (c : CoreId) (count : Nat)
    (st : SystemState) (n : Nat) (st' : SystemState)
    (hWF : declassificationTrailWellFormed st = true)
    (hStep : auditDrainVisiblePrefix ctx monitorClearance c count st = .ok (n, st')) :
    declassificationTrailWellFormed st' = true := by
  obtain ⟨hSt', -, -⟩ := auditDrain_frame ctx monitorClearance c count st n st' hStep
  subst hSt'
  unfold declassificationTrailWellFormed at hWF ⊢
  exact auditTimestampsFrom_drop _ _ _ hWF

/-- WS-SM SM9.A.3: the epoch is **monotone** — a drain advances it, never
rewinds it, so a timestamp once issued is never issued again. -/
theorem auditDrain_monotone_epoch (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (c : CoreId) (count : Nat)
    (st : SystemState) (n : Nat) (st' : SystemState)
    (hStep : auditDrainVisiblePrefix ctx monitorClearance c count st = .ok (n, st')) :
    st.declassificationAuditEpoch ≤ st'.declassificationAuditEpoch := by
  obtain ⟨hSt', -, -⟩ := auditDrain_frame ctx monitorClearance c count st n st' hStep
  subst hSt'
  show st.declassificationAuditEpoch ≤
    st.declassificationAuditEpoch + min count st.declassificationAuditLog.length
  omega

/-- WS-SM SM9.A.3 (**the headline the epoch exists for**): after a drain, the
timestamp the next recorded event will carry belongs to **no surviving entry**.

Where the pre-epoch producer put the new entry on top of a survivor
(`preEpochTimestamp_reused_after_drain`), the epoch rule leaves a gap exactly as
wide as the prefix removed.  This is `declassificationAuditLog_timestamp_identifies_event`
surviving the operation that would otherwise falsify it. -/
theorem auditDrain_next_timestamp_fresh (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (c : CoreId) (count : Nat)
    (st : SystemState) (n : Nat) (st' : SystemState)
    (hWF : declassificationTrailWellFormed st = true)
    (hStep : auditDrainVisiblePrefix ctx monitorClearance c count st = .ok (n, st')) :
    ∀ e ∈ st'.declassificationAuditLog,
      e.timestamp ≠ st'.declassificationAuditEpoch + st'.declassificationAuditLog.length := by
  have hWF' := auditDrain_preserves_wellFormed_at_epoch ctx monitorClearance c count st n st'
    hWF hStep
  intro e hMem
  unfold declassificationTrailWellFormed at hWF'
  rw [auditTimestampsFrom_iff] at hWF'
  obtain ⟨i, hi, hEq⟩ := List.getElem_of_mem hMem
  have := hWF' i hi
  rw [hEq] at this
  omega

/-- WS-SM SM9.A.3: **a drain that names at least the trail's length clears it**,
which for a qualifying caller is the whole trail — so the 256-entry cliff is
recoverable in one call. -/
theorem auditDrain_fully_clears_for_dominating_reader (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (c : CoreId) (count : Nat)
    (st : SystemState) (n : Nat) (st' : SystemState)
    (hCount : st.declassificationAuditLog.length ≤ count)
    (hStep : auditDrainVisiblePrefix ctx monitorClearance c count st = .ok (n, st')) :
    st'.declassificationAuditLog = [] ∧ n = 0 ∧
    st'.declassificationAuditEpoch =
      st.declassificationAuditEpoch + st.declassificationAuditLog.length := by
  obtain ⟨hSt', hn, -⟩ := auditDrain_frame ctx monitorClearance c count st n st' hStep
  subst hSt'
  have hMin : min count st.declassificationAuditLog.length =
      st.declassificationAuditLog.length := by omega
  refine ⟨?_, ?_, ?_⟩
  · show List.drop (min count st.declassificationAuditLog.length)
      st.declassificationAuditLog = []
    simp only [hMin]
    exact List.drop_length
  · simp only [hn, hMin]; omega
  · show st.declassificationAuditEpoch + min count st.declassificationAuditLog.length =
      st.declassificationAuditEpoch + st.declassificationAuditLog.length
    simp only [hMin]

/-- WS-SM SM9.A.3 (**the load-bearing negative**): a partially-cleared caller
drains **nothing** — not a prefix, not one entry.

The refutation of the leaky design: there is no partial-visibility prefix whose
length a reader could observe, so repeated drains cannot enumerate the hidden
layout. -/
theorem auditDrain_partial_reader_drains_nothing (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (c : CoreId) (count : Nat)
    (st : SystemState) (reader : SecurityDomain)
    (hReader : auditReaderDomain ctx st c = some reader)
    (hPartial : auditMonitorAuthorized ctx monitorClearance reader = false) :
    ¬ ∃ n st', auditDrainVisiblePrefix ctx monitorClearance c count st = .ok (n, st') := by
  rintro ⟨n, st', hStep⟩
  obtain ⟨-, -, hGate⟩ := auditDrain_frame ctx monitorClearance c count st n st' hStep
  unfold auditMonitorGate at hGate
  rw [hReader] at hGate
  simp only [hPartial] at hGate
  exact Bool.noConfusion hGate

/-- WS-SM SM9.A.3: the drain carries the whole invariant bundle — the obligation
its dispatch arm owes.

Fifteen conjuncts ride
`proofLayerInvariantBundle_setDeclassificationAuditTrail` (the transition writes
two fields and none of the fifteen reads either); the sixteenth is the capacity
bound, which a drain gets for free because it never grows the trail. -/
theorem auditDrain_preserves_proofLayerInvariantBundle (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (c : CoreId) (count : Nat)
    (st : SystemState) (n : Nat) (st' : SystemState)
    (hInv : Architecture.proofLayerInvariantBundle st)
    (hStep : auditDrainVisiblePrefix ctx monitorClearance c count st = .ok (n, st')) :
    Architecture.proofLayerInvariantBundle st' := by
  have hBounded : auditLogBounded st.declassificationAuditLog := hInv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hBounded' := auditDrain_preserves_auditLogBounded ctx monitorClearance c count st n st'
    hBounded hStep
  obtain ⟨hSt', -, -⟩ := auditDrain_frame ctx monitorClearance c count st n st' hStep
  subst hSt'
  exact Architecture.proofLayerInvariantBundle_setDeclassificationAuditTrail st _ _ hInv hBounded'

-- ============================================================================
-- §6  SM9.A.5 — stability under append, and the retry protocol
-- ============================================================================

/-! ## The concurrency contract

The trail is append-only and drain removes a prefix, so a reader's index is
stable under concurrent **append** and shifts only under concurrent **drain**.
The kernel stays simple; the protocol gets a theorem.

For a **monitor**, `status` brackets a read sequence: the epoch it returns moves
only on a drain, so an unchanged status means no drain intervened and every
index the reader used still names the entry it named.  For a **partial reader**
no retry guarantee is promised — it gets no generation at all (§4c), which is
the price of not being able to count hidden entries, and it is stated rather
than papered over: a partial reader is a monitoring convenience and the trail's
consumer of record is the monitor. -/

/-- WS-SM SM9.A.5: **appending does not disturb an existing index.**

A concurrent authorized downgrade grows the trail, and the view grows with it —
but only at the end, so every index a reader already holds still names the same
entry.  This is the substantive half of the retry protocol. -/
theorem auditVisibleEntry?_stable_under_append (ctx : GenericLabelingContext)
    (reader : SecurityDomain) (log extra : DeclassificationAuditLog) (i : Nat)
    (hi : i < (auditLogVisibleTo ctx reader log).length) :
    auditVisibleEntry? ctx reader (log ++ extra) i = auditVisibleEntry? ctx reader log i := by
  unfold auditVisibleEntry?
  rw [auditLogVisibleTo_append]
  exact List.getElem?_append_left hi

/-- WS-SM SM9.A.5: **every read at an existing index is stable under append.**

The whole-reader form: with the epoch unchanged — which an append leaves it —
each of the reader's sub-operations returns the same word before and after a
concurrent authorized downgrade, provided the index it names was already in its
view.

Stated over the *indices the caller already holds*, which is the honest scope: a
reader cannot be promised anything about an index it has not yet observed to
exist. -/
theorem auditRead_stable_under_append (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (reader : SecurityDomain)
    (st : SystemState) (extra : DeclassificationAuditLog) (op : AuditReadOp)
    (hIndex : ∀ i f k, op = .fieldChunkCount i f ∨ op = .field i f k ∨
      op = .coreAndTrust i ∨ op = .basisByteCount i ∨ op = .basisChunk i k →
      i < (auditLogVisibleTo ctx reader st.declassificationAuditLog).length)
    (hNotStatus : op ≠ .status) :
    auditReadWord ctx monitorClearance reader
        { st with declassificationAuditLog := st.declassificationAuditLog ++ extra } op =
      auditReadWord ctx monitorClearance reader st op := by
  have hEntry : ∀ i, i < (auditLogVisibleTo ctx reader st.declassificationAuditLog).length →
      (auditLogVisibleTo ctx reader (st.declassificationAuditLog ++ extra))[i]? =
        (auditLogVisibleTo ctx reader st.declassificationAuditLog)[i]? := by
    intro i hi
    rw [auditLogVisibleTo_append]
    exact List.getElem?_append_left hi
  unfold auditReadWord
  cases op with
  | status => exact absurd rfl hNotStatus
  | fieldChunkCount i f =>
    simp only [hEntry i (hIndex i f 0 (Or.inl rfl))]
  | field i f k =>
    simp only [hEntry i (hIndex i f k (Or.inr (Or.inl rfl)))]
  | coreAndTrust i =>
    simp only [hEntry i (hIndex i .srcDomain 0 (Or.inr (Or.inr (Or.inl rfl))))]
  | basisByteCount i =>
    simp only [hEntry i (hIndex i .srcDomain 0 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))]
  | basisChunk i k =>
    simp only [hEntry i (hIndex i .srcDomain k (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))]

/-- WS-SM SM9.A.5 (**the bracket**): for a monitor, an unchanged status word
means an unchanged epoch and an unchanged visible length — so no drain
intervened between the two observations.

The `noGenerationWrap` premise is the visible length's bound plus the
generation's, both stated rather than assumed: the visible length is within
capacity by the mounted invariant, and the epoch is below `2^55` by a premise
that cannot be discharged, because it is an unbounded monotone counter.  A
premise written down is the honest form of a bound that cannot be made
unconditional. -/
theorem auditRead_bracketed_detects_drain (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (reader : SecurityDomain)
    (st₁ st₂ : SystemState)
    (hBounded₁ : auditLogBounded st₁.declassificationAuditLog)
    (hBounded₂ : auditLogBounded st₂.declassificationAuditLog)
    (hStatus : auditReadWord ctx monitorClearance reader st₁ .status =
      auditReadWord ctx monitorClearance reader st₂ .status) :
    (auditLogVisibleTo ctx reader st₁.declassificationAuditLog).length =
      (auditLogVisibleTo ctx reader st₂.declassificationAuditLog).length ∧
    (auditMonitorAuthorized ctx monitorClearance reader = true →
      st₁.declassificationAuditEpoch = st₂.declassificationAuditEpoch) := by
  obtain ⟨w₁, hw₁, hL₁, hG₁⟩ :=
    auditReadStatus_atomic ctx monitorClearance reader st₁ hBounded₁
  obtain ⟨w₂, hw₂, hL₂, hG₂⟩ :=
    auditReadStatus_atomic ctx monitorClearance reader st₂ hBounded₂
  rw [hw₁, hw₂] at hStatus
  have hEq : w₁ = w₂ := by
    simpa using hStatus
  subst hEq
  refine ⟨by rw [← hL₁, ← hL₂], ?_⟩
  intro hMon
  have := hG₁.symm.trans hG₂
  simpa [hMon] using this

/-- WS-SM SM9.A.5 (**why `status` is one call**): a *split* status read —
length from one state, generation from another — produces a pair that
corresponds to **no state at all**.

The witness is the smallest interleaving that matters: a trail with one visible
entry and epoch `0`, drained to empty with epoch `1`.  A reader that read the
length first and the generation after the drain assembles `(1, 1)`, which is
neither the pre-state's `(1, 0)` nor the post-state's `(0, 1)`.  Chunking
`status` would have traded aliasing after ~2^55 drains for tearing on the very
first one. -/
theorem auditStatusSplitRead_tears :
    ∃ (lengthBefore generationBefore lengthAfter generationAfter : Nat),
      (lengthBefore, generationAfter) ≠ (lengthBefore, generationBefore) ∧
      (lengthBefore, generationAfter) ≠ (lengthAfter, generationAfter) := by
  exact ⟨1, 0, 0, 1, by decide, by decide⟩

-- ============================================================================
-- §7  SM9.A — non-interference witnesses for the reader's own writes
-- ============================================================================

/-! The drain's own non-interference witness — that it writes only the trail and
the epoch, neither of which `projectState` reads — is stated in
`InformationFlow/DeclassificationPerCore.lean` alongside the rest of the
declassification surface's NI theory, which is where
`authorizeDeclassificationOnCore_preserves_projectionOnCore` already lives.
Keeping it there is what lets this module stay below the projection layer. -/

/-- WS-SM SM9.A: **the read itself writes nothing.**  Stated as a fact about the
pure function: `auditReadWord` takes a state and returns a word, so there is no
post-state for a reader to have perturbed, and the syscall arm that wraps it
commits the state it was handed. -/
theorem auditReadWord_state_preserving (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (reader : SecurityDomain)
    (st : SystemState) (op : AuditReadOp) :
    ∃ r : Except KernelError Nat, auditReadWord ctx monitorClearance reader st op = r :=
  ⟨_, rfl⟩

-- ============================================================================
-- §8  SM9.A.10 — the operand encoding
-- ============================================================================

/-! ## Three words, and why the field rides the opcode

`.auditRead` carries `[op, index, chunk]`.  The sub-operation and the field it
selects share the opcode rather than taking a register each, because
`AuditReadOp.field` needs *three* coordinates (index, field, chunk) and a fourth
operand register would buy nothing: the field space is four values and the
opcode space is free.

Fail-closed on an unrecognised opcode, exactly as `SyscallId.ofNat?` is: an ABI
the kernel does not understand is refused, never guessed at. -/

/-- WS-SM SM9.A.10: decode an `.auditRead` operand triple. -/
def decodeAuditReadOp (opcode index chunk : Nat) : Option AuditReadOp :=
  match opcode with
  | 0  => some .status
  | 1  => some (.fieldChunkCount index .srcDomain)
  | 2  => some (.fieldChunkCount index .dstDomain)
  | 3  => some (.fieldChunkCount index .targetObject)
  | 4  => some (.fieldChunkCount index .timestamp)
  | 5  => some (.field index .srcDomain chunk)
  | 6  => some (.field index .dstDomain chunk)
  | 7  => some (.field index .targetObject chunk)
  | 8  => some (.field index .timestamp chunk)
  | 9  => some (.coreAndTrust index)
  | 10 => some (.basisByteCount index)
  | 11 => some (.basisChunk index chunk)
  | _  => none

/-- WS-SM SM9.A.10: the number of `.auditRead` opcodes.  Pinned in the Rust
mirror, so a divergence is a conformance failure rather than a silent
`.invalidSyscallArgument` on a valid request. -/
def auditReadOpcodeCount : Nat := 12

/-- WS-SM SM9.A.10: encode a sub-operation back to its operand triple. -/
def encodeAuditReadOp : AuditReadOp → Nat × Nat × Nat
  | .status => (0, 0, 0)
  | .fieldChunkCount i .srcDomain => (1, i, 0)
  | .fieldChunkCount i .dstDomain => (2, i, 0)
  | .fieldChunkCount i .targetObject => (3, i, 0)
  | .fieldChunkCount i .timestamp => (4, i, 0)
  | .field i .srcDomain k => (5, i, k)
  | .field i .dstDomain k => (6, i, k)
  | .field i .targetObject k => (7, i, k)
  | .field i .timestamp k => (8, i, k)
  | .coreAndTrust i => (9, i, 0)
  | .basisByteCount i => (10, i, 0)
  | .basisChunk i k => (11, i, k)

/-- WS-SM SM9.A.10: **the operand encoding round-trips.**  Every sub-operation
is reachable through the ABI, and reaches the arm it names. -/
theorem decodeAuditReadOp_encode (op : AuditReadOp) :
    decodeAuditReadOp (encodeAuditReadOp op).1 (encodeAuditReadOp op).2.1
      (encodeAuditReadOp op).2.2 = some op := by
  cases op with
  | status => rfl
  | fieldChunkCount i f => cases f <;> rfl
  | field i f k => cases f <;> rfl
  | coreAndTrust i => rfl
  | basisByteCount i => rfl
  | basisChunk i k => rfl

/-- WS-SM SM9.A.10 (**fail-closed**): an opcode outside the table is refused. -/
theorem decodeAuditReadOp_out_of_range (opcode index chunk : Nat)
    (hRange : auditReadOpcodeCount ≤ opcode) :
    decodeAuditReadOp opcode index chunk = none := by
  unfold auditReadOpcodeCount at hRange
  match opcode, hRange with
  | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h | 7, h | 8, h | 9, h
  | 10, h | 11, h => omega
  | n + 12, _ => rfl

/-- WS-SM SM9.A.10: every opcode the table admits is below the count — the
other half of the range pin. -/
theorem decodeAuditReadOp_isSome_lt (opcode index chunk : Nat)
    (hSome : (decodeAuditReadOp opcode index chunk).isSome = true) :
    opcode < auditReadOpcodeCount := by
  rcases Nat.lt_or_ge opcode auditReadOpcodeCount with h | h
  · exact h
  · rw [decodeAuditReadOp_out_of_range opcode index chunk h] at hSome
    simp at hSome


-- ============================================================================
-- §9  SM9.A.10 — the live entry points
-- ============================================================================

/-- WS-SM SM9.A.10: **the entry point the `.auditRead` syscall calls.**

The reader's clearance is not an argument: it is read off whichever thread core
`c` is running, exactly as `declassifyObjectFromCore` reads the declassifying
subject's domain.  A caller that could name its own clearance could read the
whole trail, which is the reason both entry points resolve it kernel-side.

Fails closed three ways: an idle core has no subject (`.illegalState`), an index
outside the caller's own view or a chunk past a field's width is
`.invalidArgument`, and a value too wide to export is `.auditFieldTooLarge`.

**The `2 ^ 64` guard is not decoration.**  The boundary hands the word back
through a 64-bit register, and `Nat.toUInt64` *truncates*.  Every arm but
`status` is structurally below that bound; `status` carries the epoch, an
unbounded monotone counter, so the guard is what turns "would silently wrap
after 2^55 drains" into a refused read (`auditReadFromCore_word_fits`). -/
def auditReadFromCore (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (c : CoreId)
    (op : AuditReadOp) : Kernel Nat :=
  fun st =>
    match auditReaderDomain ctx st c with
    | none => .error .illegalState
    | some reader =>
        match auditReadWord ctx monitorClearance reader st op with
        | .error e => .error e
        | .ok w => if w < 2 ^ 64 then .ok (w, st) else .error .auditFieldTooLarge

/-- WS-SM SM9.A.10: an idle core cannot read the trail — there is no subject
whose clearance would select a view, so the operation fails closed and the state
is untouched. -/
theorem auditReadFromCore_no_subject (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (c : CoreId) (op : AuditReadOp)
    (st : SystemState) (hIdle : st.scheduler.currentOnCore c = none) :
    auditReadFromCore ctx monitorClearance c op st = .error .illegalState := by
  simp [auditReadFromCore, auditReaderDomain, hIdle]

/-- WS-SM SM9.A.10 (**the frame**): a read writes **nothing**.  The post-state
is the pre-state, on the nose. -/
theorem auditReadFromCore_frame (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (c : CoreId) (op : AuditReadOp)
    (st : SystemState) (w : Nat) (st' : SystemState)
    (hStep : auditReadFromCore ctx monitorClearance c op st = .ok (w, st')) :
    st' = st := by
  unfold auditReadFromCore at hStep
  split at hStep
  · exact absurd hStep (by simp)
  · split at hStep
    · exact absurd hStep (by simp)
    · split at hStep
      · simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
        exact hStep.2.symm
      · exact absurd hStep (by simp)

/-- WS-SM SM9.A.10: **every word the reader returns fits the return register.**

What the `2 ^ 64` guard buys: the `Nat → UInt64` conversion at the boundary is
lossless on everything the reader accepts, so a monitor never reads a truncated
value and mistakes it for a real one. -/
theorem auditReadFromCore_word_fits (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (c : CoreId) (op : AuditReadOp)
    (st : SystemState) (w : Nat) (st' : SystemState)
    (hStep : auditReadFromCore ctx monitorClearance c op st = .ok (w, st')) :
    w < 2 ^ 64 := by
  unfold auditReadFromCore at hStep
  split at hStep
  · exact absurd hStep (by simp)
  · split at hStep
    · exact absurd hStep (by simp)
    · rename_i hFits
      split at hStep
      · simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
        rename_i hLt
        exact hStep.1 ▸ hLt
      · exact absurd hStep (by simp)

/-- WS-SM SM9.A.10: the returned word survives the boundary conversion — the
consumer-facing form of `auditReadFromCore_word_fits`. -/
theorem auditReadFromCore_toUInt64_lossless (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (c : CoreId) (op : AuditReadOp)
    (st : SystemState) (w : Nat) (st' : SystemState)
    (hStep : auditReadFromCore ctx monitorClearance c op st = .ok (w, st')) :
    w.toUInt64.toNat = w := by
  have hFits := auditReadFromCore_word_fits ctx monitorClearance c op st w st' hStep
  simpa using Nat.mod_eq_of_lt hFits

/-- WS-SM SM9.A.10: **the read the caller asked for is the read it gets.**

The value is `auditReadWord` at the resolved reader's clearance — not at a
default, not at the monitor's.  Load-bearing for the end-to-end assertion that
the returned word is the *selected* one rather than whatever happened to be in
the caller's `x0`. -/
theorem auditReadFromCore_value (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (c : CoreId) (op : AuditReadOp)
    (st : SystemState) (reader : SecurityDomain) (w : Nat) (st' : SystemState)
    (hReader : auditReaderDomain ctx st c = some reader)
    (hStep : auditReadFromCore ctx monitorClearance c op st = .ok (w, st')) :
    auditReadWord ctx monitorClearance reader st op = .ok w := by
  simp only [auditReadFromCore, hReader] at hStep
  split at hStep
  · exact absurd hStep (by simp)
  · rename_i v hRead
    split at hStep
    · simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
      exact hStep.1 ▸ hRead
    · exact absurd hStep (by simp)


end SeLe4n.Kernel
