-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-SM (SM2.A abstract memory model; closes the
-- happens-before partial-order foundation that SM2.B TicketLock and
-- SM2.C RwLock proofs consume for release/acquire pairing).

import SeLe4n.Kernel.Concurrency.Types

/-!
# WS-SM SM2.A — Abstract memory model for verified lock primitives

This module captures enough of ARMv8.1-A LSE atomic semantics to
prove the lock primitives correct.  The model is **operational**:
a trace is a sequence of memory events on shared atomic locations;
the synchronizes-with relation is derived from event order;
happens-before is the inductive transitive closure.

The four substantive theorems exported by this module form the
foundation that every SM2.B / SM2.C lock-primitive proof rests on:

* `happensBefore_irreflexive`  — no event happens-before itself
* `happensBefore_transitive`   — happens-before is closed under
                                  composition (immediate by ctor)
* `happensBefore_antisymmetric` — distinct events cannot both
                                  happens-before the other
* `happens_before_partial_order` — aggregate of the three above,
                                    the canonical surface anchor

## ARM ARM citations

The abstract memory model captures, operationally, the following
hardware properties.  Each is sourced from a public ARMv8-A
Architecture Reference Manual (ARM ARM) section and is encoded
operationally (no `axioms` introduced) by the constraints on the
`synchronizesWith` and `happensBefore` predicates.

* **ARM ARM B2.3.7** (Release/Acquire ordering): a Release-store on
  a location L synchronizes-with the next Acquire-load on L that
  observes the released value.  Encoded by `synchronizesWith`'s
  conjuncts requiring `e_R.isWrite ∧ e_R.order.isRelease ∧
  ¬ e_A.isWrite ∧ e_A.order.isAcquire ∧ e_R.loc = e_A.loc ∧
  e_R.value = e_A.value`.
* **ARM ARM B2.10** (Local event register / WFE-SEV): captured at
  the lock-primitive level (SM2.B), not in the abstract model.
* **ARM ARM C6.2.* LDADD/STADD/CAS family** (ARMv8.1-A LSE): the
  atomic RMW (Read-Modify-Write) instructions are modelled as two
  back-to-back events (load + store) on the same `seqNum`; this
  module exports the `MemoryEvent` shape so SM2.B's TicketLock can
  encode `next_ticket.fetch_add(1, Acquire)` as a single trace
  position with both events.
* **ARM ARM K11.2** (Memory model — happens-before): hb is
  irreflexive, transitive, antisymmetric on the events of a
  well-formed execution.  Encoded by Theorems 3.1.8.1 / 3.1.8.2 /
  3.1.8.3 below, aggregated into `happens_before_partial_order`.

## Axiom budget

Zero Lean `axioms`.  All hardware semantics enter as operational
constraints on the trace shape; no proof gaps either (no `sorries`).

## Decidability

`MemoryTrace.wellFormed` carries a `Decidable` instance so test
fixtures can construct traces and `decide` their well-formedness at
elaboration time.  `synchronizesWith` and `happensBefore` are
*propositions* (not booleans) — they are used to state lock-primitive
theorems, not to drive runtime control flow, so decidability of the
inductive `happensBefore` is not required.

## File scope and reuse

This file is the entry point for SM2.A; SM2.B
(`Concurrency/Locks/TicketLock.lean`) and SM2.C
(`Concurrency/Locks/RwLock.lean`) import this module to obtain
`MemoryOrder`, `MemoryTrace`, `synchronizesWith`, and the
`happens_before_partial_order` aggregate for their release/acquire
pairing theorems.
-/

namespace SeLe4n.Kernel.Concurrency

-- ============================================================================
-- SM2.A.1 — MemoryOrder
-- ============================================================================

/-- **WS-SM SM2.A.1**: ARMv8.1-A / C++20 memory-order tag attached
to every atomic memory event.

* `.relaxed` — no inter-thread synchronisation.  Models the raw
  ARM `LDR` / `STR` of an atomic location without an acquire/release
  suffix.  Used for performance-critical reads of the lock state
  that are immediately followed by a CAS retry.
* `.acquire` — acquire-load.  Models `LDAR` / `LDA*` family; reads
  the location AND establishes a synchronizes-with edge with the
  release-store that produced the observed value.
* `.release` — release-store.  Models `STLR` / `STL*` family; writes
  the location AND publishes every sequenced-before write on this
  core to any acquire-load that observes this value.
* `.acqRel` — both acquire and release semantics.  Models LSE RMW
  ops with both suffixes (`LDAXR`/`STLXR` pairs, `LDADDAL`,
  `CASAL`).  Used by the TicketLock `fetch_add` to capture a ticket.
* `.seqCst` — sequentially consistent.  Models the strongest
  ordering (acquire ∧ release ∧ single-total-order semantics).  Not
  used by v1.0.0 lock primitives but defined for completeness so
  future SM2.x phases can introduce SC ops without changing the
  inductive.

`DecidableEq` is derived (5 enum constructors) so the order can be
pattern-matched at decide-time. -/
inductive MemoryOrder where
  | relaxed
  | acquire
  | release
  | acqRel
  | seqCst
  deriving DecidableEq, Repr, Inhabited

/-- **WS-SM SM2.A.1**: `MemoryOrder.isAcquire` — true iff the order
synchronises an *observer* with prior release-stores.  Used by
`synchronizesWith` to gate the acquire-load side. -/
def MemoryOrder.isAcquire : MemoryOrder → Bool
  | .acquire | .acqRel | .seqCst => true
  | _ => false

/-- **WS-SM SM2.A.1**: `MemoryOrder.isRelease` — true iff the order
publishes prior writes to subsequent acquire-loads.  Used by
`synchronizesWith` to gate the release-store side. -/
def MemoryOrder.isRelease : MemoryOrder → Bool
  | .release | .acqRel | .seqCst => true
  | _ => false

/-- Witness: `.acquire` is acquire-strength. -/
theorem MemoryOrder.acquire_isAcquire :
    MemoryOrder.acquire.isAcquire = true := rfl

/-- Witness: `.release` is release-strength. -/
theorem MemoryOrder.release_isRelease :
    MemoryOrder.release.isRelease = true := rfl

/-- Witness: `.acqRel` is both acquire and release. -/
theorem MemoryOrder.acqRel_both :
    MemoryOrder.acqRel.isAcquire = true ∧
    MemoryOrder.acqRel.isRelease = true :=
  ⟨rfl, rfl⟩

/-- Witness: `.seqCst` is both acquire and release.  Required so
sequentially-consistent ops can stand in for either side of an
RA-pairing argument. -/
theorem MemoryOrder.seqCst_both :
    MemoryOrder.seqCst.isAcquire = true ∧
    MemoryOrder.seqCst.isRelease = true :=
  ⟨rfl, rfl⟩

/-- Witness: `.relaxed` is neither acquire nor release.  Required so
relaxed events cannot participate in a synchronizes-with edge. -/
theorem MemoryOrder.relaxed_neither :
    MemoryOrder.relaxed.isAcquire = false ∧
    MemoryOrder.relaxed.isRelease = false :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- SM2.A.2 — AtomicLocation
-- ============================================================================

/-- **WS-SM SM2.A.2**: identifier for an atomic memory location.

The lock primitives use a small fixed set of locations:
* TicketLock: 2 locations per instance (`nextTicket`, `serving`).
* RwLock: 1 location per instance (the packed `state`).

The `id` field is an opaque `Nat` here; SM2.B and SM2.C assign
concrete IDs via the module-local helpers below (`nextTicketOf`,
`servingOf`, `rwLockStateOf`).  Each lock instance offsets the
base ID so distinct instances do not alias.

`DecidableEq` lets event predicates that compare locations be
checked at decide-time. -/
structure AtomicLocation where
  /-- Numeric identifier for the location.  The lock primitives
  use a small fixed encoding; see the helpers below. -/
  id : Nat
  deriving DecidableEq, Repr, Inhabited

/-- **WS-SM SM2.A.2**: concrete location ID for a TicketLock's
`nextTicket` field within a lock instance with base ID `base`.

The encoding `base + 0` and `base + 1` reserves two slots per
TicketLock instance.  SM2.B wires this to the Rust struct's
`next_ticket: AtomicU64` field at the same offset; the refinement
relation φ uses this correspondence to match Lean trace events to
Rust atomic operations. -/
def AtomicLocation.nextTicketOf (base : Nat) : AtomicLocation :=
  ⟨base⟩

/-- **WS-SM SM2.A.2**: concrete location ID for a TicketLock's
`serving` field. -/
def AtomicLocation.servingOf (base : Nat) : AtomicLocation :=
  ⟨base + 1⟩

/-- **WS-SM SM2.A.2**: concrete location ID for an RwLock's packed
`state` field. -/
def AtomicLocation.rwLockStateOf (base : Nat) : AtomicLocation :=
  ⟨base⟩

/-- Witness: distinct TicketLock fields at the same base do not
alias.  Trivial by structural inequality on the `id` field. -/
theorem AtomicLocation.ticketLock_fields_distinct (base : Nat) :
    AtomicLocation.nextTicketOf base ≠ AtomicLocation.servingOf base := by
  intro h
  have hcong : (AtomicLocation.nextTicketOf base).id
              = (AtomicLocation.servingOf base).id :=
    congrArg AtomicLocation.id h
  simp [AtomicLocation.nextTicketOf, AtomicLocation.servingOf] at hcong

-- ============================================================================
-- SM2.A.3 — MemoryEvent
-- ============================================================================

/-- **WS-SM SM2.A.3**: an atomic memory operation observed in an
execution.

A trace is a sequence of these events; theorems quantify over all
events in a well-formed trace.  Fields:

* `core` — which `CoreId` executed the event.  Per-core sequencing
  numbers (`seqNum` below) are scoped by this field.
* `loc` — which `AtomicLocation` was read or written.
  `synchronizesWith` requires both endpoints to share this field.
* `isWrite` — true iff the event is a store; false iff it is a load.
  Read-Modify-Write operations (the LSE atomics) are modelled as
  two events with the same `seqNum` (one load + one store).
* `order` — the `MemoryOrder` tag.  Determines which synchronisation
  edges this event can participate in.
* `value` — for stores, the written value; for loads, the observed
  value.  `synchronizesWith` requires equality of this field across
  the release-store / acquire-load pair (the acquire side observes
  the released value).
* `seqNum` — per-core sequencing number.  Same-core events with
  strictly smaller `seqNum` happen-before same-core events with
  larger `seqNum` (this is the `sequencedBefore` relation).  Each
  core emits a monotonically non-decreasing sequence (equal seqNums
  allowed for RMW load + store pairs at one atomic op; strict
  inequality required for `sequencedBefore` to fire).

`DecidableEq` is derived (all fields have `DecidableEq`) so events
can be compared at decide-time and traces can carry `Nodup`. -/
structure MemoryEvent where
  /-- The core that executed this event. -/
  core    : CoreId
  /-- The atomic memory location accessed. -/
  loc     : AtomicLocation
  /-- True iff the event is a store (write).  False iff a load. -/
  isWrite : Bool
  /-- The memory-order tag of the operation. -/
  order   : MemoryOrder
  /-- Written value (stores) or observed value (loads). -/
  value   : Nat
  /-- Per-core sequencing number.  Non-strictly monotonic within a
  single core (allows RMW load + store at the same `seqNum`); not
  comparable across cores.  Strict-`<` ordering between distinct
  ops is implied by the `sequencedBefore` relation. -/
  seqNum  : Nat
  deriving DecidableEq, Repr, Inhabited

-- ============================================================================
-- SM2.A.4 — MemoryTrace + empty + append
-- ============================================================================

/-- **WS-SM SM2.A.4**: a finite sequence of memory events observed
during an execution.

The operational semantics of the lock primitives generates a trace
event-by-event; theorems quantify over all reachable traces and
require well-formedness (`MemoryTrace.wellFormed`). -/
structure MemoryTrace where
  /-- The event sequence, in execution order (earliest first). -/
  events : List MemoryEvent
  deriving Repr, Inhabited

/-- **WS-SM SM2.A.4**: the empty trace.  Used as the seed of any
operational-semantics fold. -/
def MemoryTrace.empty : MemoryTrace := { events := [] }

/-- **WS-SM SM2.A.4**: append a single event to the trace.  The new
event becomes the latest in execution order.

This is the only way to grow a trace; SM2.B / SM2.C use this to
encode the operational semantics of each lock primitive operation
step-by-step. -/
def MemoryTrace.append (t : MemoryTrace) (e : MemoryEvent) : MemoryTrace :=
  { events := t.events ++ [e] }

/-- Witness: `empty` has no events. -/
theorem MemoryTrace.empty_events : MemoryTrace.empty.events = [] := rfl

/-- Witness: `append` extends the trace by one event at the tail. -/
theorem MemoryTrace.append_events (t : MemoryTrace) (e : MemoryEvent) :
    (t.append e).events = t.events ++ [e] := rfl

/-- Witness: `append` increases the trace length by exactly one. -/
theorem MemoryTrace.append_length (t : MemoryTrace) (e : MemoryEvent) :
    (t.append e).events.length = t.events.length + 1 := by
  simp [MemoryTrace.append]

-- ============================================================================
-- SM2.A.5 — wellFormed
-- ============================================================================

/-- **WS-SM SM2.A.5**: well-formedness predicate for a memory trace.

A trace is well-formed iff:

1. **Events are unique** (`Nodup`).  No event appears twice in the
   trace: this rules out the degenerate "same event observed twice"
   case and lets every event have a unique position.
2. **Per-core seqNum monotonicity** (`Pairwise`).  For any two
   events `e₁`, `e₂` that share a core, if `e₁` appears earlier in
   the trace than `e₂`, then `e₁.seqNum ≤ e₂.seqNum`.  Encodes
   ARM ARM K11.2's per-PE program order.

The two clauses together imply that within a single core's view of
the trace (the filtered subsequence of same-core events), the
seqNums are monotonic non-decreasing — which in turn is the
foundation of the happens-before partial order's irreflexivity (the
strict `<` in `sequencedBefore` handles the strictness side).

**Why `≤` (non-strict) and not `<` (strict)?**  ARMv8.1-A LSE atomic
Read-Modify-Write operations (`LDADDA`, `STADDL`, `CASAL`, …) are
modelled at the trace level as TWO events sharing one `seqNum`: a
load with the pre-value and a store with the post-value.  Both
events occur atomically on the same core, so the per-core trace
necessarily contains pairs `(e_load, e_store)` with
`e_load.seqNum = e_store.seqNum`.  A strict `<` would reject all
RMW traces — including `TicketLock.acquire`'s
`next_ticket.fetch_add(1, Acquire)` — which would block SM2.B's
proofs.  The non-strict `≤` allows RMW pairs while still preventing
seqNum DECREASE within a core (the property that drives the
happens-before partial order).  The strict ordering for non-RMW
event pairs is recovered by the per-event `Nodup` clause plus the
strict `<` in `sequencedBefore` (which gates happens-before edges
to genuinely distinct seqNums).

`Pairwise` formulation: `List.Pairwise R l` holds iff for every
pair of elements `(x, y)` with `x` appearing strictly before `y`
in `l`, `R x y` holds.  Decidable when `R` is decidable. -/
def MemoryTrace.wellFormed (t : MemoryTrace) : Prop :=
  t.events.Nodup ∧
  List.Pairwise
    (fun e₁ e₂ => e₁.core = e₂.core → e₁.seqNum ≤ e₂.seqNum)
    t.events

/-- **WS-SM SM2.A.5**: `wellFormed` is decidable.

Both conjuncts are decidable:

* `Nodup` requires `DecidableEq MemoryEvent` (which we have via
  `deriving DecidableEq`).
* `Pairwise R l` is decidable when `R` is decidable.  Our `R` is
  `e₁.core = e₂.core → e₁.seqNum < e₂.seqNum`, which is the
  implication of two decidable propositions, hence decidable. -/
instance (t : MemoryTrace) : Decidable t.wellFormed := by
  unfold MemoryTrace.wellFormed
  exact inferInstance

/-- Witness: the empty trace is well-formed.  Both clauses hold
vacuously. -/
theorem MemoryTrace.empty_wellFormed : MemoryTrace.empty.wellFormed := by
  refine ⟨?_, ?_⟩ <;> simp [MemoryTrace.empty]

-- ============================================================================
-- Foundational helper lemmas (private, file-local)
-- ============================================================================

/-- Foundational helper: in a list, the Pairwise relation lifts to
strict positional ordering.

If `l.Pairwise R` and positions `i < j` are both in range, then
`R (l.get ⟨i, _⟩) (l.get ⟨j, _⟩)`.

Provable by induction on `l`; used by `happensBefore_strict_positional`
in the `.seq` case to bridge Pairwise to the per-core seqNum monotonicity. -/
private theorem pairwise_get_lt {α : Type _} {R : α → α → Prop} :
    ∀ {l : List α}, l.Pairwise R → ∀ {i j : Nat}
      (hi : i < l.length) (hj : j < l.length),
      i < j → R (l.get ⟨i, hi⟩) (l.get ⟨j, hj⟩) := by
  intro l h
  induction h with
  | nil => intro i j hi _ _; exact absurd hi (Nat.not_lt_zero _)
  | @cons x xs h_head h_tail ih =>
    intro i j hi hj hij
    cases i with
    | zero =>
      cases j with
      | zero => exact absurd hij (Nat.lt_irrefl _)
      | succ j' =>
        have hj' : j' < xs.length := Nat.lt_of_succ_lt_succ hj
        -- (x :: xs).get ⟨0, _⟩ = x
        -- (x :: xs).get ⟨j' + 1, _⟩ = xs.get ⟨j', hj'⟩
        show R x (xs.get ⟨j', hj'⟩)
        exact h_head _ (List.get_mem xs ⟨j', hj'⟩)
    | succ i' =>
      cases j with
      | zero => exact absurd hij (Nat.not_lt_zero _)
      | succ j' =>
        have hi' : i' < xs.length := Nat.lt_of_succ_lt_succ hi
        have hj' : j' < xs.length := Nat.lt_of_succ_lt_succ hj
        have hij' : i' < j' := Nat.lt_of_succ_lt_succ hij
        show R (xs.get ⟨i', hi'⟩) (xs.get ⟨j', hj'⟩)
        exact ih hi' hj' hij'

-- ============================================================================
-- SM2.A.5 — eventPos helper
-- ============================================================================

/-- **WS-SM SM2.A.5**: position of an event in a trace.

For events in the trace, returns the (unique under `Nodup`) index
at which it first appears (via `List.idxOf`).  For events not in
the trace, returns `t.events.length` as a sentinel (one past the
last index).

This is the canonical "trace order" used by `synchronizesWith` and
the happens-before strict-positional lemma. -/
def MemoryTrace.eventPos (t : MemoryTrace) (e : MemoryEvent) : Nat :=
  t.events.idxOf e

/-- Foundational property: for an event in the trace, `eventPos`
returns a valid index.  Discharged from `List.idxOf_lt_length_of_mem`. -/
theorem MemoryTrace.eventPos_lt_length {t : MemoryTrace} {e : MemoryEvent}
    (h : e ∈ t.events) : t.eventPos e < t.events.length :=
  List.idxOf_lt_length_of_mem h

/-- Foundational property: for an event NOT in the trace, `eventPos`
returns the sentinel `t.events.length`.  Useful for distinguishing
in-trace events from out-of-trace events. -/
theorem MemoryTrace.eventPos_eq_length_of_not_mem {t : MemoryTrace}
    {e : MemoryEvent} (h : e ∉ t.events) :
    t.eventPos e = t.events.length :=
  List.idxOf_eq_length h

/-- Foundational property: for an event in the trace, `eventPos`
returns the canonical position at which it appears.

Uses `List.findIdx_getElem` (which says `p xs[xs.findIdx p]` holds
when the index is in range) and `LawfulBEq` (derived for our
`MemoryEvent` via `DecidableEq`) to lift `(xs[idx] == e) = true`
to `xs[idx] = e`. -/
theorem MemoryTrace.eventPos_get_eq {t : MemoryTrace} {e : MemoryEvent}
    (h : e ∈ t.events) :
    t.events.get ⟨t.eventPos e, t.eventPos_lt_length h⟩ = e := by
  unfold MemoryTrace.eventPos List.idxOf
  -- Use findIdx_getElem: for the (· == e) predicate, the element at
  -- findIdx satisfies the predicate.
  have h_lt : t.events.findIdx (· == e) < t.events.length :=
    List.idxOf_lt_length_of_mem h
  have h_pred : (t.events.get ⟨t.events.findIdx (· == e), h_lt⟩) == e := by
    rw [List.get_eq_getElem]
    exact List.findIdx_getElem (w := h_lt)
  exact LawfulBEq.eq_of_beq h_pred

/-- Foundational property: `eventPos` is injective on in-trace events.

Two in-trace events at the same position must be equal; equivalently,
two distinct in-trace events have distinct positions.  This is the
"position uniqueness" property that drives the irreflexivity of
`happensBefore` (an event cannot precede itself).

**Note on the Nodup hypothesis**: the lemma deliberately does NOT
take a `Nodup` premise.  The proof relies only on `eventPos` being
a *function* (`idxOf` returns the index of the FIRST occurrence) —
so two events whose first occurrences are at the same index must be
equal, because each index in the list refers to a single element.
The Nodup property is a stronger consequence carried by
`MemoryTrace.wellFormed`, but the position-uniqueness of `eventPos`
holds for any list. -/
theorem MemoryTrace.eventPos_inj {t : MemoryTrace}
    {e₁ e₂ : MemoryEvent} (h₁ : e₁ ∈ t.events) (h₂ : e₂ ∈ t.events)
    (h_eq : t.eventPos e₁ = t.eventPos e₂) : e₁ = e₂ := by
  -- Both events appear at their canonical positions.
  have g₁ : t.events.get ⟨t.eventPos e₁, t.eventPos_lt_length h₁⟩ = e₁ :=
    t.eventPos_get_eq h₁
  have g₂ : t.events.get ⟨t.eventPos e₂, t.eventPos_lt_length h₂⟩ = e₂ :=
    t.eventPos_get_eq h₂
  -- Since positions are equal (Fin equality), the gets are equal
  -- (via congrArg, which avoids the motive-not-type-correct issue
  -- that a direct `rw [h_eq]` would hit on the dependent index).
  have h_fin_eq :
      (⟨t.eventPos e₁, t.eventPos_lt_length h₁⟩ : Fin t.events.length) =
      (⟨t.eventPos e₂, t.eventPos_lt_length h₂⟩ : Fin t.events.length) :=
    Fin.eq_of_val_eq h_eq
  calc e₁
      = t.events.get ⟨t.eventPos e₁, t.eventPos_lt_length h₁⟩ := g₁.symm
    _ = t.events.get ⟨t.eventPos e₂, t.eventPos_lt_length h₂⟩ :=
        congrArg t.events.get h_fin_eq
    _ = e₂ := g₂

-- ============================================================================
-- SM2.A.6 — synchronizesWith
-- ============================================================================

/-- **WS-SM SM2.A.6**: synchronizes-with relation on memory events.

An event `e_R` synchronizes-with an event `e_A` iff:

1. Both `e_R` and `e_A` appear in the trace `t`.
2. `e_R` is a release-store: `isWrite = true ∧ order.isRelease`.
3. `e_A` is an acquire-load: `isWrite = false ∧ order.isAcquire`.
4. They access the same atomic location: `e_R.loc = e_A.loc`.
5. The acquire-load observes the released value: `e_R.value = e_A.value`.
6. `e_R` precedes `e_A` in the trace's positional order.

This is the basic synchronisation edge per **ARM ARM B2.3.7** and
the C++20 / Rust release-acquire memory-model rule.  Constructed
into a partial order by the `happensBefore` transitive closure. -/
def synchronizesWith (t : MemoryTrace) (e_R e_A : MemoryEvent) : Prop :=
  e_R ∈ t.events ∧
  e_A ∈ t.events ∧
  e_R.isWrite = true ∧
  e_R.order.isRelease = true ∧
  e_A.isWrite = false ∧
  e_A.order.isAcquire = true ∧
  e_R.loc = e_A.loc ∧
  e_R.value = e_A.value ∧
  t.eventPos e_R < t.eventPos e_A

/-- Witness: relaxed loads cannot be the acquire side of a sync
edge.  Demonstrates the gate on `order.isAcquire = true`. -/
theorem synchronizesWith_relaxed_load_rejected (t : MemoryTrace)
    (e_R e_A : MemoryEvent) (h : synchronizesWith t e_R e_A) :
    e_A.order ≠ .relaxed := by
  intro h_relaxed
  have h_acq : e_A.order.isAcquire = true := h.2.2.2.2.2.1
  rw [h_relaxed] at h_acq
  exact absurd h_acq (by simp [MemoryOrder.isAcquire])

/-- Witness: relaxed stores cannot be the release side of a sync
edge.  Demonstrates the gate on `order.isRelease = true`. -/
theorem synchronizesWith_relaxed_store_rejected (t : MemoryTrace)
    (e_R e_A : MemoryEvent) (h : synchronizesWith t e_R e_A) :
    e_R.order ≠ .relaxed := by
  intro h_relaxed
  have h_rel : e_R.order.isRelease = true := h.2.2.2.1
  rw [h_relaxed] at h_rel
  exact absurd h_rel (by simp [MemoryOrder.isRelease])

-- ============================================================================
-- SM2.A.7 — sequencedBefore + happensBefore
-- ============================================================================

/-- **WS-SM SM2.A.7**: per-core sequenced-before order.

An event `e₁` is sequenced-before `e₂` iff both events appear in
the trace, share a core, and `e₁.seqNum < e₂.seqNum`.

Trace membership is required so the per-core view of a well-formed
trace provides positional ordering.  Without it, `sequencedBefore`
would be a pure "this fictitious event would precede that one"
relation that doesn't lift to positions in the actual trace. -/
def sequencedBefore (t : MemoryTrace) (e₁ e₂ : MemoryEvent) : Prop :=
  e₁ ∈ t.events ∧
  e₂ ∈ t.events ∧
  e₁.core = e₂.core ∧
  e₁.seqNum < e₂.seqNum

/-- **WS-SM SM2.A.7**: happens-before relation as an inductive
transitive closure.

The three constructors:

* `.seq sb` — `e₁` is sequenced-before `e₂` (same-core, smaller
  seqNum, both in the trace).
* `.sync sw` — `e_R` synchronizes-with `e_A` (release-store ↦
  matching acquire-load).
* `.trans h₁ h₂` — transitive composition.

The inductive's parameter `t : MemoryTrace` is implicit in every
edge so the per-trace partial-order theorems can be stated uniformly
across all reachable traces.

**ARM ARM K11.2**: `hb` is irreflexive, transitive, antisymmetric
on the events of a well-formed execution; defines a partial order. -/
inductive happensBefore (t : MemoryTrace) : MemoryEvent → MemoryEvent → Prop where
  /-- Lift a sequenced-before edge to happens-before. -/
  | seq : ∀ {e₁ e₂}, sequencedBefore t e₁ e₂ → happensBefore t e₁ e₂
  /-- Lift a synchronizes-with edge to happens-before. -/
  | sync : ∀ {e_R e_A}, synchronizesWith t e_R e_A → happensBefore t e_R e_A
  /-- Transitive closure: composition of two hb edges is an hb edge. -/
  | trans : ∀ {e₁ e₂ e₃}, happensBefore t e₁ e₂ → happensBefore t e₂ e₃ →
            happensBefore t e₁ e₃

-- ============================================================================
-- §3.1.7 — Trace-membership lemma
-- ============================================================================

/-- Foundational lemma: every `happensBefore` edge has both
endpoints in the trace.

Proof: induction on the `happensBefore` derivation.  Each base case
extracts trace membership from the underlying relation; the
transitive case discharges by IH on either side. -/
theorem happensBefore_in_trace (t : MemoryTrace) :
    ∀ {e₁ e₂}, happensBefore t e₁ e₂ → e₁ ∈ t.events ∧ e₂ ∈ t.events := by
  intro e₁ e₂ h
  induction h with
  | seq sb => exact ⟨sb.1, sb.2.1⟩
  | sync sw => exact ⟨sw.1, sw.2.1⟩
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩

-- ============================================================================
-- §3.1.7 — Strict positional ordering for happensBefore
-- ============================================================================

/-- **Foundational lemma for SM2.A.8/.10**: every `happensBefore`
edge strictly increases the trace position.

This is the inductive invariant that drives both irreflexivity and
antisymmetry: if `happensBefore t e₁ e₂` holds, then
`eventPos t e₁ < eventPos t e₂`, so no event can happens-before
itself and no two distinct events can be mutually hb-related.

Proof: induction on the `happensBefore` derivation.

* `.seq sb`: `sb` says `e₁.core = e₂.core ∧ e₁.seqNum < e₂.seqNum`.
  By `wellFormed`'s Pairwise clause, the same-core seqNum ordering
  implies positional ordering when both events are in the trace.

* `.sync sw`: `sw` includes `eventPos e_R < eventPos e_A` as a
  conjunct directly.

* `.trans h₁ h₂`: by IH, both edges strictly increase position; the
  composition strictly increases position by transitivity of `<`. -/
theorem happensBefore_strict_positional {t : MemoryTrace}
    (h_wf : t.wellFormed) :
    ∀ {e₁ e₂}, happensBefore t e₁ e₂ → t.eventPos e₁ < t.eventPos e₂ := by
  intro e₁ e₂ h
  induction h with
  | @seq a b sb =>
      obtain ⟨ha, hb, hcore, hseq⟩ := sb
      have h_pairwise : List.Pairwise
          (fun e₁ e₂ => e₁.core = e₂.core → e₁.seqNum ≤ e₂.seqNum)
          t.events := h_wf.2
      have h_pa_lt : t.eventPos a < t.events.length := t.eventPos_lt_length ha
      have h_pb_lt : t.eventPos b < t.events.length := t.eventPos_lt_length hb
      have h_get_a : t.events.get ⟨t.eventPos a, h_pa_lt⟩ = a :=
        t.eventPos_get_eq ha
      have h_get_b : t.events.get ⟨t.eventPos b, h_pb_lt⟩ = b :=
        t.eventPos_get_eq hb
      rcases Nat.lt_trichotomy (t.eventPos a) (t.eventPos b) with hlt | heq | hgt
      · exact hlt
      · -- positions equal → a = b (by eventPos_inj); but the strict
        -- `hseq : a.seqNum < b.seqNum` then becomes `a.seqNum < a.seqNum`.
        have h_ab : a = b := t.eventPos_inj ha hb heq
        rw [h_ab] at hseq
        exact absurd hseq (Nat.lt_irrefl _)
      · -- p_b < p_a: applying the Pairwise relation at the swapped
        -- positions (p_b earlier, p_a later) gives the non-strict
        -- ordering `b.seqNum ≤ a.seqNum`.  Combined with the strict
        -- `hseq : a.seqNum < b.seqNum`, transitivity yields
        -- `a.seqNum < a.seqNum`, contradiction.
        have h_rel := pairwise_get_lt h_pairwise h_pb_lt h_pa_lt hgt
        rw [h_get_a, h_get_b] at h_rel
        have h_le_sym : b.seqNum ≤ a.seqNum := h_rel hcore.symm
        exact absurd (Nat.lt_of_lt_of_le hseq h_le_sym) (Nat.lt_irrefl _)
  | @sync _ _ sw =>
      -- Destructure synchronizesWith to extract the positional clause
      -- by name rather than the fragile `.2.2.2.2.2.2.2.2` chain.
      obtain ⟨_, _, _, _, _, _, _, _, h_pos⟩ := sw
      exact h_pos
  | @trans _ _ _ _ _ ih₁ ih₂ =>
      exact Nat.lt_trans ih₁ ih₂

-- ============================================================================
-- SM2.A.8 — happensBefore_irreflexive
-- ============================================================================

/-- **Theorem 3.1.8.1 (SM2.A.8): happens-before is irreflexive.**

For any well-formed trace `t` and any event `e`,
`¬ happensBefore t e e`.

Proof: by the strict-positional lemma, `happensBefore t e e` would
give `eventPos e < eventPos e`, contradicting `Nat.lt_irrefl`. -/
theorem happensBefore_irreflexive {t : MemoryTrace}
    (h_wf : t.wellFormed) (e : MemoryEvent) :
    ¬ happensBefore t e e := by
  intro h
  have hpos := happensBefore_strict_positional h_wf h
  exact absurd hpos (Nat.lt_irrefl _)

-- ============================================================================
-- SM2.A.9 — happensBefore_transitive
-- ============================================================================

/-- **Theorem 3.1.8.2 (SM2.A.9): happens-before is transitive.**

For any well-formed trace `t` and any events `e₁`, `e₂`, `e₃`:
`happensBefore t e₁ e₂ → happensBefore t e₂ e₃ → happensBefore t e₁ e₃`.

Proof: immediate from the `.trans` constructor of `happensBefore`.

The `h_wf` premise is taken for uniformity with the irreflexive
and antisymmetric signatures, even though the `.trans` constructor
needs no premise. -/
theorem happensBefore_transitive {t : MemoryTrace}
    (_h_wf : t.wellFormed) :
    ∀ {e₁ e₂ e₃ : MemoryEvent},
      happensBefore t e₁ e₂ → happensBefore t e₂ e₃ → happensBefore t e₁ e₃ :=
  fun h₁ h₂ => happensBefore.trans h₁ h₂

-- ============================================================================
-- SM2.A.10 — happensBefore_antisymmetric
-- ============================================================================

/-- **Theorem 3.1.8.3 (SM2.A.10): happens-before is antisymmetric.**

For any well-formed trace `t` and any distinct events `e₁`, `e₂`,
NOT both `happensBefore t e₁ e₂` AND `happensBefore t e₂ e₁` hold.

Proof: by the strict-positional lemma, both edges would give
`eventPos e₁ < eventPos e₂` AND `eventPos e₂ < eventPos e₁`,
contradicting `Nat.lt_asymm`.

Note that we don't actually need `e₁ ≠ e₂` for this proof — even
identical events fail (irreflexivity).  We keep the hypothesis in
the statement to match the standard "antisymmetric on distinct
elements" formulation. -/
theorem happensBefore_antisymmetric {t : MemoryTrace}
    (h_wf : t.wellFormed) (e₁ e₂ : MemoryEvent) (_h_ne : e₁ ≠ e₂) :
    ¬ (happensBefore t e₁ e₂ ∧ happensBefore t e₂ e₁) := by
  intro ⟨h_fwd, h_bwd⟩
  have h_fwd_pos := happensBefore_strict_positional h_wf h_fwd
  have h_bwd_pos := happensBefore_strict_positional h_wf h_bwd
  exact Nat.lt_asymm h_fwd_pos h_bwd_pos

-- ============================================================================
-- SM2.A.11 — happens_before_partial_order (aggregate)
-- ============================================================================

/-- **Theorem 3.1.8 (SM2.A.11): happens-before is a partial order.**

The aggregate theorem combining irreflexivity, transitivity, and
antisymmetry into a single statement.  This is the canonical
surface anchor referenced by SM2.B / SM2.C lock-primitive theorems
to invoke "release-acquire pairing establishes a partial order on
the lock state's observation events."

The three conjuncts:
1. Irreflexive: no event happens-before itself.
2. Transitive: hb is closed under composition.
3. Antisymmetric: distinct events cannot be mutually hb-related. -/
theorem happens_before_partial_order (t : MemoryTrace)
    (h_wf : t.wellFormed) :
    (∀ e ∈ t.events, ¬ happensBefore t e e) ∧
    (∀ e₁ e₂ e₃ : MemoryEvent,
        happensBefore t e₁ e₂ → happensBefore t e₂ e₃ →
        happensBefore t e₁ e₃) ∧
    (∀ e₁ e₂ : MemoryEvent, e₁ ∈ t.events → e₂ ∈ t.events → e₁ ≠ e₂ →
        ¬ (happensBefore t e₁ e₂ ∧ happensBefore t e₂ e₁)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e _ h; exact happensBefore_irreflexive h_wf e h
  · intro e₁ e₂ e₃ h₁ h₂; exact happensBefore_transitive h_wf h₁ h₂
  · intro e₁ e₂ _ _ h_ne; exact happensBefore_antisymmetric h_wf e₁ e₂ h_ne

-- ============================================================================
-- Surface anchors and additional witnesses
-- ============================================================================

/-- Surface anchor: a hb cycle is impossible.  Useful as a "smoke
test" form of the partial-order property that downstream SM2.B /
SM2.C lemmas can `exact_mod_cast` against. -/
theorem happensBefore_no_cycle {t : MemoryTrace} (h_wf : t.wellFormed)
    {e₁ e₂ : MemoryEvent} (h₁ : happensBefore t e₁ e₂)
    (h₂ : happensBefore t e₂ e₁) : False :=
  happensBefore_irreflexive h_wf e₁ (happensBefore.trans h₁ h₂)

/-- Surface anchor: the per-trace happens-before partial-order
witness in a form convenient for kernel-level use; provides three
properties at once with explicit names for the strict-positional
invariant. -/
theorem happens_before_strict_partial_order
    (t : MemoryTrace) (h_wf : t.wellFormed) :
    -- Strict: irreflexive
    (∀ e, ¬ happensBefore t e e) ∧
    -- Transitive
    (∀ e₁ e₂ e₃, happensBefore t e₁ e₂ → happensBefore t e₂ e₃ →
                  happensBefore t e₁ e₃) ∧
    -- Anti-cyclic
    (∀ e₁ e₂, happensBefore t e₁ e₂ → happensBefore t e₂ e₁ → False) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e; exact happensBefore_irreflexive h_wf e
  · intro _ _ _ h₁ h₂; exact happensBefore.trans h₁ h₂
  · intro _ _ h₁ h₂; exact happensBefore_no_cycle h_wf h₁ h₂

-- ============================================================================
-- Convenience lifters for downstream SM2.B / SM2.C consumers
-- ============================================================================

/-- Surface anchor: any sequenced-before edge lifts to a happens-before
edge.  The companion to `.seq` in a tactic-friendly form (the
`.seq` constructor is also accessible directly).

Useful for SM2.B/C proofs that need to show "two same-core events
on the same core are happens-before related". -/
theorem sequencedBefore_implies_happensBefore (t : MemoryTrace)
    {e₁ e₂ : MemoryEvent} (h : sequencedBefore t e₁ e₂) :
    happensBefore t e₁ e₂ :=
  happensBefore.seq h

/-- Surface anchor: any synchronizes-with edge lifts to a
happens-before edge.  The companion to `.sync` in a tactic-friendly
form.

Useful for SM2.B/C release-acquire pairing proofs that need to
invoke happens-before from a constructed sync edge. -/
theorem synchronizesWith_implies_happensBefore (t : MemoryTrace)
    {e_R e_A : MemoryEvent} (h : synchronizesWith t e_R e_A) :
    happensBefore t e_R e_A :=
  happensBefore.sync h

/-- Surface anchor: `wellFormed` extracts to its `Nodup` clause.

Useful for SM2.B/C proofs that need the trace's Nodup property
explicitly (e.g., when reasoning about event uniqueness in a
lock-state operational step). -/
theorem MemoryTrace.wellFormed.nodup {t : MemoryTrace}
    (h_wf : t.wellFormed) : t.events.Nodup := h_wf.1

/-- Surface anchor: `wellFormed` extracts to its `Pairwise` monotonicity
clause.

Useful for SM2.B/C proofs that need to invoke per-core seqNum
monotonicity directly. -/
theorem MemoryTrace.wellFormed.pairwise {t : MemoryTrace}
    (h_wf : t.wellFormed) :
    List.Pairwise
      (fun e₁ e₂ => e₁.core = e₂.core → e₁.seqNum ≤ e₂.seqNum)
      t.events := h_wf.2

/-- Surface anchor: positional ordering between two `happensBefore`-
related events strictly increases.  Convenience form of
`happensBefore_strict_positional` for downstream consumers that
prefer the named theorem over the inductive proof. -/
theorem happensBefore_eventPos_lt {t : MemoryTrace} (h_wf : t.wellFormed)
    {e₁ e₂ : MemoryEvent} (h : happensBefore t e₁ e₂) :
    t.eventPos e₁ < t.eventPos e₂ :=
  happensBefore_strict_positional h_wf h

/-- Surface anchor: positional ordering implies trace membership
through `happensBefore_in_trace` plus `eventPos_lt_length`.
Convenience form for SM2.B/C proofs that need both facts at once.

The `wellFormed` hypothesis is NOT required for the trace-membership
plus length-bound facts (those follow purely from the
`happensBefore` inductive shape), so the signature omits it. -/
theorem happensBefore_endpoints_in_trace_with_pos {t : MemoryTrace}
    {e₁ e₂ : MemoryEvent} (h : happensBefore t e₁ e₂) :
    e₁ ∈ t.events ∧ e₂ ∈ t.events ∧
    t.eventPos e₁ < t.events.length ∧ t.eventPos e₂ < t.events.length := by
  obtain ⟨h₁, h₂⟩ := happensBefore_in_trace t h
  exact ⟨h₁, h₂, t.eventPos_lt_length h₁, t.eventPos_lt_length h₂⟩

end SeLe4n.Kernel.Concurrency
