-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

/-
WS-SM SM9.B.1/.B.2 — the declassification **refusal** record and its ledger

SM8.C's audit trail records authorized downgrades and nothing else, so a
monitoring system cannot distinguish *"no attempts"* from *"many attempts, all
denied"*.  That is a detection gap rather than an enforcement one — every
refusal is already fail-closed — and SM8.C registered it as
`DeclassificationRuleId.refusalIsUnrecorded`, whose statement SM9.B makes
false.

This module is the payload half: the record a refusal produces and the bounded
ledger it lands in.  It is a **leaf** for the plan's §6 reason — `Model/State.lean`
mounts the ledger, so the payload must sit below it — which is also why
`KernelError` was extracted to `Model/KernelError.lean` in the same cut.

## Why a ledger and not the trail

The trail is bounded and **fail-closed**: at capacity a downgrade is refused
rather than left unrecorded.  Writing refusals into it would hand an
unprivileged caller a way to exhaust those `maxDeclassificationAuditEntries`
entries and deny every subsequent *authorized* downgrade
(`refusalWrite_declassificationAuditLog_eq`, `Platform/FFI.lean`, is the
theorem that this cannot happen).  A refusal record is evidence, not an
authorized downgrade, so the two structures have opposite behaviours at
capacity: the trail refuses the operation, the ledger evicts the oldest
evidence and **counts the eviction**.

## Why the bound is structural

`auditLogBounded` is a `List` bound carried as the 16th
`proofLayerInvariantBundle` conjunct, and every writer of the trail owes it.
CLAUDE.md prefers *"enforce it structurally (record field, refinement type,
smart-constructor obligation)"* over an invariant held by convention, and a ring
can be bounded by its **type**: a `Vector` cannot exceed its size, so there is
no 17th conjunct, **no obligation on any writer**, and no `refine ⟨?_,…⟩` arity
re-count — those destructurings are right-nested and a trailing under-listing
elaborates *silently*.

**What the type-level bound does not save** is the carriage block itself.  Any
mounted field needs one, whatever it holds: `proofLayerInvariantBundle` does not
transport across a field write by `rfl`, because three conjuncts fail `isDefEq`
outright for reasons that are structural rather than about proof budget — a
`match` stuck on a symbolic `Nat` (`blockingChain`, `dualQueueSystemInvariant`)
and an `inductive` family parameterised by the state (`serviceNontrivialPath`),
the v0.32.151 diagnosis.  So the ledger has the same five-lemma block its peers
have (`Architecture.proofLayerInvariantBundle_setDeclassificationRefusals`), and
what the type buys shows up in that theorem's *shape*: it is **unconditional**,
where the trail's takes `hBounded`.

The two counters are `Fin`, not `Nat`, for the same reason and applied
consistently: "saturating" as a convention of `recordRefusal` would leave every
*other* way of building the structure unconstrained — an arbitrary
`SystemState` or `FrozenSystemState` literal, a test fixture, a future boot
path — free to carry an out-of-range count with nothing rejecting it.  With
`Fin (maxRefusalCount + 1)` the saturation is the type's, and `recordRefusal`
*cannot* overflow it.

## Why the ledger carries a version

A refusal record takes several `.auditRead` calls to reconstruct — more under
the chunk protocol — and any denied syscall in between can overwrite the
selected ring slot.  The trail's `status` token does not help: it moves on
trail *drains*, not on ledger writes, so a monitor bracketing with it can
assemble a **hybrid record** whose fields came from two different attempts and
never detect it (`auditStatus_does_not_detect_refusal_write`, `AuditRead.lean`).
So the ledger carries its own `version`, advanced by **every** `recordRefusal`,
and a read is bracketed by it exactly as a trail read is bracketed by the drain
generation.
-/
import SeLe4n.Prelude
import SeLe4n.Kernel.Concurrency.Types
import SeLe4n.Kernel.InformationFlow.AuditRecord
import SeLe4n.Model.KernelError
import SeLe4n.Model.Object.Types

namespace SeLe4n.Kernel

open SeLe4n.Kernel.Concurrency (CoreId)

-- ============================================================================
-- §1  SM9.B.1 — the refusal record
-- ============================================================================

/-- WS-SM SM9.B.1: **a refused declassification**, attributed.

Every field is already an argument at the seam that writes it
(`Platform.FFI.syscallDispatchFromAbi`), which is the whole reason the refusal
audit needs no change to the kernel's error discipline: `Kernel α` gives an
`.error` arm no post-state, but one layer up the boundary converts every kernel
error into a **committed** `(SyscallOutcome, state)` pair, and it does so with
the executing core, the resolved subject, the labeling context, the raw syscall
number (decoded there by the pure total `SyscallId.ofNat?`), the error and the
caller's `x0` all in hand.

**The target is the raw `CPtr` the caller supplied**, not a resolved `ObjId`:
it is what the caller *asked for* — the more useful datum for detection — and
resolving it would reintroduce the CSpace walk the seam design exists to avoid.

**The source domain is resolved at the seam** and stored, never recomputed.
`LabelingContext` is an *argument* to the dispatch, not persistent state, so a
later reader has no way to reconstruct which domain the subject held at the
moment it was refused: the deployment's context may differ by then, and the
thread id may have been reused.  The authorized-event trail stores its domains
for exactly the same reason.  `refusalRecord_domain_is_seam_resolved` is the
record-level half of that argument and
`Platform.FFI.refusalRecord_domain_is_seam_resolved_at_seam` the seam-level
one.

**What a two-hop refusal owes — and the premise that moved.**  Plan §3.5's
declassifying signal (SM9.C.1) authorizes two hops, and a refusal of the second
names the *resolved receiver* as well as the operand (`refusedReceiver` below;
`Platform.FFI.refusalRecord_names_failed_hop`).  The SM9.B landing deferred the
field on the ground that the receiver is resolved inside the transition, whose
error arm carries no post-state, "so the seam cannot see it" — but the seam
holds the **pre-state** and the caller's `x0`, and the transition resolves its
receiver from that same pre-state deterministically
(`declassifiedSignalReceiver?`), so the seam can re-resolve it and a theorem can
pin the two resolutions equal (`Platform.FFI.refusedSignalReceiver?_resolves`).
With a producer that provably sets it, the field stops being the
unwired-structure shape CLAUDE.md forbids and becomes the §3.1 obligation
discharged.  *Which* hop failed still rides the `reason` discriminant. -/
structure DeclassificationRefusal where
  /-- The core the refused syscall was executing on. -/
  originatingCore : CoreId
  /-- The subject that attempted the downgrade — the thread the executing core
      was running when the syscall trapped. -/
  subject : SeLe4n.ThreadId
  /-- The subject's security domain, **resolved at the seam** from the
      deployment's labeling context.  Not reconstructible later: see the
      structure docstring. -/
  subjectDomain : SecurityDomain
  /-- The syscall that was refused.  A `SyscallId` rather than the raw ABI
      number: the seam only records for syscalls its classification admits, and
      an unrecognised number cannot be classified, so a stored record always
      names a modeled syscall by construction. -/
  syscall : SeLe4n.Model.SyscallId
  /-- Why it was refused — the `KernelError` the kernel returned to the caller,
      `.auditLogCapacityExceeded` included.  That variant is the only durable
      evidence that an authorized downgrade hit the trail's capacity bound, so
      it is **recorded**; the occupancy channel it would otherwise open is
      closed by the ledger's read gate (monitor-only), not by discarding the
      evidence. -/
  reason : SeLe4n.Model.KernelError
  /-- The capability pointer the caller supplied in `x0` — what it asked for,
      verbatim. -/
  requestedTarget : SeLe4n.CPtr
  /-- WS-SM SM9.C.1 (`refusalRecord_names_failed_hop`): the receiver a refused
      **second hop** had resolved — the thread the badge would have been
      delivered onward to — and `none` for every other refusal.

      Seam-resolved like `subjectDomain`: the producer re-runs the transition's
      own pre-state resolution (`Platform.FFI.refusedSignalReceiver?`), which a
      theorem pins to the receiver the second-hop gate refused.  Without it a
      hop-2 refusal reduces to the original capability operand and a
      discriminant, and a monitor cannot identify the bound waiter an attempted
      downgrade actually targeted — while the *success* path is required to
      audit exactly that destination (`declassifiedSignal_audits_actual_destination`).

      Deliberately **not** defaulted, for the reason `DeclassificationEvent.actor`
      is not: a `:= none` default would let a future second producer compile
      while silently never naming the receiver its refusals resolved. -/
  refusedReceiver : Option SeLe4n.ThreadId
  deriving Repr, DecidableEq

/-- WS-SM SM9.B.1: **the subject's domain is not a function of the rest of the
record**, so it has to be recorded rather than recomputed.

Two refusals that agree on the core, the subject, the syscall, the reason and
the requested target can still carry different source domains — which is
exactly the situation a redeployed labeling context or a reused thread id
produces.  A reader handed the other five fields therefore cannot reconstruct
the sixth, and a design that dropped it would lose the attribution the ledger
exists to provide.

The seam-level half — that the recorded domain is the one the *dispatch's own
context* assigns, and that running the identical refusal under a different
context records a different domain — is
`Platform.FFI.refusalRecord_domain_is_seam_resolved_at_seam`. -/
theorem refusalRecord_domain_is_seam_resolved :
    ∃ r₁ r₂ : DeclassificationRefusal,
      r₁.originatingCore = r₂.originatingCore ∧
      r₁.subject = r₂.subject ∧
      r₁.syscall = r₂.syscall ∧
      r₁.reason = r₂.reason ∧
      r₁.requestedTarget = r₂.requestedTarget ∧
      r₁.subjectDomain ≠ r₂.subjectDomain := by
  refine ⟨{ originatingCore := Concurrency.bootCoreId, subject := ⟨0⟩,
            subjectDomain := ⟨0⟩, syscall := .declassify,
            reason := .declassificationDenied, requestedTarget := SeLe4n.CPtr.ofNat 1,
            refusedReceiver := none },
          { originatingCore := Concurrency.bootCoreId, subject := ⟨0⟩,
            subjectDomain := ⟨1⟩, syscall := .declassify,
            reason := .declassificationDenied, requestedTarget := SeLe4n.CPtr.ofNat 1,
            refusedReceiver := none },
          rfl, rfl, rfl, rfl, rfl, by decide⟩


-- ============================================================================
-- §2  SM9.B.2 — the bounded ledger's constants and counter algebra
-- ============================================================================

/-- WS-SM SM9.B.2: how many recent refusals the ledger retains.

A ring rather than an unbounded list, for the reason the trail is bounded: a
kernel-resident structure a userspace caller can grow is an allocation that
caller controls.  Unlike the trail the behaviour at the bound is **eviction**
rather than refusal, because the two structures hold different things — an
authorized downgrade the kernel did not record is a soundness failure, an
evicted refusal is a monitoring loss, and the eviction is itself counted
(`droppedCount`) so the loss is never silent.

Sized so that a monitor polling at any reasonable cadence sees a burst rather
than a single sample; the constant is a configuration choice, and every theorem
here is stated against the name. -/
def refusalRingSize : Nat := 32

/-- WS-SM SM9.B.2: the ring is non-empty, which is what makes `nextSlot`'s type
inhabited and the slot successor total. -/
theorem refusalRingSize_pos : 0 < refusalRingSize := by decide

/-- WS-SM SM9.B.2: the ceiling the ledger's two cumulative counters saturate
at.

`Fin (maxRefusalCount + 1)` rather than a `Nat` with a saturating updater: the
saturation is then the **type's**, so an arbitrary ledger value — a test
fixture, a frozen-state literal, a future boot path — cannot carry an
out-of-range count, and `recordRefusal` cannot overflow one. -/
def maxRefusalCount : Nat := 65535

/-- WS-SM SM9.B.2: **saturating successor** on a `Fin`-bounded counter — the
only arithmetic the ledger's counters admit.

At the ceiling it is the identity, so a saturated counter reads "at least
`maxRefusalCount`" rather than wrapping to a small number, which is the
direction a monitoring counter must fail in. -/
def saturatingSucc {n : Nat} (i : Fin (n + 1)) : Fin (n + 1) :=
  ⟨min (i.val + 1) n, by omega⟩

/-- WS-SM SM9.B.2: the saturating successor never exceeds the ceiling — by
construction, restated as the named fact consumers cite. -/
@[simp] theorem saturatingSucc_le {n : Nat} (i : Fin (n + 1)) :
    (saturatingSucc i).val ≤ n := by
  unfold saturatingSucc
  simp only []
  omega

/-- WS-SM SM9.B.2: below the ceiling it really counts. -/
theorem saturatingSucc_of_lt {n : Nat} (i : Fin (n + 1)) (h : i.val < n) :
    (saturatingSucc i).val = i.val + 1 := by
  unfold saturatingSucc
  simp only []
  omega

/-- WS-SM SM9.B.2 (**the saturation**): at the ceiling it stands still. -/
theorem saturatingSucc_at_ceiling {n : Nat} (i : Fin (n + 1)) (h : i.val = n) :
    (saturatingSucc i).val = n := by
  unfold saturatingSucc
  simp only []
  omega

/-- WS-SM SM9.B.2: the counter is monotone — it never goes backwards, which is
what lets a monitor compare two samples. -/
theorem saturatingSucc_monotone {n : Nat} (i : Fin (n + 1)) :
    i.val ≤ (saturatingSucc i).val := by
  unfold saturatingSucc
  simp only []
  omega

/-- WS-SM SM9.B.2: the ring's slot successor, modulo the ring size. -/
def refusalSlotSucc (i : Fin refusalRingSize) : Fin refusalRingSize :=
  ⟨(i.val + 1) % refusalRingSize, Nat.mod_lt _ refusalRingSize_pos⟩

/-- WS-SM SM9.B.2: the slot successor is the modular one, in the shape the
fold's closed form uses. -/
@[simp] theorem refusalSlotSucc_val (i : Fin refusalRingSize) :
    (refusalSlotSucc i).val = (i.val + 1) % refusalRingSize := rfl

-- ============================================================================
-- §3  SM9.B.2 — the ledger
-- ============================================================================

/-- WS-SM SM9.B.2: **the refusal ledger** — a saturating attempt counter, a
bounded ring of recent attributed refusals, and a version that advances on
every write.

Bounded by its **type** rather than by an invariant conjunct (see the module
docstring): a `Vector` cannot exceed its size and a `Fin` cannot exceed its
ceiling, so there is no 17th `proofLayerInvariantBundle` conjunct, no capacity
obligation on any writer, and no bundle destructuring to re-count.  The
carriage layer every mounted field needs is still there and is
**unconditional** (`proofLayerInvariantBundle_setDeclassificationRefusals`).

`droppedCount` is what keeps eviction honest: a ring that overwrote silently
would report a clean history to a monitor that had simply not polled often
enough. -/
structure RefusalLedger where
  /-- Cumulative count of refusals recorded, saturating at `maxRefusalCount`. -/
  attemptCount : Fin (maxRefusalCount + 1)
  /-- The most recent refusals, oldest evicted first.  `none` marks a slot no
      refusal has reached yet. -/
  recent : Vector (Option DeclassificationRefusal) refusalRingSize
  /-- The slot the next refusal will occupy. -/
  nextSlot : Fin refusalRingSize
  /-- How many recorded refusals have been evicted by ring wrap, saturating at
      `maxRefusalCount`.  Nonzero means a monitor has missed records. -/
  droppedCount : Fin (maxRefusalCount + 1)
  /-- Advanced by **every** `recordRefusal`.  A monitor brackets a multi-call
      read with it, exactly as a trail read is bracketed by the drain
      generation — and unlike that generation it is needed even for a single
      slot, because the ring's writes are what move a slot's content. -/
  version : Nat
  deriving Repr, DecidableEq

namespace RefusalLedger

/-- WS-SM SM9.B.2: the boot ledger — nothing attempted, nothing recorded,
nothing dropped. -/
def initial : RefusalLedger :=
  { attemptCount := ⟨0, by omega⟩
    recent := Vector.replicate refusalRingSize none
    nextSlot := ⟨0, refusalRingSize_pos⟩
    droppedCount := ⟨0, by omega⟩
    version := 0 }

instance : Inhabited RefusalLedger := ⟨initial⟩

/-- WS-SM SM9.B.2: every boot slot is empty. -/
@[simp] theorem initial_recent_get (i : Fin refusalRingSize) :
    initial.recent.get i = none := by
  simp [initial]

/-- WS-SM SM9.B.2: the boot counters are zero and the boot version is zero. -/
@[simp] theorem initial_counters :
    initial.attemptCount.val = 0 ∧ initial.droppedCount.val = 0 ∧
      initial.version = 0 ∧ initial.nextSlot.val = 0 := ⟨rfl, rfl, rfl, rfl⟩

end RefusalLedger

/-- WS-SM SM9.B.2: **record a refusal.**

Total: it never refuses, which is the load-bearing difference from
`recordDeclassificationChecked`.  A refusal record is evidence about a syscall
that has *already* failed, so refusing to record it could only turn a
monitoring loss into a second failure — and, worse, would make the ledger's
occupancy readable to the refused caller, which is the channel the trail's own
fail-closed bound already forces (CC-8) and the ledger must not add a second
instance of.  `recordRefusal_never_refuses` states the totality — as a
*contrast*, against `recordDeclassificationChecked`'s refusal at a full trail,
so the two halves of the asymmetry are one statement — and
`refusalLedger_write_is_caller_invisible` (`Platform/FFI.lean`) states the
consequence at the seam.

Eviction is counted: overwriting an occupied slot advances `droppedCount`, so a
monitor reading a nonzero drop count knows records are missing rather than
believing it has seen everything. -/
def recordRefusal (L : RefusalLedger) (r : DeclassificationRefusal) : RefusalLedger :=
  { attemptCount := saturatingSucc L.attemptCount
    recent := L.recent.set L.nextSlot.val (some r) L.nextSlot.isLt
    nextSlot := refusalSlotSucc L.nextSlot
    droppedCount :=
      if (L.recent.get L.nextSlot).isSome then saturatingSucc L.droppedCount
      else L.droppedCount
    version := L.version + 1 }

-- ============================================================================
-- §4  SM9.B.2 — what recording does, and what it cannot do
-- ============================================================================

/-- WS-SM SM9.B.2: the record lands in the slot the ledger selected. -/
@[simp] theorem recordRefusal_writes_selected_slot (L : RefusalLedger)
    (r : DeclassificationRefusal) :
    (recordRefusal L r).recent.get L.nextSlot = some r := by
  simp [recordRefusal]

/-- WS-SM SM9.B.2 (**the no-loss frame**): recording touches exactly one slot —
every other slot is carried through unchanged. -/
theorem recordRefusal_frames_other_slots (L : RefusalLedger)
    (r : DeclassificationRefusal) (j : Fin refusalRingSize) (hj : L.nextSlot ≠ j) :
    (recordRefusal L r).recent.get j = L.recent.get j := by
  simpa [recordRefusal] using SeLe4n.PerCoreVector.get_set_ne L.recent L.nextSlot j (some r) hj

/-- WS-SM SM9.B.2: the ring advances by one slot. -/
@[simp] theorem recordRefusal_nextSlot (L : RefusalLedger) (r : DeclassificationRefusal) :
    (recordRefusal L r).nextSlot = refusalSlotSucc L.nextSlot := rfl

/-- WS-SM SM9.B.2 (**the version advances on every record**): the bracket token
a monitor reads around a multi-call reconstruction.

Advanced unconditionally — including when the write evicts nothing and when the
recorded refusal is identical to the one already in the slot — because the
question the bracket answers is *"did anything write?"*, not *"did the content
change?"*.  A version that only moved on observable change would let two
identical refusals in the same slot hide a third, different one between
them. -/
@[simp] theorem refusalLedger_version_advances_on_record (L : RefusalLedger)
    (r : DeclassificationRefusal) :
    (recordRefusal L r).version = L.version + 1 := rfl

/-- WS-SM SM9.B.2 (**saturation**): the attempt counter counts below the
ceiling and stands still at it — it never wraps to a small number, which is the
direction a monitoring counter must fail in. -/
theorem recordRefusal_saturates (L : RefusalLedger) (r : DeclassificationRefusal) :
    (recordRefusal L r).attemptCount.val = min (L.attemptCount.val + 1) maxRefusalCount ∧
      (recordRefusal L r).attemptCount.val ≤ maxRefusalCount := by
  refine ⟨rfl, ?_⟩
  exact saturatingSucc_le L.attemptCount

/-- WS-SM SM9.B.2: the attempt counter is monotone, so two samples order. -/
theorem recordRefusal_attemptCount_monotone (L : RefusalLedger)
    (r : DeclassificationRefusal) :
    L.attemptCount.val ≤ (recordRefusal L r).attemptCount.val :=
  saturatingSucc_monotone L.attemptCount

/-- WS-SM SM9.B.2 (**ring wrap is counted**): overwriting an occupied slot
advances `droppedCount`, and overwriting an empty one does not.

Both directions matter.  Without the first a monitor reads a full ring and
believes it has seen every refusal; without the second a fresh ledger would
report drops it never made, and a monitor calibrating on "drops means I am
polling too slowly" would chase a phantom. -/
theorem recordRefusal_ring_wraps_counted (L : RefusalLedger)
    (r : DeclassificationRefusal) :
    ((L.recent.get L.nextSlot).isSome = true →
      (recordRefusal L r).droppedCount = saturatingSucc L.droppedCount) ∧
    ((L.recent.get L.nextSlot).isSome = false →
      (recordRefusal L r).droppedCount = L.droppedCount) := by
  constructor
  · intro h; simp [recordRefusal, h]
  · intro h; simp [recordRefusal, h]

/-- WS-SM SM9.B.2 (**the totality contrast**): recording a refusal always
succeeds, at any ledger, while the authorized-downgrade recorder **refuses** at
a full trail.

The asymmetry is the design.  A refusal record is evidence about a syscall that
has already failed, so refusing to record it could only add a second failure —
and, worse, the refusal would have to be reported to the caller, making the
ledger's occupancy readable to an unprivileged subject.  That is the CC-8
channel the trail's fail-closed bound already forces, and the ledger must not
supply a second instance of it. -/
theorem recordRefusal_never_refuses (L : RefusalLedger) (r : DeclassificationRefusal)
    (log : DeclassificationAuditLog) (e : DeclassificationEvent)
    (hFull : maxDeclassificationAuditEntries ≤ log.length) :
    (recordRefusal L r).recent.get L.nextSlot = some r ∧
      recordDeclassificationChecked log e = none :=
  ⟨recordRefusal_writes_selected_slot L r,
   recordDeclassificationChecked_eq_none log e hFull⟩

/-- WS-SM SM9.B.2 (**the bound is the type's**): every inhabitant of the
ledger is bounded — not just the ones `recordRefusal` produced.

This is what buys the absence of a 17th `proofLayerInvariantBundle` conjunct,
and of any capacity obligation on a writer.  A `List` ring with a `Nat` counter
would need an invariant every transition carries and every bundle destructuring
re-counts; here an arbitrary ledger value — a frozen-state literal, a test
fixture, a future boot path — is bounded because there is no way to write an
unbounded one. -/
theorem refusalLedger_bounded_structurally (L : RefusalLedger) :
    L.recent.toList.length = refusalRingSize ∧
      L.attemptCount.val ≤ maxRefusalCount ∧
      L.droppedCount.val ≤ maxRefusalCount ∧
      L.nextSlot.val < refusalRingSize :=
  ⟨SeLe4n.PerCoreVector.toList_length L.recent,
   Nat.lt_succ_iff.mp L.attemptCount.isLt,
   Nat.lt_succ_iff.mp L.droppedCount.isLt,
   L.nextSlot.isLt⟩

/-- WS-SM SM9.B.2 (**why the counters are `Fin` and not `Nat`**): the typed
counter is bounded at *every* inhabitant, while the `Nat` alternative has
inhabitants that are not.

Stated rather than argued, because the plan's own §3.2 draft made these fields
`Nat` with "saturating" as a convention of `recordRefusal` — which constrains
the recorder and nothing else, leaving every other way of building the
structure free to carry an out-of-range count. -/
theorem refusalCounter_bound_is_structural :
    (∀ i : Fin (maxRefusalCount + 1), i.val ≤ maxRefusalCount) ∧
      (∃ n : Nat, ¬ (n ≤ maxRefusalCount)) :=
  ⟨fun i => Nat.lt_succ_iff.mp i.isLt, ⟨maxRefusalCount + 1, by omega⟩⟩

-- ============================================================================
-- §5  SM9.B.2 — runs of refusals, and the read bracket
-- ============================================================================

/-- WS-SM SM9.B.2: a run of `n` refusals advances the version by exactly `n`. -/
theorem foldl_recordRefusal_version (L : RefusalLedger)
    (rs : List DeclassificationRefusal) :
    (rs.foldl recordRefusal L).version = L.version + rs.length := by
  induction rs generalizing L with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.length_cons, ih, refusalLedger_version_advances_on_record]
    omega

/-- WS-SM SM9.B.2: a run of `n` refusals advances the ring by `n` slots. -/
theorem foldl_recordRefusal_nextSlot (L : RefusalLedger)
    (rs : List DeclassificationRefusal) :
    (rs.foldl recordRefusal L).nextSlot.val =
      (L.nextSlot.val + rs.length) % refusalRingSize := by
  induction rs generalizing L with
  | nil => simpa using (Nat.mod_eq_of_lt L.nextSlot.isLt).symm
  | cons a t ih =>
    simp only [List.foldl_cons, ih, recordRefusal_nextSlot, refusalSlotSucc_val,
      List.length_cons, Nat.mod_add_mod]
    congr 1
    omega

/-- WS-SM SM9.B.2 (**the run-level frame**): a run of refusals leaves a slot
untouched exactly when none of the slots it writes is that slot. -/
theorem foldl_recordRefusal_frames_slot (L : RefusalLedger)
    (rs : List DeclassificationRefusal) (j : Fin refusalRingSize)
    (hMiss : ∀ i, i < rs.length → (L.nextSlot.val + i) % refusalRingSize ≠ j.val) :
    (rs.foldl recordRefusal L).recent.get j = L.recent.get j := by
  induction rs generalizing L with
  | nil => rfl
  | cons a t ih =>
    have hHead : L.nextSlot ≠ j := by
      intro hEq
      exact hMiss 0 (by simp) (by
        simpa [Nat.mod_eq_of_lt L.nextSlot.isLt] using congrArg Fin.val hEq)
    have hTail : ∀ i, i < t.length →
        ((recordRefusal L a).nextSlot.val + i) % refusalRingSize ≠ j.val := by
      intro i hi
      simp only [recordRefusal_nextSlot, refusalSlotSucc_val, Nat.mod_add_mod]
      have := hMiss (i + 1) (by simp only [List.length_cons]; omega)
      have hArith : L.nextSlot.val + 1 + i = L.nextSlot.val + (i + 1) := by omega
      rw [hArith]
      exact this
    simp only [List.foldl_cons]
    rw [ih (recordRefusal L a) hTail]
    exact recordRefusal_frames_other_slots L a j hHead

/-- WS-SM SM9.B.2 (**no loss inside the window**): a recorded refusal survives
the next `refusalRingSize - 1` refusals.

The ring's guarantee, stated as the retention window rather than as "the ring
holds the recent ones".  A run shorter than the ring cannot revisit the slot it
started at, so the record is still there — and a run that *does* reach it has
advanced `droppedCount`, so the loss is visible. -/
theorem recordRefusal_no_loss (L : RefusalLedger) (r : DeclassificationRefusal)
    (rs : List DeclassificationRefusal) (hShort : rs.length < refusalRingSize) :
    (rs.foldl recordRefusal (recordRefusal L r)).recent.get L.nextSlot = some r := by
  rw [foldl_recordRefusal_frames_slot (recordRefusal L r) rs L.nextSlot ?miss]
  · exact recordRefusal_writes_selected_slot L r
  case miss =>
    intro i hi
    simp only [recordRefusal_nextSlot, refusalSlotSucc_val, Nat.mod_add_mod]
    have hs := L.nextSlot.isLt
    unfold refusalRingSize at *
    omega

/-- WS-SM SM9.B.2: the drop count is monotone under a single record. -/
theorem recordRefusal_droppedCount_monotone (L : RefusalLedger)
    (r : DeclassificationRefusal) :
    L.droppedCount.val ≤ (recordRefusal L r).droppedCount.val := by
  unfold recordRefusal
  simp only []
  split
  · exact saturatingSucc_monotone L.droppedCount
  · exact Nat.le_refl _

/-- WS-SM SM9.B.2: and under a run of them. -/
theorem foldl_recordRefusal_droppedCount_monotone (L : RefusalLedger)
    (rs : List DeclassificationRefusal) :
    L.droppedCount.val ≤ (rs.foldl recordRefusal L).droppedCount.val := by
  induction rs generalizing L with
  | nil => exact Nat.le_refl _
  | cons a t ih =>
    exact Nat.le_trans (recordRefusal_droppedCount_monotone L a) (ih (recordRefusal L a))

/-- WS-SM SM9.B.2 (**flooding cannot hide itself**): once the ring has wrapped,
the drop count is nonzero and stays nonzero for the rest of the run.

The honest statement of the ring's limitation.  A subject that issues enough
refused declassifications evicts every other subject's record — that is
inherent to a bounded ring, and per-domain partitioning is not constructible
over an unbounded domain space.  What the design *does* guarantee is that the
eviction is **visible**: a monitor reading a nonzero `droppedCount` knows its
view of the ring is incomplete, rather than reading 32 rows and believing it
has seen everything.

Not an information-flow channel in either direction: the ledger is readable
only by the deployment's configured monitor, which dominates every subject
domain, so what it learns from a flood is an authorized `subject → monitor`
flow; and nothing about the ledger reaches the flooding subject at all
(`recordRefusal_never_refuses` — the write has no failure mode to report). -/
theorem refusalLedger_eviction_is_counted (L : RefusalLedger)
    (r : DeclassificationRefusal) (rs : List DeclassificationRefusal)
    (hOccupied : (L.recent.get L.nextSlot).isSome = true) :
    0 < (rs.foldl recordRefusal (recordRefusal L r)).droppedCount.val := by
  have hStep : (recordRefusal L r).droppedCount = saturatingSucc L.droppedCount :=
    (recordRefusal_ring_wraps_counted L r).1 hOccupied
  have hPos : 0 < (recordRefusal L r).droppedCount.val := by
    rw [hStep]
    unfold saturatingSucc maxRefusalCount
    simp only []
    omega
  exact Nat.lt_of_lt_of_le hPos
    (foldl_recordRefusal_droppedCount_monotone (recordRefusal L r) rs)

/-- WS-SM SM9.B.2 (**the read bracket**): a monitor that reads the version
before and after a multi-call reconstruction and sees the **same** value may
conclude that no refusal was recorded in between — so the record it assembled
came from one attempt, not from two.

This is the property the trail's own token cannot supply: `status` moves on
trail *drains*, so a ledger write is invisible to it and a monitor bracketing
with it would assemble a hybrid record and never detect it
(`auditStatus_does_not_detect_refusal_write`, `AuditRead.lean`, is that
negative). -/
theorem refusalRead_bracketed_detects_overwrite (L : RefusalLedger)
    (rs : List DeclassificationRefusal)
    (hSame : (rs.foldl recordRefusal L).version = L.version) :
    rs = [] ∧ rs.foldl recordRefusal L = L := by
  have hLen : rs.length = 0 := by
    have := foldl_recordRefusal_version L rs
    omega
  have hNil : rs = [] := List.eq_nil_of_length_eq_zero hLen
  exact ⟨hNil, by rw [hNil]; rfl⟩
-- ============================================================================
-- §6  SM9.B.9 / plan §3.1 — which syscalls the refusal seam records
-- ============================================================================

/-! ## A total classification, not a list

The seam has to decide, per refused syscall, whether to record.  A draft
filtered on the literal `.declassify`, which SM9.C then silently defeats: it
adds a *second* declassifying syscall (`.declassifySignal`) whose refusals
would bypass the ledger entirely, leaving a monitor unable to distinguish "no
data-carrying downgrade attempts" from "many, all denied" — the exact gap SM9.B
exists to close.

**A list plus a completeness theorem does not fix that**, and this is the third
time the shape has been tried in this plan (after `ReadableStructure` and
`ContentFlowSite`): a theorem quantified over a hand-maintained "these syscalls
consult `declassificationDecision`" list stays true when a new dispatch arm
consults it and joins neither the list nor the theorem
(`refusalSeam_list_gate_insufficient`).  The gate has to be keyed to something
exhaustive *independently* of the gate — and `SyscallId` is, because the ABI
already forces every arm to exist.

So the seam reads a **total function** over `SyscallId`: every constructor must
be classified or this module does not elaborate, and SM9.C.8 classifies
`.declassifySignal` as part of adding it because it cannot compile otherwise. -/

/-- WS-SM SM9.B.9: whether the refusal seam records a syscall's refusals. -/
inductive RefusalSeamClass where
  /-- A declassifying syscall: its refusals are attributed and recorded. -/
  | records
  /-- Every other syscall.  The ledger is deliberately **not** a general
      syscall-failure audit: a refused `.send` is ordinary kernel behaviour, and
      recording every one of them would swamp a ring sized for policy
      exceptions and hand any subject a cheap way to evict evidence. -/
  | exempt
  deriving Repr, DecidableEq, Inhabited

/-- WS-SM SM9.B.9: **the classification**, total over `SyscallId` with no
wildcard.

A wildcard would defeat the whole mechanism: SM9.C.8's `.declassifySignal`
would fall through to `.exempt` and its refusals would never reach the ledger,
with nothing failing to compile.  Written out arm by arm for exactly that
reason — the same discipline `Architecture.syscallReturnShape` follows. -/
def refusalSeamClass : SeLe4n.Model.SyscallId → RefusalSeamClass
  -- WS-SM SM9.C.8: the data-carrying declassification records too, and this
  -- arm is what the total classification *forced* the cut that added the
  -- syscall to write.  Exactly the drift §3.1 exists to prevent: a second
  -- declassifying syscall whose refusals bypassed the seam would leave a
  -- monitor unable to distinguish "no data-carrying downgrade attempts" from
  -- "many, all denied".
  | .declassify | .declassifySignal => .records
  | .send | .receive | .call | .reply => .exempt
  | .cspaceMint | .cspaceCopy | .cspaceMove | .cspaceDelete => .exempt
  | .lifecycleRetype => .exempt
  | .vspaceMap | .vspaceUnmap | .vspaceUnifyInstruction => .exempt
  | .serviceRegister | .serviceRevoke | .serviceQuery => .exempt
  | .notificationSignal | .notificationWait | .replyRecv => .exempt
  | .schedContextConfigure | .schedContextBind | .schedContextUnbind => .exempt
  | .tcbSuspend | .tcbResume => .exempt
  | .tcbSetPriority | .tcbSetMCPriority => .exempt
  | .tcbSetIPCBuffer | .tcbSetAffinity | .tcbSetFaultHandler => .exempt
  | .tcbBindNotification | .tcbUnbindNotification => .exempt
  | .mintReplyCap => .exempt
  | .auditRead | .auditDrain => .exempt

/-- WS-SM SM9.B.9: the totality anchor.  The *mechanism* is the definition
itself — an exhaustive match with no wildcard; this theorem is the named
surface for that fact, in the shape `auditReadOp_structure_total` and
`syscallReturnShape_total` established. -/
theorem refusalSeamClass_total (sid : SeLe4n.Model.SyscallId) :
    ∃ cls, refusalSeamClass sid = cls := ⟨_, rfl⟩

/-- WS-SM SM9.B.9: **the declassifying syscall records.** -/
@[simp] theorem refusalSeamClass_declassify :
    refusalSeamClass .declassify = .records := rfl

/-- WS-SM SM9.B.9 / SM9.C.8 (**the current classification, pinned**): the two
declassifying syscalls record, and nothing else does.

Deliberately a theorem a third `.records` syscall **breaks**: SM9.B stated it of
`.declassify` alone and SM9.C.8 moved it, which is how a cut records the
decision rather than discovering it.  Decided over `SyscallId.all`, which
`all_complete` makes exhaustive, so the pin is over the whole ABI rather than
over a list of interest. -/
theorem refusalSeamClass_records_iff (sid : SeLe4n.Model.SyscallId) :
    refusalSeamClass sid = .records ↔ (sid = .declassify ∨ sid = .declassifySignal) := by
  cases sid <;> simp [refusalSeamClass]

/-- WS-SM SM9.C.8: **the data-carrying declassification records too.** -/
@[simp] theorem refusalSeamClass_declassifySignal :
    refusalSeamClass .declassifySignal = .records := rfl

/-- WS-SM SM9.B.9 / SM9.C.8: the count form — exactly the two declassifying
syscalls of the ABI are recorded by the seam. -/
theorem refusalSeamClass_records_count :
    (SeLe4n.Model.SyscallId.all.filter (fun s => refusalSeamClass s == .records)).length = 2 := by
  decide

/-- WS-SM SM9.B.9 (plan §3.1, **the refuted design, kept refuted**): a
hand-maintained list of "declassifying syscalls" plus an "every listed syscall
records" gate stays satisfied by a list that **misses** a declassifying
syscall — membership cannot force a new member to join.

Witness: the empty list passes the gate vacuously while `.declassify` records
and is absent from it.  Contrast the total classification, where a new
`SyscallId` constructor is a missing case and the module stops compiling. -/
theorem refusalSeam_list_gate_insufficient :
    ∃ l : List SeLe4n.Model.SyscallId,
      (∀ sid ∈ l, refusalSeamClass sid = .records) ∧
      ∃ sid : SeLe4n.Model.SyscallId, refusalSeamClass sid = .records ∧ sid ∉ l :=
  ⟨[], by simp, .declassify, rfl, by simp⟩

end SeLe4n.Kernel
