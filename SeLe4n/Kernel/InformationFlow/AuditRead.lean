/-
Copyright (c) 2025 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license.

WS-SM SM9.A: the declassification audit trail's **reader** — and, since
WS-SM SM9.B, the refusal ledger's (see "The second readable structure" below).

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

## Two classes of reader — and why only one of them is live

|                        | Partial reader (model)     | Fully-dominating monitor |
|------------------------|----------------------------|--------------------------|
| Entry identity         | **view-local index**       | **global timestamp**     |
| `status` generation    | none (always `0`)          | the global epoch         |
| Drain                  | refused                    | permitted                |
| Retry guarantee        | none promised              | `auditRead_stable_under_append` |
| Live `.auditRead`      | **refused** (round 6)      | served                   |

The split is forced.  A `DeclassificationEvent`'s timestamp is its *global*
position, so handing it to a partial reader tells that reader how many entries
preceded the one it can see — hidden ones included.  But exporting view-local
indices to *everyone* breaks the other side: a monitor correlating an event with
an archived predecessor needs an identity that survives a drain.  So the
protocol gives each reader the identity its clearance justifies.

**And the partial class stops at the model** (PR #870 round 6).  Appends are
information-flow clean for a partial reader — an entry joins its view only when
the *writing subject's* domain flows to it — but a **drain** is the monitor's
action, and deleting a visible entry moves that reader's visible length at the
monitor's choice: one bit per drain, from the fully-dominating monitor to a
lower subject, the very signal §4c hides the generation to remove.  A drain
that preserves every partial view is not constructible (deletion is the drain's
purpose, `observerScopedGeneration_not_mountable` rules out per-observer state,
and restricting drains to universally-invisible prefixes re-opens the capacity
cliff), so the live entry point serves **monitors only**
(`auditReadFromCore_partial_reader_denied`) and every surviving reader is one
the policy clears for every subject's activity — the monitor's drains
included (`auditReadFromCore_observer_dominates_subjects`).  The partial
class's theorems remain as the record of what such a reader *would* learn, and
`auditDrain_moves_partial_readers_status` keeps the channel that forced the
exclusion exhibited.

## Why the reader chunks

Four exported trail fields are unbounded `Nat` in the model
(`SecurityDomain.id`, `ObjId.val`, the timestamp) and the fifth is a string;
the ledger adds three more (`ThreadId.val`, a `SecurityDomain.id`, a `CPtr`).
A syscall returns one word.  Each such field is therefore read through a
fixed-width chunk protocol whose theorem is **reconstruction** — folding the
chunks recovers the value exactly — rather than "each fragment fits", which
says nothing about whether the record can be rebuilt from the fragments.

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
components structurally bounded, and the wrap concern lives at exactly one
place: `auditStatusWord_fits` carries the explicit `generation < 2^55` premise
(there is no wrap inside the model, whose words are `Nat`), and the boundary
**refuses** rather than wraps above `2^64` (`auditReadFromCore_word_fits`) — a
premise that is written down is the honest form of a bound that cannot be made
unconditional.

## The second readable structure (WS-SM SM9.B)

The refusal ledger is read from here too, and its arms are shaped by the ways it
is *unlike* the trail rather than by symmetry with it:

- **No filtered view, so no partial reader.**  A trail can hand a lower reader
  the sublist its clearance admits; a ledger cannot, because the ring **evicts**
  — a refusal that reader may not see removes one it could.  So every ledger arm
  opens with the configured monitor gate and an under-cleared caller learns
  nothing at all, not even how two arbitrary ledgers differ
  (`refusalLedger_requires_full_dominance`,
  `refusalLedger_partial_reader_learns_nothing`).
- **Its own bracket token.**  A ledger write does not move the trail's `status`
  word, so a monitor bracketing a multi-call record reconstruction with the
  trail's generation would assemble a hybrid record and never detect it
  (`auditStatus_does_not_detect_refusal_write`).  `refusalStatus` carries the
  ledger's own `version`, which advances on **every** recorded refusal
  (`refusalStatus_detects_refusal_write`, `refusalRead_bracketed_detects_overwrite`).
- **The gate is the configuration, never the rows.**  The ring evicts while the
  counters are cumulative, so a records-derived gate shrinks while the data it
  guards does not (`refusalLedger_gate_is_configuration_derived`, with
  `refusalLedger_records_gate_unsound` keeping the counterexample refuted).
- **The reason is WS-RA's own discriminant**, so a monitor's decoded reason and
  the refused caller's `x1` label name the same error without a second table
  (`refusalTagsWord_reason_is_abi_discriminant`).

## What this module deliberately does not do

It adds **no kernel→user memory write path**.  A write mirror of `ipcBufferReadMr`
is feasible, but it would grow the trusted computing base — and note that
`ipcBufferReadMr` ignores `PagePermissions` entirely, which a write path must
not.  A monitor draining a 256-entry trail does not need the throughput.
Recorded as a deliberate non-goal, revisitable if throughput ever demands it.
-/
import SeLe4n.Kernel.InformationFlow.Declassification
-- WS-SM SM9.B.10: the canonical `KernelError` numbering (WS-RA's
-- `toDiscriminant` / `ofDiscriminant?` pair).  The refusal ledger exports a
-- record's reason, and a second numbering would be a second source of truth —
-- so the reader reuses the one the ABI already puts on `x1`, which is also
-- what makes a monitor's decoded reason the very discriminant the refused
-- caller received.  The module imports only `Model.State`, so this adds
-- nothing to the reader's own import closure beyond what it already carries.
import SeLe4n.Kernel.Architecture.SyscallReturn

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)

-- ============================================================================
-- §1  SM9.A.1 — the clearance-filtered, re-indexed visible view
-- ============================================================================

/-- WS-SM SM9.A.1 (PR #870 round 3): **is `reader` cleared for everything entry
`e` discloses?**

An entry does not only name its source.  It also records `dstDomain` — which
the producer sets to the *target object's own domain*
(`dstDomain := ctx.objectDomainOf targetId`) — and `targetObject`, an object
identity the projection layer classifies by exactly that domain
(`capTargetObservable` redacts an object whose domain the observer's clearance
does not admit).  A source-only filter therefore leaks: for a policy-authorized
downgrade between **incomparable** labels — the `{low, trusted} →
{high, untrusted}` pair `legacyLattice` makes expressible — a partial reader at
the source label would be handed the destination domain and the identity of an
object its own projection redacts.  So visibility is the **conjunction**: the
reader must be cleared to receive from the source *and* from the destination.
`incomparableDowngrade_hidden_from_source_reader` keeps the leak refuted, and
`auditVisibleEntry_target_domain_flows` is the capstone aligning the audit view
with the projection's own object-identity discipline.

**WS-SM SM9.C.1 — four conjuncts, and why the last two are not redundant.**
SM9.C adds two things an entry discloses.  The `actor` pair (§3.5) is a *third*
domain: on the second hop of a two-hop delivery the actor is the signalling
subject while the source is the intermediate object, so a reader cleared for the
source and destination could otherwise read off the domain of a subject it
dominates neither.  And the round-3 argument for `targetObject` stopped being
*derivable*: it went through the producer invariant "`dstDomain` is the target
object's own domain", which a second-hop event falsifies by design (its
destination is the receiving *thread's* domain, and the labeling scores a
thread and an object independently).  So the object-identity conjunct is stated
**directly** here rather than derived, which makes
`auditVisibleEntry_target_domain_flows` unconditional — strictly stronger than
the form it replaces.

The actor's *identity* needs no conjunct of its own: `actor.domain` is that
subject's own domain by construction at every producer
(`auditTrailActorsFromLabeling`), so the third conjunct gates it.  That
indirection is sound here precisely where the target's was not — SM9.C
maintains the actor invariant at both hops and breaks the destination one. -/
def auditEntryVisibleTo (ctx : GenericLabelingContext) (reader : SecurityDomain)
    (e : DeclassificationEvent) : Bool :=
  ctx.policy.canFlow e.srcDomain reader && ctx.policy.canFlow e.dstDomain reader &&
    ctx.policy.canFlow e.actor.domain reader &&
    ctx.policy.canFlow (ctx.objectDomainOf e.targetObject) reader

/-- WS-SM SM9.A.1: **what a reader at domain `reader` may see of a trail.**

An entry records a release of `srcDomain`'s information *into* `dstDomain`'s
object, so the clearance that justifies reading it is the clearance to receive
from **both** (`auditEntryVisibleTo` — PR #870 round 3; the filter was
source-only before that cut, which leaked the destination side of an
incomparable-pair downgrade).

`List.filter`, so the result is a genuine **sublist in the original order** and
is re-indexed from `0` — not a sparse view of the global trail.  That is the
whole no-gap-leak argument: a reader indexes its own view, so it cannot count
the entries between two visible ones, and `auditLogVisibleTo_hidden_insert` says
inserting an entry it cannot see leaves its view literally unchanged. -/
def auditLogVisibleTo (ctx : GenericLabelingContext) (reader : SecurityDomain)
    (log : DeclassificationAuditLog) : DeclassificationAuditLog :=
  log.filter (auditEntryVisibleTo ctx reader)

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
clearance for both disclosed domains — the characterisation every downstream
proof travels along. -/
theorem mem_auditLogVisibleTo_iff (ctx : GenericLabelingContext)
    (reader : SecurityDomain) (log : DeclassificationAuditLog)
    (e : DeclassificationEvent) :
    e ∈ auditLogVisibleTo ctx reader log ↔
      e ∈ log ∧ auditEntryVisibleTo ctx reader e = true := by
  simp [auditLogVisibleTo, List.mem_filter]

/-- WS-SM SM9.A.1: a visible entry is one the reader is cleared for — every
disclosed domain, and the domain of the object identity it discloses, at once. -/
theorem auditLogVisibleTo_cleared (ctx : GenericLabelingContext)
    (reader : SecurityDomain) (log : DeclassificationAuditLog)
    {e : DeclassificationEvent} (h : e ∈ auditLogVisibleTo ctx reader log) :
    auditEntryVisibleTo ctx reader e = true :=
  ((mem_auditLogVisibleTo_iff ctx reader log e).mp h).2

/-- WS-SM SM9.A.1: the source projection — a visible entry's source flows to the
reader. -/
theorem auditLogVisibleTo_cleared_src (ctx : GenericLabelingContext)
    (reader : SecurityDomain) (log : DeclassificationAuditLog)
    {e : DeclassificationEvent} (h : e ∈ auditLogVisibleTo ctx reader log) :
    ctx.policy.canFlow e.srcDomain reader = true := by
  have h4 := auditLogVisibleTo_cleared ctx reader log h
  unfold auditEntryVisibleTo at h4
  simp only [Bool.and_eq_true] at h4
  exact h4.1.1.1

/-- WS-SM SM9.A.1 (PR #870 round 3, **the destination projection**): a visible
entry's destination flows to the reader too — the half a source-only filter did
not have, and the reason an audit reader can no longer recover an object
identity its projection redacts. -/
theorem auditLogVisibleTo_cleared_dst (ctx : GenericLabelingContext)
    (reader : SecurityDomain) (log : DeclassificationAuditLog)
    {e : DeclassificationEvent} (h : e ∈ auditLogVisibleTo ctx reader log) :
    ctx.policy.canFlow e.dstDomain reader = true := by
  have h4 := auditLogVisibleTo_cleared ctx reader log h
  unfold auditEntryVisibleTo at h4
  simp only [Bool.and_eq_true] at h4
  exact h4.1.1.2

/-- WS-SM SM9.C.1 (**the actor projection**): a visible entry's *actor* domain
flows to the reader — the conjunct the two-hop design owes, since a second-hop
event's source is the intermediate object's domain and says nothing about the
subject that performed the downgrade. -/
theorem auditLogVisibleTo_cleared_actor (ctx : GenericLabelingContext)
    (reader : SecurityDomain) (log : DeclassificationAuditLog)
    {e : DeclassificationEvent} (h : e ∈ auditLogVisibleTo ctx reader log) :
    ctx.policy.canFlow e.actor.domain reader = true := by
  have h4 := auditLogVisibleTo_cleared ctx reader log h
  unfold auditEntryVisibleTo at h4
  simp only [Bool.and_eq_true] at h4
  exact h4.1.2

/-- WS-SM SM9.C.1 (**the object-identity projection**): a visible entry's target
object is one whose **own** domain flows to the reader.

Stated directly rather than derived through the destination, because SM9.C's
second-hop event's destination is a *thread's* domain: the derivation round 3
used holds only while `dstDomain = objectDomainOf targetObject`, which two-hop
delivery falsifies by design. -/
theorem auditLogVisibleTo_cleared_target (ctx : GenericLabelingContext)
    (reader : SecurityDomain) (log : DeclassificationAuditLog)
    {e : DeclassificationEvent} (h : e ∈ auditLogVisibleTo ctx reader log) :
    ctx.policy.canFlow (ctx.objectDomainOf e.targetObject) reader = true := by
  have h4 := auditLogVisibleTo_cleared ctx reader log h
  unfold auditEntryVisibleTo at h4
  simp only [Bool.and_eq_true] at h4
  exact h4.2

/-- WS-SM SM9.A.1 (PR #870 round 3, **the leak refuted, negatively**): an entry
whose destination does not flow to the reader is in **no** position of that
reader's view, wherever it sits in the trail. -/
theorem auditLogVisibleTo_hides_undominated_destination (ctx : GenericLabelingContext)
    (reader : SecurityDomain) (log : DeclassificationAuditLog)
    (e : DeclassificationEvent)
    (hDst : ctx.policy.canFlow e.dstDomain reader = false) :
    e ∉ auditLogVisibleTo ctx reader log := by
  intro hMem
  exact absurd (auditLogVisibleTo_cleared_dst ctx reader log hMem)
    (by simp [hDst])

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
    (hHidden : auditEntryVisibleTo ctx reader e = false) :
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
    (hAgree : ∀ e ∈ log, auditEntryVisibleTo ctx r₁ e = auditEntryVisibleTo ctx r₂ e) :
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

/-- WS-SM SM9.A.1: a reader cleared for **every** entry in the trail sees all of
it.  The bridge between the clearance filter and the drain's full-dominance
requirement (§5). -/
theorem auditLogVisibleTo_eq_self (ctx : GenericLabelingContext)
    (reader : SecurityDomain) (log : DeclassificationAuditLog)
    (hAll : ∀ e ∈ log, auditEntryVisibleTo ctx reader e = true) :
    auditLogVisibleTo ctx reader log = log :=
  List.filter_eq_self.mpr hAll

/-- WS-SM SM9.A.1 (PR #870 round 3, **the reviewer's scenario, refuted by
`decide`**): the one downgrade the legacy lattice denies as a base flow —
`{low, trusted} → {high, untrusted}` — is exactly a pair a declassification
policy can authorize, and its recorded entry is **hidden** from a partial
reader at the source label: the source flows to that reader reflexively, the
destination does not flow to it at all, and the conjunction refuses.  The
second conjunct is the load-bearing negative — it is the fact a source-only
filter ignores, and with it the entry (destination domain, target object
identity and all) was served to a reader whose projection redacts that very
object. -/
theorem incomparableDowngrade_hidden_from_source_reader :
    ∀ (e : DeclassificationEvent),
      e.srcDomain = embedLegacyLabel { confidentiality := .low, integrity := .trusted } →
      e.dstDomain = embedLegacyLabel { confidentiality := .high, integrity := .untrusted } →
      (DomainFlowPolicy.legacyLattice.canFlow e.srcDomain
          (embedLegacyLabel { confidentiality := .low, integrity := .trusted }) = true ∧
       DomainFlowPolicy.legacyLattice.canFlow e.dstDomain
          (embedLegacyLabel { confidentiality := .low, integrity := .trusted }) = false) ∧
      ∀ (ctx : GenericLabelingContext), ctx.policy = DomainFlowPolicy.legacyLattice →
        ∀ log : DeclassificationAuditLog,
          e ∉ auditLogVisibleTo ctx
            (embedLegacyLabel { confidentiality := .low, integrity := .trusted }) log := by
  intro e hSrc hDst
  refine ⟨⟨by rw [hSrc]; decide, by rw [hDst]; decide⟩, fun ctx hPolicy log => ?_⟩
  exact auditLogVisibleTo_hides_undominated_destination ctx _ log e
    (by rw [hPolicy, hDst]; decide)

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
visible length by `maxDeclassificationAuditEntries`, and the generation by the
explicitly **stated** `generation < 2^55` premise on `auditStatusWord_fits`.
The bracket theorem itself (`auditRead_bracketed_detects_drain`) needs no wrap
premise — the model's words are `Nat`, where no wrap exists — and the `UInt64`
boundary **refuses** rather than wraps (`auditReadFromCore_word_fits`), so
caller-observed equality of two accepted words implies model-level equality
(`auditReadFromCore_toUInt64_lossless` is the injectivity half).  A premise that
is written down is the honest form of a bound that cannot be made
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
  /-- WS-SM SM9.B.10: the declassification **refusal ledger**
      (`SystemState.declassificationRefusals`) — the counters, the ring and the
      version a monitor brackets its reads with.

      It joins by adding this constructor, which is what the fusion above makes
      unavoidable: the refusal read operations cannot exist without naming a
      structure, and this constructor cannot exist without a clause in
      SM9.A.4a's total clause function.  Its obligation (b) is discharged
      differently from the trail's: there is no clearance-filtered *view* of a
      ledger, so a partial reader observes **nothing** of it
      (`refusalLedger_requires_full_dominance`) and no hidden write can move
      what such a reader sees. -/
  | declassificationRefusalLedger
  deriving Repr, DecidableEq, Inhabited

namespace ReadableStructure

/-- WS-SM SM9.A.2: the enumeration. -/
def all : List ReadableStructure :=
  [.declassificationAuditTrail, .declassificationRefusalLedger]

/-- WS-SM SM9.A.2: every structure is enumerated. -/
theorem mem_all (s : ReadableStructure) : s ∈ all := by cases s <;> decide

/-- WS-SM SM9.A.2: no duplicates. -/
theorem all_nodup : all.Nodup := by decide

end ReadableStructure

/-- WS-SM SM9.A.2: the numeric fields of a `DeclassificationEvent` the reader
exports through the chunk protocol.

`originatingCore` and the basis's trust bit are **not** here: both are
structurally bounded (`CoreId` is a `Fin numCores`, the bit is a `Bool`), so
they ride one word together (`AuditReadOp.coreAndTrust`).  The basis's
designation is not here either — it is a string, and gets the byte protocol of
§3b.

**WS-SM SM9.C.1 adds the actor pair.**  A record a monitor cannot read is a
record that does not exist for the purpose it was added for, and the actor is
exactly what a monitor most needs on a second-hop event: its `srcDomain` is the
intermediate object's, so without the actor the trail names *what* crossed and
not *who* crossed it.  Both components are unbounded `Nat` in the model
(`ThreadId.toNat`, `SecurityDomain.id`), so both ride the chunk protocol. -/
inductive AuditReadField where
  | srcDomain
  | dstDomain
  | targetObject
  | timestamp
  /-- WS-SM SM9.C.1: the acting subject's thread id. -/
  | actorSubject
  /-- WS-SM SM9.C.1: the acting subject's security domain. -/
  | actorDomain
  deriving Repr, DecidableEq, Inhabited

namespace AuditReadField

/-- WS-SM SM9.A.2: the enumeration. -/
def all : List AuditReadField :=
  [.srcDomain, .dstDomain, .targetObject, .timestamp, .actorSubject, .actorDomain]

/-- WS-SM SM9.A.2: every field is enumerated. -/
theorem mem_all (f : AuditReadField) : f ∈ all := by cases f <;> decide

/-- WS-SM SM9.A.2: no duplicates. -/
theorem all_nodup : all.Nodup := by decide

end AuditReadField

/-- WS-SM SM9.B.10: the three unbounded fields of a `DeclassificationRefusal`,
exported through the chunk protocol.

`originatingCore`, `syscall` and `reason` are **not** here: all three are
structurally bounded (a `Fin numCores`, one of `SyscallId.count` variants, and
one of the `KernelError` discriminants), so they ride one word together
(`AuditReadOp.refusalSlotTags`) exactly as the trail's core and trust bit do. -/
inductive RefusalReadField where
  /-- The refused subject's thread id. -/
  | subject
  /-- The subject's seam-resolved security domain. -/
  | subjectDomain
  /-- The capability pointer the caller supplied, verbatim. -/
  | requestedTarget
  deriving Repr, DecidableEq, Inhabited

namespace RefusalReadField

/-- WS-SM SM9.B.10: the enumeration. -/
def all : List RefusalReadField := [.subject, .subjectDomain, .requestedTarget]

/-- WS-SM SM9.B.10: every field is enumerated. -/
theorem mem_all (f : RefusalReadField) : f ∈ all := by cases f <;> decide

/-- WS-SM SM9.B.10: no duplicates. -/
theorem all_nodup : all.Nodup := by decide

end RefusalReadField

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
  /-- WS-SM SM9.B.10: the refusal ledger's write position paired with its
      **version** — the token a monitor brackets a multi-call reconstruction
      with.  One call, for the reason `status` is one call: a split read could
      pair a slot index with a version from a different state, and the pair
      would then describe no ledger that ever existed. -/
  | refusalStatus
  /-- WS-SM SM9.B.10: the ledger's two cumulative counters — attempts and
      evictions — in one word.  Both are `Fin`-bounded, so no chunking is
      owed; reading them together is what lets a monitor tell "I have seen
      every refusal" from "records were dropped before I polled". -/
  | refusalCounters
  /-- WS-SM SM9.B.10: ring slot `slot`'s bounded fields — the originating
      core, the syscall and the refusal reason — in one word. -/
  | refusalSlotTags (slot : Nat)
  /-- WS-SM SM9.B.10: how many chunks unbounded field `field` of ring slot
      `slot` needs. -/
  | refusalSlotFieldChunkCount (slot : Nat) (field : RefusalReadField)
  /-- WS-SM SM9.B.10: chunk `chunk` of unbounded field `field` of ring slot
      `slot`. -/
  | refusalSlotField (slot : Nat) (field : RefusalReadField) (chunk : Nat)
  /-- WS-SM SM9.C.1 (`refusalRecord_names_failed_hop`): how many chunks ring
      slot `slot`'s **refused receiver** needs — `0` when the refusal named no
      receiver, which is unambiguous because a present value always needs at
      least one chunk (`auditFieldChunkCount?` of `0` is `some 1`).  Its own
      pair of constructors rather than a fourth `RefusalReadField`, because the
      field is the ledger's one *optional* export and the absent case needs an
      in-band encoding the total-field protocol deliberately does not have. -/
  | refusalReceiverChunkCount (slot : Nat)
  /-- WS-SM SM9.C.1: chunk `chunk` of ring slot `slot`'s refused receiver;
      `.invalidArgument` when the refusal named none. -/
  | refusalReceiverChunk (slot : Nat) (chunk : Nat)
  /-- WS-SM SM9.D.14: **the causality verdict** — does visible entry `index`
      name visible entry `index - 1` as its predecessor?

      An *opaque verdict*, deliberately, rather than an export of
      `predecessorTags`.  The tags are global declassification identities, so
      handing them out would re-open exactly what SM9.A's view-local indices
      close; the verdict is one bit about a pair of entries the reader already
      holds, and it is the bit `declassificationChainCausal` is built from —
      reading it at every index reconstructs that predicate over the whole
      view.  `index = 0` has no predecessor and is `.invalidArgument`, the same
      answer an out-of-range index gets. -/
  | chainNamesPredecessor (index : Nat)
  /-- WS-SM SM9.D.14: **the general causality verdict** — does visible entry
      `later` name visible entry `earlier` as a predecessor, for *any* two
      visible indices `earlier < later`?

      `chainNamesPredecessor` tests only the adjacent pair `(index, index - 1)`,
      but `predecessorTags` is a set that may name *any* earlier event, and
      `declassificationChainCausal` / `chainLaunders` run over an arbitrary
      non-contiguous subchain of the view.  When an unrelated event lands between
      two causal hops — a different core appending into the single global log —
      the hop is no longer adjacent, and the adjacency verdict returns `0` on it.
      This opcode closes that gap: it reads the two entries the caller already
      holds (both view-local indices) and returns the same one opaque bit — never
      the tags — so it opens no channel the adjacency verdict did not, while
      reconstructing the *general* relation rather than only its adjacent
      instances.  `earlier ≥ later` names no valid predecessor and is refused
      exactly as `index = 0` is for the adjacent form.

      It deliberately does **not** recover a predecessor that has left the view
      (a drained entry): no view-local reader can query an entry it cannot see,
      so the gap it closes is the non-adjacent-but-both-visible one. -/
  | chainNamesEntry (later earlier : Nat)
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
  | .refusalStatus => .declassificationRefusalLedger
  | .refusalCounters => .declassificationRefusalLedger
  | .refusalSlotTags _ => .declassificationRefusalLedger
  | .refusalSlotFieldChunkCount _ _ => .declassificationRefusalLedger
  | .refusalSlotField _ _ _ => .declassificationRefusalLedger
  | .refusalReceiverChunkCount _ => .declassificationRefusalLedger
  | .refusalReceiverChunk _ _ => .declassificationRefusalLedger
  | .chainNamesPredecessor _ => .declassificationAuditTrail
  | .chainNamesEntry _ _ => .declassificationAuditTrail

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
read arms.  (Model layer since PR #870 round 6: the live entry serves monitors
only, so `isMonitor = false` is reachable through `auditReadWord` alone — the
class records what a partial reader *would* learn, and that even then it could
not count hidden entries.) -/
def auditExportedFieldValue (isMonitor : Bool) (index : Nat)
    (e : DeclassificationEvent) : AuditReadField → Nat
  | .srcDomain => e.srcDomain.id
  | .dstDomain => e.dstDomain.id
  | .targetObject => e.targetObject.val
  | .timestamp => if isMonitor then e.timestamp else index
  -- WS-SM SM9.C.1: the actor pair is the entry's own content, exported
  -- verbatim like the two flow domains.  It carries no *global* position, so it
  -- needs none of the timestamp's two-class treatment.
  | .actorSubject => e.actor.subject.toNat
  | .actorDomain => e.actor.domain.id

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
-- §4d  SM9.B.10 — the refusal ledger's export encoding
-- ============================================================================

/-! ## Two words for four bounded values, and a chunk protocol for three

The ledger's shape decides the encoding.  `nextSlot` and the two counters are
`Fin`-bounded, so they need no chunking; `version` is an unbounded monotone
counter and rides the same stated-premise treatment the trail's epoch does.  A
record's `subject`, `subjectDomain` and `requestedTarget` are unbounded `Nat`
in the model and go through the §3 chunk protocol unchanged, while its core,
syscall and reason are all structurally bounded and share one word.

**`refusalStatus` pairs the write position with the version deliberately.**  A
monitor cannot interpret the ring without knowing where the next write lands,
and a `nextSlot` read at one version against slots read at another describes a
ledger that never existed — the same tearing argument that keeps the trail's
`status` a single call.  The counters are a second atomic pair for the same
reason: "how many attempts" and "how many were dropped" are only meaningful
together, and both are bracketed by the version. -/

/-- WS-SM SM9.B.10: the slot width of each bounded tag in a ring record's
packed word — one byte each, which every tag fits with room to spare. -/
def refusalTagSlots : Nat := 256

/-- WS-SM SM9.B.10: a core id fits a tag slot. -/
theorem refusalTagSlots_bounds_core (c : CoreId) : c.val < refusalTagSlots := by
  have h := c.isLt
  have : SeLe4n.Kernel.Concurrency.numCores ≤ refusalTagSlots := by decide
  omega

/-- WS-SM SM9.B.10: a syscall id fits a tag slot — checked over the whole ABI
rather than over the syscalls the seam records today, so SM9.C.8's second
declassifying syscall needs no new bound. -/
theorem refusalTagSlots_bounds_syscall (sid : SeLe4n.Model.SyscallId) :
    sid.toNat < refusalTagSlots := by
  cases sid <;> decide

/-- WS-SM SM9.B.10: a kernel-error discriminant fits a tag slot.  Rides WS-RA's
own bound, so the reader inherits the ABI's numbering rather than inventing a
second one. -/
theorem refusalTagSlots_bounds_reason (e : KernelError) :
    e.toDiscriminant < refusalTagSlots := by
  have h := KernelError.toDiscriminant_lt e
  unfold refusalTagSlots
  omega

/-- WS-SM SM9.B.10: a ring record's three bounded tags, packed into one word. -/
def refusalTagsWord (r : DeclassificationRefusal) : Nat :=
  r.originatingCore.val +
    refusalTagSlots * (r.syscall.toNat + refusalTagSlots * r.reason.toDiscriminant)

/-- WS-SM SM9.B.10: **the packing is lossless** — all three tags decode. -/
theorem refusalTagsWord_roundtrip (r : DeclassificationRefusal) :
    refusalTagsWord r % refusalTagSlots = r.originatingCore.val ∧
    refusalTagsWord r / refusalTagSlots % refusalTagSlots = r.syscall.toNat ∧
    refusalTagsWord r / refusalTagSlots / refusalTagSlots = r.reason.toDiscriminant := by
  have hCore := refusalTagSlots_bounds_core r.originatingCore
  have hSid := refusalTagSlots_bounds_syscall r.syscall
  unfold refusalTagsWord refusalTagSlots at *
  refine ⟨by omega, by omega, by omega⟩

/-- WS-SM SM9.B.10: **the recorded reason is the discriminant the refused
caller received.**

The reader reuses WS-RA's numbering, so a monitor decoding a record's reason
and the caller reading its own `x1` label are reading the same number — which
is what lets an operator correlate a user-space report with the kernel's own
record without a second table to keep in step. -/
theorem refusalTagsWord_reason_is_abi_discriminant (r : DeclassificationRefusal) :
    KernelError.ofDiscriminant? (refusalTagsWord r / refusalTagSlots / refusalTagSlots)
      = some r.reason := by
  rw [(refusalTagsWord_roundtrip r).2.2]
  exact KernelError.ofDiscriminant?_toDiscriminant r.reason

/-- WS-SM SM9.B.10: the tags word fits the return register — three byte-wide
fields, so it is below `2^24` and the bound needs no premise. -/
theorem refusalTagsWord_fits (r : DeclassificationRefusal) :
    refusalTagsWord r < 2 ^ 64 := by
  have hCore := refusalTagSlots_bounds_core r.originatingCore
  have hSid := refusalTagSlots_bounds_syscall r.syscall
  have hReason := refusalTagSlots_bounds_reason r.reason
  unfold refusalTagsWord refusalTagSlots at *
  omega

/-- WS-SM SM9.B.10: the status word — the ring's next write position in the low
field, the ledger's version above it. -/
def refusalStatusWord (nextSlot version : Nat) : Nat :=
  nextSlot + version * refusalRingSize

/-- WS-SM SM9.B.10: decode the write position. -/
def refusalStatusSlot (w : Nat) : Nat := w % refusalRingSize

/-- WS-SM SM9.B.10: decode the version. -/
def refusalStatusVersion (w : Nat) : Nat := w / refusalRingSize

/-- WS-SM SM9.B.10: the status word determines both components — one word, one
ledger state. -/
theorem refusalStatusWord_roundtrip (nextSlot version : Nat)
    (hSlot : nextSlot < refusalRingSize) :
    refusalStatusSlot (refusalStatusWord nextSlot version) = nextSlot ∧
    refusalStatusVersion (refusalStatusWord nextSlot version) = version := by
  unfold refusalStatusSlot refusalStatusVersion refusalStatusWord refusalRingSize
  unfold refusalRingSize at hSlot
  omega

/-- WS-SM SM9.B.10 (**the stated bound**): with the write position within the
ring and the version below `2^59`, the status word fits the 64-bit return
register.

A premise rather than a theorem, for the reason the trail's epoch bound is one:
the version is an unbounded monotone counter and the model's words are `Nat`.
The live boundary **refuses** above `2^64` rather than wrapping
(`auditReadFromCore_word_fits`), so the worst case is a refused read and never
a version a monitor mistakes for a smaller one. -/
theorem refusalStatusWord_fits (nextSlot version : Nat)
    (hSlot : nextSlot < refusalRingSize) (hVersion : version < 2 ^ 59) :
    refusalStatusWord nextSlot version < 2 ^ 64 := by
  unfold refusalStatusWord refusalRingSize
  unfold refusalRingSize at hSlot
  omega

/-- WS-SM SM9.B.10: the counters word — attempts in the low field, evictions
above it.  Both components are `Fin`-bounded, so this word needs no premise at
all. -/
def refusalCountersWord (attempts dropped : Nat) : Nat :=
  attempts + dropped * (maxRefusalCount + 1)

/-- WS-SM SM9.B.10: decode the attempt count. -/
def refusalCountersAttempts (w : Nat) : Nat := w % (maxRefusalCount + 1)

/-- WS-SM SM9.B.10: decode the drop count. -/
def refusalCountersDropped (w : Nat) : Nat := w / (maxRefusalCount + 1)

/-- WS-SM SM9.B.10: the counters word determines both components. -/
theorem refusalCountersWord_roundtrip (attempts dropped : Nat)
    (hAttempts : attempts ≤ maxRefusalCount) :
    refusalCountersAttempts (refusalCountersWord attempts dropped) = attempts ∧
    refusalCountersDropped (refusalCountersWord attempts dropped) = dropped := by
  unfold refusalCountersAttempts refusalCountersDropped refusalCountersWord maxRefusalCount
  unfold maxRefusalCount at hAttempts
  omega

/-- WS-SM SM9.B.10: the counters word fits the return register
**unconditionally** — sixteen bits each, so below `2^32`.  The contrast with
`refusalStatusWord_fits` is the structural-bound argument doing its work: the
counters are `Fin`s and the version is not. -/
theorem refusalCountersWord_fits (attempts dropped : Nat)
    (hAttempts : attempts ≤ maxRefusalCount) (hDropped : dropped ≤ maxRefusalCount) :
    refusalCountersWord attempts dropped < 2 ^ 64 := by
  unfold refusalCountersWord maxRefusalCount
  unfold maxRefusalCount at hAttempts hDropped
  omega

/-- WS-SM SM9.B.10: the value of an unbounded field of a ring record. -/
def refusalExportedFieldValue (r : DeclassificationRefusal) : RefusalReadField → Nat
  | .subject => r.subject.val
  | .subjectDomain => r.subjectDomain.id
  | .requestedTarget => r.requestedTarget.val

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
  -- WS-SM SM9.B.10: the refusal ledger's arms.  Every one of them opens with
  -- the **configured** monitor gate, and refuses a caller it does not admit —
  -- there is no clearance-filtered *view* of a ledger to hand a partial reader
  -- instead.  A single global ring evicts, so a hidden refusal can remove an
  -- entry a lower reader could see, and the cumulative counters move on hidden
  -- activity independently of the ring; requiring full dominance discharges
  -- both halves of the §3.7 obligation rather than dodging either
  -- (`refusalLedger_requires_full_dominance`,
  -- `refusalLedger_partial_reader_learns_nothing`).
  | .refusalStatus =>
      if isMonitor then
        .ok (refusalStatusWord st.declassificationRefusals.nextSlot.val
              st.declassificationRefusals.version)
      else .error .illegalAuthority
  | .refusalCounters =>
      if isMonitor then
        .ok (refusalCountersWord st.declassificationRefusals.attemptCount.val
              st.declassificationRefusals.droppedCount.val)
      else .error .illegalAuthority
  | .refusalSlotTags slot =>
      if isMonitor then
        (if h : slot < refusalRingSize then
          match st.declassificationRefusals.recent.get ⟨slot, h⟩ with
          | none => .error .invalidArgument
          | some r => .ok (refusalTagsWord r)
         else .error .invalidArgument)
      else .error .illegalAuthority
  | .refusalSlotFieldChunkCount slot f =>
      if isMonitor then
        (if h : slot < refusalRingSize then
          match st.declassificationRefusals.recent.get ⟨slot, h⟩ with
          | none => .error .invalidArgument
          | some r =>
              match auditFieldChunkCount? (refusalExportedFieldValue r f) with
              | none => .error .auditFieldTooLarge
              | some n => .ok n
         else .error .invalidArgument)
      else .error .illegalAuthority
  | .refusalSlotField slot f chunk =>
      if isMonitor then
        (if h : slot < refusalRingSize then
          match st.declassificationRefusals.recent.get ⟨slot, h⟩ with
          | none => .error .invalidArgument
          | some r =>
              let v := refusalExportedFieldValue r f
              match auditFieldChunkCount? v with
              | none => .error .auditFieldTooLarge
              | some n =>
                  if chunk < n then .ok (auditFieldChunk v chunk) else .error .invalidArgument
         else .error .invalidArgument)
      else .error .illegalAuthority
  -- WS-SM SM9.C.1: the refused receiver — the ledger's one optional export.
  -- Absence is in-band: chunk count 0 means "no receiver named", which no
  -- present value can produce (`auditFieldChunkCount?` of any Nat is ≥ 1).
  | .refusalReceiverChunkCount slot =>
      if isMonitor then
        (if h : slot < refusalRingSize then
          match st.declassificationRefusals.recent.get ⟨slot, h⟩ with
          | none => .error .invalidArgument
          | some r =>
              match r.refusedReceiver with
              | none => .ok 0
              | some receiver =>
                  match auditFieldChunkCount? receiver.val with
                  | none => .error .auditFieldTooLarge
                  | some n => .ok n
         else .error .invalidArgument)
      else .error .illegalAuthority
  | .refusalReceiverChunk slot chunk =>
      if isMonitor then
        (if h : slot < refusalRingSize then
          match st.declassificationRefusals.recent.get ⟨slot, h⟩ with
          | none => .error .invalidArgument
          | some r =>
              match r.refusedReceiver with
              | none => .error .invalidArgument
              | some receiver =>
                  match auditFieldChunkCount? receiver.val with
                  | none => .error .auditFieldTooLarge
                  | some n =>
                      if chunk < n then .ok (auditFieldChunk receiver.val chunk)
                      else .error .invalidArgument
         else .error .invalidArgument)
      else .error .illegalAuthority
  -- WS-SM SM9.D.14: the causality verdict.  One bit about a pair of entries
  -- the caller already holds — never the tags themselves, which are global
  -- declassification identities and would re-open what the view-local indices
  -- close.  `index = 0` names no predecessor, so it is refused exactly as an
  -- out-of-range index is: the question does not exist, rather than having the
  -- answer "no".
  | .chainNamesPredecessor index =>
      match view[index]?, view[index - 1]? with
      | some later, some earlier =>
          if index = 0 then .error .invalidArgument
          else .ok (if declassificationEventNames later earlier then 1 else 0)
      | _, _ => .error .invalidArgument
  -- WS-SM SM9.D.14: the general causality verdict — the same one opaque bit for
  -- an arbitrary visible pair `earlier < later` rather than the adjacent one, so
  -- a hop split out of adjacency by an unrelated interleaved event is still
  -- queryable.  `earlier ≥ later` names no predecessor and is refused as the
  -- adjacent form refuses `index = 0`.  Reads only `view[later]` and
  -- `view[earlier]`, so it opens no channel the adjacency verdict did not.
  | .chainNamesEntry later earlier =>
      match view[later]?, view[earlier]? with
      | some laterEvent, some earlierEvent =>
          if earlier < later then
            .ok (if declassificationEventNames laterEvent earlierEvent then 1 else 0)
          else .error .invalidArgument
      | _, _ => .error .invalidArgument

/-- WS-SM SM9.D.14: **the causality verdict, characterised.**

The word is `1` exactly when the later entry's recorded snapshot names the
earlier one — the bit `declassificationChainCausal` is built from, computed on
two entries the reader already holds and never on the tags themselves. -/
theorem chainVerdict_ok (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (reader : SecurityDomain)
    (st : SystemState) (index : Nat) (hIndex : index ≠ 0)
    (later earlier : DeclassificationEvent)
    (hLater : (auditLogVisibleTo ctx reader st.declassificationAuditLog)[index]? = some later)
    (hEarlier :
      (auditLogVisibleTo ctx reader st.declassificationAuditLog)[index - 1]? = some earlier) :
    auditReadWord ctx monitorClearance reader st (.chainNamesPredecessor index) =
      .ok (if declassificationEventNames later earlier then 1 else 0) := by
  unfold auditReadWord
  simp only [hLater, hEarlier, if_neg hIndex]

/-- WS-SM SM9.D.14: **index `0` names no predecessor**, and is refused with the
same error an out-of-range index gets — the question does not exist, rather
than having the answer "no", which a `0` word would be indistinguishable
from. -/
theorem chainVerdict_index_zero_refused (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (reader : SecurityDomain)
    (st : SystemState) :
    auditReadWord ctx monitorClearance reader st (.chainNamesPredecessor 0) =
      .error .invalidArgument := by
  unfold auditReadWord
  cases h : (auditLogVisibleTo ctx reader st.declassificationAuditLog)[0]? <;> simp [h]

/-- WS-SM SM9.D.14: **the verdict is a function of the reader's own view.**

The reason it opens no channel, stated at the arm rather than left to the
whole-reader `auditRead_no_channel`: it reads `view[index]` and
`view[index - 1]` and nothing else, so two states with the same view answer
identically whatever else differs between them — including the taint table the
tags were snapshotted from, which is exactly the mutable structure
`chainCausal_is_history_local` says the verdict must not consult. -/
theorem chainVerdict_view_local (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (reader : SecurityDomain)
    (s1 s2 : SystemState) (index : Nat)
    (hView : auditLogVisibleTo ctx reader s1.declassificationAuditLog =
      auditLogVisibleTo ctx reader s2.declassificationAuditLog) :
    auditReadWord ctx monitorClearance reader s1 (.chainNamesPredecessor index) =
      auditReadWord ctx monitorClearance reader s2 (.chainNamesPredecessor index) := by
  unfold auditReadWord
  simp only [hView]

/-- WS-SM SM9.D.14: **the general causality verdict, characterised.**

The word is `1` exactly when the later entry's snapshot names the earlier one,
for any two visible indices `earlier < later` — the same bit `chainVerdict_ok`
gives for the adjacent pair, now for an arbitrary one, so the monitor can test a
hop an interleaved event split out of adjacency. -/
theorem chainEntryVerdict_ok (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (reader : SecurityDomain)
    (st : SystemState) (later earlier : Nat) (hLt : earlier < later)
    (laterEvent earlierEvent : DeclassificationEvent)
    (hLater :
      (auditLogVisibleTo ctx reader st.declassificationAuditLog)[later]? = some laterEvent)
    (hEarlier :
      (auditLogVisibleTo ctx reader st.declassificationAuditLog)[earlier]? = some earlierEvent) :
    auditReadWord ctx monitorClearance reader st (.chainNamesEntry later earlier) =
      .ok (if declassificationEventNames laterEvent earlierEvent then 1 else 0) := by
  unfold auditReadWord
  simp only [hLater, hEarlier, if_pos hLt]

/-- WS-SM SM9.D.14: `earlier ≥ later` names no valid predecessor, and is refused
with the same error the adjacent verdict gives `index = 0` — the question does
not exist, rather than having the answer "no". -/
theorem chainEntryVerdict_refused (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (reader : SecurityDomain)
    (st : SystemState) (later earlier : Nat) (hGe : later ≤ earlier) :
    auditReadWord ctx monitorClearance reader st (.chainNamesEntry later earlier) =
      .error .invalidArgument := by
  unfold auditReadWord
  cases hL : (auditLogVisibleTo ctx reader st.declassificationAuditLog)[later]? with
  | none => simp [hL]
  | some le =>
    cases hE : (auditLogVisibleTo ctx reader st.declassificationAuditLog)[earlier]? with
    | none => simp [hL, hE]
    | some ee =>
        simp only [hL, hE]
        exact if_neg (Nat.not_lt.mpr hGe)

/-- WS-SM SM9.D.14: **the general verdict is a function of the reader's own
view**, the same no-channel argument `chainVerdict_view_local` makes for the
adjacent form: it reads `view[later]` and `view[earlier]` and nothing else. -/
theorem chainEntryVerdict_view_local (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (reader : SecurityDomain)
    (s1 s2 : SystemState) (later earlier : Nat)
    (hView : auditLogVisibleTo ctx reader s1.declassificationAuditLog =
      auditLogVisibleTo ctx reader s2.declassificationAuditLog) :
    auditReadWord ctx monitorClearance reader s1 (.chainNamesEntry later earlier) =
      auditReadWord ctx monitorClearance reader s2 (.chainNamesEntry later earlier) := by
  unfold auditReadWord
  simp only [hView]

/-- WS-SM SM9.A.2: **the reader is a function of the readable structures it is
entitled to, and of nothing else.**

The keystone the flow argument (SM9.A.4b) is built on, and the reason the
reader can be shown to open no channel without inspecting each arm: two states
whose visible views agree, and whose epochs and refusal ledgers agree *when the
caller is entitled to those at all*, are indistinguishable to this reader.

One hypothesis per `ReadableStructure` clause, in the same shape
(`readableStructureAgrees`) — the trail's filtered view unconditionally, its
epoch under the monitor gate, and the ledger whole under the same gate.  WS-SM
SM9.B.10 added the third; a fourth readable structure adds a fourth, and the
`cases op` here stops elaborating until it does. -/
theorem auditRead_determined_by_view (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (reader : SecurityDomain)
    (st₁ st₂ : SystemState) (op : AuditReadOp)
    (hView : auditLogVisibleTo ctx reader st₁.declassificationAuditLog
      = auditLogVisibleTo ctx reader st₂.declassificationAuditLog)
    (hEpoch : auditMonitorAuthorized ctx monitorClearance reader = true →
      st₁.declassificationAuditEpoch = st₂.declassificationAuditEpoch)
    (hLedger : auditMonitorAuthorized ctx monitorClearance reader = true →
      st₁.declassificationRefusals = st₂.declassificationRefusals) :
    auditReadWord ctx monitorClearance reader st₁ op =
      auditReadWord ctx monitorClearance reader st₂ op := by
  unfold auditReadWord
  cases hMon : auditMonitorAuthorized ctx monitorClearance reader with
  | false => cases op <;> simp only [hView, Bool.false_eq_true, if_false]
  | true =>
    rw [hEpoch hMon, hLedger hMon]
    cases op <;> simp only [hView]

/-- WS-SM SM9.A.2 (**a partial reader cannot count hidden entries**): its every
read is determined by its visible view — the epoch, which counts entries it may
not see, reaches it through no arm, and neither does the refusal ledger, which
has no partial view at all (WS-SM SM9.B.10).

Stated over an arbitrary pair of states, so the two may differ by any number of
hidden entries, by any epoch whatsoever, and by any two refusal ledgers. -/
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

/-- WS-SM SM9.A.3 (**the destruction guard**, PR #870 review): does the caller
core `c` is running **see the whole trail**?

`false` on an idle core.  This is the decidable, per-operation half of the
drain's authority: it restricts *destruction* by what the caller can see, which
is the direction a records-derived predicate is **sound** in.  §2's
`auditMonitorGate_records_derived_unsound` is about the opposite direction —
granting *identity* (the epoch) from records — where draining the records
widens the grant; here draining the records can only ever *narrow* what a
future drain may touch, and on the empty trail the vacuous `true` guards an
operation that removes nothing.

Under a **validated** clearance (`LabelingContext.validatedAuditMonitorClearance`)
this is provably always `true` for a gate-passing caller
(`auditDrain_validated_view_complete`), so the live path never observes the
refusal; the guard is what makes the fail-closed claim hold for *arbitrary*
contexts rather than only for well-configured ones. -/
def auditDrainViewComplete (ctx : GenericLabelingContext) (st : SystemState)
    (c : CoreId) : Bool :=
  match auditReaderDomain ctx st c with
  | none => false
  | some reader =>
      decide (auditLogVisibleTo ctx reader st.declassificationAuditLog =
        st.declassificationAuditLog)

/-- WS-SM SM9.A.3: **drain a prefix of the trail.**

Two gates, both fail-closed with the same error so a refused caller cannot
tell which one refused it: the configured monitor clearance (§2), and — the
PR #870 review's destruction guard — the caller must **see every entry** it is
about to delete (`auditDrainViewComplete`).  The second gate is what closes the
misconfigured-deployment hole at the transition itself: a "monitor" whose
clearance does not dominate every subject can neither destroy the entries it
cannot see nor learn the global length from the return value, because the drain
refuses outright rather than proceeding over its blind spots.

Removes `min count length` entries and advances the epoch by exactly that many,
so surviving timestamps keep their identities and the next append cannot reuse
one (`auditDrain_next_timestamp_fresh`).  Returns the new trail length, which
for any caller the guard admits **is** its own new visible length
(`auditDrain_returned_length_is_visible` — no longer conditional on an operator
obligation). -/
def auditDrainVisiblePrefix (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (c : CoreId) (count : Nat) : Kernel Nat :=
  fun st =>
    if auditMonitorGate ctx monitorClearance st c && auditDrainViewComplete ctx st c then
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
single SM7 memory-model field — and passed **both** gates: the configured
clearance and the destruction guard. -/
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
    (auditMonitorGate ctx monitorClearance st c = true ∧
     auditDrainViewComplete ctx st c = true) := by
  unfold auditDrainVisiblePrefix at hStep
  split at hStep
  · rename_i hGate
    simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
    exact ⟨hStep.2.symm, hStep.1.symm, by simpa using hGate⟩
  · exact absurd hStep (by simp)

/-- WS-SM SM9.A.3 (**the destruction guard, fail-closed** — PR #870 review):
a gate-passing caller whose view is **incomplete** drains nothing.

This is the misconfigured-deployment case made harmless at the transition: a
deployment whose configured clearance does not dominate every subject can have
gate-passing callers with blind spots, and before this guard such a caller
would have destroyed the entries it cannot see and read the global length off
the return value.  Now it is refused outright, with the same error as a
non-monitor so the refusal does not even distinguish the two causes. -/
theorem auditDrain_denied_for_incomplete_view (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (c : CoreId) (count : Nat)
    (st : SystemState)
    (hIncomplete : auditDrainViewComplete ctx st c = false) :
    auditDrainVisiblePrefix ctx monitorClearance c count st = .error .illegalAuthority := by
  unfold auditDrainVisiblePrefix
  rw [hIncomplete, Bool.and_false]
  rfl

/-- WS-SM SM9.A.3 (**the return value is the caller's own view length** —
PR #870 review): on success the returned length is the length of the caller's
own post-drain visible view, not merely of the global trail.

Before the destruction guard this held only under the operator obligation; now
it is unconditional on success, because the guard admits exactly the callers
for which the two coincide — so the return value cannot leak a hidden entry's
existence even in a misconfigured deployment. -/
theorem auditDrain_returned_length_is_visible (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (c : CoreId) (count : Nat)
    (st : SystemState) (n : Nat) (st' : SystemState) (reader : SecurityDomain)
    (hReader : auditReaderDomain ctx st c = some reader)
    (hStep : auditDrainVisiblePrefix ctx monitorClearance c count st = .ok (n, st')) :
    n = (auditLogVisibleTo ctx reader st'.declassificationAuditLog).length := by
  obtain ⟨hSt', hn, -, hComplete⟩ :=
    auditDrain_frame ctx monitorClearance c count st n st' hStep
  unfold auditDrainViewComplete at hComplete
  rw [hReader] at hComplete
  have hView : auditLogVisibleTo ctx reader st.declassificationAuditLog =
      st.declassificationAuditLog := by
    exact of_decide_eq_true hComplete
  have hAll : ∀ e ∈ st.declassificationAuditLog,
      auditEntryVisibleTo ctx reader e = true := by
    have hFilter := hView
    unfold auditLogVisibleTo at hFilter
    exact List.filter_eq_self.mp hFilter
  subst hSt'
  have hViewPost : auditLogVisibleTo ctx reader
      (st.declassificationAuditLog.drop
        (min count st.declassificationAuditLog.length)) =
      st.declassificationAuditLog.drop
        (min count st.declassificationAuditLog.length) :=
    auditLogVisibleTo_eq_self ctx reader _
      (fun e hMem => hAll e (List.mem_of_mem_drop hMem))
  show n = (auditLogVisibleTo ctx reader
    (st.declassificationAuditLog.drop
      (min count st.declassificationAuditLog.length))).length
  rw [hViewPost, List.length_drop, hn]

/-- WS-SM SM9.A.3: **a qualifying caller sees the whole trail.**

The bridge from the configuration obligation to the visibility fact: under a
well-formed configuration (the monitor clearance is a top of the flow policy) a
caller that passes the gate dominates every domain, hence every recorded
`srcDomain` **and** every recorded `dstDomain`, hence its visible view *is* the
trail.  This is what makes the drain positionally blind — there is no
partial-visibility prefix to probe. -/
theorem auditDrain_requires_full_dominance (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (reader : SecurityDomain)
    (log : DeclassificationAuditLog)
    (hTop : auditMonitorClearanceIsTop ctx monitorClearance)
    (hTrans : ctx.policy.isTransitive)
    (hGate : auditMonitorAuthorized ctx monitorClearance reader = true) :
    auditLogVisibleTo ctx reader log = log :=
  auditLogVisibleTo_eq_self ctx reader log
    (fun e _ => by
      have hAll := auditMonitorAuthorized_dominates_all ctx monitorClearance reader hTop
        hTrans hGate
      simp [auditEntryVisibleTo, hAll e.srcDomain, hAll e.dstDomain, hAll e.actor.domain,
        hAll (ctx.objectDomainOf e.targetObject)])

/-- WS-SM SM9.C.1: **a domain the labeling assigns to some entity** — a subject
or an object.

The generalisation SM9.C forces.  While `.declassify` was the only producer,
every recorded source was a *subject's* domain and every recorded destination an
*object's*, and the two invariants below could say so.  A two-hop delivery
records a hop whose source is the intermediate notification's domain and whose
destination is the receiving thread's, so neither of those sharper statements
survives; what does survive — and is all the drain's dominance argument needs —
is that a recorded domain is one the labeling gives to *something*, since the
configured monitor is validated to dominate both families. -/
def labelingAssignedDomain (ctx : GenericLabelingContext) (d : SecurityDomain) : Prop :=
  (∃ tid : SeLe4n.ThreadId, d = ctx.threadDomainOf tid) ∨
    (∃ oid : SeLe4n.ObjId, d = ctx.objectDomainOf oid)

/-- WS-SM SM9.C.1: a subject's domain is labeling-assigned. -/
theorem labelingAssignedDomain_thread (ctx : GenericLabelingContext)
    (tid : SeLe4n.ThreadId) : labelingAssignedDomain ctx (ctx.threadDomainOf tid) :=
  Or.inl ⟨tid, rfl⟩

/-- WS-SM SM9.C.1: an object's domain is labeling-assigned. -/
theorem labelingAssignedDomain_object (ctx : GenericLabelingContext)
    (oid : SeLe4n.ObjId) : labelingAssignedDomain ctx (ctx.objectDomainOf oid) :=
  Or.inr ⟨oid, rfl⟩

/-- WS-SM SM9.A.3: **every entry's source is a domain the labeling assigns.**

A property of kernel-produced trails rather than a gate: the audited producer
records `srcDomain := ctx.threadDomainOf tid` for the subject the executing core
is running, and SM9.C's second hop records the intermediate object's domain, so
every entry either writes satisfies this by construction.

It is *not* the visibility gate, and it does not age the way a records-derived
gate would.  A records-derived gate becomes **more permissive** as entries
vanish, which is the failure §2 refutes; this predicate becomes *more* true, and
it is a soundness hypothesis on the trail rather than the thing that decides who
may drain. -/
def auditTrailSourcesFromLabeling (ctx : GenericLabelingContext)
    (log : DeclassificationAuditLog) : Prop :=
  ∀ e ∈ log, labelingAssignedDomain ctx e.srcDomain

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
      [declassifyStoreEvent c (declassificationActorOf ctx tid) (ctx.threadDomainOf tid) (ctx.objectDomainOf targetId)
        targetId st] := hMem
  rcases List.mem_append.mp hMem' with hOld | hNew
  · exact hSources e hOld
  · rcases List.mem_singleton.mp hNew with rfl
    exact labelingAssignedDomain_thread ctx tid

/-! ### The destination invariant, generalised (WS-SM SM9.C.1)

PR #870 round 3 stated the destination sibling of `auditTrailSourcesFromLabeling`
in its **sharp** form — `dstDomain = ctx.objectDomainOf targetObject`, so a
reader cleared for the destination was cleared for the disclosed object's own
domain — and built the capstone `auditVisibleEntry_target_domain_flows` on it.

SM9.C's second-hop event makes that statement **false**: its destination is the
receiving *thread's* domain while its target names that thread's TCB, and the
labeling scores a thread and an object independently.  Retiring it is therefore
the honest move, and the two things it bought are both kept, each by something
stronger or equal:

* the object-identity discipline moves **into the filter** as its own conjunct,
  so the capstone holds with no trail hypothesis at all;
* the drain's dominance argument keeps the general form below, which every
  producer establishes and which the validated monitor clearance discharges.

A Tier-3 negative anchor forbids the retired name's return, in the SM8.E
retirement pattern. -/

/-- WS-SM SM9.C.1: **every entry's destination is a domain the labeling
assigns** — the surviving generalisation of the retired
`auditTrailDestinationsAreTargetDomains`. -/
def auditTrailDestinationsFromLabeling (ctx : GenericLabelingContext)
    (log : DeclassificationAuditLog) : Prop :=
  ∀ e ∈ log, labelingAssignedDomain ctx e.dstDomain

/-- WS-SM SM9.A.3: removing entries preserves it — the drain direction. -/
theorem auditTrailDestinationsFromLabeling_drop (ctx : GenericLabelingContext)
    (log : DeclassificationAuditLog) (d : Nat)
    (h : auditTrailDestinationsFromLabeling ctx log) :
    auditTrailDestinationsFromLabeling ctx (log.drop d) :=
  fun e hMem => h e (List.mem_of_mem_drop hMem)

/-- WS-SM SM9.A.3: the empty trail satisfies it — the boot witness. -/
@[simp] theorem auditTrailDestinationsFromLabeling_nil (ctx : GenericLabelingContext) :
    auditTrailDestinationsFromLabeling ctx [] := by
  intro e hMem; simp at hMem

/-- WS-SM SM9.C.1: **every entry's recorded actor domain is that actor's own
domain.**

The third trail invariant, and the one that lets the visibility filter gate the
disclosed *subject identity* through the `actor.domain` conjunct rather than
through a fifth conjunct of its own.  Unlike the destination invariant this one
**survives** SM9.C: both hops of a two-hop delivery share one actor, read off
the state by the same `declassificationActorOf` the single-hop producer uses. -/
def auditTrailActorsFromLabeling (ctx : GenericLabelingContext)
    (log : DeclassificationAuditLog) : Prop :=
  ∀ e ∈ log, e.actor.domain = ctx.threadDomainOf e.actor.subject

/-- WS-SM SM9.C.1: removing entries preserves it — the drain direction. -/
theorem auditTrailActorsFromLabeling_drop (ctx : GenericLabelingContext)
    (log : DeclassificationAuditLog) (d : Nat)
    (h : auditTrailActorsFromLabeling ctx log) :
    auditTrailActorsFromLabeling ctx (log.drop d) :=
  fun e hMem => h e (List.mem_of_mem_drop hMem)

/-- WS-SM SM9.C.1: the empty trail satisfies it — the boot witness. -/
@[simp] theorem auditTrailActorsFromLabeling_nil (ctx : GenericLabelingContext) :
    auditTrailActorsFromLabeling ctx [] := by
  intro e hMem; simp at hMem

/-- WS-SM SM9.A.3 / SM9.C.1: **the live declassification establishes it** — the
appended event's destination is `ctx.objectDomainOf targetId`, hence
labeling-assigned. -/
theorem declassifyObjectFromCore_preserves_trailDestinations
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (targetId : SeLe4n.ObjId) (st st' : SystemState)
    (hDests : auditTrailDestinationsFromLabeling ctx st.declassificationAuditLog)
    (hStep : declassifyObjectFromCore ctx declPolicy c targetId st = .ok ((), st')) :
    auditTrailDestinationsFromLabeling ctx st'.declassificationAuditLog := by
  obtain ⟨tid, -, hSt'⟩ :=
    declassifyObjectFromCore_frame_of_ok ctx declPolicy c targetId st st' hStep
  subst hSt'
  intro e hMem
  have hMem' : e ∈ st.declassificationAuditLog ++
      [declassifyStoreEvent c (declassificationActorOf ctx tid) (ctx.threadDomainOf tid)
        (ctx.objectDomainOf targetId) targetId st] := hMem
  rcases List.mem_append.mp hMem' with hOld | hNew
  · exact hDests e hOld
  · rcases List.mem_singleton.mp hNew with rfl
    exact labelingAssignedDomain_object ctx targetId

/-- WS-SM SM9.C.1: the live single-hop declassification establishes the actor
invariant — its actor is `declassificationActorOf ctx tid`, whose domain is that
thread's by definition. -/
theorem declassifyObjectFromCore_preserves_trailActors
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (targetId : SeLe4n.ObjId) (st st' : SystemState)
    (hActors : auditTrailActorsFromLabeling ctx st.declassificationAuditLog)
    (hStep : declassifyObjectFromCore ctx declPolicy c targetId st = .ok ((), st')) :
    auditTrailActorsFromLabeling ctx st'.declassificationAuditLog := by
  obtain ⟨tid, -, hSt'⟩ :=
    declassifyObjectFromCore_frame_of_ok ctx declPolicy c targetId st st' hStep
  subst hSt'
  intro e hMem
  have hMem' : e ∈ st.declassificationAuditLog ++
      [declassifyStoreEvent c (declassificationActorOf ctx tid) (ctx.threadDomainOf tid)
        (ctx.objectDomainOf targetId) targetId st] := hMem
  rcases List.mem_append.mp hMem' with hOld | hNew
  · exact hActors e hOld
  · rcases List.mem_singleton.mp hNew with rfl
    rfl

/-- WS-SM SM9.A.3 (PR #870 round 3, **the capstone aligning the audit view with
the projection**): a visible entry's target object is one whose **own domain
flows to the reader** — the same condition `capTargetObservable` applies before
revealing an object identity in the projected state.

This is the "structurally establish every exported field is classified by a
dominated domain" closure: an audit reader can never use the trail to recover an
object identity its own projection redacts.

**WS-SM SM9.C.1 — now unconditional.**  Round 3 derived it from the destination
conjunct plus the producer invariant `dstDomain = objectDomainOf targetObject`,
which SM9.C's second-hop event falsifies (its destination is the receiving
*thread's* domain).  The object-identity conjunct is in the filter itself, so
the capstone needs no hypothesis about the trail at all — a strengthening, and
the reason the retired invariant is not merely weakened but replaced. -/
theorem auditVisibleEntry_target_domain_flows (ctx : GenericLabelingContext)
    (reader : SecurityDomain) (log : DeclassificationAuditLog)
    {e : DeclassificationEvent} (h : e ∈ auditLogVisibleTo ctx reader log) :
    ctx.policy.canFlow (ctx.objectDomainOf e.targetObject) reader = true :=
  auditLogVisibleTo_cleared_target ctx reader log h

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

/-- WS-SM SM9.A.3 (PR #870 round 3): the **object** half of the dominance
obligation — the configured clearance dominates every domain the labeling can
assign to an object.

Owed since the visibility filter gained its destination conjunct, and owed
independently since the fourth conjunct disclosed `objectDomainOf targetObject`
for every entry: a first-hop entry's `dstDomain` is an *object* domain (the
producer sets it to the target object's own), so subject dominance alone does
not imply the monitor sees the whole trail.  A second-hop entry's `dstDomain`
is a *thread* domain instead (WS-SM SM9.C.1 — the reason
`auditTrailDestinationsAreTargetDomains` was retired), and that side rides the
subject half; both halves together cover every conjunct the filter checks.
Configuration-derived exactly as the subject half is. -/
def auditMonitorDominatesObjects (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) : Prop :=
  ∃ m, monitorClearance = some m ∧
    ∀ oid : SeLe4n.ObjId, ctx.policy.canFlow (ctx.objectDomainOf oid) m = true

/-- WS-SM SM9.A.3 (PR #870 round 3): a caller that passes the gate dominates
every object domain. -/
theorem auditMonitorAuthorized_dominates_objects (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (reader : SecurityDomain)
    (hDom : auditMonitorDominatesObjects ctx monitorClearance)
    (hTrans : ctx.policy.isTransitive)
    (hGate : auditMonitorAuthorized ctx monitorClearance reader = true) :
    ∀ oid : SeLe4n.ObjId, ctx.policy.canFlow (ctx.objectDomainOf oid) reader = true := by
  obtain ⟨m, hm, hAll⟩ := hDom
  subst hm
  intro oid
  exact hTrans _ m reader (hAll oid) hGate

/-- WS-SM SM9.A.3 (**the form a real deployment uses**): under the labeling's
dominance obligations — subjects for the sources, objects for the
destinations — a caller that passes the gate sees **the whole trail**: every
entry's source is a subject domain the monitor dominates, and every entry's
destination is its target object's domain, which the monitor dominates too.

This is what makes the drain positionally blind on the contexts the live path
actually carries: there is no partial-visibility prefix to probe.  (Named
`_of_labeling` since PR #870 round 3 — the pre-round form consumed the subject
half alone, which the destination conjunct in `auditEntryVisibleTo` makes
insufficient.) -/
theorem auditDrain_requires_full_dominance_of_labeling (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (reader : SecurityDomain)
    (log : DeclassificationAuditLog)
    (hDom : auditMonitorDominatesSubjects ctx monitorClearance)
    (hDomObj : auditMonitorDominatesObjects ctx monitorClearance)
    (hTrans : ctx.policy.isTransitive)
    (hSources : auditTrailSourcesFromLabeling ctx log)
    (hDests : auditTrailDestinationsFromLabeling ctx log)
    (hActors : auditTrailActorsFromLabeling ctx log)
    (hGate : auditMonitorAuthorized ctx monitorClearance reader = true) :
    auditLogVisibleTo ctx reader log = log := by
  have hAssigned : ∀ d, labelingAssignedDomain ctx d → ctx.policy.canFlow d reader = true := by
    rintro d (⟨tid, rfl⟩ | ⟨oid, rfl⟩)
    · exact auditMonitorAuthorized_dominates_subjects ctx monitorClearance reader hDom hTrans
        hGate tid
    · exact auditMonitorAuthorized_dominates_objects ctx monitorClearance reader hDomObj hTrans
        hGate oid
  refine auditLogVisibleTo_eq_self ctx reader log (fun e hMem => ?_)
  have hSrc := hAssigned _ (hSources e hMem)
  have hDst := hAssigned _ (hDests e hMem)
  have hActor : ctx.policy.canFlow e.actor.domain reader = true := by
    rw [hActors e hMem]
    exact auditMonitorAuthorized_dominates_subjects ctx monitorClearance reader hDom hTrans
      hGate e.actor.subject
  have hTarget := hAssigned _ (labelingAssignedDomain_object ctx e.targetObject)
  simp [auditEntryVisibleTo, hSrc, hDst, hActor, hTarget]


-- ============================================================================
-- §5b  SM9.A.3 / PR #870 review — the VALIDATED clearance
-- ============================================================================

/-! ## The dominance obligation, enforced structurally on the live path

The PR #870 review's P1 finding: `auditMonitorAuthorized` checks that the
caller dominates the configured clearance, and **nothing ever checked that the
clearance dominates the subjects** — `auditMonitorDominatesSubjects` existed
only as a hypothesis on theorems, so a deployment that configured a non-top
clearance (say, embedded `low`) minted "monitors" with blind spots: readers of
the global epoch that counts entries they cannot see, and drainers of evidence
they cannot see.

The obligation is not decidable for an arbitrary `GenericLabelingContext`
(`threadDomainOf` quantifies over an unbounded `ThreadId` space).  But the
**live path** never carries an arbitrary context: the dispatch arms run
`liftLegacyContext ctx`, whose `threadDomainOf` is
`embedLegacyLabel ∘ ctx.threadLabelOf` — every subject domain the live kernel
can ever assign is one of the **four** embedded labels
(`liftLegacyContext_threadDomain_embedded`), and — PR #870 round 3 — so is
every *object* domain (`liftLegacyContext_objectDomain_embedded`), which the
visibility filter's destination conjunct made load-bearing.  Over four labels
the obligation is a four-conjunct `Bool`, so the fix is the project's
enforce-it-structurally pattern: the live arms consume
`validatedAuditMonitorClearance`, which returns the configured clearance only
when it dominates all four embedded labels and **`none` otherwise** — a
misconfigured deployment behaves exactly like an unconfigured one, which is
the fail-closed posture SM8.C established for the declassification policy
itself.  One four-label check discharges **both** dominance halves
(`validatedAuditMonitorClearance_dominates_subjects` / `_dominates_objects`),
because subject and object domains land in the same embedded range.

The drain's `auditDrainViewComplete` guard (§5) stays alongside it as defense
in depth: validation closes the hole for the live context by construction, and
the guard closes it at the transition for **any** context. -/

/-- WS-SM SM9.A.3 (PR #870 review): the four legacy security labels — the
entire subject-label space of the live kernel. -/
def legacySubjectLabels : List SecurityLabel :=
  [{ confidentiality := .low,  integrity := .untrusted },
   { confidentiality := .low,  integrity := .trusted },
   { confidentiality := .high, integrity := .untrusted },
   { confidentiality := .high, integrity := .trusted }]

/-- WS-SM SM9.A.3: the enumeration is complete — `cases` over the two
two-valued fields. -/
theorem mem_legacySubjectLabels (l : SecurityLabel) : l ∈ legacySubjectLabels := by
  obtain ⟨c, i⟩ := l
  cases c <;> cases i <;> decide

/-- WS-SM SM9.A.3: **every subject domain the live context can assign is an
embedded legacy label.**  The range fact that makes the dominance obligation
decidable on the live path. -/
theorem liftLegacyContext_threadDomain_embedded (ctx : LabelingContext)
    (tid : SeLe4n.ThreadId) :
    ∃ l ∈ legacySubjectLabels,
      (liftLegacyContext ctx).threadDomainOf tid = embedLegacyLabel l :=
  ⟨ctx.threadLabelOf tid, mem_legacySubjectLabels _, rfl⟩

/-- WS-SM SM9.A.3 (PR #870 round 3): **every object domain the live context can
assign is an embedded legacy label too** — `liftLegacyContext`'s
`objectDomainOf` is `embedLegacyLabel ∘ objectLabelOf`, so the four-label
validation covers the destination conjunct exactly as it covers the source
one. -/
theorem liftLegacyContext_objectDomain_embedded (ctx : LabelingContext)
    (oid : SeLe4n.ObjId) :
    ∃ l ∈ legacySubjectLabels,
      (liftLegacyContext ctx).objectDomainOf oid = embedLegacyLabel l :=
  ⟨ctx.objectLabelOf oid, mem_legacySubjectLabels _, rfl⟩

/-- WS-SM SM9.A.3 (PR #870 review, **the validated clearance**): the configured
audit-monitor clearance, admitted only when it dominates every legacy subject
label under the live policy — `none` otherwise.

This is what the live `.auditRead` / `.auditDrain` arms consume in place of the
raw `LabelingContext.auditMonitorClearance`.  A deployment that configures a
non-dominating clearance therefore has **no monitor at all**: nothing reads a
global identity, nothing reads the epoch, nothing drains — exactly the
unconfigured deployment's posture, rather than a "monitor" with blind spots. -/
def validatedAuditMonitorClearance (ctx : LabelingContext) : Option SecurityDomain :=
  match ctx.auditMonitorClearance with
  | none => none
  | some m =>
      if legacySubjectLabels.all (fun l =>
          DomainFlowPolicy.legacyLattice.canFlow (embedLegacyLabel l) m) then
        some m
      else
        none

/-- WS-SM SM9.A.3: an unconfigured deployment validates to unconfigured. -/
@[simp] theorem validatedAuditMonitorClearance_none (ctx : LabelingContext)
    (h : ctx.auditMonitorClearance = none) :
    validatedAuditMonitorClearance ctx = none := by
  unfold validatedAuditMonitorClearance
  rw [h]

/-- WS-SM SM9.A.3 (**validation discharges the obligation**): a clearance that
survives validation dominates every subject domain the live context can
assign — the hypothesis `auditDrain_requires_full_dominance_of_subjects` and
`auditMonitorAuthorized_dominates_subjects` consume, now a theorem about the
live configuration rather than an operator's promise. -/
theorem validatedAuditMonitorClearance_dominates_subjects (ctx : LabelingContext)
    (m : SecurityDomain)
    (hVal : validatedAuditMonitorClearance ctx = some m) :
    auditMonitorDominatesSubjects (liftLegacyContext ctx) (some m) := by
  unfold validatedAuditMonitorClearance at hVal
  split at hVal
  · exact absurd hVal (by simp)
  · rename_i m' hEqCfg
    split at hVal
    · rename_i hAll
      obtain rfl : m' = m := Option.some.inj hVal
      refine ⟨m', rfl, fun tid => ?_⟩
      obtain ⟨l, hl, hEq⟩ := liftLegacyContext_threadDomain_embedded ctx tid
      rw [hEq]
      exact List.all_eq_true.mp hAll l hl
    · exact absurd hVal (by simp)

/-- WS-SM SM9.A.3 (PR #870 round 3): validation discharges the **object** half
of the obligation too — the destination conjunct's dominance, from the same
four-label check, because object domains land in the same embedded range as
subject domains. -/
theorem validatedAuditMonitorClearance_dominates_objects (ctx : LabelingContext)
    (m : SecurityDomain)
    (hVal : validatedAuditMonitorClearance ctx = some m) :
    auditMonitorDominatesObjects (liftLegacyContext ctx) (some m) := by
  unfold validatedAuditMonitorClearance at hVal
  split at hVal
  · exact absurd hVal (by simp)
  · rename_i m' hEqCfg
    split at hVal
    · rename_i hAll
      obtain rfl : m' = m := Option.some.inj hVal
      refine ⟨m', rfl, fun oid => ?_⟩
      obtain ⟨l, hl, hEq⟩ := liftLegacyContext_objectDomain_embedded ctx oid
      rw [hEq]
      exact List.all_eq_true.mp hAll l hl
    · exact absurd hVal (by simp)

/-- WS-SM SM9.A.3 (**the live-path visibility fact, unconditional**): under a
validated clearance, a gate-passing caller sees **the whole trail** — every
hypothesis of the dominance bridge discharged by construction: both dominance
halves from validation, transitivity from `legacyLattice_wellFormed`, sources
and destinations from the producer's own invariants. -/
theorem auditDrain_validated_view_complete (ctx : LabelingContext)
    (m reader : SecurityDomain) (log : DeclassificationAuditLog)
    (hVal : validatedAuditMonitorClearance ctx = some m)
    (hSources : auditTrailSourcesFromLabeling (liftLegacyContext ctx) log)
    (hDests : auditTrailDestinationsFromLabeling (liftLegacyContext ctx) log)
    (hActors : auditTrailActorsFromLabeling (liftLegacyContext ctx) log)
    (hGate : auditMonitorAuthorized (liftLegacyContext ctx) (some m) reader = true) :
    auditLogVisibleTo (liftLegacyContext ctx) reader log = log :=
  auditDrain_requires_full_dominance_of_labeling (liftLegacyContext ctx) (some m) reader log
    (validatedAuditMonitorClearance_dominates_subjects ctx m hVal)
    (validatedAuditMonitorClearance_dominates_objects ctx m hVal)
    DomainFlowPolicy.legacyLattice_wellFormed.2 hSources hDests hActors hGate

/-- WS-SM SM9.A.3 (PR #870 review, **the misconfiguration witness**): a
deployment that names embedded `low` as its monitor clearance validates to
`none` — the misconfigured deployment IS the unconfigured one, fail-closed.

`{high, trusted}` does not flow to `{low, untrusted}` (confidentiality would
descend), so the four-label check refuses, and with it every consumer: no
epoch, no global identities, no drain. -/
theorem validatedAuditMonitorClearance_misconfigured_low (ctx : LabelingContext) :
    validatedAuditMonitorClearance
        { ctx with
          auditMonitorClearance := some (embedLegacyLabel SecurityLabel.publicLabel) }
      = none := rfl

/-- WS-SM SM9.A.3 (PR #870 review, **the fail-closed closure at the arm's
inputs**): under a misconfigured clearance the drain is refused for every
caller on every state — because the live arm consumes the VALIDATED clearance,
and a misconfigured one validates to `none`. -/
theorem misconfiguredDeployment_cannot_drain (ctx : LabelingContext)
    (c : CoreId) (count : Nat) (st : SystemState)
    (hMis : validatedAuditMonitorClearance ctx = none) :
    auditDrainVisiblePrefix (liftLegacyContext ctx) (validatedAuditMonitorClearance ctx)
        c count st = .error .illegalAuthority := by
  rw [hMis]
  exact auditDrain_unconfigured_denied (liftLegacyContext ctx) c count st

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

/-- WS-SM SM9.A.3: the returned length never exceeds the pre-state trail's —
unconditional, since the drain only removes. -/
theorem auditDrain_returned_length_le (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (c : CoreId) (count : Nat)
    (st : SystemState) (n : Nat) (st' : SystemState)
    (hStep : auditDrainVisiblePrefix ctx monitorClearance c count st = .ok (n, st')) :
    n ≤ st.declassificationAuditLog.length := by
  obtain ⟨-, hn, -⟩ := auditDrain_frame ctx monitorClearance c count st n st' hStep
  omega

/-- WS-SM SM9.A.3 (**the drain's boundary-narrowing witness**): under the
mounted capacity bound the returned length fits the 64-bit return register,
so the `.auditDrain` arm's `Nat → UInt64` conversion is lossless.

The read side carries this as `auditReadFromCore_word_fits` /
`_toUInt64_lossless`; without this theorem the drain's narrowing was justified
only by an argument living outside the tree — the asymmetry the audit of this
phase found.  Unlike the read, no runtime guard is needed: the bound is the
16th `proofLayerInvariantBundle` conjunct, held in every reachable state. -/
theorem auditDrain_returned_length_fits (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (c : CoreId) (count : Nat)
    (st : SystemState) (n : Nat) (st' : SystemState)
    (hBounded : auditLogBounded st.declassificationAuditLog)
    (hStep : auditDrainVisiblePrefix ctx monitorClearance c count st = .ok (n, st')) :
    n < 2 ^ 64 := by
  have hLe := auditDrain_returned_length_le ctx monitorClearance c count st n st' hStep
  unfold auditLogBounded maxDeclassificationAuditEntries at hBounded
  omega

/-- WS-SM SM9.A.3: the consumer-facing form — the length the `.auditDrain` arm
stages survives the boundary conversion exactly. -/
theorem auditDrain_returned_length_toUInt64_lossless (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (c : CoreId) (count : Nat)
    (st : SystemState) (n : Nat) (st' : SystemState)
    (hBounded : auditLogBounded st.declassificationAuditLog)
    (hStep : auditDrainVisiblePrefix ctx monitorClearance c count st = .ok (n, st')) :
    n.toUInt64.toNat = n := by
  have hFits := auditDrain_returned_length_fits ctx monitorClearance c count st n st'
    hBounded hStep
  simpa using Nat.mod_eq_of_lt hFits

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
  obtain ⟨-, -, hGate, -⟩ := auditDrain_frame ctx monitorClearance c count st n st' hStep
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
-- §5c  PR #870 round 7 — the occupancy channel (CC-8), witnessed
-- ============================================================================

/-! ## The channel the capacity refusal carries — and why it is registered, not closed

Round 6 closed the occupancy's *gratuitous* receiver surface: the audit reader
is monitor-only, so no partial reader observes the trail through `.auditRead`.
The round-7 finding is that the **capacity refusal is a second receiver
surface**: `.declassify` is fail-closed at the bound, so a policy-authorized
subject reads the fill level off its own syscall outcome
(`.auditLogCapacityExceeded` vs success) — and a monitor's drain, which frees
capacity, thereby changes a lower subject's outcome.

This surface is **irreducible** under the trail's other commitments, each a
deliberate security decision with its own theorem: the trail is bounded
(`auditLogBounded`, the 16th bundle conjunct), refusal is fail-closed rather
than record-dropping (`declassifyStoreOnCore_never_unaudited` — an authorized
downgrade is recorded or does not happen), and the bound is recoverable (the
SM9.A drain — the 256-entry cliff is the phase's own subject).  Any actor who
can free a fail-closed bounded resource transmits to every consumer that can
observe its refusals; making the drain invisible to a subject means never
freeing that subject's capacity, which is the cliff again.  So the channel
gets the CC treatment rather than a third receiver-surface patch:
`acceptedCovertChannel_auditOccupancy` (CC-8) registers it with its receiver
set, alphabet and self-disclosure bounds, and the theorems here are its
witnesses. -/

/-- PR #870 round 7 (CC-8, **the alphabet**): under the mounted capacity bound
the fill level ranges over `maxDeclassificationAuditEntries + 1 = 257` values —
what one full occupancy observation can carry, and the figure the CC-8 entry's
per-drain bound (freed count ≤ 256, about 8 bits) is computed from. -/
theorem auditOccupancy_alphabet_bounded (st : SystemState)
    (hBounded : auditLogBounded st.declassificationAuditLog) :
    st.declassificationAuditLog.length < maxDeclassificationAuditEntries + 1 := by
  unfold auditLogBounded at hBounded
  omega

/-- PR #870 round 7 (CC-8, **the receiver's read**): at a full trail, a
policy-authorized declassification with a resolved subject and a present
target is refused with `.auditLogCapacityExceeded` — the outcome through which
an authorized declassifier observes occupancy.  The forward half of the flip
witness below. -/
theorem declassify_capacity_refusal_of_full
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (c : CoreId) (targetId : SeLe4n.ObjId) (st : SystemState)
    (tid : SeLe4n.ThreadId) (ty : SeLe4n.Model.KernelObjectType)
    (hCur : st.scheduler.currentOnCore c = some tid)
    (hType : st.getObjectType? targetId = some ty)
    (hDec : declassificationDecision ctx declPolicy (ctx.threadDomainOf tid)
      (ctx.objectDomainOf targetId) = .ok ())
    (hFull : maxDeclassificationAuditEntries ≤ st.declassificationAuditLog.length) :
    declassifyObjectFromCore ctx declPolicy c targetId st
      = .error .auditLogCapacityExceeded := by
  rw [declassifyObjectFromCore_eq_onCore ctx declPolicy c targetId st tid ty hCur hType]
  unfold authorizeDeclassificationOnCore
  rw [hDec]
  have hNone : recordDeclassificationChecked st.declassificationAuditLog
      (declassifyStoreEvent c (declassificationActorOf ctx tid) (ctx.threadDomainOf tid) (ctx.objectDomainOf targetId)
        targetId st) = none := by
    unfold recordDeclassificationChecked
    rw [if_neg (by omega)]
  rw [hNone]

/-- PR #870 round 7 (CC-8, **the flip witness**): a monitor's drain changes a
lower subject's declassification outcome.

If the same authorized request that succeeds after the drain is replayed
against the pre-drain full trail, it is refused with
`.auditLogCapacityExceeded` — so the drain transmitted at least one bit to
that subject.  Stated with the post-drain success as a premise, which is the
strongest honest shape: it quantifies over every way the request can be
well-formed rather than reconstructing the success conditions by hand, and the
drain's own frame supplies that nothing but the trail and its epoch moved.
This is the theorem the CC-8 inventory entry cites, and the reason the channel
cannot be closed by excluding another reader: the receiver here is the
subject's *own* syscall. -/
theorem auditDrain_flips_declassify_outcome
    (ctx : GenericLabelingContext) (declPolicy : DeclassificationPolicy)
    (monitorClearance : Option SecurityDomain) (cDrain cObs : CoreId)
    (count : Nat) (targetId : SeLe4n.ObjId) (st : SystemState)
    (n : Nat) (st' st'' : SystemState)
    (hFull : maxDeclassificationAuditEntries ≤ st.declassificationAuditLog.length)
    (hStep : auditDrainVisiblePrefix ctx monitorClearance cDrain count st = .ok (n, st'))
    (hOk : declassifyObjectFromCore ctx declPolicy cObs targetId st' = .ok ((), st'')) :
    declassifyObjectFromCore ctx declPolicy cObs targetId st
      = .error .auditLogCapacityExceeded := by
  obtain ⟨hSt', -, -⟩ := auditDrain_frame ctx monitorClearance cDrain count st n st' hStep
  have hCurEq : st'.scheduler.currentOnCore cObs = st.scheduler.currentOnCore cObs := by
    rw [hSt']
  have hTypeEq : st'.getObjectType? targetId = st.getObjectType? targetId := by
    rw [hSt']; rfl
  obtain ⟨tid, hCur', -⟩ :=
    declassifyObjectFromCore_frame_of_ok ctx declPolicy cObs targetId st' st'' hOk
  have hCur : st.scheduler.currentOnCore cObs = some tid := by
    rw [← hCurEq]; exact hCur'
  cases hType : st.getObjectType? targetId with
  | none =>
      exfalso
      have hType' : st'.getObjectType? targetId = none := by rw [hTypeEq]; exact hType
      rw [declassifyObjectFromCore_absent_target ctx declPolicy cObs targetId st' tid
        hCur' hType'] at hOk
      exact absurd hOk (by simp)
  | some ty =>
      have hType' : st'.getObjectType? targetId = some ty := by rw [hTypeEq]; exact hType
      rw [declassifyObjectFromCore_eq_onCore ctx declPolicy cObs targetId st' tid ty
        hCur' hType'] at hOk
      obtain ⟨-, -, hDec⟩ := authorizeDeclassificationOnCore_frame ctx declPolicy cObs
        (declassificationActorOf ctx tid) (ctx.threadDomainOf tid) (ctx.objectDomainOf targetId)
        targetId st' st'' hOk
      exact declassify_capacity_refusal_of_full ctx declPolicy cObs targetId st tid ty
        hCur hType hDec hFull

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
no retry protocol exists at all: since PR #870 round 6 the live entry refuses
it outright (`auditReadFromCore_partial_reader_denied`) — a reader whose view a
monitor's drain can move is a reader the drain signals to — so the partial-class
stability theorems below quantify over the *model* reader, recording what such
a caller would have been promised.  The trail's consumer of record is the
monitor. -/

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
      op = .coreAndTrust i ∨ op = .basisByteCount i ∨ op = .basisChunk i k ∨
      op = .chainNamesPredecessor i →
      i < (auditLogVisibleTo ctx reader st.declassificationAuditLog).length)
    (hEntryIdx : ∀ l e, op = .chainNamesEntry l e →
      l < (auditLogVisibleTo ctx reader st.declassificationAuditLog).length ∧
      e < (auditLogVisibleTo ctx reader st.declassificationAuditLog).length)
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
    simp only [hEntry i (hIndex i .srcDomain k
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))]
  -- WS-SM SM9.B.10: the refusal arms read the ledger and never the trail, so an
  -- append leaves them untouched for a reason the trail's arms do not have —
  -- there is nothing in them for the append to move.
  | refusalStatus => rfl
  | refusalCounters => rfl
  | refusalSlotTags slot => rfl
  | refusalSlotFieldChunkCount slot f => rfl
  | refusalSlotField slot f k => rfl
  | refusalReceiverChunkCount slot => rfl
  | refusalReceiverChunk slot k => rfl
  -- WS-SM SM9.D.14: the causality verdict reads TWO entries — `i` and its
  -- predecessor — so it needs both to be stable, which `i - 1 ≤ i` supplies
  -- from the single index hypothesis.
  | chainNamesPredecessor i =>
    have hi := hIndex i .srcDomain 0 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    simp only [hEntry i hi, hEntry (i - 1) (Nat.lt_of_le_of_lt (Nat.sub_le i 1) hi)]
  -- WS-SM SM9.D.14: the general verdict reads TWO independent visible indices, so
  -- it needs both stable under the append — the dedicated two-index hypothesis.
  | chainNamesEntry l e =>
    obtain ⟨hl, he⟩ := hEntryIdx l e rfl
    simp only [hEntry l hl, hEntry e he]

/-- WS-SM SM9.A.5 (**the bracket**): for a monitor, an unchanged status word
means an unchanged epoch and an unchanged visible length — so no drain
intervened between the two observations.

Stated over the model's `Nat` words, where no wrap exists, so no wrap premise
appears here; what makes the statement usable by a real caller — which compares
the `UInt64` words it received — is that the boundary refuses any word at or
above `2^64` (`auditReadFromCore_word_fits`), so on everything a caller can
ever hold, `UInt64` equality coincides with the `Nat` equality this theorem
consumes (`auditReadFromCore_toUInt64_lossless`). -/
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
-- §7b  SM9.B.10 — what the refusal ledger's reader promises, and to whom
-- ============================================================================

/-! ## One gate, and no view at all below it

The trail gives a partially-cleared reader a *filtered view*: entries whose
disclosed domains it dominates, re-indexed so the hidden ones leave no gap.
There is no analogue for a ledger, and the reason is structural rather than a
choice.

A single global ring **evicts**.  Once a low-visible refusal occupies a slot,
enough higher-domain refusals *the reader cannot see* wrap the ring and
overwrite it — so a hidden write removes an entry from that reader's view,
which is §3.7's obligation (b) violated directly.  The counters carry the same
defect independently: a saturating global `attemptCount` moves on hidden
activity, so returning it to a partial reader leaks the same bit even with the
ring fixed.  Partitioning by domain does not type — `SecurityDomain.id` is an
unbounded `Nat`, so there is no finite family of domains to give a ring each
(`observerScopedGeneration_not_mountable`, again).

So the ledger is readable **only** under the configured monitor clearance, and
a caller below it observes *nothing* of it — which discharges obligation (b)
rather than dodging it, because there is no view for a hidden write to move.

**And the gate is the configuration, not the ring's surviving rows.**  The two
halves age differently: the ring evicts while the counters are cumulative.  Let
a run of hidden high-domain refusals bump `attemptCount` and `droppedCount`,
then let a ringful of low-domain refusals overwrite every high entry.  A low
reader now dominates every *surviving* row — so a records-derived gate admits
it — and reads counters that still carry the hidden history.
`refusalLedger_records_gate_unsound` keeps that counterexample refuted. -/

/-- WS-SM SM9.B.10 (**the gate**): a caller the configured monitor gate refuses
reads **nothing** of the refusal ledger — every one of its sub-operations fails
closed with `.illegalAuthority`, the same error every other authority refusal
returns. -/
theorem refusalLedger_requires_full_dominance (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (reader : SecurityDomain)
    (st : SystemState) (op : AuditReadOp)
    (hLedgerOp : op.readsStructure = .declassificationRefusalLedger)
    (hPartial : auditMonitorAuthorized ctx monitorClearance reader = false) :
    auditReadWord ctx monitorClearance reader st op = .error .illegalAuthority := by
  cases op <;> simp_all [auditReadWord, AuditReadOp.readsStructure]

/-- WS-SM SM9.B.10 (**the load-bearing negative**): an under-cleared caller
learns nothing of the ledger — its refusal reads are identical across states
that differ by an **arbitrary** ledger.

Stronger than "it is refused": a refusal that depended on the ledger's contents
would still be a channel.  Here the two states may differ by any number of
recorded attempts, any drop count and any version, and the caller cannot tell
them apart. -/
theorem refusalLedger_partial_reader_learns_nothing (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (reader : SecurityDomain)
    (st : SystemState) (L₁ L₂ : RefusalLedger) (op : AuditReadOp)
    (hLedgerOp : op.readsStructure = .declassificationRefusalLedger)
    (hPartial : auditMonitorAuthorized ctx monitorClearance reader = false) :
    auditReadWord ctx monitorClearance reader
        { st with declassificationRefusals := L₁ } op =
      auditReadWord ctx monitorClearance reader
        { st with declassificationRefusals := L₂ } op := by
  rw [refusalLedger_requires_full_dominance ctx monitorClearance reader _ op hLedgerOp hPartial,
      refusalLedger_requires_full_dominance ctx monitorClearance reader _ op hLedgerOp hPartial]

/-- WS-SM SM9.B.10 (**the gate is configuration-derived**): moving the ledger —
by any amount, in any component — does not move the gate's verdict.

The ledger's instance of `auditMonitorGate_is_configuration_derived`, stated
over exactly the field the seam writes.  It is what lets the ledger share the
trail's single privileged-reader gate without inheriting a predicate that ages
out from under it. -/
theorem refusalLedger_gate_is_configuration_derived (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (st : SystemState) (c : CoreId)
    (L : RefusalLedger) :
    auditMonitorGate ctx monitorClearance
        { st with declassificationRefusals := L } c =
      auditMonitorGate ctx monitorClearance st c := rfl

/-- WS-SM SM9.B.10: a minimal refusal record at a chosen domain, used to exhibit
concrete ledgers in the negatives below. -/
def refusalWitnessRecord (d : SecurityDomain) : DeclassificationRefusal :=
  { originatingCore := bootCoreId
    subject := ⟨0⟩
    subjectDomain := d
    syscall := .declassify
    reason := .declassificationDenied
    requestedTarget := SeLe4n.CPtr.ofNat 1
    refusedReceiver := none }

/-- WS-SM SM9.B.10: a ledger whose ring is all-low except for one high-domain
record sitting exactly where the next write lands — the state one further
refusal turns into "every surviving row is visible to a low reader". -/
def refusalEvictionWitness : RefusalLedger :=
  { attemptCount := ⟨5, by decide⟩
    recent :=
      (Vector.replicate refusalRingSize (some (refusalWitnessRecord ⟨0⟩))).set 0
        (some (refusalWitnessRecord ⟨3⟩)) (by decide)
    nextSlot := ⟨0, by decide⟩
    droppedCount := ⟨0, by decide⟩
    version := 7 }

/-- WS-SM SM9.B.10 (**the load-bearing negative the gate exists for**): a gate
computed from the domains present in the ledger's **current** rows is unsound,
because the ring evicts while the counters do not.

The witness runs the whole story in one step.  Before: the ring holds a
`high`-sourced refusal a `low` reader cannot see, so a rows-derived predicate
refuses that reader.  One further low refusal overwrites it — and now **every
surviving row** is one the low reader dominates, so the rows-derived predicate
admits it, while `attemptCount` and `droppedCount` still count the hidden
attempt.  The reader would be handed counters describing activity it was never
cleared for, and the drop count would tell it exactly how much.

The configured gate refuses that reader throughout, because it never looked at
the rows.  Kept as a theorem so a later cut cannot quietly revert to the
cheaper gate: doing so makes this statement unprovable. -/
theorem refusalLedger_records_gate_unsound :
    ∃ (ctx : GenericLabelingContext) (monitorClearance : Option SecurityDomain)
      (reader : SecurityDomain) (Lbefore : RefusalLedger) (r : DeclassificationRefusal),
      (∃ i : Fin refusalRingSize,
        ((Lbefore.recent.get i).any
          (fun rec => !ctx.policy.canFlow rec.subjectDomain reader)) = true) ∧
      (∀ i : Fin refusalRingSize,
        (((recordRefusal Lbefore r).recent.get i).all
          (fun rec => ctx.policy.canFlow rec.subjectDomain reader)) = true) ∧
      0 < (recordRefusal Lbefore r).droppedCount.val ∧
      Lbefore.attemptCount.val < (recordRefusal Lbefore r).attemptCount.val ∧
      auditMonitorAuthorized ctx monitorClearance reader = false := by
  refine ⟨{ policy := DomainFlowPolicy.linearOrder
            objectDomainOf := fun _ => SecurityDomain.lowest
            threadDomainOf := fun _ => SecurityDomain.lowest
            endpointDomainOf := fun _ => SecurityDomain.lowest
            serviceDomainOf := fun _ => SecurityDomain.lowest },
          some ⟨3⟩, ⟨0⟩, refusalEvictionWitness, refusalWitnessRecord ⟨0⟩,
          ⟨⟨0, by decide⟩, by decide⟩, by decide, by decide, by decide, by decide⟩

/-- WS-SM SM9.B.10 (**why the ledger needs its own version**): the trail's
`status` token does **not** move when a refusal is recorded.

A monitor that bracketed a multi-call ledger read with the trail's status would
therefore assemble a **hybrid record** — fields from two different attempts —
and never detect it.  This is the negative that makes
`refusalLedger_version_advances_on_record` load-bearing rather than
decorative. -/
theorem auditStatus_does_not_detect_refusal_write (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (reader : SecurityDomain)
    (st : SystemState) (L : RefusalLedger) :
    auditReadWord ctx monitorClearance reader
        { st with declassificationRefusals := L } .status =
      auditReadWord ctx monitorClearance reader st .status := rfl

/-- WS-SM SM9.B.10 (**and the ledger's own token does**): recording a refusal
moves the refusal status word a monitor reads, so an unchanged word between two
reads means no refusal intervened.

The positive dual of the negative above, and the reader-level half of
`refusalRead_bracketed_detects_overwrite`. -/
theorem refusalStatus_detects_refusal_write (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (reader : SecurityDomain)
    (st : SystemState) (L : RefusalLedger) (r : DeclassificationRefusal)
    (hMonitor : auditMonitorAuthorized ctx monitorClearance reader = true) :
    auditReadWord ctx monitorClearance reader
        { st with declassificationRefusals := recordRefusal L r } .refusalStatus ≠
      auditReadWord ctx monitorClearance reader
        { st with declassificationRefusals := L } .refusalStatus := by
  simp only [auditReadWord, hMonitor, if_true, ne_eq, Except.ok.injEq]
  have hSlot : L.nextSlot.val < refusalRingSize := L.nextSlot.isLt
  have hSlot' : (recordRefusal L r).nextSlot.val < refusalRingSize :=
    (recordRefusal L r).nextSlot.isLt
  intro hEq
  have hVer := congrArg refusalStatusVersion hEq
  rw [(refusalStatusWord_roundtrip _ _ hSlot').2,
      (refusalStatusWord_roundtrip _ _ hSlot).2] at hVer
  simp only [refusalLedger_version_advances_on_record] at hVer
  omega

/-- WS-SM SM9.B.10: **the chunk protocol reconstructs a ring record's unbounded
fields exactly**, over the domain the export accepts.

The ledger's instance of `auditReadField_reconstructs`: folding the chunks a
monitor reads recovers the field's value on the nose, so a reconstructed
`subject`, `subjectDomain` or `requestedTarget` is the one the seam recorded
and never a truncation of it. -/
theorem refusalSlotField_reconstructs (r : DeclassificationRefusal)
    (f : RefusalReadField) (n : Nat)
    (hCount : auditFieldChunkCount? (refusalExportedFieldValue r f) = some n) :
    auditFoldChunks n
        (fun i => auditFieldChunk (refusalExportedFieldValue r f) i)
      = refusalExportedFieldValue r f :=
  auditReadField_reconstructs (refusalExportedFieldValue r f) n hCount

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
  -- WS-SM SM9.B.10: the refusal ledger's opcodes.  `index` names a **ring
  -- slot** here rather than a view index — the ledger has no clearance-filtered
  -- view, because a caller that is not the configured monitor is refused
  -- outright.
  | 12 => some .refusalStatus
  | 13 => some .refusalCounters
  | 14 => some (.refusalSlotTags index)
  | 15 => some (.refusalSlotFieldChunkCount index .subject)
  | 16 => some (.refusalSlotFieldChunkCount index .subjectDomain)
  | 17 => some (.refusalSlotFieldChunkCount index .requestedTarget)
  | 18 => some (.refusalSlotField index .subject chunk)
  | 19 => some (.refusalSlotField index .subjectDomain chunk)
  | 20 => some (.refusalSlotField index .requestedTarget chunk)
  -- WS-SM SM9.C.1: the actor pair, appended so every opcode below stays where
  -- it was — an ABI number is a contract, and renumbering to keep the field
  -- opcodes contiguous would break every already-compiled monitor.
  | 21 => some (.fieldChunkCount index .actorSubject)
  | 22 => some (.fieldChunkCount index .actorDomain)
  | 23 => some (.field index .actorSubject chunk)
  | 24 => some (.field index .actorDomain chunk)
  -- WS-SM SM9.C.1: the refused receiver, appended after the actor pair so
  -- every earlier opcode keeps its value.
  | 25 => some (.refusalReceiverChunkCount index)
  | 26 => some (.refusalReceiverChunk index chunk)
  -- WS-SM SM9.D.14: the causality verdict, appended for the same reason — an
  -- ABI number is a contract.
  | 27 => some (.chainNamesPredecessor index)
  -- WS-SM SM9.D.14: the general causality verdict (an arbitrary visible pair),
  -- appended after the adjacency verdict so every earlier opcode keeps its
  -- value.  `index` is `later`, `chunk` is `earlier` — the existing operand
  -- triple, no new register.
  | 28 => some (.chainNamesEntry index chunk)
  | _  => none

/-- WS-SM SM9.A.10: the number of `.auditRead` opcodes.  Pinned in the Rust
mirror, so a divergence is a conformance failure rather than a silent
`.invalidSyscallArgument` on a valid request. -/
def auditReadOpcodeCount : Nat := 29

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
  | .refusalStatus => (12, 0, 0)
  | .refusalCounters => (13, 0, 0)
  | .refusalSlotTags i => (14, i, 0)
  | .refusalSlotFieldChunkCount i .subject => (15, i, 0)
  | .refusalSlotFieldChunkCount i .subjectDomain => (16, i, 0)
  | .refusalSlotFieldChunkCount i .requestedTarget => (17, i, 0)
  | .refusalSlotField i .subject k => (18, i, k)
  | .refusalSlotField i .subjectDomain k => (19, i, k)
  | .refusalSlotField i .requestedTarget k => (20, i, k)
  | .fieldChunkCount i .actorSubject => (21, i, 0)
  | .fieldChunkCount i .actorDomain => (22, i, 0)
  | .field i .actorSubject k => (23, i, k)
  | .field i .actorDomain k => (24, i, k)
  | .refusalReceiverChunkCount i => (25, i, 0)
  | .refusalReceiverChunk i k => (26, i, k)
  | .chainNamesPredecessor i => (27, i, 0)
  | .chainNamesEntry l e => (28, l, e)

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
  | refusalStatus => rfl
  | refusalCounters => rfl
  | refusalSlotTags i => rfl
  | refusalSlotFieldChunkCount i f => cases f <;> rfl
  | refusalSlotField i f k => cases f <;> rfl
  | refusalReceiverChunkCount i => rfl
  | refusalReceiverChunk i k => rfl
  | chainNamesPredecessor i => rfl
  | chainNamesEntry l e => rfl

/-- WS-SM SM9.A.10 (**fail-closed**): an opcode outside the table is refused. -/
theorem decodeAuditReadOp_out_of_range (opcode index chunk : Nat)
    (hRange : auditReadOpcodeCount ≤ opcode) :
    decodeAuditReadOp opcode index chunk = none := by
  unfold auditReadOpcodeCount at hRange
  match opcode, hRange with
  | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h | 7, h | 8, h | 9, h
  | 10, h | 11, h | 12, h | 13, h | 14, h | 15, h | 16, h | 17, h | 18, h
  | 19, h | 20, h | 21, h | 22, h | 23, h | 24, h | 25, h | 26, h
  | 27, h | 28, h => omega
  | n + 29, _ => rfl

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

**The configuration gate comes first** (PR #870 review, round 2): with no
configured monitor clearance the read refuses outright, before any subject is
resolved.  Capability provisioning is an axis the labeling context cannot see —
a boot layer can install a readable `.auditTrail` capability whether or not the
deployment ever names a monitor — so without this gate "an unconfigured
deployment has no audit reader" would be false in exactly that deployment
shape: the capability would admit a partial reader the configuration never
opted into.  The gate makes the validated clearance the facility's one on/off
switch (the SM9.B direction: a single *configured* privileged-reader gate), and
the refusal is `.illegalAuthority` — the same error the drain's monitor gate
returns — so a probing caller cannot distinguish "feature off" from "not a
monitor".  The live arm passes `validatedAuditMonitorClearance`, so a
*misconfigured* deployment — a clearance that fails dominance validation — is
refused identically (`misconfiguredDeployment_cannot_read`).

**The live facility is monitor-only** (PR #870 review, round 6): after the
subject is resolved, a caller the monitor gate refuses is refused the *read*,
with the same `.illegalAuthority` as every other refusal cause.  Round 2 left
partial readers live in configured deployments, and that coexists with the
drain only by opening the channel §4c forbids: a monitor's drain removes
entries a partial reader can see, so that reader's visible length moves at the
monitor's choice — one bit per drain, from the fully-dominating monitor to a
lower subject, exactly the signal hiding the generation was meant to remove
(`auditDrain_moves_partial_readers_status` keeps the channel exhibited; hiding
the epoch narrows the *alphabet*, not the channel).  Making the drain preserve
every partial view instead is not available: a drain's purpose is deletion, no
per-observer state is mountable (`observerScopedGeneration_not_mountable`), and
a drain restricted to universally-invisible prefixes re-opens the 256-entry
cliff for any trail with a low-sourced entry.  So the partial class survives as
the **model layer** (`auditReadWord` still keys on the caller, and its §4b/§4c
theorems record what such a reader *would* learn), while the live syscall
serves only callers for whom every recorded subject's activity — the monitor's
drains included — is an authorized flow
(`auditReadFromCore_observer_dominates_subjects`).

Fails closed five ways: an unconfigured deployment has no reader
(`.illegalAuthority`), an idle core has no subject (`.illegalState`), a
resolved subject below the monitor clearance is not a live reader
(`.illegalAuthority` again — indistinguishable from the other authority
refusals), an index outside the caller's own view or a chunk past a field's
width is `.invalidArgument`, and a value too wide to export is
`.auditFieldTooLarge`.

**The `2 ^ 64` guard is not decoration.**  The boundary hands the word back
through a 64-bit register, and `Nat.toUInt64` *truncates*.  Exactly two arms can
exceed that bound, and for the same reason: each pairs a structurally bounded
component with an **unbounded monotone counter** — `status` with the trail's
epoch (`auditStatusWord_fits`, premise `generation < 2^55`) and `refusalStatus`
with the ledger's version (`refusalStatusWord_fits`, premise `version < 2^59`).
Every other arm is structurally below the bound: the chunk arms return a single
base-`2^32` digit, and the ledger's counters and tags are `Fin`s
(`refusalCountersWord_fits`, `refusalTagsWord_fits`).  So the guard is what
turns "would silently wrap after 2^55 drains, or after 2^59 refusals" into a
refused read (`auditReadFromCore_word_fits`) — one guard covering both, because
it is applied to the word rather than to the arm that produced it. -/
def auditReadFromCore (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (c : CoreId)
    (op : AuditReadOp) : Kernel Nat :=
  fun st =>
    match monitorClearance with
    | none => .error .illegalAuthority
    | some _ =>
        match auditReaderDomain ctx st c with
        | none => .error .illegalState
        | some reader =>
            if auditMonitorAuthorized ctx monitorClearance reader then
              match auditReadWord ctx monitorClearance reader st op with
              | .error e => .error e
              | .ok w => if w < 2 ^ 64 then .ok (w, st) else .error .auditFieldTooLarge
            else .error .illegalAuthority

/-- WS-SM SM9.A.10 (PR #870 round 2): **an unconfigured deployment cannot read
at all** — the deny-by-default posture the drain has had since landing
(`auditDrain_unconfigured_denied`), now on the read side, for *every* caller,
*every* operation, *every* state.  This is the theorem that makes the
capability-provisioning axis irrelevant to the "no audit reader by default"
claim: a boot-provisioned `.auditTrail` capability reaches an arm whose
transition refuses before resolving a subject. -/
theorem auditRead_unconfigured_denied (ctx : GenericLabelingContext)
    (c : CoreId) (op : AuditReadOp) (st : SystemState) :
    auditReadFromCore ctx none c op st = .error .illegalAuthority := rfl

/-- WS-SM SM9.A.10 (PR #870 round 2): a **misconfigured** deployment — a
configured clearance that fails the dominance validation — cannot read either,
because the live arm consumes the VALIDATED clearance and a misconfigured one
validates to `none`.  The read sibling of `misconfiguredDeployment_cannot_drain`:
a monitor with blind spots is refused the epoch and the entries alike, not just
the drain. -/
theorem misconfiguredDeployment_cannot_read (ctx : LabelingContext)
    (c : CoreId) (op : AuditReadOp) (st : SystemState)
    (hMis : validatedAuditMonitorClearance ctx = none) :
    auditReadFromCore (liftLegacyContext ctx) (validatedAuditMonitorClearance ctx)
        c op st = .error .illegalAuthority := by
  rw [hMis]
  exact auditRead_unconfigured_denied (liftLegacyContext ctx) c op st

/-- WS-SM SM9.A.10: an idle core cannot read the trail — there is no subject
whose clearance would select a view, so the operation fails closed and the state
is untouched.  Stated at a configured clearance, because in an unconfigured
deployment the configuration gate refuses first
(`auditRead_unconfigured_denied`) and the idle core is never consulted. -/
theorem auditReadFromCore_no_subject (ctx : GenericLabelingContext)
    (m : SecurityDomain) (c : CoreId) (op : AuditReadOp)
    (st : SystemState) (hIdle : st.scheduler.currentOnCore c = none) :
    auditReadFromCore ctx (some m) c op st = .error .illegalState := by
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
      · split at hStep
        · exact absurd hStep (by simp)
        · split at hStep
          · simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
            exact hStep.2.symm
          · exact absurd hStep (by simp)
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
    · split at hStep
      · split at hStep
        · exact absurd hStep (by simp)
        · rename_i hFits
          split at hStep
          · simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
            rename_i hLt
            exact hStep.1 ▸ hLt
          · exact absurd hStep (by simp)
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
  cases monitorClearance with
  | none => exact absurd (auditRead_unconfigured_denied ctx c op st ▸ hStep) (by simp)
  | some m =>
    simp only [auditReadFromCore, hReader] at hStep
    split at hStep
    · split at hStep
      · exact absurd hStep (by simp)
      · rename_i v hRead
        split at hStep
        · simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
          exact hStep.1 ▸ hRead
        · exact absurd hStep (by simp)
    · exact absurd hStep (by simp)

/-- WS-SM SM9.A.10 (PR #870 round 6, **the exclusion**): a resolved subject the
monitor gate refuses is refused the read — with the same error as an
unconfigured deployment and a non-monitor drain, so the refusal reveals nothing
a caller does not already know.

This is what closes the drain-signal channel at the live entry: the model-level
partial reader (`auditReadWord` at a non-monitor clearance) would observe its
visible length move under a monitor's drain
(`auditDrain_moves_partial_readers_status`), and the length rides both the
`status` word and the `.invalidArgument` boundary of every indexed
sub-operation, so hiding the generation alone leaves the one-bit-per-drain
signal §4c forbids.  Excluding the receiver removes the channel rather than
narrowing it. -/
theorem auditReadFromCore_partial_reader_denied (ctx : GenericLabelingContext)
    (m : SecurityDomain) (c : CoreId) (op : AuditReadOp) (st : SystemState)
    (reader : SecurityDomain)
    (hReader : auditReaderDomain ctx st c = some reader)
    (hPartial : auditMonitorAuthorized ctx (some m) reader = false) :
    auditReadFromCore ctx (some m) c op st = .error .illegalAuthority := by
  simp [auditReadFromCore, hReader, hPartial]

/-- WS-SM SM9.A.10 (PR #870 round 6): **every successful live read's observer is
a gate-passing monitor.**  The success-side characterisation of the exclusion —
the form the flow-closure theorem below and the NI inventory consume. -/
theorem auditReadFromCore_ok_is_monitor (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (c : CoreId) (op : AuditReadOp)
    (st : SystemState) (w : Nat) (st' : SystemState) (reader : SecurityDomain)
    (hReader : auditReaderDomain ctx st c = some reader)
    (hStep : auditReadFromCore ctx monitorClearance c op st = .ok (w, st')) :
    auditMonitorAuthorized ctx monitorClearance reader = true := by
  cases monitorClearance with
  | none => exact absurd (auditRead_unconfigured_denied ctx c op st ▸ hStep) (by simp)
  | some m =>
    simp only [auditReadFromCore, hReader] at hStep
    split at hStep
    · rename_i hGate
      exact hGate
    · exact absurd hStep (by simp)

/-- WS-SM SM9.A.10 (PR #870 round 6, **the channel, kept exhibited**): a
monitor's drain **moves a non-monitor reader's model-level status word** — the
reader's visible length drops when the drained prefix holds an entry it can
see, so a monitor choosing whether to include one transmits a bit per drain to
that reader.

The receiver is the *model* reader (`auditReadWord` at a non-monitor
clearance): the live entry refuses that caller outright
(`auditReadFromCore_partial_reader_denied`), which is what makes this a
refuted design rather than a live channel.  Kept as a theorem so a cut that
re-admits partial readers to the live path must confront it — hiding the drain
generation (§4c) does **not** discharge it, because the length is a second
carrier of the same bit.  The drained shape is exactly `auditDrain_frame`'s
committed post-state: the trail's `drop` and the epoch advanced by the count
removed. -/
theorem auditDrain_moves_partial_readers_status :
    ∃ (ctx : GenericLabelingContext) (monitorClearance : Option SecurityDomain)
      (reader : SecurityDomain) (log : DeclassificationAuditLog)
      (removed epoch w₁ w₂ : Nat),
      auditMonitorAuthorized ctx monitorClearance reader = false ∧
      auditReadWord ctx monitorClearance reader
          { (default : SystemState) with
            declassificationAuditLog := log,
            declassificationAuditEpoch := epoch } .status = .ok w₁ ∧
      auditReadWord ctx monitorClearance reader
          { (default : SystemState) with
            declassificationAuditLog := log.drop removed,
            declassificationAuditEpoch := epoch + removed } .status = .ok w₂ ∧
      w₁ ≠ w₂ := by
  refine ⟨{ policy := DomainFlowPolicy.linearOrder
            objectDomainOf := fun _ => SecurityDomain.lowest
            threadDomainOf := fun _ => SecurityDomain.lowest
            endpointDomainOf := fun _ => SecurityDomain.lowest
            serviceDomainOf := fun _ => SecurityDomain.lowest },
          some ⟨3⟩, ⟨0⟩,
          [{ auditTimestampWitness 0 with srcDomain := ⟨0⟩, dstDomain := ⟨0⟩ }],
          1, 0, _, _, by decide, rfl, rfl, by decide⟩

/-- WS-SM SM9.A.10 (PR #870 round 6, **the flow closure**): under the validated
clearance the live path consumes, a surviving reader dominates **every subject
domain** — so every subject's observable activity, the monitor's own drains
included, is a flow the policy already authorizes into that reader.

This is the formal content of "the drain-signal channel has no forbidden
receiver": the drain is performed by a running subject, and whatever a live
audit reader learns of it is a `subjectDomain → reader` flow this theorem
admits.  Composes the round-6 success characterisation with the round-1
validation (`validatedAuditMonitorClearance_dominates_subjects`) and the
lattice's transitivity. -/
theorem auditReadFromCore_observer_dominates_subjects (ctx : LabelingContext)
    (c : CoreId) (op : AuditReadOp) (st : SystemState) (w : Nat) (st' : SystemState)
    (reader : SecurityDomain)
    (hReader : auditReaderDomain (liftLegacyContext ctx) st c = some reader)
    (hStep : auditReadFromCore (liftLegacyContext ctx) (validatedAuditMonitorClearance ctx)
      c op st = .ok (w, st')) :
    ∀ tid : SeLe4n.ThreadId,
      (liftLegacyContext ctx).policy.canFlow
        ((liftLegacyContext ctx).threadDomainOf tid) reader = true := by
  cases hVal : validatedAuditMonitorClearance ctx with
  | none =>
      rw [hVal] at hStep
      exact absurd (auditRead_unconfigured_denied (liftLegacyContext ctx) c op st ▸ hStep)
        (by simp)
  | some m =>
      rw [hVal] at hStep
      have hMon := auditReadFromCore_ok_is_monitor (liftLegacyContext ctx) (some m) c op st
        w st' reader hReader hStep
      exact auditMonitorAuthorized_dominates_subjects (liftLegacyContext ctx) (some m) reader
        (validatedAuditMonitorClearance_dominates_subjects ctx m hVal)
        DomainFlowPolicy.legacyLattice_wellFormed.2 hMon

/-- WS-SM SM9.A.5 (**the bracket, at the words the caller actually holds**): a
monitor that reads `status` twice through the live entry point and observes the
**same `UInt64`** may conclude an unchanged visible length — and, being the
monitor, an unchanged epoch — so no drain intervened.

`auditRead_bracketed_detects_drain` is the model-level statement over `Nat`
words, where no wrap exists; a real caller compares the 64-bit registers it
received, and the composition from register equality back to the model-level
conclusion used to live only in a docstring's argument.  This theorem *is* that
composition: `auditReadFromCore_word_fits` puts both accepted words below
`2^64`, where `toUInt64` is injective, so register equality is model equality
and the model bracket applies.  The two reads may come from different cores —
the protocol's real shape, one subject observing twice from wherever it runs. -/
theorem auditReadFromCore_bracketed_detects_drain_u64 (ctx : GenericLabelingContext)
    (monitorClearance : Option SecurityDomain) (reader : SecurityDomain)
    (c₁ c₂ : CoreId) (st₁ st₂ : SystemState) (w₁ w₂ : Nat) (r₁ r₂ : SystemState)
    (hBounded₁ : auditLogBounded st₁.declassificationAuditLog)
    (hBounded₂ : auditLogBounded st₂.declassificationAuditLog)
    (hReader₁ : auditReaderDomain ctx st₁ c₁ = some reader)
    (hReader₂ : auditReaderDomain ctx st₂ c₂ = some reader)
    (hStep₁ : auditReadFromCore ctx monitorClearance c₁ .status st₁ = .ok (w₁, r₁))
    (hStep₂ : auditReadFromCore ctx monitorClearance c₂ .status st₂ = .ok (w₂, r₂))
    (hObs : w₁.toUInt64 = w₂.toUInt64) :
    (auditLogVisibleTo ctx reader st₁.declassificationAuditLog).length =
      (auditLogVisibleTo ctx reader st₂.declassificationAuditLog).length ∧
    (auditMonitorAuthorized ctx monitorClearance reader = true →
      st₁.declassificationAuditEpoch = st₂.declassificationAuditEpoch) := by
  have hL₁ := auditReadFromCore_toUInt64_lossless ctx monitorClearance c₁ .status st₁ w₁ r₁
    hStep₁
  have hL₂ := auditReadFromCore_toUInt64_lossless ctx monitorClearance c₂ .status st₂ w₂ r₂
    hStep₂
  have hEq : w₁ = w₂ := by rw [← hL₁, ← hL₂, hObs]
  have hv₁ := auditReadFromCore_value ctx monitorClearance c₁ .status st₁ reader w₁ r₁
    hReader₁ hStep₁
  have hv₂ := auditReadFromCore_value ctx monitorClearance c₂ .status st₂ reader w₂ r₂
    hReader₂ hStep₂
  exact auditRead_bracketed_detects_drain ctx monitorClearance reader st₁ st₂
    hBounded₁ hBounded₂ (by rw [hv₁, hv₂, hEq])

/-- WS-SM SM9.B.10: **the ledger's reads reach only the deployment's monitor**,
at the live entry point.

The entry refuses every non-monitor before any sub-operation runs (PR #870
round 6), so the ledger's model-level gate and the live gate agree — the ledger
never had a partial-reader class to lose.  Stated so a cut that re-admits
partial readers to the live entry has to confront the ledger's own eviction
channel rather than inheriting an exemption. -/
theorem refusalRead_requires_monitor_at_entry (ctx : GenericLabelingContext)
    (m : SecurityDomain) (c : CoreId) (op : AuditReadOp) (st : SystemState)
    (reader : SecurityDomain)
    (hReader : auditReaderDomain ctx st c = some reader)
    (hPartial : auditMonitorAuthorized ctx (some m) reader = false) :
    auditReadFromCore ctx (some m) c op st = .error .illegalAuthority :=
  auditReadFromCore_partial_reader_denied ctx m c op st reader hReader hPartial


end SeLe4n.Kernel
