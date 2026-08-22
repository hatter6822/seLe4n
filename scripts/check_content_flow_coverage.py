#!/usr/bin/env python3
"""Fail if a live syscall arm moves content its taint classification does not admit.

WS-SM SM9.D.7.  `contentFlowClass` (`InformationFlow/TaintPropagation.lean`) is
a **total** `SyscallId -> ContentFlowClass`, so a new syscall is a missing case
at elaboration.  That is necessary and not sufficient, and §3.7 of
`docs/planning/SMP_DECLASSIFICATION_COMPLETION_PLAN.md` says why in the sharpest
form the plan reaches: *totality over the wrong domain proves nothing about the
right one*.  `SyscallId` is exhaustive of dispatch **arms**; the taint
propagation is about **sub-transitions**, and no type in the tree enumerates
those.

So the completeness of the classification is established by **reach**, in the
idiom `check_live_arm_per_core_routing.py` already set for exactly this shape of
obligation: start from the live arms, walk the transitive callees through Lean's
elaborated environment, and fail on any arm that reaches a content write its
class does not admit.

Three properties, and each one has caught a different mistake in review:

* **(A) No unclassified content movement.**  An arm classified `.inert` (or
  `.clearsProvenance`) must not reach a constant that writes a content channel.
  A missed site here is a detector that misses real laundering — the unsafe
  direction.
* **(B) No vacuous classification.**  An arm classified `.movesContent` must
  reach one.  A classification that claims content movement and declares no
  edges is a lie in the other direction, and it is exactly what a hand-written
  table drifts into.
* **(C) One taint writer.**  The constants that write `SystemState.declassificationTaint`
  must be exactly the declared propagation surface.  This is the machine-checked
  form of SM9.D.12's "frames for every non-content transition": rather than
  hand-writing a frame lemma per transition, the gate establishes that no other
  constant can move the field at all, which `storeObject_declassificationTaint_eq`
  then makes true of every object write.

**What a content channel is — a declared scope, not a derivation.**  This model
tracks user *payload*: `TCB.pendingMessage` (the IPC message a thread holds) and
`Notification.pendingBadge` (the badge).  That list is a **threat-model boundary**, and
it is stated on the Lean side as `contentTrackedFields`, which this file's
`CONTENT_CHANNELS` mirrors; `contentFlowClass`'s docstring cites the same
boundary, and `capabilityBadgeChannel_out_of_scope` records the one deliberate
exclusion as a theorem.

The exclusion worth naming, because it is the one an arm could hide behind:
`CNode.slots`.  A capability's badge and rights are caller-supplied on a
`.cspaceMint`, so a mint *does* write caller-controlled bits into a CNode — but
those bits are capability **metadata** (the authority a capability names), not
payload, and tracking them would have to follow every `cspace*` operation and
every badged delivery.  So a cap-slot write is out of scope **by declaration**,
and the classification of an arm that only writes cap slots is a scope statement
rather than a claim that its writes are self-loops.  Changing that decision means
adding the channel here *and* deleting the Lean theorem — one edit, two places
that must agree, rather than a silent widening.

Within the declared scope the probe finds *writes* structurally: an application
of the structure's constructor whose argument at that field's index is neither a
projection of the same record (an unchanged field in a `{ r with ... }` update)
nor a closed term (`none`, `.idle` — a **clear**, which destroys content rather
than moving it).  No spelling of the update can hide from that, which is the
reason detection runs against the elaborated environment and not against source
text.

**Reach, stated honestly.**  Arm bodies come from the source text of the three
dispatch functions — text answers "which functions does this arm name" correctly
— read through the comment-free code view, so a commented-out call cannot add a
root and a docstring cannot remove one.  Everything after that is the elaborated
environment.  The walk is bounded by `--depth`; `--self-test` is the check that
the reach is not vacuous, planting a content write under an inert arm and
requiring the gate to find it.

Usage:  scripts/check_content_flow_coverage.py [--depth N] [--list] [--self-test]
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import tempfile

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(REPO, "scripts"))
import lean_code_view  # noqa: E402  (needs the path insert above)

API = os.path.join(REPO, "SeLe4n", "Kernel", "API.lean")
TAINT = os.path.join(REPO, "SeLe4n", "Kernel", "InformationFlow", "TaintPropagation.lean")

# The three dispatch functions whose arms are the live roots.  `dispatchWithCap`
# is the unchecked twin; it is walked too, because a content move reachable only
# from the unchecked arm is still a content move.
DISPATCHERS = ("dispatchCapabilityOnly", "dispatchWithCap", "dispatchWithCapChecked")

# WS-SM SM9.D.7 (C): the declared taint-writing surface.  Every other constant
# in the tree must leave `declassificationTaint` alone — which is what makes
# `applySyscallTaint` "the one writer" a checked fact.  Entries are the
# propagation API itself plus the entry point that applies it.
DECLARED_TAINT_WRITERS = {
    "SeLe4n.Kernel.TaintTable.set",
    "SeLe4n.Kernel.TaintTable.joinAt",
    "SeLe4n.Kernel.TaintTable.clearAt",
    "SeLe4n.Kernel.applyTaintFlow",
    "SeLe4n.Kernel.applyTaintClears",
    "SeLe4n.Kernel.applyOrigination",
    "SeLe4n.Kernel.applySyscallTaint",
}

# The two content channels, as (structure, field) pairs.  Named because they are
# the *subject* the gate is about; the gate then checks that the domain it
# quantifies over — every live arm — is exhaustive of what it polices.
# WS-SM SM9.D.7 (C): definitions that legitimately consume the taint-writing API
# without being part of it — the live entry point that applies a plan, and the
# planner that builds one.  Anything else naming the API is a finding.
DECLARED_TAINT_CONSUMERS = {
    # PR #873 round 6: the seam sits at the two **dispatchers**, not at the two
    # entries above them.  It used to be the entries, and that was the defect:
    # `dispatchSyscall`'s own docstring points integrators at
    # `dispatchSyscallChecked` for production user-space entry, and an integrator
    # who called it directly never reached a seam sitting one layer up — content
    # moved with no provenance, and a retype kept the destroyed object's tags.
    # Both dispatchers now apply the plan and both entries inherit it, which is
    # why the entries no longer appear here: they name the dispatcher, not the
    # API.
    "SeLe4n.Kernel.dispatchSyscallChecked",
    "SeLe4n.Kernel.dispatchSyscall",
    "SeLe4n.Kernel.TaintTable.empty",
    # PR #873 round 16: the builder's provenance seed.  The one-writer rule
    # governs the **propagation** surface -- within a running system only
    # `applySyscallTaint` moves provenance -- and a builder-phase constructor is
    # the other side of that boundary, as `Builder.createObject` writes
    # `objects` without being an object-store transition.
    #
    # It is here because provenance has exactly one genesis: origination by a
    # recording syscall.  Propagation moves what already exists, so from a state
    # where every tag is empty no propagation step is observable at all — which
    # is why the frozen/live taint-layer mismatch survived until a differential
    # scenario could start from a tagged state.  Without a seed the propagation
    # surface is untestable, and an untestable surface is how this branch's
    # divergences kept reaching review.
    "SeLe4n.Model.Builder.withTaint",
}

# WS-SM SM9.D.17 (audit): the definitions allowed to write
# `SystemState.declassificationTaint` DIRECTLY (a `{ st with .. }` update whose
# taint argument is not the field's own projection).  Exactly the apply step —
# everything else must route through it or leave the field alone.
DECLARED_FIELD_WRITERS = {
    "SeLe4n.Kernel.applySyscallTaint",
}

CONTENT_CHANNELS = [
    ("SeLe4n.Model.TCB", "pendingMessage"),
    ("SeLe4n.Model.Notification", "pendingBadge"),
]

# WS-SM SM9.D.13a (C3): arms that write the audit trail without being able to
# APPEND to it, each with the theorem that says so.
#
# The reach check below asks "does this arm write `declassificationAuditLog`",
# which is the detectable question; the one that matters for origination is "can
# this arm make `newlyRecordedEvents` non-empty".  `.auditDrain` separates them:
# it rewrites the field on every successful call, and it removes a prefix while
# advancing the epoch by exactly what it removed — a shape that yields `[]` in
# both branches (`newlyRecordedEvents_of_drop` covers the zero-length drain that
# leaves the epoch guard unfired).
#
# An exemption is only as good as its justification, so the probe asserts the
# named theorem is in the elaborated environment.  Delete the theorem and this
# arm goes back to failing the gate rather than quietly keeping a pass it no
# longer earns.
AUDIT_APPEND_EXEMPT = {
    "auditDrain": "SeLe4n.Kernel.newlyRecordedEvents_auditDrain",
}

# The self-test's planted channel: a field every inert scheduling arm writes
# with an open value (`priority := newPrio`).  If the write detector has stopped
# detecting, planting it flags nothing and the self-test fails — which is the
# whole point, since a gate that has lost its reach reports PASS.
SELF_TEST_CHANNEL = ("SeLe4n.Model.TCB", "priority")

# The self-test's planted rogue writer: a **private** definition that rewrites
# `SystemState.declassificationTaint` outright and reaches it through the declared
# API, so it must be reported by BOTH sweeps — the direct-field one (C2) and the
# API-naming one (C).
#
# Private on purpose.  Lean stores `private def foo` as `_private.<Module>.<n>.foo`,
# which answers `isInternal = true`, and both sweeps filtered on exactly that — so
# a private helper reachable from syscall dispatch could clear or replace provenance
# while the gate reported "one writer" over the 3 872 private definitions it never
# opened.  Planting the rogue *private* rather than *public* is what makes this
# case bite: a public plant passes against the old filter too and would have
# reported PASS on the blind gate.
SELF_TEST_ROGUE = "cfPlantedPrivateTaintWriter"

# A second plant, in the shape a matcher could have hidden: the helper
# **pattern-matches the `SystemState`** and rebuilds it with a replacement taint
# table.  Lean puts `SystemState.mk` in the generated `.match_1` for this shape as
# well as in the user definition, so it is the case where "the sweep skips
# generated auxiliaries" could have meant "the sweep skips the write".  Planted
# so that stays a checked fact rather than a reading of the elaborator.
SELF_TEST_ROGUE_MATCH = "cfPlantedMatchingTaintWriter"

# A third plant, for the *other* half of the private-name defect.  The two above
# pin the **sweeps**; this one pins **root resolution**.  `cfRoots` names an
# arm's helpers by the stem a human wrote, while Lean stores `private def foo` as
# `_private.<Module>.<n>.foo` — so an arm delegating its only payload write to a
# directly-called private helper produced no seed at all, its reach came back
# empty, and an `.inert` classification was accepted for an arm that moves
# content.  The plant is wired into a synthetic arm below, so the witness
# exercises resolution rather than the sweeps a public plant would also satisfy.
SELF_TEST_ROOT_HELPER = "cfPlantedPrivateArmHelper"
SELF_TEST_ROOT_ARM = "cfSelfTestPrivateRootArm"

# A fourth plant, for the spelling the detector stopped depending on (PR #873
# round 12).  The matcher plant above destructures and then rebuilds with
# `{ st with .. }`, so its unchanged fields are still projections; this one
# rebuilds through `SystemState.mk` positionally, so they are the *bound
# variables* of the match and no projection appears anywhere in the term.  That
# is the shape the old `isUpdate` test read as a fresh literal, letting a second
# direct writer pass the one-writer gate.  Generated from the structure's own
# field list rather than hand-written: 26 fields is too many to keep in step by
# hand, and a plant that silently stopped elaborating would take the witness
# with it.
SELF_TEST_ROGUE_REBUILD = "cfPlantedRebuildTaintWriter"

# Definitions that build a `SystemState` from nothing rather than rewrite one.
# See `cfStateConstructors` in the probe for why this is a named list.
#
# PR #873 round 16 adds the builder's provenance seed.  The one-writer rule is
# about the *propagation* surface -- within a running system only
# `applySyscallTaint` may move provenance -- and a builder-phase constructor is
# the other side of that boundary, exactly as `Builder.createObject` writes
# `objects` without being an object-store transition.  It earns its place rather
# than being excused: without a way to build a state that already carries
# provenance, no test can exercise the propagation step at all, which is how the
# frozen/live taint-layer mismatch stayed invisible until round 16.  The
# staleness check below fails if a name here stops matching a real definition,
# so this list cannot rot into a set of excuses for code that no longer exists.
STATE_CONSTRUCTORS = ["SeLe4n.Model.instInhabitedSystemState",
                      "SeLe4n.Model.Builder.withTaint"]

SELF_TEST_ROGUE_SRC = f"""
private def {SELF_TEST_ROGUE} (st : SeLe4n.Model.SystemState) :
    SeLe4n.Model.SystemState :=
  {{ st with declassificationTaint :=
      SeLe4n.Kernel.applyTaintClears [] SeLe4n.Kernel.TaintTable.empty }}

private def {SELF_TEST_ROGUE_MATCH} (st : SeLe4n.Model.SystemState)
    (t : SeLe4n.Kernel.TaintTable) : SeLe4n.Model.SystemState :=
  match st with
  | {{ declassificationTaint := _, .. }} => {{ st with declassificationTaint := t }}

private def {SELF_TEST_ROOT_HELPER} (tcb : SeLe4n.Model.TCB)
    (p : SeLe4n.Priority) : SeLe4n.Model.TCB :=
  {{ tcb with priority := p }}
"""

# PR #873 round 10: implementations that deliberately **refuse**.
#
# Splitting the reachability key per dispatcher (so a healthy arm can no longer
# mask a broken sibling) surfaces the arms that exist in a dispatcher only to
# fail closed: `.declassify` and `.declassifySignal` have no unchecked form,
# because their authority *is* a policy and "unchecked" would mean "every
# downgrade is authorized".  Their `dispatchWithCap` arms are
# `fun _ => .error .declassificationDenied`.
#
# Named rather than inferred, like `RETURN_FRAME_DELIVERY` and
# `AUDIT_APPEND_EXEMPT`, and given the same bite: a listed implementation must
# reach **nothing** — no content write and no trail write.  An entry that starts
# reaching one is a refusal that stopped refusing, which is a worse defect than
# the masking this set exists to allow past.
FAIL_CLOSED_ARMS: set[tuple[str, str]] = {
    ("dispatchWithCap", "declassify"),
    ("dispatchWithCap", "declassifySignal"),
}

SHAPE = os.path.join(REPO, "SeLe4n", "Kernel", "Architecture", "SyscallReturn.lean")
STATE = os.path.join(REPO, "SeLe4n", "Model", "State.lean")


def system_state_fields() -> list[str]:
    """`SystemState`'s field names, in declaration order, read off its own source.

    The rebuild plant needs every field positionally, and there are 26 of them.
    Reading the list here keeps the plant in step with the structure: a field
    added or reordered changes the plant with it, where a hand-written list would
    quietly stop elaborating and take the witness with it.
    """
    src = code_view(STATE)
    head = src.index("structure SystemState where")
    fields: list[str] = []
    for line in src[head:].split("\n")[1:]:
        if not line.strip():
            continue
        if not line.startswith("  "):
            break
        m = re.match(r"^  ([A-Za-z][A-Za-z0-9_']*)\s*:", line)
        if m:
            fields.append(m.group(1))
    if "declassificationTaint" not in fields:
        raise RuntimeError(
            f"parsed {len(fields)} SystemState fields with no `declassificationTaint`; "
            "the structure's shape moved and the rebuild plant cannot be generated")
    return fields


def rebuild_plant_src() -> str:
    """The destructured-rebuild plant, positional so no projection appears."""
    fields = system_state_fields()
    binders = ", ".join(f"f{i}" for i in range(len(fields)))
    args = " ".join(
        "t" if f == "declassificationTaint" else f"f{i}"
        for i, f in enumerate(fields))
    return f"""
private def {SELF_TEST_ROGUE_REBUILD} (st : SeLe4n.Model.SystemState)
    (t : SeLe4n.Kernel.TaintTable) : SeLe4n.Model.SystemState :=
  match st with
  | ⟨{binders}⟩ => SeLe4n.Model.SystemState.mk {args}
"""

PROBE = r"""
import SeLe4n
import SeLe4n.Platform.Staged
import Lean.Elab.Command

open Lean Elab Command

private def cfChannels : List (Name × Name) :=
  [@CHANNELS@]

private def cfRoots : List (String × String) :=
  [@ROOTS@]

private def cfTaintApi : List Name :=
  [@TAINTAPI@]

private def cfJustifications : List Name :=
  [@JUSTIFICATIONS@]

private def cfDepth : Nat := @DEPTH@

@PLANTED@

/-- Total: `Name.getString!` panics on a numeric component and this environment
has well over a hundred thousand constants. -/
private def cfLast : Name -> String
  | .str _ s => s
  | _        => ""

/-- Is `e` the projection of `field` out of *some* record?  Both spellings:
the compiler's `Expr.proj` and an application of the generated projection
function.  An unchanged field of a `{ r with .. }` update is one of these, and
must not be read as a write. -/
private def cfIsProjection (structName field : Name) (idx : Nat) (e : Expr) : Bool :=
  match e with
  | .proj s i _ => s == structName && i == idx
  | _ =>
    match e.getAppFn with
    | .const n _ => n == structName ++ field
    | _ => false

/-- **Is `hit` true of any application subterm?**, asking each distinct subterm
once.

An elaborated `Expr` is a DAG with heavy sharing, and the obvious recursive
predicate walks it as a tree: a subterm reached by k paths is re-examined k
times, which on kernel-sized bodies is the difference between milliseconds and
minutes.  The `||` short-circuit hides this on a body that *does* write the
field -- the walk stops at the first hit -- and not at all on one that does not,
which is the answer this gate needs for the inert arms and for every definition
it sweeps.  So the walk carries the set of subterms already examined: reaching
one again means it was examined and did not hit, because a hit returns
immediately.

`hit` is asked only of applications, which is where both callers' shapes live;
asking it of a bare `.const` constructor would be harmless (no argument at the
field index) but would not match what the uncached form did. -/
private partial def cfAnySubterm (hit : Expr -> Bool) (e : Expr)
    (seen : Std.HashSet Expr) : Bool × Std.HashSet Expr := Id.run do
  if seen.contains e then return (false, seen)
  let mut seen := seen.insert e
  match e with
  | .app .. =>
      if hit e then return (true, seen)
      let r := cfAnySubterm hit e.getAppFn seen
      if r.1 then return (true, r.2)
      seen := r.2
      for a in e.getAppArgs do
        let r := cfAnySubterm hit a seen
        if r.1 then return (true, r.2)
        seen := r.2
      return (false, seen)
  | .lam _ t b _ =>
      let r := cfAnySubterm hit t seen
      if r.1 then return (true, r.2)
      return cfAnySubterm hit b r.2
  | .forallE _ t b _ =>
      let r := cfAnySubterm hit t seen
      if r.1 then return (true, r.2)
      return cfAnySubterm hit b r.2
  | .letE _ t v b _ =>
      let r := cfAnySubterm hit t seen
      if r.1 then return (true, r.2)
      let r2 := cfAnySubterm hit v r.2
      if r2.1 then return (true, r2.2)
      return cfAnySubterm hit b r2.2
  | .mdata _ b => return cfAnySubterm hit b seen
  | .proj _ _ b => return cfAnySubterm hit b seen
  | _ => return (false, seen)

/-- A **write** of one content channel: the constructor applied with an argument
at the field's index that is neither a projection (unchanged) nor a closed term
(a clear -- `none`, `.idle`).  An open term is content coming from somewhere
else, which is precisely what taint has to follow. -/
private def cfScanHit (structName field : Name) (idx : Nat) (e : Expr) : Bool :=
  match e.getAppFn with
  | .const n _ =>
      if n == structName ++ `mk then
        match e.getAppArgs[idx]? with
        | none => false
        | some a =>
            !cfIsProjection structName field idx a && (a.hasLooseBVars || a.hasFVar)
      else false
  | _ => false

private def cfScan (structName field : Name) (idx : Nat) (e : Expr) : Bool :=
  (cfAnySubterm (cfScanHit structName field idx) e {}).1

/-- The channel indices, resolved once. -/
private def cfChannelIdx (env : Environment) : List (Name × Name × Nat) :=
  cfChannels.filterMap fun (structName, field) =>
    match (getStructureFields env structName).findIdx? (· == field) with
    | none => none
    | some idx => some (structName, field, idx)

/-- Prefiltered on the constructor's presence, the same way the field-writer
sweep below is: `cfScanHit` fires only where the application head is
`structName ++ `mk`, so a body whose used-constant set does not contain that
name cannot contain such an application, and the structural walk can be skipped
outright.  The used-constant set costs a fraction of a walk, and the filter is
exact rather than heuristic -- it excludes only bodies where `cfScan` is
provably `false`. -/
private def cfWritesChannel (idxs : List (Name × Name × Nat)) (e : Expr) : Bool :=
  let used := e.getUsedConstants
  idxs.any fun (structName, field, idx) =>
    used.contains (structName ++ `mk) && cfScan structName field idx e

/-- The name a human wrote, recovered from the name the elaborator stored.

`private def foo` is not stored as `foo`: Lean mangles it to
`_private.<Module>.<n>.foo`, which reports `isInternal = true` **and**
`isInternalDetail = true`.  Both sweeps below filtered on `isInternal`, so every
private definition in the tree — 11 292 of them — was skipped before its body was
ever inspected.  A private helper that rewrote `SystemState.declassificationTaint`
would therefore have passed the "one writer" checks by being private, which is
the opposite of what privacy should buy a definition in a gate whose subject is
"who writes this field". -/
private def cfUserName (n : Name) : Name := (privateToUserName? n).getD n

/-- The human-written definition a generated auxiliary belongs to.

`Ns.helper.match_1`, `Ns.helper.eq_3`, `Ns.helper._proof_1` all strip back to
`Ns.helper`.  A name with no such suffix is its own owner.

Why attribute rather than skip: a helper that pattern-matches a `SystemState`
before rebuilding it puts the `SystemState.mk` application in the generated
matcher **as well as** in its own body (checked — the self-test plants exactly
that shape).  "As well as" is what makes skipping auxiliaries safe today, and it
is not a property this gate should depend on the elaborator continuing to have.
Scanning the auxiliary and reporting it under its owner keeps the coverage
without turning `applySyscallTaint.match_1` into an undeclared writer. -/
private partial def cfOwnerName : Name -> Name
  | .str p s =>
      if s.startsWith "match_" || s.startsWith "eq_" || s.startsWith "proof_"
          || s.startsWith "_" || s == "eq_def" || s == "brecOn"
          || s == "below" || s == "induct" || s == "fun_cases" then
        cfOwnerName p
      else
        .str p s
  | n => n

/-- Resolve short names to every non-internal constant whose last component
matches, for **every** stem in one pass.  Ambiguity is harmless here: the walk
is a union, so over-resolving can only widen the reach, never hide a write.

Built as an index rather than a per-stem search.  Resolving one stem means
scanning all 126 700 constants, the 34 arms name some 680 stems between them,
and `run_cmd` bodies run in Lean's *interpreter* -- so the per-stem form was
~86 million interpreted iterations and essentially this gate's whole runtime
(`interpretation took 79.9s` against 3 s of everything else).  One pass fills
the index; a stem is then a hash lookup. -/
private def cfStemIndex (env : Environment) (wanted : Std.HashSet String) :
    Std.HashMap String (Array Name) := Id.run do
  let mut idx : Std.HashMap String (Array Name) := {}
  for (n, _) in env.constants.toList do
    -- PR #873 round 8: keyed on the name a **human wrote**, not on the name the
    -- elaborator stored.  `private def foo` is stored as
    -- `_private.<Module>.<n>.foo` and reports `isInternal`, so filtering on that
    -- dropped every private definition from this index — and `cfRoots` names
    -- arm helpers by their user-facing stem.  An arm whose only payload write
    -- lives in a directly-called private helper therefore produced **no seed**,
    -- its reach was empty, and an `.inert` classification could be accepted for
    -- an arm that moves content.  The round-6 fix taught the *sweeps* to see
    -- private writers; this teaches the *roots* to resolve them, which is the
    -- other half of the same defect.
    --
    -- Generated auxiliaries are attributed to their owner (`cfOwnerName`), so a
    -- helper whose body Lean split into `foo.match_1` is still reachable under
    -- the stem `foo`.  Over-resolving is harmless by the same argument as
    -- ambiguity above: the walk is a union, so a wider seed set can only widen
    -- the reach, never hide a write.
    let owner := cfOwnerName (cfUserName n)
    if !owner.isInternalDetail then
      let c := cfLast owner
      if wanted.contains c then
        idx := idx.insert c ((idx.getD c #[]).push n)
  return idx

/-- The value of a constant, **unless it is a proof** -- the same distinction the
field-writer and taint-writer sweeps below already make, applied to the walk.

Those sweeps report only `.defnInfo` because "a theorem naming the API states a
property of it, and a property cannot move a field".  The reach that feeds them
was reading `value?` uniformly, which is the same claim taken in the other
direction: a proof term is `Prop`-valued and erased, so it executes nothing and
cannot be the step by which an arm reaches a write.  Including proofs could only
widen the reach with constants no arm actually runs -- and they are the majority
of the environment. -/
private def cfExecutableValue (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .thmInfo _ => none
  | _ => ci.value?

/-- Is this a constant whose body belongs to something a human wrote?

Decided on the **owner**, so a generated auxiliary is inspected on behalf of its
definition instead of being dropped, and a constant with no human-written owner
(the matcher of a matcher, a purely internal detail) is still skipped. -/
private def cfInspectable (n : Name) : Bool :=
  !(cfOwnerName (cfUserName n)).isInternalDetail

/-- How a writer is reported: the readable name, with private ones marked.

The mark is not cosmetic.  Reporting a private constant under its bare user name
would let `_private.Rogue.0.SeLe4n.Kernel.applySyscallTaint` match the declared
writer list and pass — a private definition impersonating the one writer is
precisely the finding this sweep must not miss. -/
private def cfReportName (n : Name) : String :=
  let owner := cfOwnerName (cfUserName n)
  if isPrivateName n then s!"private@{owner}" else toString owner

private def cfUsed (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | none => #[]
  | some ci =>
    match cfExecutableValue ci with
    | some v => v.getUsedConstants
    | none => #[]

/-- Bounded transitive closure over the elaborated call graph.

**The frontier is deduplicated as it is built.**  It was not: the membership
test ran against the level's *starting* `seen`, so a constant used by fifty
members of one level passed the filter fifty times, entered the next frontier
fifty times, and was re-expanded fifty times -- and that multiplies again at
every level.  At depth 6 over a kernel-sized graph it was this gate's entire
runtime: 1.1-4.1 s per arm across 34 arms, for reaches of only 1 200-2 500
constants.

The resulting set is unchanged.  A name enters `seen` at the first level that
reaches it either way, so both forms compute "reachable within `depth` hops";
only the number of times each name is expanded differs. -/
private partial def cfClosureGo (env : Environment) (frontier : Array Name) (d : Nat)
    (seen : NameSet) : NameSet × Bool := Id.run do
  match d with
  | 0 => return (seen, !frontier.isEmpty)
  | d + 1 =>
    let mut seen := seen
    let mut fresh : Array Name := #[]
    for m in frontier do
      for u in cfUsed env m do
        if !seen.contains u then
          seen := seen.insert u
          fresh := fresh.push u
    if fresh.isEmpty then return (seen, false)
    return cfClosureGo env fresh d seen

private def cfClosure (env : Environment) (seeds : List Name) (depth : Nat) :
    NameSet × Bool :=
  cfClosureGo env seeds.toArray depth (seeds.foldl (fun s n => s.insert n) ({} : NameSet))

/-- **A direct write of one structure field**: the constructor applied with the
watched field's argument not being that field of an incoming value.

PR #873 round 12: this used to require, additionally, that some *other* argument
be a projection of the same structure -- the thing that distinguishes
`{ st with .. }` from a fresh literal.  That is a test on the **spelling**, and a
helper that pattern-matches the structure into its fields and rebuilds it with
`mk` passes bound variables for the unchanged fields, not projections.  Its
rewrite of the watched field was therefore read as a fresh literal and the
one-writer gate saw nothing.  A detector for a laundering channel cannot be
satisfied by choosing a different way to write the same term, so the spelling test
is gone: every `mk` whose watched argument is not the corresponding projection is
a write, whatever the rest of the application looks like.

What that would otherwise sweep in -- genuine constructions, which write the field
because they write *every* field -- is excluded before the walk by
`cfRewritesState`, from a named list rather than from another reading of the body.

Open or closed: a closed non-projection argument is a silent *clear*, which for a
provenance table is a laundering enabler and must be as visible as a rewrite. -/
private def cfWritesFieldHit (structName field : Name) (idx : Nat) (e : Expr) : Bool :=
  match e.getAppFn with
  | .const n _ =>
      if n == structName ++ `mk then
        match e.getAppArgs[idx]? with
        | none => false
        | some a => !cfIsProjection structName field idx a
      else false
  | _ => false

private def cfWritesField (structName field : Name) (idx : Nat) (e : Expr) : Bool :=
  (cfAnySubterm (cfWritesFieldHit structName field idx) e {}).1

/-- Is `n` the structure's own generated machinery rather than something a human
wrote?  `casesOn`/`recOn`/`brecOn` (`isAuxRecursor`), `noConfusion`
(`isNoConfusion`) and the constructor itself all name `mk` by construction and
write nothing.

Decided on the **owner**, like `cfInspectable`: the constructor carries generated
auxiliaries of its own (`SystemState.mk._flat_ctor` is a `defn`, not a `ctor`, so
the sweep's `.defnInfo` filter does not skip it), and each is machinery for the
same reason its owner is. -/
private def cfStructureMachinery (env : Environment) (structName n : Name) : Bool :=
  let owner := cfOwnerName (cfUserName n)
  isAuxRecursor env owner || isNoConfusion env owner || owner == structName ++ `mk

/-- Definitions that **construct** a `SystemState` rather than rewrite one.

Dropping the spelling test means a constructor application counts as a write of
every field, which is right for a rewrite and wrong for a construction: something
has to build the first state, and it necessarily supplies the watched field.  The
tree has exactly one such definition, so it is named rather than inferred — the
`FAIL_CLOSED_ARMS` shape, and for the same reason.  A structural test was tried
first and is the wrong tool: "takes a `SystemState` argument" reads false for
every monadic definition, whose state argument lives inside `Kernel α`.

The list carries bite in `--self-test`: an entry that stops being reported is a
construction that became something else, or a name that no longer exists, and
either way the exemption must not stay. -/
private def cfStateConstructors : List Name := [@STATECTORS@]

/-- **Can this constant rewrite an existing `structName`'s field?** -/
private def cfRewritesState (env : Environment) (structName n : Name) : Bool :=
  !cfStructureMachinery env structName n && !cfStateConstructors.contains n

run_cmd do
  let env <- getEnv

  let idxs := cfChannelIdx env
  if idxs.length != cfChannels.length then
    logInfo m!"CF_CHANNEL_UNRESOLVED {cfChannels.length - idxs.length}"
  -- (C2) every definition that writes `SystemState.declassificationTaint`
  -- DIRECTLY, in a structure update — the write no API-naming check can see.
  let stateName := `SeLe4n.Model.SystemState
  let stateFields := (getStructureFields env stateName).toList
  match stateFields.findIdx? (· == `declassificationTaint) with
  | none => logInfo m!"CF_FIELD_UNRESOLVED declassificationTaint"
  | some fieldIdx =>
    let fieldWriters : List Name :=
      env.constants.fold (init := []) fun acc n ci =>
        if !cfInspectable n || !cfRewritesState env stateName n then acc
        else match ci with
          | .defnInfo di =>
              -- Prefilter on the constructor's presence: an Expr that never
              -- names `SystemState.mk` cannot apply it, and the used-constant
              -- set is cached where a structural walk is not.
              if di.value.getUsedConstants.contains (stateName ++ `mk)
                  && cfWritesField stateName `declassificationTaint fieldIdx di.value
              then n :: acc
              else acc
          | _ => acc
    for w in fieldWriters do
      logInfo m!"CF_FIELD_WRITER {cfReportName w}"
    -- The exempted constructions, reported so a stale entry is visible: a name
    -- that no longer writes the field (or no longer exists) must leave the list.
    for c in cfStateConstructors do
      match env.find? c with
      | some (.defnInfo di) =>
          if cfWritesField stateName `declassificationTaint fieldIdx di.value then
            logInfo m!"CF_STATE_CTOR {c}"
      | _ => pure ()
  -- (C) every constant whose value names the taint-writing API.
  -- Only **definitions** are reported: a theorem naming the API states a
  -- property of it, and a property cannot move a field.  `ConstantInfo.defnInfo`
  -- is exactly that distinction, decided by the elaborator rather than by a
  -- name pattern.
  let writers : List Name :=
    env.constants.fold (init := []) fun acc n ci =>
      if !cfInspectable n then acc
      else match ci with
        | .defnInfo di =>
            if cfTaintApi.any (fun a => di.value.getUsedConstants.contains a) then n :: acc
            else acc
        | _ => acc
  for w in writers do
    logInfo m!"CF_TAINT_WRITER {cfReportName w}"
  -- (C3) WS-SM SM9.D.13a: **who can append to the audit trail.**
  --
  -- `applySyscallTaint` skips the origination diff for every arm
  -- `syscallRecordsDeclassification` calls non-recording, which is what keeps two
  -- O(n) trail walks off the IPC path.  That skip is only sound if those arms
  -- really cannot append -- and "really cannot" is a reachability fact about the
  -- elaborated call graph, not something a hand-written `match` can be trusted to
  -- remember.  So the same field-write detector runs against
  -- `declassificationAuditLog`, and the reach below reports which arms hit one.
  let auditIdx? := stateFields.findIdx? (· == `declassificationAuditLog)
  if auditIdx?.isNone then
    logInfo m!"CF_FIELD_UNRESOLVED declassificationAuditLog"
  let auditWriters : NameSet :=
    match auditIdx? with
    | none => {}
    | some auditIdx =>
      env.constants.fold (init := ({} : NameSet)) fun acc n ci =>
        if !cfInspectable n || !cfRewritesState env stateName n then acc
        else match ci with
          | .defnInfo di =>
              if di.value.getUsedConstants.contains (stateName ++ `mk)
                  && cfWritesField stateName `declassificationAuditLog auditIdx di.value
              then acc.insert n
              else acc
          | _ => acc
  for w in auditWriters.toList do
    logInfo m!"CF_AUDIT_WRITER {cfReportName w}"
  -- The theorems the append exemptions below rest on.  An exemption whose
  -- justification has been deleted must stop being an exemption.
  for j in cfJustifications do
    if (env.find? j).isSome then
      logInfo m!"CF_JUSTIFIED {j}"
  -- Shared across arms.  "Does this constant write a content channel?" depends
  -- on the constant and the channel set, neither of which varies per arm, and
  -- the 34 arms' reaches overlap almost entirely -- they are all rooted in the
  -- same kernel core.  Asking it per arm re-walked the same ~2 000 bodies up to
  -- 34 times, which was this gate's runtime.
  let mut writesMemo : Std.HashMap Name Bool := {}
  -- Every stem every arm names, resolved in one pass over the environment.
  let wantedStems : Std.HashSet String :=
    Std.HashSet.emptyWithCapacity.insertMany
      (cfRoots.flatMap fun (_, stems) => (stems.splitOn " ").filter (fun s => s != ""))
  let stemIdx := cfStemIndex env wantedStems
  -- roots: resolve each arm's named callees, then walk.
  for (arm, stems) in cfRoots do
    let stemList := (stems.splitOn " ").filter (fun s => s != "")
    let seeds : List Name := stemList.flatMap fun s => (stemIdx.getD s #[]).toList
    if seeds.isEmpty then
      logInfo m!"CF_NO_ROOT {arm}"
    else
      let (reach, truncated) := cfClosure env seeds cfDepth
      if truncated then
        logInfo m!"CF_TRUNCATED {arm}"
      let mut hits : List Name := []
      for n in reach.toList do
        let w ←
          match writesMemo.get? n with
          | some b => pure b
          | none =>
            let b :=
              match env.find? n with
              | none => false
              | some ci =>
                match cfExecutableValue ci with
                | none => false
                | some v => cfWritesChannel idxs v
            writesMemo := writesMemo.insert n b
            pure b
        if w then hits := n :: hits
      logInfo m!"CF_ARM {arm} {hits.length}"
      for h in hits.take 6 do
        logInfo m!"CF_HIT {arm} {h}"
      -- (C3) the same reach, asked about the trail instead of the channels.
      let auditHits := reach.toList.filter (fun n => auditWriters.contains n)
      logInfo m!"CF_AUDIT_ARM {arm} {auditHits.length}"
      for h in auditHits.take 4 do
        logInfo m!"CF_AUDIT_HIT {arm} {cfReportName h}"
"""


def return_shapes() -> dict[str, str]:
    """`syscallReturnShape`'s own arms — the WS-RA total map from syscall to
    the shape of the value it hands back."""
    src = code_view(SHAPE)
    m = re.search(r"^def syscallReturnShape", src, re.M)
    if m is None:
        raise RuntimeError("`syscallReturnShape` not found in SyscallReturn.lean")
    body = src[m.end():]
    nxt = re.search(r"\n(?:private )?(?:def|theorem|abbrev|instance)\s", body)
    if nxt is not None:
        body = body[: nxt.start()]
    out = {}
    for arm, shape in re.findall(r"\|\s*\.([A-Za-z][A-Za-z0-9']*)\s*=>\s*\.([A-Za-z]+)", body):
        out[arm] = shape
    if not out:
        raise RuntimeError("`syscallReturnShape` parsed to no arms")
    return out


def code_view(path: str) -> str:
    return lean_code_view.strip(open(path, encoding="utf-8").read())


def arm_key(dispatcher: str, arm: str) -> str:
    """The reachability key: one syscall arm **in one dispatcher**."""
    return f"{dispatcher}::{arm}"


def arm_of(key: str) -> str:
    """The syscall name inside a reachability key."""
    return key.split("::", 1)[1] if "::" in key else key


def dispatcher_of(key: str) -> str:
    """The dispatcher inside a reachability key."""
    return key.split("::", 1)[0] if "::" in key else ""


def split_dispatch_arms(body: str) -> list[tuple[str, str]]:
    """Every `| .<name> =>` arm of a dispatcher body, one entry per constructor.

    A single arm may name several: `| .auditRead | .auditDrain => …`.  Both run
    the same body, so both get an entry over that body.

    PR #873 round 17: the splitter recognised only a constructor *immediately*
    followed by `=>`, so a grouped arm produced no entry for either constructor
    — and its text stayed inside the preceding arm, attributing code to an arm
    that does not run it.  The unchecked dispatcher groups its two audit arms, so
    neither `dispatchWithCap::auditRead` nor `::auditDrain` existed; the
    missing-arm check was satisfied by the *checked* dispatcher's separate
    implementations, and the gate never verified that the unchecked pair stays
    fail-closed.

    `recording_classification` already expanded groups.  Two parsers over the
    same syntax, one of them right, is how this survived — so the splitting is a
    named function with its own witness (`--self-test`) rather than a regex
    inlined at one of its two call sites.
    """
    parts = re.split(
        r"\n\s*\|\s*((?:\.[A-Za-z][A-Za-z0-9']*\s*\|\s*)*"
        r"\.[A-Za-z][A-Za-z0-9']*)\s*=>",
        body)
    out: list[tuple[str, str]] = []
    for i in range(1, len(parts) - 1, 2):
        arms, text = parts[i], parts[i + 1]
        for arm in re.findall(r"\.([A-Za-z][A-Za-z0-9']*)", arms):
            out.append((arm, text))
    return out


def arm_roots() -> dict[str, set[str]]:
    """Root stems per `(dispatcher, arm)`, read off the dispatch arms' own text.

    PR #873 round 10: keyed on the **pair**, not on the syscall alone.  Merging
    `dispatchCapabilityOnly`, `dispatchWithCap` and `dispatchWithCapChecked`
    under one name let a healthy implementation mask a broken sibling: if the
    checked `.receive` arm stopped reaching its `pendingMessage` write while the
    unchecked one still did, the union kept a content hit and check (B) reported
    success — for the route production actually takes.  Every live
    implementation of a content-moving syscall must satisfy the classification on
    its own.
    """
    src = code_view(API)
    roots: dict[str, set[str]] = {}
    for dispatcher in DISPATCHERS:
        m = re.search(rf"^(?:private )?def {dispatcher}\b", src, re.M)
        if m is None:
            raise RuntimeError(f"dispatcher `{dispatcher}` not found in API.lean")
        body = src[m.start():]
        nxt = re.search(r"\n(?:private )?(?:def|theorem|abbrev|instance)\s", body[1:])
        if nxt is not None:
            body = body[: nxt.start() + 1]
        for arm, text in split_dispatch_arms(body):
            ids = set(re.findall(r"\b([a-z][A-Za-z0-9_']{3,})\b", text))
            roots.setdefault(arm_key(dispatcher, arm), set()).update(ids)
    if not roots:
        raise RuntimeError("no dispatch arms parsed from API.lean")
    return roots


def recording_classification() -> dict[str, bool]:
    """`syscallRecordsDeclassification`'s own arms, read off its source.

    Multi-constructor arms (`| .a | .b => false`) are expanded, since that is how
    the 31 non-recording syscalls are actually written.
    """
    src = code_view(TAINT)
    m = re.search(r"^def syscallRecordsDeclassification : SyscallId → Bool$", src, re.M)
    if m is None:
        raise RuntimeError(
            "`syscallRecordsDeclassification` not found in TaintPropagation.lean")
    body = src[m.end():]
    nxt = re.search(r"\n(?:private )?(?:def|theorem|abbrev|instance)\s", body)
    if nxt is not None:
        body = body[: nxt.start()]
    out: dict[str, bool] = {}
    for arms, verdict in re.findall(
            r"\|\s*((?:\.[A-Za-z][A-Za-z0-9']*\s*\|?\s*)+)=>\s*(true|false)", body):
        for arm in re.findall(r"\.([A-Za-z][A-Za-z0-9']*)", arms):
            out[arm] = (verdict == "true")
    if not out:
        raise RuntimeError("`syscallRecordsDeclassification` parsed to no arms")
    return out


def classification() -> dict[str, str]:
    """`contentFlowClass`'s own arms, read off its source."""
    src = code_view(TAINT)
    m = re.search(r"^def contentFlowClass : SyscallId → ContentFlowClass$", src, re.M)
    if m is None:
        raise RuntimeError("`contentFlowClass` not found in TaintPropagation.lean")
    body = src[m.end():]
    nxt = re.search(r"\n(?:private )?(?:def|theorem|abbrev|instance)\s", body)
    if nxt is not None:
        body = body[: nxt.start()]
    out = {}
    for arm, cls in re.findall(r"\|\s*\.([A-Za-z][A-Za-z0-9']*)\s*=>\s*\.([A-Za-z]+)", body):
        out[arm] = cls
    if not out:
        raise RuntimeError("`contentFlowClass` parsed to no arms")
    return out


def tracked_fields() -> list[tuple[str, str]]:
    """`contentTrackedFields`'s own entries, read off its source.

    The declared threat-model boundary on the Lean side.  `CONTENT_CHANNELS`
    below must name the same fields: the scope is a decision, and a decision
    stated in two places is a decision that drifts unless something compares
    them.  Excluding a channel here while the Lean side still claims it is
    tracked (or the reverse) is exactly the silent widening this gate exists to
    prevent, so a mismatch is a hard failure rather than a warning.
    """
    src = code_view(TAINT)
    m = re.search(r"^def contentTrackedFields : List \(String × String\) :=$", src, re.M)
    if m is None:
        raise RuntimeError("`contentTrackedFields` not found in TaintPropagation.lean")
    body = src[m.end():]
    nxt = re.search(r"\n(?:private )?(?:def|theorem|abbrev|instance)\s", body)
    if nxt is not None:
        body = body[: nxt.start()]
    return re.findall(r'\("([A-Za-z0-9_]+)",\s*"([A-Za-z0-9_]+)"\)', body)


def check_scope_matches_lean() -> list[str]:
    """Compare the probe's channels with the Lean-side declared scope."""
    lean = {(s, f) for s, f in tracked_fields()}
    # `CONTENT_CHANNELS` carries fully-qualified structure names; the Lean list
    # names the structure only, since it is the boundary statement rather than
    # the probe's lookup key.
    probe = {(s.rsplit(".", 1)[-1], f) for s, f in CONTENT_CHANNELS}
    problems = []
    for miss in sorted(lean - probe):
        problems.append(
            f"`contentTrackedFields` declares {miss[0]}.{miss[1]} tracked, but "
            f"CONTENT_CHANNELS does not scan it")
    for extra in sorted(probe - lean):
        problems.append(
            f"CONTENT_CHANNELS scans {extra[0]}.{extra[1]}, but "
            f"`contentTrackedFields` does not declare it tracked")
    return problems


def run_probe(roots: dict[str, set[str]], depth: int, channels,
              plant_rogue: bool = False) -> str:
    quoted_channels = ", ".join(f"(`{s}, `{f})" for s, f in channels)
    quoted_roots = ", ".join(
        '("{}", "{}")'.format(arm, " ".join(sorted(stems)))
        for arm, stems in sorted(roots.items()))
    quoted_api = ", ".join(f"`{n}" for n in sorted(DECLARED_TAINT_WRITERS))
    quoted_just = ", ".join(f"`{n}" for n in sorted(set(AUDIT_APPEND_EXEMPT.values())))
    quoted_ctors = ", ".join(f"`{n}" for n in sorted(STATE_CONSTRUCTORS))
    src = (PROBE
           .replace("@CHANNELS@", quoted_channels)
           .replace("@ROOTS@", quoted_roots)
           .replace("@TAINTAPI@", quoted_api)
           .replace("@JUSTIFICATIONS@", quoted_just)
           .replace("@STATECTORS@", quoted_ctors)
           .replace("@PLANTED@",
                    SELF_TEST_ROGUE_SRC + rebuild_plant_src() if plant_rogue else "")
           .replace("@DEPTH@", str(depth)))
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as fh:
        fh.write(src)
        path = fh.name
    try:
        proc = subprocess.run(["lake", "env", "lean", path],
                              cwd=REPO, capture_output=True, text=True)
    except FileNotFoundError:
        raise RuntimeError(
            "`lake` is not on PATH, so the content-flow probe cannot elaborate.\n"
            "      This gate detects against Lean's elaborated environment and must run\n"
            "      in a tier that has a built toolchain — it is wired into\n"
            "      test_tier1_build.sh, after the builds.  Tier 0 is deliberately\n"
            "      build-free and cannot host it.") from None
    finally:
        os.unlink(path)
    out = proc.stdout + proc.stderr
    if proc.returncode != 0:
        raise RuntimeError(f"the content-flow probe exited {proc.returncode}\n{out[-4000:]}")
    if re.search(r"^.*\.lean:\d+:\d+: error", out, re.M):
        raise RuntimeError(f"the content-flow probe did not elaborate\n{out[-4000:]}")
    return out


def parse(out: str):
    hits = {}
    for arm, n in re.findall(r"CF_ARM (\S+) (\d+)", out):
        hits[arm] = int(n)
    detail = {}
    for arm, name in re.findall(r"CF_HIT (\S+) (\S+)", out):
        detail.setdefault(arm, []).append(name)
    writers = set(re.findall(r"CF_TAINT_WRITER (\S+)", out))
    field_writers = set(re.findall(r"CF_FIELD_WRITER (\S+)", out))
    field_unresolved = bool(re.search(r"CF_FIELD_UNRESOLVED", out))
    noroot = set(re.findall(r"CF_NO_ROOT (\S+)", out))
    state_ctors = set(re.findall(r"CF_STATE_CTOR (\S+)", out))
    truncated = set(re.findall(r"CF_TRUNCATED (\S+)", out))
    justified = set(re.findall(r"CF_JUSTIFIED (\S+)", out))
    audit_hits = {arm: int(n) for arm, n in re.findall(r"CF_AUDIT_ARM (\S+) (\d+)", out)}
    audit_detail: dict[str, list[str]] = {}
    for arm, name in re.findall(r"CF_AUDIT_HIT (\S+) (\S+)", out):
        audit_detail.setdefault(arm, []).append(name)
    return (hits, detail, writers, field_writers, field_unresolved, noroot, truncated,
            audit_hits, audit_detail, justified, state_ctors)


def main() -> int:
    ap = argparse.ArgumentParser()
    # PR #873 round 10: the default is **fixed-point fuel**, not a horizon.  At
    # 6 hops every arm's walk stopped with an unexpanded frontier and the gate
    # said nothing about it, so an inert arm whose payload write sat behind a
    # seventh helper passed both coverage checks silently.  The reach converges
    # at ~25 hops (2 046..3 358 constants) in about 13 s and the classification
    # is unchanged there, so the walk now runs to a fixed point; this bound only
    # exists so a pathological graph fails loudly instead of hanging.
    ap.add_argument("--depth", type=int, default=200)
    ap.add_argument("--list", action="store_true")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()

    cls = classification()
    roots = arm_roots()
    # Only arms the classification knows about are in scope: an arm name parsed
    # out of the dispatch source that is not a `SyscallId` is a parse artefact,
    # not a syscall.
    roots = {k: v for k, v in roots.items() if arm_of(k) in cls}

    missing = sorted(set(cls) - {arm_of(k) for k in roots})

    # The declared scope must agree with what the probe scans, BEFORE any
    # finding is computed: a scope that has silently narrowed makes every
    # "no unclassified content movement" result below vacuous for the channel
    # it dropped.
    scope_problems = check_scope_matches_lean()
    if scope_problems:
        print("FAIL: the declared content scope and the probe's channels disagree.")
        for p in scope_problems:
            print(f"  {p}")
        print("      The scope is a threat-model boundary stated in two places")
        print("      (`contentTrackedFields` and CONTENT_CHANNELS); they must match.")
        return 1

    channels = list(CONTENT_CHANNELS)
    if args.self_test:
        channels = channels + [SELF_TEST_CHANNEL]
        # The root-resolution witness: a synthetic arm whose only named helper is
        # the planted PRIVATE definition.  If the stem index skips private
        # names this arm resolves to no seed at all, and the assertion below
        # fires — which is exactly what happened before PR #873 round 8.
        roots = dict(roots)
        roots[SELF_TEST_ROOT_ARM] = {SELF_TEST_ROOT_HELPER}
        cls = dict(cls)
        cls[SELF_TEST_ROOT_ARM] = "inert"

    out = run_probe(roots, args.depth, channels, plant_rogue=args.self_test)
    (hits, detail, writers, field_writers, field_unresolved, noroot, truncated,
     audit_hits, audit_detail, justified, state_ctors) = parse(out)

    failures: list[str] = []

    # PR #873 round 10: **the walk must reach a fixed point.**  `cfClosureGo`
    # used to return its `seen` set when the counter hit zero and say nothing
    # about the frontier it had not expanded, so every reachability verdict was
    # silently "within N hops" rather than "ever" — and an inert arm whose
    # payload or audit-log write moved behind one more helper would have passed
    # both coverage checks.  A truncated walk is now a hard failure, not a
    # quieter answer.
    if truncated:
        print("FAIL: the call-graph walk hit its fuel with an unexpanded frontier")
        print(f"      on arm(s): {', '.join(sorted(truncated))}.")
        print("      Every verdict from a truncated walk is 'no write within N")
        print("      hops', which is not what checks (A)-(C3) claim.  Raise")
        print("      --depth until the walk converges, or find out why the reach")
        print("      does not terminate.")
        return 1

    if args.list:
        for key in sorted(roots):
            print(f"  {key:<52} {cls[arm_of(key)]:<18} content-writes reached: "
                  f"{hits.get(key, 0)}  audit-writes reached: {audit_hits.get(key, 0)}")
        print(f"  taint writers: {len(writers)}")

    if args.self_test:
        # PR #873 round 17: the arm splitter recognised only a constructor
        # immediately followed by `=>`, so a grouped arm produced no entry for
        # either constructor and its text was attributed to the preceding arm.
        # Planted rather than asserted against the live tree, because the live
        # tree only exhibits the shape while some dispatcher happens to group its
        # arms — a witness that stops witnessing when the source is reformatted
        # is the kind of check this gate exists to replace.
        grouped_body = (
            "\n  | .alpha => alphaHelper st\n"
            "  | .auditRead | .auditDrain => auditHelper st\n"
            "  | .omega => omegaHelper st\n")
        split = dict(split_dispatch_arms(grouped_body))
        if "auditRead" not in split or "auditDrain" not in split:
            print("FAIL: --self-test — the arm splitter dropped a grouped arm")
            print("      (`| .auditRead | .auditDrain =>`).  Neither constructor")
            print("      gets a reach key, so the missing-arm check is satisfied by")
            print("      whichever dispatcher spells them separately and the grouped")
            print("      pair is never verified fail-closed.")
            return 1
        if "auditHelper" not in split.get("auditRead", ""):
            print("FAIL: --self-test — a grouped arm's entries do not carry the")
            print("      arm's own body, so each alternative would be classified")
            print("      against code it does not run.")
            return 1
        if "auditHelper" in split.get("alpha", ""):
            print("FAIL: --self-test — a grouped arm's text leaked into the")
            print("      PRECEDING arm, attributing a reach to code that arm never")
            print("      executes.  That is how the old splitter failed: it did not")
            print("      terminate the previous arm at an unrecognised `|`.")
            return 1
        planted = [k for k in roots if cls[arm_of(k)] == "inert" and hits.get(k, 0) > 0]
        if not planted:
            print("FAIL: --self-test planted `TCB.priority` as a content channel and the")
            print("      gate flagged no inert arm.  The write detector has stopped")
            print("      detecting: every production finding below would be a false PASS.")
            return 1
        # PR #873 round 10: the dispatchers must stay SEPARATE keys.  Merging
        # them let a healthy implementation mask a broken sibling — a checked
        # `.receive` that lost its `pendingMessage` write still passed on the
        # unchecked arm's hit.  A collapse back to one key per syscall would be
        # invisible in the verdict, so it is asserted here: `.receive` is
        # implemented in two dispatchers and both must reach a content write.
        recv_keys = [k for k in roots if arm_of(k) == "receive"]
        if len(recv_keys) < 2:
            print("FAIL: --self-test — `.receive` resolved to fewer than two")
            print(f"      dispatcher implementations ({recv_keys}).  The reach key")
            print("      has collapsed back to the syscall name, so one dispatcher's")
            print("      healthy arm can again mask a broken sibling.")
            return 1
        blind_recv = [k for k in recv_keys if hits.get(k, 0) == 0]
        if blind_recv:
            print("FAIL: --self-test — `.receive` reaches no content write in")
            print(f"      {', '.join(blind_recv)}.  Every live implementation of a")
            print("      content-moving syscall must satisfy the classification on")
            print("      its own; this one does not.")
            return 1

        # Root resolution must reach a PRIVATE helper an arm names.  The two
        # plants above would both be found by a sweep over the whole
        # environment; this one is found only if the arm's stem resolved to the
        # private constant, so it pins the half of the defect the sweeps cannot.
        if SELF_TEST_ROOT_ARM in noroot or hits.get(SELF_TEST_ROOT_ARM, 0) == 0:
            print("FAIL: --self-test — the synthetic arm naming the planted PRIVATE")
            print(f"      helper `{SELF_TEST_ROOT_HELPER}` resolved to no reachable")
            print("      content write.  Root resolution is skipping private")
            print("      definitions, so an arm that delegates its only payload write")
            print("      to a private helper can be classified `.inert` and pass.")
            return 1
        # The field-writer sweep must detect the one real writer: a sweep that
        # has gone blind reports zero unexpected writers for the same reason it
        # would miss a rogue one, so its bite is asserted here rather than
        # trusted.
        if "SeLe4n.Kernel.applySyscallTaint" not in field_writers:
            print("FAIL: --self-test — the direct-field-writer sweep did not detect")
            print("      `applySyscallTaint`, the one definition that writes")
            print("      `SystemState.declassificationTaint`.  The sweep is blind:")
            print("      a rogue writer would pass check (C2) for the same reason.")
            return 1
        # …and it must detect one that hides behind `private`.  Both sweeps
        # filtered on `isInternal`, which is true of every private constant, so
        # each opened only public bodies and a private rewrite of the field was
        # invisible to both.  A public plant cannot show this — it passes against
        # the blind filter too — so the plant is private and both sweeps are
        # asserted separately.
        rogue = f"private@{SELF_TEST_ROGUE}"
        if rogue not in field_writers:
            print("FAIL: --self-test — the direct-field-writer sweep did not detect")
            print(f"      the planted PRIVATE writer `{SELF_TEST_ROGUE}`, which")
            print("      rewrites `SystemState.declassificationTaint` outright.")
            print("      The sweep is skipping private definitions, so a private")
            print("      helper could launder provenance and still report one writer.")
            return 1
        # …and the destructuring shape, where the elaborator also puts the
        # constructor application inside the generated matcher.
        rogue_match = f"private@{SELF_TEST_ROGUE_MATCH}"
        if rogue_match not in field_writers:
            print("FAIL: --self-test — the direct-field-writer sweep did not detect")
            print(f"      the planted PRIVATE writer `{SELF_TEST_ROGUE_MATCH}`, which")
            print("      pattern-matches the `SystemState` before rebuilding it with a")
            print("      replacement taint table.  A helper can hide a write behind a")
            print("      `match` if the sweep only reads unmatched bodies.")
            return 1
        # …and the positional rebuild, where no projection appears at all.  The
        # matcher plant above still writes `{ st with .. }` in its body, so it
        # passed the old spelling test too; this one is the shape that did not,
        # and it is the witness that the detector no longer depends on spelling.
        rogue_rebuild = f"private@{SELF_TEST_ROGUE_REBUILD}"
        if rogue_rebuild not in field_writers:
            print("FAIL: --self-test — the direct-field-writer sweep did not detect")
            print(f"      the planted PRIVATE writer `{SELF_TEST_ROGUE_REBUILD}`, which")
            print("      destructures the `SystemState` and rebuilds it positionally")
            print("      through `SystemState.mk`.  Its unchanged fields are bound")
            print("      variables rather than projections, so a detector that infers")
            print("      'this is an update' from a projection being present reads the")
            print("      rewrite as a fresh literal — and a second direct writer passes")
            print("      check (C2) by being spelled this way.")
            return 1
        # …and every named construction must still be one.  The exemption exists
        # because a constructor application counts as a write of every field, so
        # an entry that stops being reported is a name that no longer builds a
        # state — a stale exemption that would hide the next writer spelled that
        # way.
        stale = [c for c in STATE_CONSTRUCTORS if c not in state_ctors]
        if stale:
            print("FAIL: --self-test — STATE_CONSTRUCTORS names definitions that no")
            print(f"      longer write `declassificationTaint`: {', '.join(stale)}.")
            print("      An exemption that has stopped applying must be deleted, not")
            print("      carried: it exempts nothing and hides whatever takes the name.")
            return 1
        if rogue not in writers:
            print("FAIL: --self-test — the API-naming sweep did not detect the")
            print(f"      planted PRIVATE consumer `{SELF_TEST_ROGUE}`, which calls")
            print("      the declared taint-writing API.  A private caller of the")
            print("      API is invisible to check (C) for the same reason.")
            return 1
        # (C3) must have bite.  Its verdict is "no arm records while claiming
        # not to", and a sweep that found no audit writers at all would return
        # that verdict for every arm without having looked — the same vacuous
        # pass the planted channel above exists to rule out.  The two arms that
        # provably do append are the witnesses.
        blind = [a for a in ("declassify", "declassifySignal")
                 if all(audit_hits.get(k, 0) == 0
                        for k in roots if arm_of(k) == a)]
        if blind:
            print("FAIL: --self-test — the audit-trail reach found no writer under")
            print(f"      {', '.join('`.' + a + '`' for a in blind)}, which append on")
            print("      every authorized hop.  Check (C3) has lost its reach, so it")
            print("      would clear an arm that records while declared silent — and")
            print("      `applySyscallTaint` skips the origination diff on that word.")
            return 1
        print(f"PASS: --self-test — the planted channel was detected on "
              f"{len(planted)} inert arm(s); both sweeps detected the declared "
              f"writer, the planted private rogue writer, the one that hides its "
              f"rebuild behind a `match` and the one that rebuilds positionally "
              f"with no projection anywhere; root resolution reached a PRIVATE "
              f"arm helper; `.receive` was checked in each of its dispatchers "
              f"separately; the audit-trail reach found the two recording arms.")
        return 0

    # (A) no unclassified content movement
    for key in sorted(roots):
        arm = arm_of(key)
        if cls[arm] in ("inert", "clearsProvenance") and hits.get(key, 0) > 0:
            failures.append(
                f"  `.{arm}` (in `{dispatcher_of(key)}`) is classified "
                f"`.{cls[arm]}` but reaches "
                f"{hits[arm]} content write(s): {', '.join(detail.get(arm, [])[:4])}")

    # (C3) WS-SM SM9.D.13a: the recording classification must match the reach.
    #
    # `applySyscallTaint` skips the origination diff — two O(n) walks of the audit
    # trail — for every arm `syscallRecordsDeclassification` calls non-recording.
    # That skip is what keeps the trail off the IPC hot path, and it is sound only
    # while those arms genuinely cannot append.  An arm that reaches a writer of
    # `declassificationAuditLog` while classified `false` would record a downgrade
    # and originate nothing from it: a MISSED chain, which is the direction this
    # module must never err in, and it would be silent.
    #
    # So the classification is checked against the call graph rather than trusted.
    # Both directions fail: under-declaring is the unsound one, over-declaring
    # means an arm pays the trail walk for a diff it can never fill, and a set
    # that has drifted either way is a set nobody is reading.
    records = recording_classification()
    for arm, thm in sorted(AUDIT_APPEND_EXEMPT.items()):
        if thm not in justified:
            failures.append(
                f"  `.{arm}` is exempted from the audit-append check by `{thm}`, "
                f"which is not in the elaborated environment — the exemption has "
                f"outlived its justification")
    for key in sorted(roots):
        arm = arm_of(key)
        declared = records.get(arm)
        if declared is None:
            failures.append(
                f"  `.{arm}` has no `syscallRecordsDeclassification` arm, so "
                f"whether its commit can append to the audit trail is undeclared")
            continue
        # An arm that writes the trail without being able to append to it is
        # exempt — but only while the theorem saying so is still there.
        reached = (audit_hits.get(key, 0) > 0
                   and arm not in AUDIT_APPEND_EXEMPT)
        if reached and not declared:
            failures.append(
                f"  `.{arm}` reaches {audit_hits[arm]} audit-trail write(s) "
                f"({', '.join(audit_detail.get(arm, [])[:3])}) but "
                f"`syscallRecordsDeclassification` says it cannot record — "
                f"`applySyscallTaint` would skip the origination diff and lose "
                f"every causal chain through this arm")
        elif declared and not reached and (dispatcher_of(key), arm) not in FAIL_CLOSED_ARMS:
            failures.append(
                f"  `.{arm}` (in `{dispatcher_of(key)}`) is declared as "
                f"recording a declassification but "
                f"reaches no writer of `declassificationAuditLog`, so it pays the "
                f"trail diff on every call for events it cannot produce")

    # …and the exemption's bite.  A refusal that reaches a write is not a
    # refusal, and without this the set above would be a way to switch checks off.
    for key in sorted(roots):
        arm = arm_of(key)
        if (dispatcher_of(key), arm) not in FAIL_CLOSED_ARMS:
            continue
        if hits.get(key, 0) > 0 or audit_hits.get(key, 0) > 0:
            failures.append(
                f"  `.{arm}` (in `{dispatcher_of(key)}`) is listed as failing "
                f"closed but reaches {hits.get(key, 0)} content write(s) and "
                f"{audit_hits.get(key, 0)} audit write(s) — the arm that is "
                f"supposed to refuse is doing something")

    # (B) no vacuous classification.  A content-moving arm must either write a
    # content channel or deliver through the WS-RA return frame.
    #
    # The excuse used to be derived from `syscallReturnShape` — any arm whose
    # shape was not `.unit` was taken to move content.  That reads the ABI, not
    # the implementation: the shape says a value comes back, never that the value
    # is still drawn from kernel state.  Delete the `pendingMessage` delivery from
    # `.receive` and its `.message` shape is untouched, so the arm would reach
    # zero content writes and still pass — which is exactly the lost-plumbing
    # regression (B) exists to catch.  A constant or empty return frame passes for
    # the same reason.
    #
    # So the excuse is now a named set, and membership is a claim about the
    # implementation.  An arm joins it only when the delivery is established:
    # `.notificationWait` clears the notification's `pendingBadge` — a closed
    # write — and the badge reaches the waiter in `x0`, so no *object* carries it.
    # Adding an arm without that evidence reopens the hole this closes.
    RETURN_FRAME_DELIVERY = {"notificationWait"}
    shapes = return_shapes()
    for key in sorted(roots):
        arm = arm_of(key)
        if (dispatcher_of(key), arm) in FAIL_CLOSED_ARMS:
            continue
        if cls[arm] == "movesContent" and hits.get(key, 0) == 0:
            if arm not in RETURN_FRAME_DELIVERY:
                shape = shapes.get(arm, "unit")
                failures.append(
                    f"  `.{arm}` is classified `.movesContent`, reaches no content write, "
                    f"and is not an established return-frame delivery (return shape "
                    f"`.{shape}`) — either the classification is wrong or the reach has "
                    f"been lost")

    # (C) one taint writer
    # A *theorem* naming the API states a property of it; only a **definition**
    # can move the field.  The check is therefore over constants with
    # computational content, minus the compiler's own equation and match
    # auxiliaries, which carry a definition's body rather than a new one.
    def is_auxiliary(name: str) -> bool:
        return any(seg in name for seg in
                   (".eq_", ".eq_def", "._eq", ".match_", ".proof_", ".induct",
                    ".fun_cases", ".brecOn", ".below", "._sunfold", "._unsafe_rec",
                    ".ind_", ".congr", ".sizeOf"))

    unexpected = sorted(w for w in writers
                        if w not in DECLARED_TAINT_WRITERS
                        and not is_auxiliary(w)
                        and w not in DECLARED_TAINT_CONSUMERS)
    if unexpected:
        failures.append(
            "  constants outside the declared propagation surface name the taint-writing "
            "API:\n      " + "\n      ".join(unexpected[:12]))

    # (C2) one field writer.  Check (C) sees only constants that NAME the taint
    # API; a definition writing `SystemState.declassificationTaint` directly in
    # a `{ st with .. }` update names nothing and would escape it — including a
    # closed-term write, which for a provenance table is a silent whole-table
    # clear, a laundering enabler.  The probe therefore scans every definition's
    # elaborated value for an update whose taint-field argument is not the
    # field's own projection.  Fresh literals (boot, defaults, test builders)
    # carry no same-structure projection and are exactly the constructions this
    # sweep must not flag.
    if field_unresolved:
        failures.append(
            "  the probe could not resolve `SystemState.declassificationTaint`'s field "
            "index — the direct-write sweep ran on nothing.  Fails closed.")
    unexpected_field = sorted(w for w in field_writers
                              if w not in DECLARED_FIELD_WRITERS
                              and not is_auxiliary(w))
    if unexpected_field:
        failures.append(
            "  constants write `SystemState.declassificationTaint` directly, outside "
            "the declared writer:\n      " + "\n      ".join(unexpected_field[:12]))

    if noroot:
        failures.append(
            "  no callee could be resolved for arm(s): " + ", ".join(sorted(noroot)) +
            "\n      The gate fails closed: an arm whose roots do not resolve is "
            "unchecked, not clean.")

    if missing:
        failures.append(
            "  classified syscalls with no dispatch arm parsed: " + ", ".join(missing) +
            "\n      Either the arm was renamed or the parser has lost its reach.")

    if failures:
        print("FAIL: content-flow coverage (WS-SM SM9.D.7)")
        for f in failures:
            print(f)
        return 1

    moving = len({arm_of(k) for k in roots if cls[arm_of(k)] == "movesContent"})
    by_write = len({arm_of(k) for k in roots
                    if cls[arm_of(k)] == "movesContent" and hits.get(k, 0) > 0})
    recording = len({arm_of(k) for k in roots if records.get(arm_of(k))})
    arms = {arm_of(k) for k in roots}
    print(f"PASS: content-flow coverage — {len(arms)} live arms classified across "
          f"{len(roots)} dispatcher implementation(s); "
          f"{moving} moving content ({by_write} reaching an object content write, "
          f"{moving - by_write} delivering through the return frame); "
          f"{len(arms) - moving} inert or clearing, none reaching a content write; "
          f"{recording} recording a declassification, and no other arm reaches an "
          f"audit-trail append.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
