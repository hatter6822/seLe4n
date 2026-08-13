#!/usr/bin/env python3
"""Fail if a live syscall arm can reach a boot-pinned scheduler primitive.

WS-SM SM8.B, PR #861 review rounds 10 and 12 found the same defect three times,
one syscall per round: a live dispatch arm whose *scheduling* effects target
`bootCoreId` unconditionally.  `.tcbResume` enqueued on the boot core,
`.send` woke a rendezvous receiver there and descheduled a blocking sender
there, and `.tcbSetPriority` / `.tcbSetMCPriority` re-bucketed and preempted
there.  Each was fixed on discovery; none was found by a gate.

A grep over the dispatch arms would have caught none of them.  Every one was
**one level down**: the arm named `setPriorityOp`, and `setPriorityOp` called
`migrateRunQueueBucket`.  So the property to check is transitive — the
operation an arm reaches, and everything *it* reaches, must not hardcode the
boot core in a scheduler effect.

This script checks that.  It starts from `syscallIdToEnforcementNamePerCore`
(the total `SyscallId → String` map recording which operation each syscall
actually reaches under SMP), walks the call graph of Lean definitions to a
bounded depth, and fails on any boot-pinned primitive reached along the way.
Exceptions live in `scripts/per_core_routing_allowlist.json`, one entry per
(syscall, symbol) with a written reason, so a deliberate boot-pinning is a
counted, justified fact rather than an oversight waiting for a reviewer.

**Reach, stated honestly.**  The call graph is extracted from source text, so a
followed name is any identifier token appearing in a definition's body.  That is
sound at short range and useless at long range: by three hops the closure is
near-total and reports definitions the arm cannot reach.  The gate therefore
walks **two hops** from the named operation — arm -> operation -> helper — which
is where every defect found so far lived (`setPriorityOp` -> `migrateRunQueueBucket`
was the deepest).  `--self-test` is the check that this reach is not vacuous: it
re-runs the walk over the *canonical* pre-SMP map, which still names the
boot-pinned operations, and fails if the gate does not flag them.

Detection runs against **Lean's elaborated environment**, not the source text
(PR #861 review round 29).  Rounds 15, 23, 24, 26, 27 and 29 were six findings
against this gate and none against the kernel it checks -- truncated bodies,
reads-but-not-writes, single-line-only, dot-notation-only,
identifier-receivers-only, a character budget -- each one a regex under-reaching
some spelling while the gate reported PASS, and each fix local to the spelling
reported.  A term has no spelling: `sched.currentOnCore bootCoreId`,
`currentOnCore st.scheduler bootCoreId`, `currentOnCore (prepare st).scheduler
bootCoreId` and the same call wrapped over four lines are one `Expr`.  So the
question is now "is this application's argument the `bootCoreId` constant",
which no formatting can hide, and `determineExecutingCore`'s `find?…getD`
fallback is excluded structurally rather than by tuning.

Source text is still read for *root resolution* -- which definition a mapped
enforcement label names, and whether the dispatch arm calls it.  That is a
question about the data tables and the dispatch source, which text answers
correctly -- and, from round 44, the text read is the **code view**
(`lean_code_view.strip` at every read), so a trailing comment cannot satisfy
root verification, a block-comment code sample cannot inject a dispatch arm
or override a mapping arm, and docstring prose cannot register a cross-core
inventory entry.

Usage:  scripts/check_live_arm_per_core_routing.py [--depth N] [--list] [--self-test]
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import tempfile

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SRC = os.path.join(REPO, "SeLe4n")
MAPFILE = os.path.join(SRC, "Kernel", "InformationFlow", "CovertChannelPerCore.lean")
API = os.path.join(SRC, "Kernel", "API.lean")
NIFILE = os.path.join(SRC, "Kernel", "InformationFlow", "NonInterferenceCrossCore.lean")
CANON = os.path.join(SRC, "Kernel", "InformationFlow", "Enforcement", "Wrappers.lean")
ALLOWLIST = os.path.join(REPO, "scripts", "per_core_routing_allowlist.json")
ALIASES = os.path.join(REPO, "scripts", "per_core_routing_aliases.json")

sys.path.insert(0, os.path.join(REPO, "scripts"))
import lean_code_view  # noqa: E402  (needs the path insert above)


def read_code(path: str) -> str:
    """Read a Lean source through the code view: comments blanked in place.

    PR #861 review round 44: the gate's raw reads were the last comment-blind
    scans on this surface.  `strip_comments` dropped whole `--` lines but kept
    *trailing* comments, so `replacement st  -- oldMappedRoot` fed
    `oldMappedRoot` to `called_names` and a retired root surviving only in
    prose verified as called — the fail-open class this gate exists to close,
    reproduced inside it.  The same raw reads let a block-comment code sample
    inject a phantom dispatch arm (`dispatch_arm_bodies`), *override* a
    mapping arm (`parse_map`, where the later regex match wins the dict
    write), or register a phantom cross-core inventory entry
    (`parse_live_arm_syscalls`, whose `=> some .<syscall>` pattern matched
    docstring prose and thereby suppressed a missing-inventory finding).
    Stripping at the read closes all four at the helper, the way `test_lib.sh`
    routes `run_check` — and the way the `SchedulerState` field parse already
    did (round 43).  `lean_code_view.strip` preserves length, line count and
    column offsets, so every line-arithmetic consumer is unaffected.
    """
    return lean_code_view.strip(open(path, encoding="utf-8").read())


# Scheduler effects that name the boot core rather than a supplied `CoreId`.
# Each is the *single-core* member of a per-core pair; its sibling takes a core.
BOOT_PINNED = {
    "ensureRunnable":            "enqueues on bootCoreId; per-core form is enqueueRunnableOnCore",
    "removeRunnable":            "clears bootCoreId's slots; per-core form is removeRunnableOnCore",
    "resumeThread":              "boot-core resume; per-core form is resumeThreadOnCore",
    "suspendThread":             "boot-core suspend; per-core form is suspendThreadOnCore",
    "migrateRunQueueBucket":     "re-buckets runQueueOnCore bootCoreId; per-core form is migrateRunQueueBucketOnCore",
    "propagatePriorityInheritance": "boot-core chain walk; per-core form is propagatePipChainCrossCore",
    "updatePipBoost":            "boot-core re-bucket; per-core form is updatePipBoostOnCore",
    # NOTE (round 29): `handleRescheduleSgi` used to sit here.  The
    # elaborated-environment engine fails closed on a watched name it cannot
    # resolve, and that is how we learned there is no such constant — only
    # `handleRescheduleSgiOnCore`.  The regex engine had been "checking" for a
    # symbol that does not exist, matching nothing, for as long as the entry
    # existed.  A hand-written list of names nothing verifies is exactly the
    # class of defect this rewrite removes, so the entry is gone rather than
    # renamed: the per-core form is a *primitive*, watched for a literal
    # `bootCoreId` argument, not a boot-pinned form to be banned outright.
}
# A raw read of the boot core's scheduler slots inside a live operation.
#
# PR #861 review round 17: `replenishQueueOnCore` joined the list because it is
# the third per-core scheduler slot and the gate could not see it.  A
# replenishment is enqueued on the bound thread's home core (`replenishOnCore`)
# and drained by that core's tick, so a purge keyed on `bootCoreId` is a silent
# no-op for any SC bound to a thread homed elsewhere.  Three live sites had it —
# `schedContextConfigure` and both arms of `schedContextUnbind` — after
# round 13 had routed the *run-queue* half of the very same operations per-core.
# Two slots checked out of three is how that survived.
STATE = os.path.join(SRC, "Model", "State.lean")


def per_core_scheduler_fields() -> list[str]:
    """The `SchedulerState` fields that are per-core `Vector`s.

    PR #861 review round 25: the read and write inventories were hand-written,
    and a hand-written inventory is how three of the seven per-core slots came
    to be unchecked — `activeDomain`, `domainScheduleIndex`,
    `domainTimeRemaining` and `lastTimeoutErrors` were all absent, so a live
    helper selecting against `activeDomainOnCore bootCoreId` passed the gate
    and its self-test alike.  Deriving the list from the structure means a
    field added to `SchedulerState` is covered the day it lands, which is the
    same reason the axiom sweep enumerates the elaborated environment and this
    gate's roots come from the enforcement map.

    Fails closed: a parse that finds nothing raises rather than returning an
    empty inventory, which would silently disable every pattern below.

    Round 43 made the parse independent of two things a regex over raw text was
    silently sensitive to.  **Line wrapping**: the old pattern required the
    field name, `Vector` and `numCores` on one physical line, so a slot
    formatted across two lines would be absent from the inventory, its
    `fooOnCore`/`setFooOnCore` stems absent from `routePrims`, and a live
    helper could hardcode the boot core through it while the gate reported
    PASS.  Field declarations are accumulated to their next sibling instead, so
    wrapping is irrelevant.  **Comments**: the structure body is read through
    the code view, so a docstring inside it that mentions `Vector … numCores`
    cannot inject a field that does not exist.
    """
    src = read_code(STATE)
    m = re.search(r"^structure SchedulerState where$(.*?)^\S", src, re.M | re.S)
    if not m:
        raise SystemExit("[per-core-routing] cannot locate `structure SchedulerState`")

    # Accumulate each declaration up to the next one, so a field wrapped over
    # several lines is one unit.  A new field starts at the structure's own
    # indent with `name :`; anything more indented continues the current one.
    decls: list[tuple[str, list[str]]] = []
    for line in m.group(1).splitlines():
        head = re.match(r"^\s{2}([a-z][A-Za-z0-9_']*)\s*:", line)
        if head:
            decls.append((head.group(1), [line]))
        elif decls and line.strip():
            decls[-1][1].append(line)

    fields = [name for name, body in decls
              if re.search(r"\bVector\b", " ".join(body))
              and re.search(r"\bnumCores\b", " ".join(body))]
    if not fields:
        raise SystemExit("[per-core-routing] no per-core Vector fields parsed from "
                         "SchedulerState -- the gate would check nothing")
    return fields


PER_CORE_FIELDS = per_core_scheduler_fields()

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|partial\s+|noncomputable\s+)*"
                  r"(?:def|abbrev)\s+([A-Za-z_][A-Za-z0-9_.'?!]*)", re.M)
TOP = re.compile(r"^(?:@\[|/--|/-!|private\s|protected\s|partial\s|noncomputable\s|def\s|abbrev\s|"
                 r"theorem\s|lemma\s|instance\s|structure\s|inductive\s|end\s|namespace\s|section\s|"
                 r"open\s|import\s|example\s|macro\s|syntax\s|deriving\s)", re.M)


# ---------------------------------------------------------------------------
# The detection engine: Lean's elaborated environment, not the source text.
#
# PR #861 review rounds 15, 23, 24, 26, 27 and 29 were six findings against
# this gate and none against the kernel it checks: truncated bodies,
# reads-but-not-writes, single-line-only, dot-notation-only,
# identifier-receivers-only, and a character budget.  Every one was the same
# defect -- a regex under-reaching some spelling while the gate reported PASS
# -- and every fix was local to the spelling reported, which is why there was
# another one each round.
#
# A regex over source has a spelling dimension.  An elaborated `Expr` does not:
# `sched.currentOnCore bootCoreId`, `currentOnCore st.scheduler bootCoreId`,
# `currentOnCore (prepare st).scheduler bootCoreId` and the same call wrapped
# across four lines are the SAME TERM by the time Lean is done.  So the
# question moves from "does this text match" to "is this application's
# argument the `bootCoreId` constant", which no formatting can hide.
#
# It also gets last round's precision for free.  `determineExecutingCore`
# reads `currentOnCore c` for a *searched* core and uses `bootCoreId` as a
# `find?.getD` fallback; as a term the primitive's arguments simply are not
# `bootCoreId`, so no tuning is needed to exclude it.
# ---------------------------------------------------------------------------

PROBE_TEMPLATE = """-- Both roots: `SeLe4n` is the production library; `Platform.Staged` pulls the
-- staged modules in.  Without the second, a per-core primitive defined in a
-- staged module (`advanceDomainOnCore`, in
-- `Scheduler/Operations/PerCoreDomain.lean`) is not a constant in this
-- environment and the fail-closed stem resolution rejects the run — which is
-- how the split was noticed.  Watching the whole tree is the point.
import SeLe4n
import SeLe4n.Platform.Staged
import Lean.Elab.Command

open Lean Elab Command

/-- Total.  `Name.getString!` *panics* on a numeric or anonymous component,
and this environment has ~126 700 constants -- more than enough to contain
some.  The first draft of this probe used it and died with no output. -/
private def routeLastComponent (n : Name) : String :=
  match n with
  | .str _ s => s
  | _        => ""

private def routeRoots : List String :=
  [@ROOTS@]

private def routePrims : List String :=
  [@PRIMS@]

/-- The syscall dispatch entry points, used only to disambiguate colliding
short names.  All three are `private`, so they are found by stem, not by full
name. -/
private def routeDispatch : List String :=
  ["dispatchCapabilityOnly", "dispatchWithCap", "dispatchWithCapChecked"]

private def routePinned : List String :=
  [@PINNED@]

/-- Applications of a per-core primitive, paired with each of their **closed**
arguments.  Purely collected here; whether an argument *is* the boot core is
decided in `MetaM` below, because that question is definitional rather than
syntactic.

`bootCoreId` elaborates to `⟨0, numCores_pos⟩`, so a hand-written `(0 : CoreId)`
or `⟨0, h⟩` is the same value carrying a different proof term — a different
`Expr`, invisible to a `.const` test (PR #861 review round 33).  Loose bvars are
excluded: an open term cannot be compared soundly. -/
private partial def routeBootHits (boot : Std.HashSet Name) (e : Expr) :
    Array (Name × Expr) := Id.run do
  let mut hits : Array (Name × Expr) := #[]
  -- Beta-reduce the head for the same reason: `(fun c => removeRunnableOnCore
  -- st tid c) bootCoreId` is an application of a lambda, not of the primitive.
  let e := e.headBeta
  -- No head filter (PR #861 review round 37).  This used to admit only heads on
  -- a hand-written primitive list, which omitted every *composite* per-core
  -- scheduler operation -- `scheduleEffectiveOnCore`, `scheduleOrIdleOnCore`,
  -- `saveOutgoingContextOnCore` -- so `scheduleEffectiveOnCore st bootCoreId`
  -- produced no finding despite mutating the boot core's scheduler state.
  -- Every head is collected here and the *decision* moved downstream, where a
  -- head is reported iff it transitively reaches a scheduler-slot setter.  That
  -- test is derived from `SchedulerState`'s own fields, so a composite added
  -- tomorrow is covered the day it lands.
  if let .const p _ := e.getAppFn then
    for a in e.getAppArgs do
      let a := a.consumeMData
      if let .const c _ := a then
        if boot.contains c then hits := hits.push (p, a)
      else if !a.hasLooseBVars then
        hits := hits.push (p, a)
  match e with
  | .app f a         => return hits ++ routeBootHits boot f
                                 ++ routeBootHits boot a
  | .lam _ t b _     => return hits ++ routeBootHits boot t
                                 ++ routeBootHits boot b
  | .forallE _ t b _ => return hits ++ routeBootHits boot t
                                 ++ routeBootHits boot b
  -- Zeta-reduce.  `let c := bootCoreId; removeRunnableOnCore st tid c` passes a
  -- *bound variable*, not the constant, so matching the body as written misses
  -- it -- the spelling dimension reappearing one level down, at the term rather
  -- than the syntax.  Substituting the bound value into the body turns the
  -- alias back into the constant.  The value is still walked on its own, in
  -- case it contains an unrelated application; findings are a `HashSet`, so the
  -- overlap costs nothing.
  | .letE _ t v b _  => return hits ++ routeBootHits boot t
                                 ++ routeBootHits boot v
                                 ++ routeBootHits boot (b.instantiate1 v)
  | .mdata _ b       => return hits ++ routeBootHits boot b
  | .proj _ _ b      => return hits ++ routeBootHits boot b
  | _                => return hits

/-- **Does this constant touch a per-core scheduler slot?**  (PR #861 review
round 37.)

Derived, not listed.  The seed is the field-level accessor/setter pair that
`probe_stems` builds from `SchedulerState`'s own `Vector … numCores` fields, so
the base set closes over the struct by construction.  Everything else that
touches a slot must call one of them, and this is that transitive question.

Reads count as well as writes: `schedContextUnbind` checking
`currentOnCore bootCoreId` for its preemption guard was one of the round-15
defects, and it wrote nothing.

Bounded depth because the answer only has to be right for heads that were
actually passed the boot core, and an unbounded walk over a 126 700-constant
environment is not worth paying for a predicate with a two-hop caller.

Fails **closed** in the sense that matters: an unresolvable or value-less
constant answers `false`, but such a constant has no body to write a slot with.
-/
private partial def routeReachesPerCoreSlot (env : Environment)
    (setters : Std.HashSet Name) (fuel : Nat) (n : Name) : Bool :=
  if setters.contains n then true
  else match fuel with
    | 0 => false
    | fuel + 1 =>
      match env.find? n with
      | none => false
      | some ci =>
        match ci.value? with
        | none => false
        | some v =>
          v.getUsedConstants.any (routeReachesPerCoreSlot env setters fuel)

/-- The **composite** witness (PR #861 review round 37): a helper that reaches
the scheduler through `scheduleEffectiveOnCore` rather than through a field
setter directly.  Detected only if the reach test above is live, so the fix for
round 37 cannot silently regress into the hand-list it replaced. -/
def routeSelfTestComposite (st : SeLe4n.Model.SystemState) :
    Except SeLe4n.Model.KernelError SeLe4n.Model.SystemState :=
  SeLe4n.Kernel.scheduleEffectiveOnCore st SeLe4n.Kernel.Concurrency.bootCoreId

/-- A witness with the `let`-alias shape, so the traversal is checked against
the form that motivated zeta-reduction rather than only against whatever the
kernel happens to contain today. -/
-- NOT `private`: a private definition is mangled to `_private.…`, so
-- `env.find? \`routeSelfTestAlias` would return none and the witness would
-- report itself missing.  That is the same trap as the dispatch seeds above,
-- hit twice in one sitting -- which is the argument for the witness existing.
def routeSelfTestAlias st tid :=
  let c := SeLe4n.Kernel.Concurrency.bootCoreId
  SeLe4n.Kernel.removeRunnableOnCore st tid c

/-- A second witness, for the *other* spelling: `bootCoreId` elaborates to
`⟨0, numCores_pos⟩`, so a hand-written core zero is the same value with a
different proof term.  A `.const` test misses it; the definitional test below
must not. -/
def routeSelfTestLiteralZero st tid :=
  SeLe4n.Kernel.removeRunnableOnCore st tid ⟨0, SeLe4n.Kernel.Concurrency.numCores_pos⟩

run_cmd do
  let env ← getEnv
  let wanted : Std.HashSet String :=
    Std.HashSet.emptyWithCapacity.insertMany
      (routeRoots ++ routePrims ++ routePinned ++ routeDispatch ++ ["bootCoreId"])
  -- Two indexes.  `byStem` skips internal names, which is right for roots and
  -- primitives.  `byStemAll` keeps them, because the dispatch entry points are
  -- `private` and Lean mangles a private definition to
  -- `_private.SeLe4n.Kernel.API.0.SeLe4n.Kernel.dispatchCapabilityOnly` --
  -- which `Name.isInternal` rejects.  Seeding the dispatch walk by full name
  -- therefore resolved NOTHING (`ROUTE_DISPATCH_REACH 3`, the three unresolved
  -- seeds themselves) and the disambiguation it was supposed to drive silently
  -- did nothing.  The last component survives the mangling, so stem lookup
  -- finds them.
  let mut byStem : Std.HashMap String (Array Name) := {}
  let mut byStemAll : Std.HashMap String (Array Name) := {}
  for (n, _) in env.constants.toList do
    let c := routeLastComponent n
    if wanted.contains c then
      byStemAll := byStemAll.insert c ((byStemAll.getD c #[]).push n)
      if !n.isInternal then
        byStem := byStem.insert c ((byStem.getD c #[]).push n)
  let gather (ss : List String) : Std.HashSet Name := Id.run do
    let mut h : Std.HashSet Name := {}
    for x in ss do
      for n in byStem.getD x #[] do h := h.insert n
    return h
  let prims := gather routePrims
  let pinned := gather routePinned
  let boot := gather ["bootCoreId"]
  -- Fail closed on a primitive this gate claims to watch but cannot resolve.
  for x in routePrims ++ routePinned ++ ["bootCoreId"] do
    if (byStem.getD x #[]).isEmpty then
      logInfo m!"ROUTE_STEM_UNRESOLVED {x}"
  logInfo m!"ROUTE_SIZES prims={prims.size} pinned={pinned.size} boot={boot.size}"
  -- The alias witness must be detected, here, every run.  Without it the
  -- zeta-reduction above is a claim rather than a checked fact.
  --
  -- Each witness runs the **whole** production verdict, head and argument both
  -- (PR #861 review round 42).  This loop used to discard the head and pass on
  -- the argument alone, which made the COMPOSITE witness attest to nothing it
  -- was built for: its point is that the *head* classification is derived
  -- rather than hand-listed, so with `routeReachesPerCoreSlot` regressed to a
  -- constant `false` the production scan would go silent while COMPOSITE still
  -- reported ok.  A self-test that cannot fail when the thing it guards breaks
  -- is the fail-open shape this gate exists to close, reproduced inside the
  -- gate itself.  All three heads reach a slot, so requiring the conjunction
  -- costs nothing and each witness now checks the same decision the scan makes.
  for (wit, tag) in [(`routeSelfTestAlias, "ALIAS"), (`routeSelfTestLiteralZero, "ZERO"),
                     (`routeSelfTestComposite, "COMPOSITE")] do
    let mut ok := false
    if let some ci := env.find? wit then
      if let some v := ci.value? then
        for (p, a) in routeBootHits boot v do
          if !(routeReachesPerCoreSlot env prims 6 p) then continue
          if let .const c _ := a then
            if boot.contains c then ok := true
          if !ok then
            for b in boot do
              if ← liftTermElabM (Lean.Meta.isDefEq a (.const b [])) then ok := true
    if ok then logInfo m!"ROUTE_WITNESS_{tag} ok"
    else logInfo m!"ROUTE_WITNESS_MISSED {tag}"
  -- Everything the syscall dispatch can reach, computed once and used only to
  -- disambiguate colliding short names.
  let mut dispatchReach : Std.HashSet Name := {}
  let mut dFrontier : Array Name := Id.run do
    let mut a : Array Name := #[]
    for d in routeDispatch do
      for n in byStemAll.getD d #[] do a := a.push n
    return a
  for d in routeDispatch do
    if (byStemAll.getD d #[]).isEmpty then
      logInfo m!"ROUTE_DISPATCH_UNRESOLVED {d}"
  for _ in [0:6] do
    let mut nxt : Array Name := #[]
    for m in dFrontier do
      if dispatchReach.contains m then continue
      dispatchReach := dispatchReach.insert m
      if let some ci := env.find? m then
        if let some v := ci.value? then
          for u in v.getUsedConstants do nxt := nxt.push u
    dFrontier := nxt
  logInfo m!"ROUTE_DISPATCH_REACH {dispatchReach.size}"
  for r in routeRoots do
    let cands := byStem.getD r #[]
    if cands.isEmpty then
      logInfo m!"ROUTE_UNRESOLVED {r}"
    else
      -- A short name can occur in several namespaces (a production operation
      -- and its staged sibling, an operation and a same-named lock-set
      -- definition).  Rather than pick one and risk walking the wrong
      -- constant, walk ALL of them: the union over-approximates the arm's
      -- reach, so the gate can report a finding the arm does not really have
      -- but never miss one it does.  Over-approximation is the safe direction
      -- for a gate, and the count is logged so an unexpected collision is
      -- visible rather than silent.
      -- Disambiguate by DISPATCH REACHABILITY, not by name shape.  A short
      -- name can occur in several namespaces, and the collision that matters
      -- here is real: `registerService` is both the syscall operation and a
      -- *boot builder* (`Model.Builder`) that legitimately populates the boot
      -- core's run queue, because at boot there is no other core.  Unioning
      -- both reported the builder's correct `runQueueOnCore bootCoreId` as a
      -- finding against `.serviceRegister`.  Keeping only candidates the API
      -- dispatch can actually reach removes the builder without an ad-hoc
      -- namespace exclusion.
      let narrowed :=
        if cands.size > 1 then cands.filter dispatchReach.contains else cands
      -- Fail closed.  Silently falling back to the unnarrowed candidates is
      -- how the first attempt at this hid its own broken seeds.
      if narrowed.isEmpty then
        logInfo m!"ROUTE_UNNARROWABLE {r}"
      let cands := if narrowed.isEmpty then cands else narrowed
      if cands.size > 1 then
        logInfo m!"ROUTE_MULTI {r} {cands.size}"
      let mut seen : Std.HashSet Name := {}
      let mut frontier : Array Name := cands
      for _ in [0:@HOPS@] do
        let mut nxt : Array Name := #[]
        for m in frontier do
          if seen.contains m then continue
          seen := seen.insert m
          if let some ci := env.find? m then
            if let some v := ci.value? then
              for u in v.getUsedConstants do nxt := nxt.push u
        frontier := nxt
      let mut findings : Std.HashSet Name := {}
      let mut slotMemo : Std.HashMap Name Bool := {}
      for m in seen do
        if pinned.contains m then findings := findings.insert m
        if let some ci := env.find? m then
          if let some v := ci.value? then
            for (p, a) in routeBootHits boot v do
              -- Report a head only if it actually touches a per-core scheduler
              -- slot.  Passing `bootCoreId` to something else is ordinary.
              -- Memoised: the traversal now collects every application head, so
              -- this predicate is the hot path.
              let verdict ←
                match slotMemo.get? p with
                | some b => pure b
                | none =>
                  let b := routeReachesPerCoreSlot env prims 6 p
                  slotMemo := slotMemo.insert p b
                  pure b
              if !verdict then continue
              if let .const c _ := a then
                if boot.contains c then
                  findings := findings.insert p
                  continue
              -- Definitional test: `(0 : CoreId)` and `⟨0, h⟩` are `bootCoreId`
              -- by any other spelling.  `isDefEq` fails fast on a type mismatch,
              -- so passing every closed argument through it is cheap.
              for b in boot do
                let same ← liftTermElabM (Lean.Meta.isDefEq a (.const b []))
                if same then
                  findings := findings.insert p
                  break
      for f in findings do
        logInfo m!"ROUTE_FINDING {r} {f}"
      logInfo m!"ROUTE_ROOT {r} {seen.size}"
"""


def probe_stems() -> tuple[list[str], list[str]]:
    """(per-core primitives, boot-pinned single-core forms), by short name.

    The per-core half is still derived from `SchedulerState`'s own `Vector …
    numCores` fields (round 25), so a field added there is watched the day it
    lands; the probe resolves each stem to whatever full names the environment
    actually has.
    """
    prims = []
    for f in PER_CORE_FIELDS:
        prims.append(f"{f}OnCore")
        prims.append(f"set{f[0].upper()}{f[1:]}OnCore")
    # `removeReplenishmentsOnCore` was in the regex list and is NOT a constant
    # in this environment — the probe's fail-closed stem resolution is what
    # surfaced that, after the pattern had sat there matching nothing.
    prims += ["removeRunnableOnCore", "enqueueRunnableOnCore",
              "handleRescheduleSgiOnCore", "migrateRunQueueBucketOnCore",
              "switchToThreadOnCore", "preemptCurrentOnCore",
              "advanceDomainOnCore", "decrementDomainTimeOnCore"]
    return sorted(set(prims)), sorted(BOOT_PINNED)


def run_probe(roots: list[str], hops: int) -> tuple[dict, str]:
    """Elaborate the probe and return {root: [findings]} plus raw output."""
    prims, pinned = probe_stems()
    quoted = lambda xs: ", ".join(f'"{x}"' for x in xs)
    src = (PROBE_TEMPLATE
           .replace("@ROOTS@", quoted(sorted(set(roots))))
           .replace("@PRIMS@", quoted(prims))
           .replace("@PINNED@", quoted(pinned))
           .replace("@HOPS@", str(hops + 1)))
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as fh:
        fh.write(src)
        path = fh.name
    try:
        proc = subprocess.run(["lake", "env", "lean", path],
                              cwd=REPO, capture_output=True, text=True)
    except FileNotFoundError:
        # Detection needs a built Lean environment, so this gate belongs in a
        # tier that has one.  It shipped in Tier 0 for one commit and took the
        # toolchain-free ARM64 lane red with a bare traceback; it now runs in
        # Tier 1 after `lake build`.  Say which, so a future misplacement is
        # diagnosed rather than debugged.
        raise RuntimeError(
            "`lake` is not on PATH, so the routing probe cannot elaborate.\n"
            "      This gate detects against Lean's elaborated environment and "
            "must run in\n"
            "      a tier that has a built toolchain — it is wired into "
            "test_tier1_build.sh,\n"
            "      after the builds.  Tier 0 is deliberately build-free and "
            "cannot host it.") from None
    finally:
        os.unlink(path)
    out = proc.stdout + proc.stderr
    # Any nonzero exit is rejected before the output is read: the probe can
    # print findings and then die, and a partial walk proves nothing about the
    # constants it never reached.  Same rule as the axiom sweep.
    if proc.returncode != 0:
        raise RuntimeError(f"the routing probe exited {proc.returncode}\n{out[-3000:]}")
    diag = re.compile(r"^.*\.lean:\d+:\d+: error")
    if any(diag.match(ln) for ln in out.splitlines()):
        raise RuntimeError(f"the routing probe did not elaborate\n{out[-3000:]}")
    missed = re.findall(r"ROUTE_WITNESS_MISSED (\S+)", out)
    if missed:
        raise RuntimeError(
            f"the probe's own boot-core witnesses were NOT detected: {missed}.\n"
            "      ALIAS = a core passed through a local binding "
            "(`let c := bootCoreId; f … c`);\n"
            "      ZERO  = a core written as the literal `⟨0, _⟩` rather than "
            "as `bootCoreId`;\n"
            "      COMPOSITE = the boot core reaching a slot through a "
            "*composite* operation\n"
            "                  (`scheduleEffectiveOnCore`) rather than a field "
            "setter directly,\n"
            "                  so this one fails when the derived reach "
            "predicate stops reaching.\n"
            "      All three miss at once when `routeReachesPerCoreSlot` is "
            "broken, since every\n"
            "      witness runs the full head-and-argument verdict.")
    for tag in ("ROUTE_STEM_UNRESOLVED", "ROUTE_UNRESOLVED",
                "ROUTE_DISPATCH_UNRESOLVED", "ROUTE_UNNARROWABLE"):
        bad = re.findall(rf"{tag} (\S+)", out)
        if bad:
            raise RuntimeError(f"{tag}: {sorted(set(bad))}")
    found: dict = {r: [] for r in roots}
    for r, f in re.findall(r"ROUTE_FINDING (\S+) (\S+)", out):
        found.setdefault(r, []).append(f)
    return found, out


def lean_files() -> list[str]:
    out = []
    for root, _dirs, files in os.walk(SRC):
        for f in files:
            if f.endswith(".lean"):
                out.append(os.path.join(root, f))
    return out


def index_definitions() -> dict[str, str]:
    """Map a definition's *short* name to its body text (declaration to next top-level).

    PR #861 review round 15: the scan for "where does this declaration end" must
    start below the `def`/`abbrev` **keyword** line, not below the declaration's
    first line.  `DECL` deliberately matches Lean's two-line
    `@[attribute]` / `def name` form, so for those the match begins on the
    attribute line — and `TOP` matches `def `, so a scan starting one line later
    hit the declaration's own keyword and stopped immediately, recording the
    attribute alone as the body.  Every `@[export ...] def` in the tree was
    therefore indexed as an empty definition: `suspendThreadInner`
    (`Platform/FFI.lean`) came out as the literal string
    `@[export suspend_thread_inner]`.  A boot-pinned primitive inside any such
    body was invisible and the gate reported PASS — the fail-open mode this
    gate exists to eliminate, in the gate itself.

    Round 44: read through the code view, so a `def` inside a block-comment
    code sample is not indexed as a resolvable definition and a comment's
    `:=` cannot truncate the signature `takes_a_core` inspects.
    """
    bodies: dict[str, str] = {}
    for path in lean_files():
        text = read_code(path)
        lines = text.split("\n")
        starts = []
        for m in DECL.finditer(text):
            # `m.start()` is the attribute (or modifier) line; `m.end()` sits just
            # past the declared name and so is always on the `def`/`abbrev` line.
            starts.append((text[:m.start()].count("\n"),
                           text[:m.end()].count("\n"),
                           m.group(1)))
        for ln, kw_ln, name in starts:
            end = len(lines)
            for j in range(kw_ln + 1, len(lines)):
                if TOP.match(lines[j]):
                    end = j
                    break
            body = "\n".join(lines[ln:end])
            # A short name can be defined in several namespaces; concatenating the
            # bodies is the conservative direction for a "can this reach X" gate.
            bodies[name] = bodies.get(name, "") + "\n" + body
    return bodies


ARM = re.compile(r"^([ \t]*)\|\s*\.([A-Za-z][A-Za-z0-9]*)\s*=>", re.M)
COL0 = re.compile(r"^[A-Za-z@/]")
# The definitions whose `SyscallId` arms are live dispatch paths.  Anything else
# matching on `SyscallId` in `API.lean` — the authority table, the lock-set
# table, delegation-theorem statements — is not a code path and must not be
# walked (round 20).
DISPATCH_DEFS = re.compile(r"^dispatch(WithCap|CapabilityOnly|Syscall)")


def dispatch_arm_bodies(path: str) -> dict[str, list[str]]:
    """Map a `SyscallId` constructor to the text of each dispatch arm matching it.

    PR #861 review round 20: **one entry per arm, not one concatenated blob.**
    A syscall commonly has two production roots — the unchecked arm and the
    information-flow-checked one — and `.send` is the case in point
    (`endpointSendDualWithCapsOnCore` vs `endpointSendCrossCoreDispatchChecked`).
    Concatenating them let the checked arm satisfy root verification while the
    unchecked arm was never walked, so a boot-pinned regression confined to it
    would have left this gate green.

    PR #861 review round 15: the label -> definition translation must be
    *verified against the dispatch*, not assumed.  An enforcement-boundary label
    that happens to be some Lean definition's name was accepted even when the
    live arm called a different operation — `.tcbSetAffinity` resolved to
    `setThreadCpuAffinity` while `dispatchCapabilityOnly` calls
    `setThreadCpuAffinityOp`, so the scheduling-relevant body was never walked
    and the advertised fail-closed check passed by coincidence.

    An arm runs to the next `| .ctor =>` at the same or shallower indent, or to
    the next column-0 top-level, whichever comes first.  Arms for one
    constructor across several dispatch functions are concatenated.

    Round 44: read through the code view.  The arm text this returns is
    comment-free, so a retired root surviving only in a trailing comment
    cannot satisfy root verification, and a block-comment code sample cannot
    inject a phantom arm (`ARM` matches `| .ctor =>` at any indent, which a
    comment can otherwise contain verbatim).
    """
    text = read_code(path)
    lines = text.split("\n")
    marks = [(text[:m.start()].count("\n"), len(m.group(1)), m.group(2))
             for m in ARM.finditer(text)]
    # Round 20: an arm counts only if it sits inside a *dispatch* definition.
    # `API.lean` also matches on `SyscallId` for the authority table
    # (`| .send => .write`) and inside delegation-theorem statements, and those
    # are not code paths.  Walking them produced spurious reach — a theorem
    # statement's `∀`-bound names resolve to unrelated definitions.
    def_at: list[tuple[int, str]] = []
    for m in DECL.finditer(text):
        def_at.append((text[:m.start()].count("\n"), m.group(1)))

    def enclosing(line: int) -> str:
        name = ""
        for ln, nm in def_at:
            if ln <= line:
                name = nm
            else:
                break
        return name

    out: dict[str, list[str]] = {}
    for i, (ln, indent, sid) in enumerate(marks):
        if not DISPATCH_DEFS.match(enclosing(ln)):
            continue
        end = len(lines)
        for j in range(i + 1, len(marks)):
            if marks[j][1] <= indent:
                end = marks[j][0]
                break
        for j in range(ln + 1, end):
            if COL0.match(lines[j]):
                end = j
                break
        out.setdefault(sid, []).append("\n".join(lines[ln:end]))
    return out


def parse_map(path: str, fn: str) -> dict[str, str]:
    """Read `fn`'s `| .ctor => "label"` arms (through the code view — a
    block-comment sample below the real arm would otherwise *override* it,
    since the later regex match wins the dict write; round 44)."""
    text = read_code(path)
    i = text.index(f"def {fn} : SyscallId → String")
    j = TOP.search(text, text.index("\n", i) + 1)
    seg = text[i: j.start() if j else len(text)]
    out = {}
    for m in re.finditer(r"^\s*\|\s*\.([A-Za-z][A-Za-z0-9]*)\s*=>\s*\"([^\"]+)\"", seg, re.M):
        out[m.group(1)] = m.group(2)
    return out


def parse_live_arm_syscalls(path: str) -> set[str]:
    """The `SyscallId`s the cross-core NI inventory claims as live arms.

    Read from `crossCoreLiveArmSyscall`'s `=> some .<syscall>` arms — through
    the code view, because the pattern matches *anywhere* in the segment and a
    docstring citing an arm shape would otherwise register a phantom entry,
    suppressing the missing-inventory finding for that syscall (round 44).
    """
    text = read_code(path)
    i = text.index("def crossCoreLiveArmSyscall : CrossCoreTransition → Option SyscallId")
    j = TOP.search(text, text.index("\n", i) + 1)
    seg = text[i: j.start() if j else len(text)]
    return set(re.findall(r"=>\s*some\s+\.([A-Za-z][A-Za-z0-9]*)", seg))


def takes_a_core(body: str) -> bool:
    """Does this definition's *signature* take a `CoreId`?

    The signature is everything before the first `:=`.  A live arm's operation
    taking a core is the mechanical signal that it was re-routed to a per-core
    form and can therefore write a core other than the executing one.
    """
    head = body.split(":=", 1)[0]
    return re.search(r"(?<![A-Za-z0-9_'])CoreId(?![A-Za-z0-9_'])", head) is not None


# A *leading-dot* term — a dot not preceded by an identifier character.  In Lean
# that is anonymous-constructor notation (`.ok`, `.error`, `.schedContextUnbind`),
# never a call by short name.  A qualified call keeps its dot preceded by an
# identifier (`SchedContextOps.schedContextUnbindOnCore`) and so is left alone.
LEADING_DOT_CTOR = re.compile(r"(?<![A-Za-z0-9_'])\.[A-Za-z][A-Za-z0-9_']*")


def strip_arm_patterns(body: str) -> str:
    """Remove constructor references so only genuine call sites remain.

    PR #861 review round 16: the dispatch-verification check tokenized the whole
    arm, so the arm header `| .schedContextUnbind =>` made the *label*
    `schedContextUnbind` look like a call.  The live arm calls
    `schedContextUnbindOnCore`; the check passed on the header alone, and the
    walk then started from the single-core body — missing the wrapper's
    `priorityRescheduleOnCore` path entirely.  Same fail-open shape as the two
    round-15 gate defects.

    Stripping only `|`-prefixed patterns is not enough, which the fix's own first
    attempt proved: `decoded.syscallId = .schedContextUnbind` in the
    `syscallDelegates` arm reintroduced the bare name with no `|` in sight.  The
    boundary that actually separates the two is the *leading dot*.
    """
    return LEADING_DOT_CTOR.sub(" ", body)


def called_names(body: str) -> set[str]:
    return set(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", body))


def scan(percore: dict[str, str], bodies: dict[str, str], depth: int,
         allow: dict[tuple[str, str], str]) -> list[tuple[str, str, str, str]]:
    """Findings per syscall, from the elaborated environment.

    `bodies` is accepted and ignored — it is the source index the previous
    engine walked, kept in the signature only so the two self-test call sites
    read unchanged.  The walk itself now happens inside Lean: `run_probe`
    resolves each root to a constant, follows `getUsedConstants` for `depth`
    hops, and reports both a reference to a boot-pinned single-core form and an
    application of a per-core primitive whose argument IS `bootCoreId`.
    """
    del bodies
    roots = sorted(set(percore.values()))
    found, _out = run_probe(roots, depth)
    by_root: dict[str, list[str]] = {}
    for r, fs in found.items():
        by_root[r] = fs
    findings: list[tuple[str, str, str, str]] = []
    for sid, op in sorted(percore.items()):
        for full in sorted(set(by_root.get(op, []))):
            short = full.rsplit(".", 1)[-1]
            if (sid, short) in allow or (sid, full) in allow:
                continue
            why = (BOOT_PINNED.get(short)
                   or "per-core primitive applied at a literal bootCoreId; "
                      "pass the operation's own core")
            findings.append((sid, op, short, why))
    return findings


def main() -> int:
    depth = 2
    listing = "--list" in sys.argv
    if "--depth" in sys.argv:
        depth = int(sys.argv[sys.argv.index("--depth") + 1])

    # Source index, still used for *root resolution* — verifying that a mapped
    # label names a definition the dispatch arm actually calls.  Detection no
    # longer uses it: that happens in `run_probe`, against Lean's elaborated
    # environment.  Resolution is a question about the data tables and the
    # dispatch source, which text answers correctly.
    bodies = index_definitions()
    canonical = parse_map(CANON, "syscallIdToEnforcementName")
    percore = dict(canonical)
    percore.update(parse_map(MAPFILE, "syscallIdToEnforcementNamePerCore"))
    # Enforcement-boundary labels and Lean definition names are two namespaces;
    # where they differ, an alias names the definition the arm reaches.  Missing
    # aliases are rejected below rather than skipped, and every resolution —
    # aliased or not — is verified against the dispatch arm (round 15).
    try:
        aliases = {k: v for k, v in json.load(open(ALIASES)).items()
                   if not k.startswith("_")}
    except (OSError, ValueError):
        aliases = {}
    labels = dict(percore)
    percore = {sid: aliases.get(op, op) for sid, op in percore.items()}

    try:
        allow = {(e["syscall"], e["symbol"]): e["reason"] for e in json.load(open(ALLOWLIST))}
    except (OSError, ValueError):
        allow = {}

    if "--self-test" in sys.argv:
        # The gate must FLAG the operations these arms called *before* this cut.
        # Probed by definition name rather than through the canonical map, because
        # that map's strings are enforcement-boundary labels and several
        # (`setPriority`, `setMCPriority`) are not Lean definitions at all —
        # which is the fail-open `unresolved` below now rejects.
        pre_smp = {"tcbResume": "resumeThread",
                   "tcbSetPriority": "setPriorityOp",
                   "tcbSetMCPriority": "setMCPriorityOp",
                   "send": "endpointSendDualWithCaps"}
        detected = {f[0] for f in scan(pre_smp, bodies, depth, {})}
        expected = set(pre_smp)
        missing = expected - detected
        if missing:
            print(f"[per-core-routing] SELF-TEST FAIL: reach {depth} does not detect "
                  f"the known boot-pinned arms: {sorted(missing)}")
            return 1
        # Round 23: the boot-*write* patterns must actually match.  They were
        # added to a tree that has no violation of that shape, so the scan went
        # green the moment they landed — which is equally what a broken regex
        # looks like.  These synthetic spellings are the difference between the
        # two, and the last one pins that a genuine per-core call (core taken
        # from `determineTargetCore`, not a literal) is NOT flagged, so the
        # patterns cannot be "fixed" into rejecting correct code.
        # Round 25: the derivation must see every per-core slot.  A parse that
        # silently returns a subset is the failure mode the hand-written list
        # already demonstrated, so the count is pinned rather than trusted.
        want_fields = {"runQueue", "current", "activeDomain", "domainTimeRemaining",
                       "domainScheduleIndex", "replenishQueue", "lastTimeoutErrors"}
        if set(PER_CORE_FIELDS) != want_fields:
            print(f"[per-core-routing] SELF-TEST FAIL: per-core field derivation gives "
                  f"{sorted(PER_CORE_FIELDS)}, expected {sorted(want_fields)}.  If a field "
                  f"was added to SchedulerState, extend this set in the same commit.")
            return 1
        # Round 43: the set above is a hard-coded expectation, so it agrees with
        # a parser that has stopped parsing as readily as with one that works —
        # it pins today's answer, not the mechanism.  These two witnesses pin
        # the mechanism, over shapes the old single-line regex got wrong: a
        # field wrapped across lines must be FOUND, and a comment inside the
        # structure that mentions the pattern must NOT invent one.
        witness = (
            "structure SchedulerState where\n"
            "  runQueue :\n"
            "    Vector RunQueue\n"
            "      numCores\n"
            "  /-- A doc mentioning phantomField : Vector Nat numCores. -/\n"
            "  scalarField : Nat\n"
            "def after := 1\n"
        )
        _body = re.search(r"^structure SchedulerState where$(.*?)^\S",
                          lean_code_view.strip(witness), re.M | re.S)
        _decls: list[tuple[str, list[str]]] = []
        for _line in (_body.group(1).splitlines() if _body else []):
            _h = re.match(r"^\s{2}([a-z][A-Za-z0-9_']*)\s*:", _line)
            if _h:
                _decls.append((_h.group(1), [_line]))
            elif _decls and _line.strip():
                _decls[-1][1].append(_line)
        _got = {n for n, b in _decls
                if re.search(r"\bVector\b", " ".join(b))
                and re.search(r"\bnumCores\b", " ".join(b))}
        if _got != {"runQueue"}:
            print(f"[per-core-routing] SELF-TEST FAIL: the field parse gives {sorted(_got)} on "
                  f"the wrapped/commented witness, expected ['runQueue'] — a wrapped field "
                  f"must be found and a commented one must not be invented.")
            return 1
        print("[per-core-routing] SELF-TEST PASS: the per-core field parse survives line "
              "wrapping and ignores comments.")
        # Round 44: every source read is through the code view, and these
        # witnesses pin the four closures over shapes the raw reads got wrong.
        # A retired root surviving only in a *trailing* comment must not
        # satisfy root verification (`strip_comments` kept those lines whole);
        # a block-comment code sample must inject neither a dispatch arm nor
        # a `parse_map` override (the later regex match wins the dict write);
        # and prose citing `=> some .<syscall>` must not register a cross-core
        # inventory entry.  The raw-text assert keeps the fixture honest: the
        # traps must really be present in the bytes on disk, so the witness
        # cannot drift vacuous by losing them.
        fixture = (
            "def dispatchWithCapWitness (st : Nat) : SyscallId → Nat\n"
            "  | .tcbResume =>\n"
            "    resumeThreadOnCoreLive st  -- resumeThread\n"
            "  /- a retired sample:\n"
            "| .phantomArm =>\n"
            "    phantomArmRoot st\n"
            "  -/\n"
            "  | .send => endpointSendWitnessRoot st\n"
            "def syscallMapWitness : SyscallId → String\n"
            "  | .send => \"realLabel\"\n"
            "/- an old sample:\n"
            "  | .send => \"phantomLabel\"\n"
            "-/\n"
            "def crossCoreLiveArmSyscall : CrossCoreTransition → Option SyscallId\n"
            "  /- prose citing the arm shape `| .x => some .phantomSyscall` -/\n"
            "  | .realTransition => some .realSyscall\n"
            "def after := 1\n"
        )
        with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False,
                                         encoding="utf-8") as _tf:
            _tf.write(fixture)
            _fx = _tf.name
        try:
            _raw = open(_fx, encoding="utf-8").read()
            _arms = dispatch_arm_bodies(_fx)
            _called: set[str] = set()
            for _a in _arms.get("tcbResume", []):
                _called |= called_names(strip_arm_patterns(_a))
            _bad = []
            if "resumeThreadOnCoreLive" not in _called:
                _bad.append("the real call disappeared from the arm")
            if "resumeThread" in _called:
                _bad.append("a trailing comment reached called_names")
            if "phantomArm" in _arms:
                _bad.append("a block-comment sample injected a dispatch arm")
            if parse_map(_fx, "syscallMapWitness") != {"send": "realLabel"}:
                _bad.append("a block-comment sample overrode a parse_map arm")
            if parse_live_arm_syscalls(_fx) != {"realSyscall"}:
                _bad.append("comment prose registered an inventory entry")
            if ("-- resumeThread" not in _raw or "phantomLabel" not in _raw
                    or "phantomSyscall" not in _raw or "phantomArm" not in _raw):
                _bad.append("the fixture lost its traps (witness gone vacuous)")
            if _bad:
                print("[per-core-routing] SELF-TEST FAIL: comment-blind source "
                      "reads — " + "; ".join(_bad) + ".")
                return 1
        finally:
            os.unlink(_fx)
        print("[per-core-routing] SELF-TEST PASS: root verification, arm "
              "splitting, map parsing and the inventory read see code only.")
        # Round 29 (the rewrite): the checks below are about the ENGINE the
        # gate now runs.  The pattern probes they replace tested regexes that
        # no longer exist; six review rounds of them is what motivated moving
        # detection into the elaborated environment.
        #
        # (1) The dispatch reach must be substantial.  This is the exact
        # fail-open that shipped in the first attempt: the disambiguation seeds
        # are `private` definitions, Lean mangles those to `_private.…`, the
        # full-name lookup resolved none of them, and the narrowing it drives
        # silently did nothing while the gate still printed a verdict.  The
        # observable symptom was `ROUTE_DISPATCH_REACH 3` — the three
        # unresolved seeds.  A floor of 500 is far below the real figure
        # (~2200) and far above the broken one.
        _f, probe_out = run_probe(["schedContextUnbindOnCore"], depth)
        m = re.search(r"ROUTE_DISPATCH_REACH (\d+)", probe_out)
        if not m:
            print("[per-core-routing] SELF-TEST FAIL: the probe reported no dispatch "
                  "reach at all.")
            return 1
        if int(m.group(1)) < 500:
            print(f"[per-core-routing] SELF-TEST FAIL: dispatch reach is "
                  f"{m.group(1)}, so short-name disambiguation is not working. "
                  f"The usual cause is a seed in `routeDispatch` that no longer "
                  f"resolves — they are `private`, so they are found by stem.")
            return 1

        # (2) The collision that disambiguation exists for must still be
        # disambiguated.  `registerService` is both the syscall operation and a
        # boot builder that legitimately writes `runQueueOnCore bootCoreId`
        # (at boot there is no other core).  Walking both reported the builder
        # against `.serviceRegister`; this is that regression as a witness.
        print(f"[per-core-routing] SELF-TEST PASS: dispatch reach {m.group(1)} "
              f"constants, so short-name disambiguation is live.")
        svc, _ = run_probe(["registerServiceChecked"], depth)
        if svc.get("registerServiceChecked"):
            print("[per-core-routing] SELF-TEST FAIL: `registerServiceChecked` picked "
                  "up findings from a same-named constant outside the dispatch reach "
                  f"({svc['registerServiceChecked']}).")
            return 1
        print("[per-core-routing] SELF-TEST PASS: the `registerService` "
              "builder/operation collision stays disambiguated.")

        print(f"[per-core-routing] SELF-TEST PASS: reach {depth} detects all of "
              f"{sorted(expected)} in the pre-SMP map "
              f"({len(detected)} arm(s) flagged there in total).")
        return 0

    # FAIL-CLOSED: a mapped operation that is not a definition means the walk
    # starts nowhere and the syscall is silently unchecked.  The self-test found
    # this: the canonical map's `.tcbSetPriority => "setPriority"` resolves to no
    # Lean definition, so that arm was passing by vacuity, not by correctness.
    unresolved = sorted({(sid, op) for sid, op in percore.items() if op not in bodies})
    if unresolved:
        print("[per-core-routing] FAIL: a mapped operation does not resolve to a "
              "definition, so its arm is unchecked rather than clean:")
        for sid, op in unresolved:
            print(f"  .{sid} -> `{op}` (no `def`/`abbrev` of that name in SeLe4n/)")
        return 1

    # FAIL-CLOSED (round 15): resolving to *a* definition is not enough — it must
    # be the definition the live arm actually calls.  A label that coincidentally
    # names some unrelated `def` walked the wrong body and passed by accident.
    arms = dispatch_arm_bodies(API)
    unverified = []
    # Round 20: every arm is verified and walked, not just the one that happens
    # to name the mapped root.  `.send` has two production arms — the unchecked
    # one calls `endpointSendDualWithCapsOnCore`, the checked one
    # `endpointSendCrossCoreDispatchChecked` — so requiring only that *some* arm
    # mentions the mapped operation let a boot-pinned regression hide in the
    # other.  `extra_roots` carries each arm's own callees into the scan below.
    extra_roots: dict[str, set[str]] = {}
    for sid, root in sorted(percore.items()):
        armlist = arms.get(sid)
        if not armlist:
            unverified.append((sid, root, "no `| .<syscall> =>` arm in API.lean"))
            continue
        # The arm text is comment-free at the read (round 44), so tokenizing
        # it here sees code alone — `strip_comments`, which kept trailing
        # `--` comments, is retired rather than repaired.
        called_per_arm = [called_names(strip_arm_patterns(a)) for a in armlist]
        # Every root this syscall is declared to have: the mapped one, plus any
        # siblings named in the aliases file under `<label>#alt`.  Declared
        # rather than inferred — taking each arm's callees as roots would walk
        # names an arm merely mentions, and over-approximating a *reach* gate
        # produces findings against code the arm cannot run.
        declared = {root}
        alt = aliases.get(labels[sid] + "#alt")
        if isinstance(alt, str):
            declared.add(alt)
        elif isinstance(alt, list):
            declared.update(alt)
        uncovered = [i for i, c in enumerate(called_per_arm)
                     if not (declared & c)]
        if uncovered:
            unverified.append((sid, root,
                               f"dispatch arm #{uncovered[0]} calls none of "
                               f"{sorted(declared)} — declare it as "
                               f"`\"{labels[sid]}#alt\"` in the aliases file"))
            continue
        extra_roots.setdefault(sid, set()).update(d for d in declared
                                                  if d != root and d in bodies)
    if unverified:
        print("[per-core-routing] FAIL: a mapped operation is not the one its live "
              "dispatch arm calls, so the walk starts from the wrong body:")
        for sid, root, why in unverified:
            print(f"  .{sid} -> `{root}` — {why}")
        print("[per-core-routing] Add a verified entry to "
              "scripts/per_core_routing_aliases.json naming the operation the arm")
        print("[per-core-routing] really calls.")
        return 1

    # FAIL-CLOSED (round 15): the *other* half of the per-core obligation.
    #
    # Re-routing an arm to a per-core operation is only half the work — the
    # operation can now write a core it is not executing on, which is exactly
    # what the cross-core non-interference inventory exists to bound.  Rounds 12
    # and 14 rerouted five arms and gave three of them inventory entries; the
    # miss was found by a reviewer, one arm at a time, because nothing checked
    # the pairing.  This does: an operation whose signature takes a `CoreId` is
    # a per-core form, and its syscall must appear in `crossCoreLiveArmSyscall`.
    inventory = parse_live_arm_syscalls(NIFILE)
    missing_entry = []
    for sid, root in sorted(percore.items()):
        if not takes_a_core(bodies[root]):
            continue
        if sid in inventory or (sid, "cross-core-inventory") in allow:
            continue
        missing_entry.append((sid, root))
    if missing_entry:
        print("[per-core-routing] FAIL: a per-core-routed arm has no cross-core "
              "non-interference entry, so nothing bounds what it writes remotely:")
        for sid, root in missing_entry:
            print(f"  .{sid} -> `{root}` (takes a CoreId; absent from "
                  f"crossCoreLiveArmSyscall)")
        print("[per-core-routing] Add the entry with its write set and confinement")
        print("[per-core-routing] proof, or allowlist (syscall, \"cross-core-inventory\")")
        print("[per-core-routing] with the reason its per-core writes are unobservable.")
        return 1

    # Round 20: scan the mapped root AND every second-arm root discovered above,
    # so both production paths of a two-arm syscall are walked.
    scan_roots = dict(percore)
    for sid, roots in extra_roots.items():
        for i, extra in enumerate(sorted(roots)):
            scan_roots[f"{sid}#{i}"] = extra
    findings = scan(scan_roots, bodies, depth, allow)
    # Report a second-arm finding against the syscall, not the synthetic key.
    findings = [(sid.split("#", 1)[0], *rest) for sid, *rest in findings]

    if listing:
        for sid, op in sorted(percore.items()):
            print(f"  {sid:24s} -> {op}")

    print(f"[per-core-routing] {len(percore)} syscalls, reach depth {depth} "
          f"(two hops: arm -> operation -> helper), "
          f"{len(allow)} allowlisted exception(s)")
    if findings:
        print("[per-core-routing] FAIL: a live syscall arm can reach a boot-pinned "
              "scheduler primitive.")
        for sid, via, sym, why in sorted(set(findings)):
            print(f"  .{sid}: reaches `{sym}` via `{via}` — {why}")
        print("[per-core-routing] Route the arm through the per-core form, or add a")
        print("[per-core-routing] justified entry to scripts/per_core_routing_allowlist.json.")
        return 1
    print("[per-core-routing] PASS: no live arm reaches a boot-pinned scheduler primitive.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
