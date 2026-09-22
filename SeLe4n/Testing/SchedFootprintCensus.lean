-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
import Lean.Elab.Command
import SeLe4n
import SeLe4n.Platform.Staged
import SeLe4n.Kernel.SyscallSchedFootprint
import SeLe4n.Testing.DeclarationKind

/-!
# WS-RR RR8.12 Cut C5 — the scheduler domain's footprint family, derived

The object domain has had `LockFootprintBoundCensus` since WS-RR RR7.18, for a
reason that reads the same here: a hand-written conjunction cannot notice that
it is missing members.  The scheduler domain had nothing, and the measurement
that said so is Cut 8a-ii's: of the family's forty-seven theorems, **thirty-three
had neither a consumer nor a Tier 3 anchor** — every RR2.4 / RR2.10 / RR8.12
footprint property, silently deletable, because their consumer is the bracket
cut and the bracket cut has not landed.  Eight hand anchors were the stopgap.
A hand-written list is what this census retires.

## The two questions

**Is every footprint the canonical shape?**  A scheduler footprint's whole
usable surface is delegated: `schedFootprintOfCores_write_only`,
`_pairwise_le`, `_keys_nodup`, `_subset` and `mem_schedFootprintOfCores_*_iff`
are stated once, of `schedFootprintOfCores`, and every footprint inherits them
*because it is that function applied to two core lists*.  Restating them per
footprint would be a delegation with no content — which is why Cut 7 and every
cut after it omitted them — and that economy is sound exactly as long as the
shape holds.  A footprint written any other way loses all five **silently**:

* `_keys_nodup` is `SchedLockSet.ofList?`'s own obligation, so a footprint
  outside the shape can make the constructor **refuse**, and the resolver's arm
  then answers `none`.  That is an *undeclared* arm — which the bracket treats
  as "no exclusion established", so it is sound, and it drops the arm out of the
  very coverage this workstream is building, with nothing saying so.
* `_pairwise_le` is the acquisition-order obligation the bracket's ladder rests
  on, and there is no other proof of it in the tree.

So the shape is not a style rule; it is the premise every generic lemma is
consumed under.  This census requires it, at each footprint's **full arity**,
decided by reducing the applied definition *towards* `schedFootprintOfCores`
(`Meta.whnfUntil`) rather than by reading its source.  That is round 21's rule:
where the subject is code this project writes, require a canonical spelling and
refuse the rest.

**Is every footprint consumed, and is every exemption real?**  A footprint the
syscall resolver never names is a footprint nobody acquires — the "silently
deletable" half of the finding above.  The consumed set is derived from
`schedLockSetForSyscall`'s own elaborated value (closing over the compiler's
auxiliaries for that definition, since a `match` puts its arms in an auxiliary's
application), and reconciled against `resolverExemptions` in **both** directions:
an unconsumed footprint that is not registered fails, and a registered footprint
that has become consumed fails too — a stale exemption reads exactly like
coverage.

## What is outside this census, and why that is a decision

The universe is the `schedLockSet_`-prefixed definitions, which is the family
`schedLockSetForSyscall` dispatches to.  The RR2.4 / RR2.10 **parametric**
footprints (`wakeThreadLockSet`, `descheduleThreadLockSet`,
`suspendThreadOnCoreSchedLockSet`, …) are deliberately outside it: their cores
are *parameters* rather than values resolved from a state, several are literal
two-element ladders at a fixed single core of each kind (where there is nothing
to sort and nothing to merge), and they are related to the resolved family by
coverage theorems rather than consumed by the resolver.  Requiring the canonical
shape of them would refuse the literals, which are correct; requiring them to be
consumed would refuse every one, since the resolver consumes the resolved forms.
`PriorityInheritance.pipChainSchedFootprint` is outside for the sharper reason
that its object segment is a per-thread TCB lock per chain member rather than
the single table lock, so its ladder is a different proposition.

Building this module is the check; `scripts/test_tier1_build.sh` builds it.
-/

namespace SeLe4n.Testing.SchedFootprintCensus

open Lean Elab Command Meta

/-- The prefix a scheduler-domain footprint's last name component carries.

One spelling, so a footprint under any other name is one this census cannot
find — deliberate, and the same contract `lockSet_` carries in the object
domain: a caller looking for an arm's footprint must be able to find it by
name. -/
def footprintPrefix : String := "schedLockSet_"

/-- Footprints the syscall resolver does not name, each with the reason.

Both entries are *supersessions*: a second footprint exists for the same
syscall, the live dispatch reaches the other one, and the resolver names the one
the dispatch reaches.  Neither is dead — each is the footprint of a transition
in its own right, related to its sibling by theorem — which is why they are
registered rather than deleted. -/
def resolverExemptions : List (Name × String) :=
  [ (``SeLe4n.Kernel.schedLockSet_notificationSignalOnCore,
      "the BARE signal's footprint.  `API.dispatchWithCap{,Checked}` routes \
       `.notificationSignal` through `notificationSignalBoundCrossCoreDispatch`, so the \
       resolver names `schedLockSet_notificationSignalBoundOnCore`; the two genuinely \
       differ, because on the bound-delivery path the woken thread is the BOUND TCB, \
       whose home core the bare signal's set does not name.  \
       `schedLockSet_notificationSignalBoundOnCore_of_no_target` is the relation off \
       that path, where the two are definitionally equal")
  , (``SeLe4n.Kernel.schedLockSet_endpointReplyOnCore,
      "the DISPATCH-level reply footprint.  `.reply`'s live arm is seL4's \
       `doReplyTransfer` (`replyTransferOnCore`), whose footprint sits OVER this one: \
       `v0.35.163` proved the fault-abandon branch deschedules the answered thread on \
       its home core, a write the dispatch never performs, so a resolver naming this \
       footprint would be short by that member.  \
       `schedLockSet_replyTransferOnCore_covers_dispatch_of_no_fault` and `_of_fault` \
       are the relation between the two") ]

/-- Is this a scheduler-domain footprint declaration — a body-bearing constant
named `schedLockSet_…` whose type ends in `List (SchedLockId × AccessMode)`?

The name test is on the **last component**, so a footprint is found wherever it
is declared; the type test is what makes it a footprint rather than something
that merely reads like one. -/
def isSchedFootprintDecl (env : Environment) (n : Name) : MetaM Bool := do
  match n with
  | .str _ s =>
    if !s.startsWith footprintPrefix then return false
    match env.find? n with
    | some ci =>
        if !SeLe4n.Testing.DeclarationKind.bodyBearing ci then return false
        forallTelescopeReducing ci.type fun _ result => do
          let expected ← mkAppM ``List
            #[← mkAppM ``Prod #[mkConst ``SeLe4n.Kernel.SchedLockId,
                                mkConst ``SeLe4n.Kernel.Concurrency.AccessMode]]
          isDefEq result expected
    | none => return false
  | _ => return false

/-- The verdict on one footprint's **shape**: `none` when the definition, applied
to its own binders, reduces to a term headed by `schedFootprintOfCores`.

Reducing *towards* the constant rather than to weak head normal form is the
point: `whnf` would run past `schedFootprintOfCores` into the `List.cons` its
body builds, so the question "is this footprint the canonical ladder" would be
unaskable.  `whnfUntil` stops at the head this contract names.

There is deliberately **no arity test** beside it.  The applied term is the
definition at its full telescope and its type is `List (SchedLockId × AccessMode)`,
so a reduction that stops with `schedFootprintOfCores` as head has it fully
applied by type-correctness: an arity condition there could only ever be true,
and a condition no input can decide is indistinguishable from a wrong one. -/
def shapeViolation (env : Environment) (n : Name) : MetaM (Option String) := do
  let some ci := env.find? n
    | return some "is not a constant this environment knows"
  forallTelescopeReducing ci.type fun xs _ => do
    let applied := mkAppN (mkConst n) xs
    match ← whnfUntil applied ``SeLe4n.Kernel.schedFootprintOfCores with
    | none =>
        return some "does not reduce to `schedFootprintOfCores` at its full arity — every \
          generic lemma the scheduler domain delegates to (`_write_only`, `_pairwise_le`, \
          `_keys_nodup`, `_subset`, `mem_…_iff`) is stated of that function, so a footprint \
          outside the shape loses all five SILENTLY, and `SchedLockSet.ofList?` may then \
          refuse it and leave the arm undeclared"
    | some _ => return none

/-- The constants `root` names **directly** — the constants occurring in its own
elaborated value, and no further.

*Names*, not *reaches*: the claim this census makes is that an arm of
`schedLockSetForSyscall` dispatches to the footprint, and a transitive closure
answers a weaker question — a footprint mentioned by some other footprint's
write-set helper would count as consumed while no arm names it, which is the
presence-for-relation substitution one level down.  The planted pair below
witnesses the boundedness in exactly that direction.

One level is enough because a `match` passes its arms to the generated matcher
as **arguments**, so the arm bodies sit in this definition's own value.  Were a
future toolchain to move them into an auxiliary, this walk would miss every
footprint and the census would report all sixteen declared arms as unconsumed —
a named build failure, not a silence. -/
def namedBy (env : Environment) (root : Name) : NameSet :=
  match env.find? root with
  | some ci =>
      match ci.value? (allowOpaque := true) with
      | some v => v.getUsedConstants.foldl (fun s c => s.insert c) ({} : NameSet)
      | none => {}
  | none => {}

/-- The footprints the syscall resolver dispatches to. -/
def resolverConsumed (env : Environment) : NameSet :=
  namedBy env ``SeLe4n.Kernel.schedLockSetForSyscall

run_cmd Command.liftTermElabM do
  let env ← getEnv
  let mut footprints : Array Name := #[]
  for (n, _) in env.constants.toList do
    if ← isSchedFootprintDecl env n then
      footprints := footprints.push n
  let sorted := footprints.qsort (fun a b => a.toString < b.toString)
  if sorted.size == 0 then
    throwError "scheduler-footprint census: found NO footprints, so it would pass \
      vacuously — the name or type test is wrong"
  let consumed := resolverConsumed env
  let mut violations : Array String := #[]
  -- (1) Every footprint is the canonical ladder, at its full arity.
  for n in sorted do
    match ← shapeViolation env n with
    | some why => violations := violations.push s!"  {n}: {why}"
    | none => pure ()
  -- (2) Every footprint is consumed by the resolver, or registered with a reason.
  let mut unconsumed : Array Name := #[]
  for n in sorted do
    if !consumed.contains n then
      unconsumed := unconsumed.push n
      if !resolverExemptions.any (fun p => p.1 == n) then
        violations := violations.push s!"  {n}: is named by no arm of \
          `schedLockSetForSyscall`, so it is a footprint nobody acquires — declare the arm \
          that needs it, or register it in `resolverExemptions` with the reason"
  -- (3) ...and every registered exemption is really unconsumed, because a stale
  -- exemption reads exactly like coverage.
  for (n, _) in resolverExemptions do
    if !sorted.contains n then
      violations := violations.push s!"  {n}: is registered in `resolverExemptions` but is \
        not a scheduler footprint of this environment — a register entry naming nothing is \
        an exemption nobody can check"
    else if consumed.contains n then
      violations := violations.push s!"  {n}: is registered as unconsumed and the resolver \
        DOES name it — a stale exemption reads exactly like coverage"
  if violations.size != 0 then
    throwError "scheduler-footprint census: {violations.size} finding(s) over \
      {sorted.size} declared footprints:\n{String.intercalate "\n" violations.toList}"
  logInfo s!"scheduler-footprint census: {sorted.size} declared SchedLockId footprints, \
    every one the canonical `schedFootprintOfCores` ladder at its full arity; \
    {sorted.size - unconsumed.size} consumed by `schedLockSetForSyscall`, \
    {unconsumed.size} registered as superseded"

-- ============================================================================
-- Witnesses
-- ============================================================================
--
-- Both questions above are answerable today on every member of the family, so
-- neither failing branch can fire on the live tree — and a check that cannot
-- fire and carries no witness is indistinguishable from one that is wrong.
-- These plants sit on the far side of each decision.

/-- A planted **canonical** footprint: the shape every family member has.

Named out of the family (`censusPlanted…`, not `schedLockSet_…`) so the census's
own run does not see it, and read by the self-test below through
`shapeViolation` directly. -/
private def censusPlantedCanonical (executingCore : SeLe4n.Kernel.Concurrency.CoreId) :
    List (SeLe4n.Kernel.SchedLockId × SeLe4n.Kernel.Concurrency.AccessMode) :=
  SeLe4n.Kernel.schedFootprintOfCores [executingCore] []

/-- A planted **non-canonical** one, carrying a member the canonical form also
carries: the mutation that keeps the token and breaks the relation.  Every
generic lemma the scheduler domain delegates to is unavailable for it, and
`SchedLockSet.ofList?` has no `Nodup` proof to consume. -/
private def censusPlantedInlined (executingCore : SeLe4n.Kernel.Concurrency.CoreId) :
    List (SeLe4n.Kernel.SchedLockId × SeLe4n.Kernel.Concurrency.AccessMode) :=
  [(SeLe4n.Kernel.SchedLockId.runQueue ⟨executingCore⟩,
    SeLe4n.Kernel.Concurrency.AccessMode.write)]

/-- A planted **direct** namer: a definition whose own value mentions a real
footprint.  `namedBy` must contain it. -/
private def censusPlantedNamer :
    List (SeLe4n.Kernel.SchedLockId × SeLe4n.Kernel.Concurrency.AccessMode) :=
  SeLe4n.Kernel.schedLockSet_notificationWaitOnCore SeLe4n.Kernel.Concurrency.bootCoreId

/-- …and a planted **indirect** one, which names only the namer.

This is the pair that witnesses the walk's boundedness: a transitive closure
would put the footprint in this definition's set, and "consumed" would then mean
*reached* rather than *dispatched to*, so a footprint no arm names could be
counted as acquired because some helper mentions it. -/
private def censusPlantedIndirectNamer :
    List (SeLe4n.Kernel.SchedLockId × SeLe4n.Kernel.Concurrency.AccessMode) :=
  censusPlantedNamer

/-- A planted constant carrying the family's **name** and not its **type**.

It must stay outside the derived family: dropping the type test would admit it,
the shape check would then refuse it, and the build would break — so this plant
decides the type half of `isSchedFootprintDecl` permanently rather than for the
length of one mutation run. -/
private def schedLockSet_censusPlantedNotAFootprint : Nat := 0

run_cmd Command.liftTermElabM do
  let env ← getEnv
  let mut failures : Array String := #[]
  -- (a) the canonical plant passes the shape check…
  if (← shapeViolation env ``censusPlantedCanonical).isSome then
    failures := failures.push "the canonical plant is refused by `shapeViolation`, so the \
      shape check refuses the shape every family member has"
  -- (b) …and the inlined one does not, which is the branch the live tree cannot reach.
  if (← shapeViolation env ``censusPlantedInlined).isNone then
    failures := failures.push "the inlined plant passes `shapeViolation`, so the shape check \
      decides nothing — a hand-written ladder would inherit no generic lemma and still pass"
  -- (c) a constant with the family's name and not its type stays out of the family.
  if ← isSchedFootprintDecl env ``schedLockSet_censusPlantedNotAFootprint then
    failures := failures.push "a `schedLockSet_`-named constant that is not a footprint \
      entered the family, so the type half of `isSchedFootprintDecl` decides nothing"
  -- (d) the consumption derivation distinguishes: a resolver-named footprint is in
  -- it and a superseded one is not.  Without this a derivation that answered
  -- "everything" or "nothing" would read as coverage in one direction.
  let consumed := resolverConsumed env
  if !consumed.contains ``SeLe4n.Kernel.schedLockSet_endpointCallOnCore then
    failures := failures.push "`schedLockSet_endpointCallOnCore` is not in the consumed set, \
      though `schedLockSetForSyscall`'s `.call` arm names it — the derivation is too narrow"
  if consumed.contains ``SeLe4n.Kernel.schedLockSet_endpointReplyOnCore then
    failures := failures.push "`schedLockSet_endpointReplyOnCore` is in the consumed set, \
      though no arm names it — the derivation is too wide, and every exemption would then \
      read as coverage"
  -- (e) …and it is what its name says: a namer's own value, not what that value
  -- transitively reaches.  A closure would count a footprint as consumed because
  -- a helper mentions it, which is *reached* rather than *dispatched to*.
  if !(namedBy env ``censusPlantedNamer).contains
      ``SeLe4n.Kernel.schedLockSet_notificationWaitOnCore then
    failures := failures.push "the direct plant's own footprint is not in its named set, \
      so `namedBy` misses a constant the definition literally applies"
  if !(namedBy env ``censusPlantedIndirectNamer).contains ``censusPlantedNamer then
    failures := failures.push "the indirect plant does not name the direct one, so the \
      plant pair cannot witness anything"
  if (namedBy env ``censusPlantedIndirectNamer).contains
      ``SeLe4n.Kernel.schedLockSet_notificationWaitOnCore then
    failures := failures.push "the indirect plant's named set reaches THROUGH the direct \
      one, so `namedBy` is a transitive closure — it answers `reached`, and this census's \
      claim is `dispatched to`"
  -- (f) the WIRING case: the plants above decide `namedBy`, and a `resolverConsumed`
  -- that closed transitively over it would pass every one of them.  A write-set
  -- helper is named by a footprint and by no arm, so it is reached at depth two
  -- and named at depth one by nothing — which separates the two readings on the
  -- live tree rather than on a plant.
  if consumed.contains ``SeLe4n.Kernel.notificationSignalBoundWriteSet then
    failures := failures.push "a write-set helper no arm names is in the consumed set, so \
      `resolverConsumed` closes transitively — and a footprint nobody dispatches to would \
      then count as acquired because some reachable helper mentions it"
  if failures.size != 0 then
    throwError "scheduler-footprint census self-test: {failures.size} failure(s):\n\
      {String.intercalate "\n" failures.toList}"
  logInfo "scheduler-footprint census self-test: the shape check decides both ways, a \
    name without the type stays out of the family, and the consumption derivation \
    separates a named footprint from a superseded one"

end SeLe4n.Testing.SchedFootprintCensus
