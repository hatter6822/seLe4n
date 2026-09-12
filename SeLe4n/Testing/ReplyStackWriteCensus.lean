-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
import Lean.Elab.Command
-- Both roots, for the reason the export-commit census records: `SeLe4n` is the
-- production library and `Platform.Staged` pulls the staged modules in beside
-- it.  A writer defined in a module only one of them imports must be visible
-- here, or this census would pass vacuously about it.
import SeLe4n
import SeLe4n.Platform.Staged
-- The chain surface itself: the two cancellation shape modules and the reply
-- dispatch invariant sit outside the staged closure, and their results are what
-- the registry names.
import SeLe4n.Kernel.Lifecycle.Invariant.CancellationReplyShape
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyDispatchInvariant
import SeLe4n.Kernel.IPC.Invariant.FaultPreservation

/-!
# WS-RM RM5.3 — every reply-stack write names a chain result

`v0.35.4` made the reply stack doubly linked, and `donationChainWellFormed` is
the invariant that says the links agree.  What keeps that invariant true is not
the code that maintains it — it is that **the next writer cannot quietly skip
it**, which is exactly how the reply path came to consume a caller's Reply and
leave its frame on the stack: `consumeCallerReply` was called bare, and nothing
asked whether the frame above had been detached first.

The subject is every project definition whose own body **directly writes
reply-stack data**, and the question is which theorem says what that write does
to the chain.  The set is derived from the environment; the registry is
reconciled against it in both directions, so a new write site is a failure here
on the day it is written.

## Why one level rather than the transitive closure

The plan's phrase is "every transition reaching a write of reply-stack data",
and taken transitively that is the whole syscall dispatcher: `dispatchSyscall`
reaches `Reply.consumed` like everything below it.  The frontier this census
uses is the **direct** one — a definition whose own `getUsedConstants` contains
a chain-write primitive — and that loses nothing, because it is closed under
refinement: every path from a composite down to a primitive passes through some
direct site, and that site is in the census.  A new composite that calls
`removeCallerReplyFrame` inherits its chain theorem by composition (which is
what `donationChainFrame`'s algebra is for); a new composite that calls
`consumeCallerReply` *bare* is a new direct site and fails here.

## Why the elaborator and not a scanner

This is a question about which constants a definition's body references, and
`Expr.getUsedConstants` answers it exactly: by the time a declaration is in the
environment its references are resolved constants, and a constant has one
definition.  A text scanner asking it has eleven rounds of review findings
against it in `scripts/check_kernel_entry_exports.py`'s history.

Runs at elaboration: `lake build SeLe4n.Testing.ReplyStackWriteCensus`, wired
into `scripts/test_tier1_build.sh` beside the other environment censuses.
-/

namespace SeLe4n.Testing.ReplyStackWriteCensus

open Lean Elab Command

/-- The primitives that write reply-stack data.

"Reply-stack data" is exactly what `donationChainFrame` quantifies over: a
`Reply`'s `prev` and `next`, a `SchedContext`'s `scReply`, and a `Reply`'s
`caller` in the *clearing* direction (linking a caller cannot falsify the
frame's `callerKept` field; consuming one can).

Each entry writes one of those fields in its own body — this list is a pin on
what the tree contains, and the reconciliation below is what keeps it honest:
a definition that writes a chain field through a helper not listed here is not a
primitive, it is a *site*, and it must appear in the registry. -/
def chainWritePrimitives : List Name :=
  [ -- The caller clear, and the link clear off a frame that heads nothing.
    `SeLe4n.Kernel.Reply.consumed
    -- Its two state-level spellings.  They are primitives rather than sites
    -- because the defect this census exists for is a transition calling one of
    -- them *bare* -- WS-RM's own: the reply leg consumed the answered caller's
    -- Reply and left its frame on the stack.  With them here, any such call is
    -- a site and has to be registered.
  , `SeLe4n.Model.SystemState.consumeReply
  , `SeLe4n.Model.SystemState.consumeCallerReply
    -- The detach: the frame above's `prev`, and its total fold.
  , `SeLe4n.Kernel.detachReplyFrameAbove
  , `SeLe4n.Kernel.detachReplyFrameAboveOrSelf
    -- The push: the new head's two links, and the old head's `next`.
  , `SeLe4n.Kernel.storeDonationFramePush
    -- The pop: the head's two links, the frame below re-headed, and the pair.
  , `SeLe4n.Kernel.storeDonationHeadClear
  , `SeLe4n.Kernel.storeReplyReHead
  , `SeLe4n.Kernel.storeDonationHeadPop ]

/-- `true` for a constant this project defines, auxiliaries and private
manglings included. -/
def isProjectConstant (n : Name) : Bool :=
  n.components.any (· == `SeLe4n)

/-- `true` when `n` is a compiler auxiliary rather than a declaration a
contributor wrote: match arms, equation lemmas, proof terms and the like.  They
inherit their parent's references, so counting them would report one site many
times under names nobody can register. -/
def isAuxiliary (n : Name) : Bool :=
  (n.eraseMacroScopes != n) ||
  n.components.any fun c => match c with
    | .str _ s =>
        "match_".isPrefixOf s || "proof_".isPrefixOf s || "eq_".isPrefixOf s ||
        s == "_sunfold" || s == "_unsafe_rec" || s == "eq_def" || s == "_cstage1" ||
        s == "_cstage2" || s == "noConfusionType" || s == "_proof_1"
    | _ => false

/-- `true` when `n`'s own body directly references any of `targets`. -/
def usesDirectly (env : Environment) (targets : List Name) (n : Name) : Bool :=
  match (env.find? n).bind (·.value? (allowOpaque := true)) with
  | none => false
  | some v => v.getUsedConstants.any (fun c => targets.contains c)

/-- `true` when `n` is a *definition* rather than a proof.  A theorem whose
statement mentions a primitive is a result *about* a write, not a write; and a
`Prop`-valued `def` (this tree has several: predicates, well-formedness
conditions) is a statement too.  Both are excluded, the first structurally and
the second by the type check the caller performs in `MetaM`. -/
def isDefinitionShaped (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.defnInfo _) => true
  | some (.opaqueInfo _) => true
  | _ => false

/-- The derived subject set: every project definition that directly writes
reply-stack data.

The primitives are included — each one writes, so each one owes a chain result
— and auxiliaries and `Prop`-valued definitions are not.  The `Prop` filter is
the caller's, since deciding it needs `MetaM`. -/
def directWriteCandidates (env : Environment) : List Name :=
  env.constants.toList.foldl
    (fun acc (n, _) =>
      if isProjectConstant n && !isAuxiliary n && isDefinitionShaped env n &&
          (chainWritePrimitives.contains n || usesDirectly env chainWritePrimitives n)
      then n :: acc else acc) []

/-! ## What a write site owes

A site either **states** what it does to the chain, or is a **half-step** whose
chain behaviour only exists in the composite that completes it.  Both are
legitimate and the second is not a loophole: a push's first store leaves the
stack with a head whose frame below does not yet point up, so no theorem about
that store alone could say the chain holds, and demanding one would force a
false statement rather than a true one.  What the half-step record costs is the
name of the composite, which must itself be registered as *stating* and must
actually run the half-step. -/
inductive ChainDiscipline where
  /-- The site carries its own chain results.  Each named theorem must mention
  the site and a `donationChain…` form, so the record cannot drift into naming
  a theorem about something else. -/
  | states (results : List Name)
  /-- The site is one store of a multi-store transition: on its own the chain is
  broken by construction.  The composite named here is what re-establishes it,
  and it must be registered `states` and must run this half-step. -/
  | halfStep (composite : Name)
  deriving Inhabited

/-- `true` when `n` names a member of the `donationChain…` family: the invariant,
its relaxed form, the frame, and the walk. -/
def isChainForm (n : Name) : Bool :=
  match n with
  | .str _ s => "donationChain".isPrefixOf s
  | _ => false

/-- The chain results a site may be recorded as stating, and the shape check on
each: a proposition whose statement mentions the site **and** a chain form.

"Mentions" is `Expr.getUsedConstants` over the *type*, so a theorem whose name
suggests a subject it does not actually take is refused — the shape this tree
calls "a name is not a definition". -/
def resultViolations (env : Environment) (site : Name) (result : Name) : List String :=
  match env.find? result with
  | none =>
      [s!"`{site}` names the chain result `{result}`, which is not a declaration of this \
          environment"]
  | some info =>
      let used := info.type.getUsedConstants
      (if used.contains site then [] else
        [s!"`{site}` names the chain result `{result}`, whose statement does not mention \
            `{site}` — a result about some other subject"]) ++
      (if used.any isChainForm then [] else
        [s!"`{site}` names `{result}` as a chain result, but its statement mentions no \
            `donationChain…` form"])

/-! ## The registry

One entry per reply-stack write site.  The **set** is derived from the
environment and reconciled against this list in both directions, so a new site
is a failure here on the day it is written — which is precisely the shape WS-RM
exists to close: the reply leg consumed a caller's Reply with nothing asking
what that did to the frame above it. -/

/-- Every reply-stack write site of this kernel, with what it owes. -/
def chainWriteRegistry : List (Name × ChainDiscipline) :=
  [ -- The field-level clear.  A pure function on a `Reply`, so it has no state
    -- and no chain statement of its own; the store that installs its result is
    -- what the chain results are about.
    (`SeLe4n.Kernel.Reply.consumed, .halfStep `SeLe4n.Model.SystemState.consumeReply)
    -- The store that installs it.  The Reply half of the pair below; nothing in
    -- the tree reasons about it alone, and the chain statements live one level
    -- up where the TCB's inverse link is cleared too.
  , (`SeLe4n.Model.SystemState.consumeReply,
      .halfStep `SeLe4n.Model.SystemState.consumeCallerReply)
    -- The TCB-and-Reply pair.  Its two cases are the whole of WS-RM's reason
    -- for existing: off a head the chain survives; *at* a head the consumed
    -- frame keeps its links and `Reply.wellFormed` is relaxed at that one key
    -- until the donation pop takes it off.
  , (`SeLe4n.Model.SystemState.consumeCallerReply,
      .states [`SeLe4n.Kernel.consumeCallerReply_preserves_donationChainWellFormed,
               `SeLe4n.Kernel.consumeCallerReply_head_preserves_donationChainWellFormedExcept])
    -- seL4's `reply_remove`: the detach, then the unlink.  This is the step both
    -- reply spines run, and the one a new reply path must call rather than
    -- reaching for the consume.
  , (`SeLe4n.Kernel.removeCallerReplyFrame,
      .states [`SeLe4n.Kernel.removeCallerReplyFrame_preserves_donationChainWellFormed,
               `SeLe4n.Kernel.removeCallerReplyFrame_head_preserves_donationChainWellFormedExcept])
    -- The detach itself, its total fold, and the thread-keyed wrapper the
    -- cancellation path runs.
  , (`SeLe4n.Kernel.detachReplyFrameAbove,
      .states [`SeLe4n.Kernel.detachReplyFrameAbove_preserves_donationChainWellFormed])
  , (`SeLe4n.Kernel.detachReplyFrameAboveOrSelf,
      .states [`SeLe4n.Kernel.detachReplyFrameAboveOrSelf_preserves_donationChainWellFormed])
  , (`SeLe4n.Kernel.detachFrameAboveThreadReply,
      .states [`SeLe4n.Kernel.detachFrameAboveThreadReply_preserves_donationChainWellFormed])
    -- The teardown's TCB-side clear.
  , (`SeLe4n.Kernel.Lifecycle.Suspend.clearReplyObjectCaller,
      .states [`SeLe4n.Kernel.clearReplyObjectCaller_preserves_donationChainWellFormed])
    -- The push's second store: the new head's links and the old head's `next`.
    -- Between the two stores the context's head names a frame that does not yet
    -- answer it, so the chain is broken by construction here.
  , (`SeLe4n.Kernel.storeDonationFramePush, .halfStep `SeLe4n.Kernel.donateSchedContext)
  , (`SeLe4n.Kernel.donateSchedContext,
      .states [`SeLe4n.Kernel.donateSchedContext_preserves_donationChainWellFormed])
    -- The pop's three stores, and the pair that composes the first two.
  , (`SeLe4n.Kernel.storeDonationHeadClear, .halfStep `SeLe4n.Kernel.storeDonationHeadPop)
  , (`SeLe4n.Kernel.storeReplyReHead, .halfStep `SeLe4n.Kernel.storeDonationHeadPop)
  , (`SeLe4n.Kernel.storeDonationHeadPop, .halfStep `SeLe4n.Kernel.returnDonatedSchedContext)
  , (`SeLe4n.Kernel.returnDonatedSchedContext,
      .states [`SeLe4n.Kernel.returnDonatedSchedContext_preserves_donationChainWellFormed,
               `SeLe4n.Kernel.returnDonatedSchedContext_preserves_donationChainWellFormed_of_except]) ]

/-- Follow a chain of `halfStep` records to the entry that states something.

A half-step of a half-step is legitimate — the pop's head clear is one store of
`storeDonationHeadPop`, which is itself one store of the donation return — so
the requirement is that the chain **terminates in a `states` entry**, not that
the immediate composite is one.  Fuel-bounded, and exhaustion answers `false`,
which makes a cycle of half-step records a violation rather than a hang: a
record that closes on itself covers nothing.

`registry` is a parameter so the resolution is a pure function over a list and
can be self-tested on synthetic registries below. -/
def halfStepResolves (registry : List (Name × ChainDiscipline)) (composite : Name) : Bool :=
  go composite registry.length
where
  go (n : Name) (fuel : Nat) : Bool :=
    match fuel with
    | 0 => false
    | fuel' + 1 =>
      match registry.find? (fun (m, _) => m == n) with
      | none => false
      | some (_, .states _) => true
      | some (_, .halfStep next) => go next fuel'

/-- Why a registry entry does not hold up; `[]` when it does. -/
def disciplineViolations (env : Environment) (registry : List (Name × ChainDiscipline))
    (site : Name) (d : ChainDiscipline) : List String :=
  match d with
  | .states results =>
      if results.isEmpty then
        [s!"`{site}` is recorded as stating its chain behaviour and names no result"]
      else results.flatMap (resultViolations env site)
  | .halfStep composite =>
      (if halfStepResolves registry composite then [] else
        [s!"`{site}` is recorded as a half-step of `{composite}`, and following the \
            half-step records from there reaches no entry that states a chain result — a \
            half-step whose composite states nothing is a write nothing covers"]) ++
      (if usesDirectly env [site] composite then [] else
        [s!"`{site}` is recorded as a half-step of `{composite}`, whose body does not run \
            it — the record names a composite that does not complete this write"])

/-- Where the derived set of write sites and the registry disagree; `[]` when
they are the same set.

**Both directions.**  An *unregistered* site is the dangerous one: a new
definition that writes reply-stack data and is nowhere here has joined the tree
with nothing saying what it does to the chain.  A *stale* entry is the other:
this list is the project's statement of where chain data is written, and one
naming a definition that no longer writes it says the surface is wider than it
is.

Pure, over two lists, so the reconciliation is self-tested on synthetic inputs
below. -/
def reconciliationViolations (derived recorded : List Name) : List String :=
  let unregistered := derived.filter (fun n => !recorded.contains n)
  let stale := recorded.filter (fun n => !derived.contains n)
  (if unregistered.isEmpty then [] else
    [s!"{unregistered.length} reply-stack write site(s) are not registered ({unregistered}).  \
        Every definition that writes a `Reply`'s stack links, a `SchedContext`'s stack head, \
        or clears a `Reply`'s caller either states what it does to the donation chain or is \
        recorded as a half-step of the composite that does"]) ++
  (if stale.isEmpty then [] else
    [s!"{stale.length} registry entr(ies) name definitions that do not write reply-stack \
        data ({stale}) — this list is what the chain surface is read off, so a stale entry \
        overstates it"])

/-! ## Witnesses

A census that accepted everything would read exactly like a passing one.  These
are ordinary private declarations held against the same predicates the registry
entries are.  The derived half is exercised in place — unlike the export census,
planting a write site here costs nothing, since a `def` emits no symbol. -/

/-- **The bare consume the plan asks this gate to catch**: a transition that
clears a caller's Reply link with no detach anywhere in it.  This is WS-RM's own
defect, in miniature. -/
private def censusWitnessBareConsume (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) :
    SeLe4n.Model.Kernel Unit :=
  SeLe4n.Model.SystemState.consumeCallerReply caller rid

/-- Writes no reply-stack data: reads a Reply and returns. -/
private def censusWitnessNoWrite (st : SeLe4n.Model.SystemState) (rid : SeLe4n.ReplyId) :
    Option SeLe4n.Kernel.Reply :=
  st.getReply? rid

run_cmd Command.liftTermElabM do
  let env ← getEnv
  -- The production root must be in this environment, or a site defined in a
  -- module only it imports would read as absent and the census would be silent
  -- about exactly the declarations a kernel image contains.
  unless env.header.moduleNames.contains `SeLe4n do
    throwError "reply-stack write census: the production library root `SeLe4n` is not in \
      this environment, so a write site defined in a module only it imports would read as \
      absent"
  -- The primitives exist.  A census whose primitive names had been renamed would
  -- classify every definition as writing nothing and pass.
  for n in chainWritePrimitives do
    unless (env.find? n).isSome do
      throwError "reply-stack write census: `{n}` is not a declaration of this environment, \
        so the property this census decides does not exist"
  -- Witnesses, both directions.
  unless usesDirectly env chainWritePrimitives ``censusWitnessBareConsume do
    throwError "reply-stack write census: the BARE CONSUME witness is not seen to write \
      reply-stack data — the gate does not detect the shape it exists for"
  if usesDirectly env chainWritePrimitives ``censusWitnessNoWrite then
    throwError "reply-stack write census: a definition that only reads a Reply is seen to \
      write reply-stack data"
  -- The result-shape check refuses a theorem about another subject, and one
  -- that says nothing about the chain.
  unless (resultViolations env `SeLe4n.Kernel.removeCallerReplyFrame
      `SeLe4n.Kernel.removeCallerReplyFrame_preserves_donationChainWellFormed).isEmpty do
    throwError "reply-stack write census: a genuine chain result was refused"
  if (resultViolations env `SeLe4n.Kernel.removeCallerReplyFrame
      `SeLe4n.Kernel.removeCallerReplyFrame_isOk).isEmpty then
    throwError "reply-stack write census: a result that mentions the site but no \
      `donationChain…` form was accepted as a chain result"
  if (resultViolations env `SeLe4n.Kernel.removeCallerReplyFrame
      `SeLe4n.Kernel.donateSchedContext_preserves_donationChainWellFormed).isEmpty then
    throwError "reply-stack write census: a chain result about a DIFFERENT site was \
      accepted — a name is not a subject"
  if (resultViolations env `SeLe4n.Kernel.removeCallerReplyFrame
      `SeLe4n.Kernel.thisDeclarationDoesNotExist).isEmpty then
    throwError "reply-stack write census: a result that is not a declaration was accepted"
  -- The half-step check refuses a composite that does not run the half-step,
  -- and one that states nothing itself.
  unless (disciplineViolations env chainWriteRegistry `SeLe4n.Kernel.storeDonationHeadClear
      (.halfStep `SeLe4n.Kernel.storeDonationHeadPop)).isEmpty do
    throwError "reply-stack write census: a genuine half-step record was refused"
  if (disciplineViolations env chainWriteRegistry `SeLe4n.Kernel.storeDonationHeadClear
      (.halfStep `SeLe4n.Kernel.donateSchedContext)).isEmpty then
    throwError "reply-stack write census: a half-step recorded under a composite that does \
      not run it was accepted"
  if (disciplineViolations env chainWriteRegistry `SeLe4n.Kernel.removeCallerReplyFrame
      (.states [])).isEmpty then
    throwError "reply-stack write census: a `states` record naming no result was accepted"
  -- The half-step resolution, on synthetic registries: a chain that reaches a
  -- stating entry resolves; one that closes on itself, one that runs off the
  -- end of the registry, and one that is not registered at all do not.
  unless halfStepResolves [(`a, .halfStep `b), (`b, .states [`t])] `a do
    throwError "reply-stack write census: a half-step chain reaching a stating entry was \
      not resolved"
  if halfStepResolves [(`a, .halfStep `b), (`b, .halfStep `a)] `a then
    throwError "reply-stack write census: a CYCLE of half-step records resolved — the \
      records would close on nothing"
  if halfStepResolves [(`a, .halfStep `b)] `a then
    throwError "reply-stack write census: a half-step chain running off the end of the \
      registry resolved"
  if halfStepResolves [(`b, .states [`t])] `a then
    throwError "reply-stack write census: an unregistered composite resolved"
  -- The reconciliation, on synthetic inputs.
  unless (reconciliationViolations [`a, `b] [`a, `b]).isEmpty do
    throwError "reply-stack write census: agreeing derived/registry sets were reported as \
      disagreeing"
  if (reconciliationViolations [`a, `b] [`a]).isEmpty then
    throwError "reply-stack write census: an UNREGISTERED write site was accepted — the \
      shape this gate exists to catch"
  if (reconciliationViolations [`a] [`a, `b]).isEmpty then
    throwError "reply-stack write census: a stale registry entry was accepted"
  unless (reconciliationViolations [] []).isEmpty do
    throwError "reply-stack write census: two empty sets were reported as disagreeing"
  -- The census.  The set is derived; the registry is reconciled against it in
  -- both directions; the witnesses above are excluded by name, since they are
  -- planted write sites rather than kernel ones.
  let witnesses : List Name := [``censusWitnessBareConsume]
  let mut derived : List Name := []
  for n in directWriteCandidates env do
    if witnesses.contains n then continue
    let some info := env.find? n | continue
    if (← Meta.isProp info.type) then continue
    derived := n :: derived
  let recorded : List Name := chainWriteRegistry.map (·.1)
  let mismatches := reconciliationViolations derived recorded
  unless mismatches.isEmpty do
    throwError "reply-stack write census: {mismatches}"
  for (n, d) in chainWriteRegistry do
    let violations := disciplineViolations env chainWriteRegistry n d
    unless violations.isEmpty do
      throwError "reply-stack write census: {violations}"
  let stating := chainWriteRegistry.filter
    (fun (_, d) => match d with | .states _ => true | .halfStep _ => false)
  logInfo m!"reply-stack write census: {derived.length} write sites, {stating.length} of \
    them stating their own chain result; the rest are half-steps of a composite that does"

end SeLe4n.Testing.ReplyStackWriteCensus
