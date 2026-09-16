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
-- The frozen execution surface.  Until `v0.35.60` neither root reached it -- it
-- was built by its own `lean_exe` target (`tests.FrozenOpsSuite`) and was in
-- neither staged allowlist -- which is why this census had to be widened by hand
-- at `v0.35.12`, after a defect had already shipped through the hole; it is in
-- `SeLe4n.lean` now, so the import below is the root's rather than this file's
-- alone.  `FrozenKernelObject.reply` carries the **live**
-- `SeLe4n.Kernel.Reply` — links and all — and `Model.freeze` copies a live
-- state's Reply objects verbatim, so a frozen state taken mid-call-chain holds
-- a real reply stack and a frozen transition can falsify the chain exactly as a
-- live one can.  Without this import the census's claim held for every module
-- except the one that had the defect.
import SeLe4n.Kernel.FrozenOps.Operations

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

/-- The environment name of a `private def`.

Lean mangles one to `_private.<Module>.0.<userName>`, and **no name literal can
spell that**: a numeric component is not an identifier, so `` `_private.M.0.f ``
is a parse error.  This calls Lean's own `mkPrivateNameCore`, so the registry
names a private declaration exactly rather than through a resemblance, and the
mangling cannot drift away from the compiler's.

A wrong module here is not silent: the name matches no candidate, and the
reconciliation reports it as a stale entry. -/
def privateIn (mod user : Name) : Name := Lean.mkPrivateNameCore mod user

/-- The primitives that write reply-stack data.

"Reply-stack data" is exactly what `donationChainFrame` quantifies over: a
`Reply`'s `prev` and `next`, a `SchedContext`'s `scReply`, and a `Reply`'s
`caller` in the *clearing* direction (linking a caller cannot falsify the
frame's `callerKept` field; consuming one can).

Each entry writes one of those fields in its own body.  This list is a **pin**,
not the derivation: what keeps it honest is `primitiveCoverageViolations` below,
which derives the candidate frontier from what the code does — a definition that
constructs a `Reply` or a `SchedContext` record *and* reaches a store — and
requires every candidate to be a primitive, a registered site, or a member of
`chainNeutralConstructors` with a stated reason.

Without that, this list would be an enumeration standing in for a derivation:
`storeObject` takes a whole `KernelObject`, so a definition writing
`{ r with next := … }` directly, calling none of the nine names here, would be
invisible to this census and to the registry it drives. -/
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
    -- The removal: the composed store step (WS-HP HP6.3 -- the frame above's
    -- `prev`, the frame below's `next`, and the cut frame's own unlink), the
    -- validated operation over it, and its total fold.  The store step is a
    -- primitive for the same reason the pop's two component stores are: it
    -- performs the writes with none of `spliceReplyFrameOut`'s resolution or
    -- validation, so a transition reaching for it directly is a site.
  , `SeLe4n.Kernel.spliceReplyFrameStores
  , `SeLe4n.Kernel.spliceReplyFrameOut
  , `SeLe4n.Kernel.spliceReplyFrameOutOrSelf
    -- ...and the frozen surface's counterparts, which write the same field of
    -- the same `SeLe4n.Kernel.Reply` record in `FrozenSystemState.objects`.
    -- **WS-HP HP8.1** renamed these for the operation they became: the frozen
    -- removal splices rather than severing, so the store step is a third entry
    -- beside the two it composes, exactly as the live `spliceReplyFrameStores`
    -- is.
  , `SeLe4n.Kernel.FrozenOps.frozenSpliceReplyFrameStores
  , `SeLe4n.Kernel.FrozenOps.frozenSpliceReplyFrameOut
  , `SeLe4n.Kernel.FrozenOps.frozenSpliceReplyFrameOutOrSelf
    -- The push: the new head's two links, and the old head's `next`.
  , `SeLe4n.Kernel.storeDonationFramePush
    -- The pop: the head's two links, the frame below re-headed, and the pair.
  , `SeLe4n.Kernel.storeDonationHeadClear
  , `SeLe4n.Kernel.storeReplyReHead
  , `SeLe4n.Kernel.storeDonationHeadPop ]

/-- The record constructors a chain write has to go through.

`storeObject` takes a whole `KernelObject`, so the only way to change a
`Reply`'s links or a `SchedContext`'s stack head is to *build* one of those
records — a `{ r with … }` update elaborates to the constructor like any other
application.  That makes "constructs one of these" the derivable half of the
frontier, where a helper's *name* is not. -/
def chainRecordConstructors : List Name :=
  [ `SeLe4n.Kernel.Reply.mk, `SeLe4n.Kernel.SchedContext.mk ]

/-- The **table-level** writes: the only way a built record becomes state.

`SystemState.objects` is an `RHTable` and `FrozenSystemState.objects` a
`FrozenMap`, so every store in the tree — named helper or open-coded record
update — ends at one of these two.  They are the derivable half of the store
question, where a helper's *name* is not. -/
def objectStorePrimitives : List Name :=
  [ `SeLe4n.Kernel.RobinHood.RHTable.insert
  , `SeLe4n.Model.FrozenMap.set ]

/-- The project helpers that wrap them.

**A pin, not an enumeration** (PR #895 review round 7).  This list used to be
the whole answer, and it named the FROZEN primitive (`FrozenMap.set`) while
omitting the LIVE one: a definition writing
`{ st with objects := st.objects.insert rid.toObjId (.reply r) }` — which is how
`Lifecycle/Suspend.lean` writes a consumed Reply — stored a chain-bearing record
through a spelling the derivation did not know, so it was in neither candidate
set.  That is precisely the defect this PR corrected on the READ side in round 1
(*a spelling is not a read*, `objects[k]?` versus `objects.get? k`), on the same
two tables, in the opposite direction, and the sweep the rule calls for was not
run.

They are kept because they buy the frontier a level: `storesObject` reaches one
hop, so with the primitives alone a caller of `storeObject` is recognised and a
caller of *that* is not.  Each is reconciled against the derivation by
`objectStoreHelpers_reach_primitives` in the `run_cmd` below, so a helper that
stops reaching a primitive is a stale pin rather than a silent narrowing. -/
def objectStoreHelpers : List Name :=
  [ `SeLe4n.Model.storeObject
    -- The capacity guard and the kind guard, each a wrapper over `storeObject`.
    -- `storeObjectChecked` was absent from this list and
    -- `SeLe4n.Model.SystemState.storeObject` — which names no declaration at
    -- all — was in it: a dead entry contributing nothing beside a live helper
    -- nobody had noticed, both found the moment the pin below was written,
    -- which is the argument for the pin.
  , `SeLe4n.Model.storeObjectChecked
  , `SeLe4n.Model.storeObjectKindChecked
    -- The frozen surface's own store.  It lands a built record in
    -- `FrozenSystemState.objects`, which is where the frozen chain lives, so a
    -- derivation that knows only the live spellings sees a frozen writer build
    -- a `Reply` and store it nowhere.
  , `SeLe4n.Kernel.FrozenOps.frozenStoreObject ]

/-- The stores a built record has to reach to become state. -/
def objectStoreSpellings : List Name :=
  objectStorePrimitives ++ objectStoreHelpers

/-- Definitions that build a chain-bearing record and store it, and yet write no
chain field — each with the reason, which is a property of the code rather than
a convention.

The derivation over-approximates on purpose: it cannot see *which* fields a
record update changes, so a definition rebuilding a `SchedContext` to set its
budget looks exactly like one rebuilding it to re-head its stack.  Narrowing
that in the scanner would mean reading the term's field assignments, which is
the analysis-instead-of-contract shape this project has retired twice.  Stating
the reason here is the contract, and adding an entry is a reviewed act. -/
def chainNeutralConstructors : List (Name × String) :=
  [ -- `caller` only, and only on a Reply the `isFree` guard has proved carries
    -- no link in either direction.  Linking a caller cannot falsify a chain
    -- clause (`Reply.wellFormed`'s antecedent becomes false, and the walk reads
    -- `prev` / `next` / `scReply`), and the guard is what makes that structural
    -- rather than incidental.
    (`SeLe4n.Model.SystemState.linkReply,
      "writes `Reply.caller` only, gated on `Reply.isFree` — no link in either direction")
    -- A `{ sc with budget := …, period := …, … }` update: `scReply` is not in
    -- the assignment list, so the stored record carries the value it read.
  , (`SeLe4n.Kernel.SchedContextOps.schedContextConfigure,
      "rebuilds a SchedContext for its CBS parameters; `scReply` is untouched by the update")
    -- The frozen surface's counterparts of the two shapes above.  Each is the
    -- frozen twin of a live definition already exempt for the same reason, so
    -- these are not a new judgement — they are the existing one applied to the
    -- surface this census could not see before `v0.35.12`.
  , (`SeLe4n.Kernel.FrozenOps.frozenLinkCallerReply,
      "writes `Reply.caller` only, gated on `Reply.isFree` — no link in either direction; the frozen twin of `Model.linkReply`, and reading the same guard since `v0.35.12` (it read `caller` alone, so a frame still on a live stack was linkable here while the live kernel refuses it)")
  , (`SeLe4n.Kernel.FrozenOps.frozenSchedContextConfigure,
      "rebuilds a SchedContext for its CBS parameters; `scReply` is not in the assignment list, so the stored record carries the value it read")
  , (`SeLe4n.Kernel.FrozenOps.frozenSchedContextBind,
      "`{ sc with boundThread := some _ }`; `scReply` is untouched by the update")
    -- **WS-HP HP10.5**: the destroy path's reservation-origin scrub.  It is a
    -- `{ sc with donationOrigin := none }` update and nothing else, on the
    -- contexts whose origin names the thread being destroyed — `scReply` is not
    -- in the assignment list, so the stored record carries the stack head it
    -- read.  The census found this on the day the sweep landed, which is the
    -- derivation working: a fold that rebuilds a `SchedContext` and stores it is
    -- indistinguishable from one re-heading a stack until somebody says which.
  , (`SeLe4n.Kernel.clearDonationOriginReferences,
      "`{ sc with donationOrigin := none }` on the destroy path; `scReply` is untouched by the update")
  , (`SeLe4n.Kernel.FrozenOps.frozenSchedContextUnbind,
      "`{ sc with boundThread := none, isActive := false }`; `scReply` is untouched")
  , (`SeLe4n.Kernel.FrozenOps.frozenSetPriority,
      "`{ sc with priority := _ }` on the bound SchedContext; `scReply` is untouched")
  , (`SeLe4n.Kernel.FrozenOps.frozenTimerTickBudget,
      "rebuilds a SchedContext for its budget accounting; `scReply` is untouched")
    -- ---------------------------------------------------------------------
    -- Reached through a helper, which is what the frontier started following
    -- at `v0.35.13`.  Each of these composes `Model.linkReply` and touches no
    -- other chain field itself, so each is neutral for the reason that one is
    -- — and each has to say so, because the frontier now sees them.
  , (`SeLe4n.Model.SystemState.linkCallerReply,
      "`linkReply` (caller only, gated on `Reply.isFree`) plus the caller TCB's `replyObject`, which is not chain data")
  , (`SeLe4n.Model.SystemState.linkServerStashedReply,
      "`linkCallerReply` plus the server TCB's `pendingReceiveReply`; no chain field")
  , (`SeLe4n.Kernel.endpointReceiveDual,
      "links a dequeued caller through `linkCallerReply`; writes no chain field itself")
  , (`SeLe4n.Kernel.endpointReceiveDualOnCore,
      "the per-core spelling of the same receive; same reason")
    -- ---------------------------------------------------------------------
    -- Inventories of THEOREMS.  Their values embed theorem statements, and a
    -- statement about `storeObject` mentions `storeObject` — so they reach both
    -- halves of the frontier while performing no store at all.  Specification
    -- vocabulary, like the theorems they list.
  , (`SeLe4n.Kernel.kernelOperationPerCoreNiTheorem,
      "an inventory of non-interference theorem statements; performs no store")
  , (`SeLe4n.Kernel.perCoreInvariantSuiteTheorems,
      "an inventory of per-core invariant theorem statements; performs no store")
    -- ---------------------------------------------------------------------
    -- Reached through the RAW table write, which the frontier started seeing at
    -- `v0.35.20`.  `objectStoreSpellings` named four helpers and the FROZEN
    -- primitive while omitting the LIVE one, so every definition that writes
    -- `{ st with objects := st.objects.insert … }` — the spelling most of the
    -- kernel's SchedContext updates use — was in neither derivation.  Each of
    -- these builds a `SchedContext` (or, for the payoff witnesses, a fresh
    -- `Reply`) whose chain fields it does not name; the assignment list is the
    -- reason, and it is checkable by reading the update.
  , (`SeLe4n.Kernel.SchedContextOps.schedContextBind,
      "`{ sc with boundThread := some _ }`; reads `sc.scReply` as the bind guard and assigns it nowhere")
  , (`SeLe4n.Kernel.SchedContextOps.schedContextUnbind,
      "`{ sc with boundThread := none, isActive := false }`; `scReply` is untouched")
  , (`SeLe4n.Kernel.SchedContextOps.schedContextYieldTo,
      "rebuilds both SchedContexts for their budget accounting; `scReply` is in neither assignment list")
  , (`SeLe4n.Kernel.SchedContext.PriorityManagement.updatePrioritySource,
      "`{ sc with priority := _ }` or `{ tcb with priority := _ }`; `scReply` is untouched")
  , (`SeLe4n.Kernel.SchedContext.PriorityManagement.setMCPriorityOp,
      "`{ targetTcb with maxControlledPriority := _ }`; writes no SchedContext field at all")
  , (`SeLe4n.Kernel.SchedContext.PriorityManagement.setMCPriorityOnCore,
      "the per-core spelling of the same MCP write; same reason")
  , (`SeLe4n.Kernel.timerTickBudget,
      "`{ sc with budgetRemaining := _, … }` plus the TCB's time slice; `scReply` is untouched")
  , (`SeLe4n.Kernel.timerTickBudgetOnCore,
      "the per-core spelling of the same budget accounting; same reason")
  , (`SeLe4n.Kernel.refillSchedContext,
      "rebuilds a SchedContext for its replenishment; `scReply` is untouched")
  , (`SeLe4n.Kernel.handleYieldWithBudget,
      "`{ sc with budgetRemaining := Budget.zero, isActive := false }`; `scReply` is untouched")
  , (`SeLe4n.Kernel.Lifecycle.Suspend.cancelBoundDonation,
      "`{ sc with boundThread := none, isActive := false }` and the TCB's `schedContextBinding`; the binding graph, not the stack")
  , (`SeLe4n.Kernel.cancelBoundDonationOnCore,
      "the per-core spelling of the same binding cancel; same reason")
  , (`SeLe4n.Kernel.Lifecycle.Suspend.suspendThread,
      "composes `consumeReplyLink`, which is registered; writes no chain field in its own body")
  , (`SeLe4n.Kernel.Lifecycle.Suspend.suspendThreadOnCore,
      "the per-core spelling of the same suspend; same reason")
  , (`SeLe4n.Kernel.Liveness.stepPost,
      "the scheduler trace model's step: a SchedContext budget update and a replenish queue; no chain field")
    -- The dispatch payoff's pack-inhabitation witnesses.  They build a fresh
    -- `Reply` (every link `none`) and a `SchedContext` whose only assignment is
    -- `boundThread`, so they construct chain-bearing records and set no chain
    -- field.  Named as the environment holds them, because a `private def` is
    -- mangled and this census matches exact constants rather than resemblances.
  , (privateIn `SeLe4n.Kernel.IPC.Invariant.DispatchPayoff `SeLe4n.Kernel.witnessSt2,
      "stores `{ witnessScFresh with … }`, whose assignment list is `boundThread`; no chain field")
  , (privateIn `SeLe4n.Kernel.IPC.Invariant.DispatchPayoff `SeLe4n.Kernel.witnessSt3,
      "stores the bound TCB and SchedContext; `scReply` is in neither assignment list")
  , (privateIn `SeLe4n.Kernel.IPC.Invariant.DispatchPayoff `SeLe4n.Kernel.witnessSt4,
      "stores `{ replyId := witnessReplyId }` — a fresh Reply, every link `none`") ]

/-- Where the derived frontier and the primitive list disagree.

A candidate — a project definition that builds a chain-bearing record and
reaches a store — must be a primitive, a registered write site, or carry a
stated reason in `chainNeutralConstructors`.  Anything else is a definition that
can write chain data with nothing saying what it does to the chain, which is the
one thing this census exists to make impossible.

Also reconciles `chainNeutralConstructors` in the other direction: an entry that
is no longer a candidate is a stale exemption, and a stale exemption reads like
coverage. -/
def primitiveCoverageViolations (candidates recorded : List Name)
    (neutral : List (Name × String)) : List String :=
  let neutralNames := neutral.map (·.1)
  let uncovered := candidates.filter fun n =>
    !(chainWritePrimitives.contains n) && !(recorded.contains n) &&
      !(neutralNames.contains n)
  let staleNeutral := neutralNames.filter fun n => !(candidates.contains n)
  (if uncovered.isEmpty then [] else
    [s!"{uncovered.length} definition(s) build a `Reply` or `SchedContext` record and store \
        it, and are neither a chain-write primitive, nor a registered write site, nor a \
        stated chain-neutral constructor ({uncovered}).  A definition that can write \
        `Reply.prev` / `Reply.next` / `Reply.caller` or `SchedContext.scReply` through a \
        record update is a write site whatever helper it does or does not call"]) ++
  (if staleNeutral.isEmpty then [] else
    [s!"{staleNeutral.length} chain-neutral exemption(s) name definitions that no longer \
        build a chain-bearing record and store it ({staleNeutral}) — a stale exemption \
        reads like coverage"])

/-- `true` for a constant this project defines, auxiliaries and private
manglings included. -/
def isProjectConstant (n : Name) : Bool :=
  n.components.any (· == `SeLe4n)

/-- `true` when `n` is a compiler auxiliary rather than a declaration a
contributor wrote: matchers, recursors and macro-scoped constants.  They inherit
their parent's references, so counting them would report one site many times
under names nobody can register.

**Asked of the environment, and of nothing else** (PR #895 review round 4).  Two
earlier cuts decided this by NAME — first `"eq_".isPrefixOf`, then the prefix
plus a numeral — and both are spellings a contributor can write: `eq_clearReply`
is an ordinary name, and so is `eq_1`.  A writer named either way was filtered
out of both derivations *before* its constants were read, so it could consume a
caller's Reply and never enter the registry while the reconciliation stayed
clean.  Narrowing a resemblance produces a smaller resemblance, not a relation.

`Meta.isMatcherCore` is the environment's own answer for matchers and is pure,
which is what the previous cut's comment said it was not; with it consulted, the
whole name list is **redundant** rather than merely narrower.  Measured on this
environment rather than argued: of the project constants that are definition-
shaped, non-`Prop` and reference a chain primitive, the number kept only by a
name test is **zero**, so `isGeneratedComponent` was deleted instead of being
narrowed a third time.  Equation and proof auxiliaries need no test at all —
every one of the 5185 in this environment is `Prop`-typed, and `isDefinitionShaped`
plus the caller's `Meta.isProp` filter exclude them structurally.

**Not `Name.isInternal` and not `Name.isInternalDetail`**: the first is true of
the `_private.…` mangling, so it would have excluded every `private def` in the
kernel — a silent narrowing of exactly the kind this census exists to prevent,
introduced by the fix for one — and the second is itself a prefix test over
`match_` / `proof_` / `eq_`, which is the defect this rewrite removes. -/
def isAuxiliary (env : Environment) (n : Name) : Bool :=
  (n.eraseMacroScopes != n) ||
  isAuxRecursor env n || isRecCore env n || Meta.isMatcherCore env n

/-- `true` when `n`'s own body directly references any of `targets`. -/
def usesDirectly (env : Environment) (targets : List Name) (n : Name) : Bool :=
  match (env.find? n).bind (·.value? (allowOpaque := true)) with
  | none => false
  | some v => v.getUsedConstants.any (fun c => targets.contains c)

/-- `true` when `n` stores a kernel object — directly, or by handing a record it
built to a project helper that stores it.

**One derived hop, and the frontier is stated rather than implied** (PR #895
review round 3).  The store half used to be `usesDirectly` alone, so a writer
that constructs `.reply { r with prev := none }` and passes it to a generic
helper was absent from the candidates: the caller builds the record and never
stores, the helper stores and cannot see the constructor it was handed.  Neither
entered the registry, and a reply-stack mutation went unrecorded.

The remedy is deliberately **bounded** rather than transitive.  "Which
definitions write the reply stack" is a property of what a program *does*, and
nothing in the environment answers that — chasing stores transitively makes
every IPC composite a candidate, which is the frontier this census deliberately
stops at (a composite inherits its chain result by `donationChainFrame`'s
algebra).  Measured rather than assumed: pairing this with the *transitive*
constructor half reports 22 composites — `endpointCall`, `endpointReply`,
`dispatchWithCap` among them.

So **each disjunct of the frontier has one direct side**, which is what keeps a
composite out: it builds no chain record in its own body.  A candidate either
reaches a constructor through helpers and stores *directly* (the existing rule,
which catches a delegated `clearPrev`), or constructs *directly* and stores
through one hop (the shape reported here).  A deeper delegation on both sides at
once is outside the frontier, and `chainWriteFrontier` is printed beside the site
count by the `run_cmd` below rather than leaving the number to read as a proof of
absence. -/
def storesVia (env : Environment) (targets : List Name) (n : Name) : Bool :=
  usesDirectly env targets n ||
  (match (env.find? n).bind (·.value? (allowOpaque := true)) with
   | none => false
   | some v => v.getUsedConstants.any fun c =>
       isProjectConstant c && usesDirectly env targets c)

/-- The frontier's store half, over every spelling. -/
def storesObject (env : Environment) (n : Name) : Bool :=
  storesVia env objectStoreSpellings n

/-- What the store half of the frontier recognises, printed beside the count. -/
def chainWriteFrontier : String :=
  "a chain record reached through helpers and stored directly, or built \
directly and stored through one helper hop; delegating BOTH halves at once is \
outside the recognised frontier"

/-- `true` when `n` is a *definition* rather than a proof.

A theorem whose statement mentions a primitive is a result *about* a write, not
a write, and is excluded here structurally.  The caller's `Meta.isProp` check
excludes the other shape a proof takes — a proof written with `def`, whose
**type is** a proposition.

It does **not** exclude a *predicate*: `def p : SystemState → Prop` has type
`SystemState → Prop`, which is a `Type` rather than a `Prop`, so `Meta.isProp`
answers `false` for it.  That is the safe direction — such a definition would be
reported as an unregistered write site rather than silently skipped — and the
tree currently contains none, since the census's own reconciliation passes.  A
predicate written in terms of a chain-write primitive would therefore fail this
gate and want an explicit decision, not a silent pass. -/
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
      if isProjectConstant n && !isAuxiliary env n && isDefinitionShaped env n &&
          (chainWritePrimitives.contains n || usesDirectly env chainWritePrimitives n)
      then n :: acc else acc) []

/-- `true` when `n` builds a chain-bearing record in its **own** body.

The direct half of the frontier's second disjunct: a composite calls a helper
that constructs, and so is excluded here, which is what keeps the candidate set
to the sites rather than the call graph above them. -/
def constructsChainRecord (env : Environment) (n : Name) : Bool :=
  usesDirectly env chainRecordConstructors n

/-- `true` when `n` reaches a chain-bearing record constructor — in its own
body, or through any chain of project definitions it calls.

**Through helpers, because a conjunction over one body is not the question.**
The frontier asks "does this definition build a chain record *and* store it",
and an earlier cut asked both halves of `n` itself.  A writer that delegates the
update splits the conjunction and defeats both: `clearPrev r` returns
`{ r with prev := none }` and uses no store, while the caller passes
`.reply (clearPrev r)` to `storeObject` and names no constructor.  Neither is a
candidate, so the write lands with no chain result — the one thing this census
exists to make impossible.

Walked **backwards from the storing definitions** and memoised, rather than as a
forward fixed point over the whole environment: nearly every definition in the
tree reaches a constructor eventually, so the forward closure is both expensive
and uninformative.  What makes the frontier small is that its partner half stays
direct — see `storesObject` for why each disjunct pairs a transitive side with a
direct one. -/
partial def reachesChainConstructor (env : Environment)
    (seen : Std.HashSet Name) (n : Name) : Bool × Std.HashSet Name :=
  if seen.contains n then (false, seen) else
  let seen := seen.insert n
  match (env.find? n).bind (·.value? (allowOpaque := true)) with
  | none => (false, seen)
  | some v =>
    let used := v.getUsedConstants
    if used.any (fun c => chainRecordConstructors.contains c) then (true, seen)
    else
      used.foldl (fun (acc : Bool × Std.HashSet Name) c =>
        if acc.1 then acc
        else if isProjectConstant c then reachesChainConstructor env acc.2 c
        else acc) (false, seen)

/-- The derived candidate frontier for the primitive list: every project
definition that stores, and that reaches a chain-bearing record constructor.

Deliberately over-approximating — it sees *that* a record was built, not which
of its fields moved, and it follows calls rather than values — so it fails
closed: a definition it cannot classify is reported rather than skipped. -/
def recordConstructingStoreCandidates (env : Environment) : List Name :=
  env.constants.toList.foldl
    (fun acc (n, _) =>
      if isProjectConstant n && !isAuxiliary env n && isDefinitionShaped env n &&
          ((usesDirectly env objectStoreSpellings n && (reachesChainConstructor env {} n).1) ||
            (storesObject env n && constructsChainRecord env n))
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
  /-- The site is on the **frozen execution surface**, which has no chain
  invariant of its own to state: `donationChainWellFormed` is a predicate on
  `SystemState`, and `FrozenSystemState.objects` is a `FrozenMap`.

  Requiring a `donationChain…` result of a frozen site would therefore demand a
  theorem that cannot be written, and accepting no record at all would be the
  silence this census exists to refuse.  What carries the chain here is the
  frozen surface's own reason for existing: it performs the **same removal** as
  its live counterpart, and the differential suite exercises the agreement.  So
  the entry names that counterpart, which must itself be registered `states` —
  a frozen writer with no live twin is a frozen transition the live kernel never
  performs, and that is a finding rather than an exemption. -/
  | mirrors (live : Name)
  deriving Inhabited

/-- `true` when `n` names a member of the `donationChain…` family: the invariant,
its relaxed form, the frame, and the walk. -/
def isChainForm (n : Name) : Bool :=
  match n with
  | .str _ s => "donationChain".isPrefixOf s
  | _ => false

/-- The conclusion of a `∀`-telescope — what a theorem actually *proves*. -/
partial def conclusionOf : Expr → Expr
  | .forallE _ _ body _ => conclusionOf body
  | .letE _ _ _ body _ => conclusionOf body
  | .mdata _ e => conclusionOf e
  | e => e

/-- `true` when `n`'s own result type is `Prop` — a predicate rather than data. -/
def isPredicate (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some info => (conclusionOf info.type).isSort && (conclusionOf info.type) == .sort .zero
  | none => false

/-- `true` when `n` is a chain **predicate**: a `donationChain…` family member
whose own result is a `Prop`.

The prefix alone admits data — `donationChainWitnessContext` is a record, not a
claim — so a theorem mentioning one satisfied the family test while asserting
nothing about the chain. -/
def isChainPredicate (env : Environment) (n : Name) : Bool :=
  isChainForm n && isPredicate env n

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
      -- **The chain form must be in the CONCLUSION, not merely in the type.**
      -- Asking `getUsedConstants` of the whole type is a presence check: a
      -- theorem taking `donationChainWellFormed st` as an unused *hypothesis*
      -- and concluding anything at all satisfied it, so a registry entry could
      -- claim a chain result while proving none (PR #895 review round 3).  The
      -- site may still appear anywhere — a preservation theorem names its
      -- operation in a hypothesis (`op st = .ok st'`) by construction — but
      -- what the theorem *asserts* is its conclusion, and that is where the
      -- chain claim has to be.
      let concluded := (conclusionOf info.type).getUsedConstants
      (if used.contains site then [] else
        [s!"`{site}` names the chain result `{result}`, whose statement does not mention \
            `{site}` — a result about some other subject"]) ++
      (if concluded.any (isChainPredicate env) then [] else
        [s!"`{site}` names `{result}` as a chain result, but its CONCLUSION asserts no \
            `donationChain…` predicate — a hypothesis mentioning one is not a result"])

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
    -- ---------------------------------------------------------------------
    -- The frozen execution surface.
    --
    -- These were invisible to this census until `v0.35.12`: `FrozenOps` was
    -- reached by neither root, so the closure it claims held for every module
    -- except one that writes the live `Reply` record.  The root cause -- a
    -- subsystem outside every derived domain -- closed at `v0.35.60`.  And the gap was not
    -- theoretical — `frozenEndpointReply` cleared a caller's Reply bare, which
    -- is WS-RM's own defect, surviving on the surface nothing was looking at.
    --
    -- **WS-HP HP8**: the three splice entries below are the two the sever had
    -- plus its store step, and each `mirrors` the live counterpart of the same
    -- shape.  The store step is registered rather than folded into the removal
    -- for the reason the live one is: it performs the writes with none of the
    -- removal's resolution or validation, so a transition reaching for it
    -- directly is a site.  It mirrors `spliceReplyFrameStores`, which is itself
    -- a `.halfStep` of the live removal — so the chain from here terminates in a
    -- stating entry two hops out rather than one, which the registry's own
    -- closure check follows.
  , (`SeLe4n.Kernel.FrozenOps.frozenSpliceReplyFrameStores,
      .mirrors `SeLe4n.Kernel.spliceReplyFrameStores)
  , (`SeLe4n.Kernel.FrozenOps.frozenSpliceReplyFrameOut,
      .mirrors `SeLe4n.Kernel.spliceReplyFrameOut)
  , (`SeLe4n.Kernel.FrozenOps.frozenSpliceReplyFrameOutOrSelf,
      .mirrors `SeLe4n.Kernel.spliceReplyFrameOutOrSelf)
    -- The frozen reply, which runs the removal before the consume in the order
    -- the live one does.  `FO-031` is the differential scenario that exercises
    -- the agreement.
  , (`SeLe4n.Kernel.FrozenOps.frozenEndpointReply,
      .mirrors `SeLe4n.Kernel.removeCallerReplyFrame)
    -- **The frozen donation pop** (PR #895 review round 13).  `Reply.consumed`
    -- keeps a stack head's links *because the pop that follows clears them*,
    -- and this surface had no pop -- so a frozen state captured mid-chain left
    -- the answered Reply failing `Reply.isFree` for good: never relinkable,
    -- never retypeable.  These two are the frozen counterparts of the live
    -- pop's stores, and `frozenEndpointReplyWithDonationReturn` is the mirror
    -- of the whole `.reply` operation rather than of its reply leg alone.
  , (`SeLe4n.Kernel.FrozenOps.frozenStoreDonationHeadPop,
      .mirrors `SeLe4n.Kernel.storeDonationHeadPop)
  , (`SeLe4n.Kernel.FrozenOps.frozenReturnDonatedSchedContext,
      .mirrors `SeLe4n.Kernel.returnDonatedSchedContext)
    -- The detach itself, its total fold, and the thread-keyed wrapper the
    -- cancellation path runs.
    -- **WS-HP HP6.3**: the composed store step is a *half-step* of the operation
    -- that validates it.  It cannot state a chain result of its own: given only
    -- `above` and the two records, nothing says the frame above the cut is the
    -- one whose `prev` names `rid`, and the three reciprocal links it writes are
    -- coherent only under the resolution `spliceReplyFrameOut` performs.  That
    -- resolution is exactly what the operation adds, and it is where the chain
    -- result is stated.
  , (`SeLe4n.Kernel.spliceReplyFrameStores,
      .halfStep `SeLe4n.Kernel.spliceReplyFrameOut)
  , (`SeLe4n.Kernel.spliceReplyFrameOut,
      .states [`SeLe4n.Kernel.spliceReplyFrameOut_preserves_donationChainWellFormed])
  , (`SeLe4n.Kernel.spliceReplyFrameOutOrSelf,
      .states [`SeLe4n.Kernel.spliceReplyFrameOutOrSelf_preserves_donationChainWellFormed])
  , (`SeLe4n.Kernel.spliceThreadReplyFrameOut,
      .states [`SeLe4n.Kernel.spliceThreadReplyFrameOut_preserves_donationChainWellFormed])
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
               `SeLe4n.Kernel.returnDonatedSchedContext_preserves_donationChainWellFormed_of_except])
    -- ---------------------------------------------------------------------
    -- The tree's own depth-2 chain fixture (WS-OD OD2.4).  It stores a
    -- `SchedContext` whose `scReply` heads the stack and two `Reply` objects
    -- carrying `prev` / `next`, through a RAW table write — so until
    -- `v0.35.20` added the live primitive to `objectStoreSpellings` the census
    -- of chain writes could not see the fixture that exercises the chain.
    --
    -- Three stores, built one on the last, so the first two are half-steps by
    -- construction: after the SchedContext alone the head it names does not
    -- exist yet, and after the outer frame the inner one does not.  Named as
    -- the environment holds them: `chainWitnessSt1` and `chainWitnessSt2` are
    -- `private`, and this census matches exact constants.
  , (privateIn `SeLe4n.Kernel.IPC.Invariant.Reachability `SeLe4n.Kernel.chainWitnessSt1,
      .halfStep (privateIn `SeLe4n.Kernel.IPC.Invariant.Reachability
        `SeLe4n.Kernel.chainWitnessSt2))
  , (privateIn `SeLe4n.Kernel.IPC.Invariant.Reachability `SeLe4n.Kernel.chainWitnessSt2,
      .halfStep `SeLe4n.Kernel.donationChainWitness)
  , (`SeLe4n.Kernel.donationChainWitness,
      .states [`SeLe4n.Kernel.donationChainWitness_wellFormed]) ]

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
        -- A chain that ends at a `mirrors` entry follows through to the live
        -- twin, so a frozen half-step is covered exactly when that twin is.
      | some (_, .mirrors live) => go live fuel'

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
  | .mirrors live =>
      -- The live twin must exist, must itself state a chain result, and must not
      -- be the site itself: a frozen entry pointing at a frozen entry would be
      -- the record carrying its own weight.
      (if (env.find? live).isSome then [] else
        [s!"`{site}` is recorded as mirroring `{live}`, which is not a declaration of \
            this environment"]) ++
      (if live == site then
        [s!"`{site}` is recorded as mirroring itself"] else []) ++
      (if halfStepResolves registry live then [] else
        [s!"`{site}` is recorded as mirroring `{live}`, which states no chain result — a \
            frozen writer whose live twin is itself uncovered is covered by nothing"])

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
def reconciliationViolations (derived alsoWriting recorded : List Name) : List String :=
  let unregistered := derived.filter (fun n => !recorded.contains n)
  -- **Two derivations of "writes chain data", and an entry justified by either
  -- is not stale.**  `derived` is the primitive-reaching frontier — a site that
  -- calls one of the nine chain-write helpers — and `alsoWriting` is the
  -- independent record-constructing one, which sees a definition that builds a
  -- `Reply` or `SchedContext` and stores it without naming any helper.  The
  -- tree's own depth-2 chain fixture is in the second and not the first, so
  -- reconciling the registry against `derived` alone called its entries stale
  -- while they name real chain writes (PR #895 review round 7).
  let stale := recorded.filter
    (fun n => !(derived.contains n || alsoWriting.contains n))
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

/-- **The write that calls no primitive**: a transition that rewrites a Reply's
upward stack link through a record update and `storeObject`, naming none of the
nine helpers in `chainWritePrimitives`.

This is what makes that list a pin rather than the definition of the frontier.
Nothing in `usesDirectly env chainWritePrimitives` can see it; only
`recordConstructingStoreCandidates` can. -/
private def censusWitnessDirectLinkWrite (rid : SeLe4n.ReplyId) :
    SeLe4n.Model.Kernel Unit :=
  fun st =>
    match st.getReply? rid with
    | some r => SeLe4n.Model.storeObject rid.toObjId (.reply { r with next := none }) st
    | none => .ok ((), st)

/-- **The write that names no store helper either**: the same chain write as the
witness above, spelled `{ st with objects := st.objects.insert … }`.

The store half of the frontier used to be four project helpers plus the FROZEN
table primitive, with the LIVE one — `RHTable.insert` — missing, so a definition
written this way built a chain-bearing record and stored it through a spelling
neither derivation knew (PR #895 review round 7).  That is the defect this PR
corrected on the READ side in round 1, on the same two tables, in the opposite
direction: *a spelling is not a read*, and it is not a write either.

Token-preserving against `censusWitnessDirectLinkWrite`: the same record update
and the same field, differing only in how the record reaches the table. -/
private def censusWitnessRawTableWrite (rid : SeLe4n.ReplyId) :
    SeLe4n.Model.SystemState → SeLe4n.Model.SystemState :=
  fun st =>
    match st.getReply? rid with
    | some r => { st with objects := st.objects.insert rid.toObjId (.reply { r with prev := none }) }
    | none => st

/-- The SPLIT-CONJUNCTION shape: the helper half.  Builds a chain-bearing
record and names no store, so a frontier that conjoins both halves over one body
sees it as harmless — which it is.  The *writer* below is the site. -/
private def censusWitnessSplitHelper (r : SeLe4n.Kernel.Reply) : SeLe4n.Kernel.Reply :=
  { r with prev := none }

/-- ...and the writer half: it stores, and names no constructor.  Neither half
was a candidate while the frontier asked both questions of one body, so the
write landed with nothing saying what it did to the chain.  This witness is why
`reachesChainConstructor` follows calls. -/
private def censusWitnessSplitWriter (rid : SeLe4n.ReplyId) :
    SeLe4n.Model.Kernel Unit :=
  fun st =>
    match st.getReply? rid with
    | some r =>
        SeLe4n.Model.storeObject rid.toObjId (.reply (censusWitnessSplitHelper r)) st
    | none => .ok ((), st)

/-- The MIRROR-IMAGE split: the caller constructs and the **callee** stores.
`censusWitnessSplitWriter` above delegates the *construction*; this one
delegates the *store*, handing a record it built to a generic helper.  Both
halves escaped while the store side demanded a direct call, so the write landed
with nothing recorded — the shape PR #895 review round 3 reported. -/
private def censusWitnessDelegatedStoreHelper (oid : SeLe4n.ObjId)
    (obj : SeLe4n.Model.KernelObject) : SeLe4n.Model.Kernel Unit :=
  SeLe4n.Model.storeObject oid obj

private def censusWitnessDelegatedStoreWriter (rid : SeLe4n.ReplyId) :
    SeLe4n.Model.Kernel Unit :=
  fun st =>
    match st.getReply? rid with
    | some r =>
        censusWitnessDelegatedStoreHelper rid.toObjId (.reply { r with next := none }) st
    | none => .ok ((), st)

/-- A writer whose name *resembles* a compiler auxiliary.  `eq_` is the prefix
Lean gives equation lemmas, and the component test used to accept it on any
name — so this definition was filtered out of both derivations before its used
constants were read, and could write the stack unregistered. -/
private def eq_censusWitnessUserNamed (rid : SeLe4n.ReplyId) :
    SeLe4n.Model.Kernel Unit :=
  fun st =>
    match st.getReply? rid with
    | some r => SeLe4n.Model.storeObject rid.toObjId (.reply { r with prev := none }) st
    | none => .ok ((), st)

/-- The same writer under the name a *generated* equation lemma actually takes.

The fix for the witness above required the prefix plus a numeral, which is a
narrower resemblance and not a relation: `eq_1` is a legal identifier a
contributor may write, and under that rule this definition was filtered out of
both derivations before its constants were read.  `isAuxiliary` consults the
environment now and no name shape at all, so this is a candidate — and it is a
permanent witness that no third name test creeps back in. -/
private def eq_1 (rid : SeLe4n.ReplyId) : SeLe4n.Model.Kernel Unit :=
  fun st =>
    match st.getReply? rid with
    | some r => SeLe4n.Model.storeObject rid.toObjId (.reply { r with next := none }) st
    | none => .ok ((), st)

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
  -- ...and so do the table primitives, for the same reason: a renamed
  -- `RHTable.insert` would make every store invisible and the census would pass
  -- by recognising nothing.
  for n in objectStorePrimitives do
    unless (env.find? n).isSome do
      throwError "reply-stack write census: `{n}` is not a declaration of this environment, \
        so the store half of the frontier recognises nothing"
  -- The helper list is a PIN, reconciled against the derivation rather than
  -- standing in for it.  Each named helper must itself reach a table primitive;
  -- one that stops storing is then a stale entry that says so, instead of
  -- quietly buying the frontier a level it no longer has.  This is the
  -- both-directions treatment the registry already gets, applied to the list
  -- whose omission of the LIVE primitive was PR #895 review round 7's finding.
  for h in objectStoreHelpers do
    unless (env.find? h).isSome do
      throwError "reply-stack write census: the store helper `{h}` is not a declaration of \
        this environment"
    unless storesVia env objectStorePrimitives h do
      throwError "reply-stack write census: the store helper `{h}` no longer reaches a \
        table primitive, so naming it buys the frontier a level it does not have — a stale \
        pin reads like coverage"
  -- Witnesses, both directions.
  unless usesDirectly env chainWritePrimitives ``censusWitnessBareConsume do
    throwError "reply-stack write census: the BARE CONSUME witness is not seen to write \
      reply-stack data — the gate does not detect the shape it exists for"
  if usesDirectly env chainWritePrimitives ``censusWitnessNoWrite then
    throwError "reply-stack write census: a definition that only reads a Reply is seen to \
      write reply-stack data"
  -- The primitive list's own witness, in both directions.  The direct-link write
  -- must be INVISIBLE to the name-based derivation -- that is the hole -- and
  -- VISIBLE to the record-based one, or the coverage check below asserts nothing.
  if usesDirectly env chainWritePrimitives ``censusWitnessDirectLinkWrite then
    throwError "reply-stack write census: the DIRECT LINK WRITE witness calls a chain-write \
      primitive, so it no longer stands for the shape the primitive list cannot see"
  -- ...and the same write reaching the table with no helper at all, which is the
  -- spelling the store half could not see until the LIVE primitive joined the
  -- frozen one.  Both directions, for the same reason.
  if usesDirectly env chainWritePrimitives ``censusWitnessRawTableWrite then
    throwError "reply-stack write census: the RAW TABLE WRITE witness calls a chain-write \
      primitive, so it no longer stands for the shape the primitive list cannot see"
  unless (recordConstructingStoreCandidates env).contains ``censusWitnessRawTableWrite do
    throwError "reply-stack write census: a definition that builds a `Reply` and writes it \
      with `st.objects.insert` is not a candidate — the store half of the frontier is \
      measuring a SPELLING, and a chain write escapes by being written the other way"
  -- The split-conjunction witness, both directions: the WRITER is a candidate
  -- (it stores and reaches a constructor through the helper) and the HELPER is
  -- not (it constructs and stores nothing -- the site is where the store is).
  -- The delegated-STORE split: the writer is a candidate, the generic helper is
  -- not (it constructs nothing).  Fails without `storesObject`'s helper hop.
  unless (recordConstructingStoreCandidates env).contains
      ``censusWitnessDelegatedStoreWriter do
    throwError "the census frontier misses a writer that delegates its STORE to a helper"
  if (recordConstructingStoreCandidates env).contains
      ``censusWitnessDelegatedStoreHelper then
    throwError "the census frontier reports a generic store helper that builds no record"
  -- A user name shaped like a compiler auxiliary is still inspected.  Two of
  -- these, because the previous cut's fix was itself a name shape: `eq_1` is as
  -- legal a definition name as `eq_clearReply`, so a filter that reads either
  -- as generated is reading a spelling a contributor can choose.
  if isAuxiliary env ``eq_censusWitnessUserNamed then
    throwError "`isAuxiliary` filters a user definition whose name merely resembles \
      a generated one"
  unless (recordConstructingStoreCandidates env).contains ``eq_censusWitnessUserNamed do
    throwError "the census frontier misses a writer named like a compiler auxiliary"
  if isAuxiliary env ``eq_1 then
    throwError "`isAuxiliary` filters a user definition named exactly like a generated \
      equation lemma -- `eq_1` is a legal name a contributor may write"
  unless (recordConstructingStoreCandidates env).contains ``eq_1 do
    throwError "the census frontier misses a writer named exactly `eq_1`"
  -- ...and the environment's own answer for a genuine auxiliary is still
  -- consulted, so the deletion above narrowed nothing.  Derived rather than
  -- named: a pin on one hand-picked matcher would age out with its parent.
  let mut matchers := 0
  for (n, _) in env.constants.toList do
    if Meta.isMatcherCore env n then
      matchers := matchers + 1
      unless isAuxiliary env n do
        throwError "`isAuxiliary` no longer recognises the matcher {n}, which the \
          environment reports as one"
  if matchers == 0 then
    throwError "no matcher in this environment, so the auxiliary check is vacuous"
  unless (recordConstructingStoreCandidates env).contains ``censusWitnessSplitWriter do
    throwError "reply-stack write census: the SPLIT-CONJUNCTION witness is not derived as a \
      candidate — a writer that delegates its record update escapes the frontier, which is \
      how a chain write can land with nothing saying what it does"
  if (recordConstructingStoreCandidates env).contains ``censusWitnessSplitHelper then
    throwError "reply-stack write census: the split-conjunction HELPER is derived as a \
      candidate — the frontier is following construction into definitions that store \
      nothing, so the site it names is not where the write happens"
  unless (recordConstructingStoreCandidates env).contains ``censusWitnessDirectLinkWrite do
    throwError "reply-stack write census: the DIRECT LINK WRITE witness is not derived as a \
      candidate -- a definition can rewrite a Reply's stack links with nothing noticing"
  unless (recordConstructingStoreCandidates env).contains ``censusWitnessNoWrite = false do
    throwError "reply-stack write census: a definition that only reads a Reply is derived as \
      a record-constructing store candidate"
  -- ...and the coverage check rejects it when it is not excluded, accepts the
  -- real frontier, and refuses a stale exemption.
  if (primitiveCoverageViolations [``censusWitnessDirectLinkWrite]
      (chainWriteRegistry.map (·.1)) chainNeutralConstructors).isEmpty then
    throwError "reply-stack write census: an unregistered record-constructing store was \
      accepted -- the shape the primitive list cannot see"
  unless (primitiveCoverageViolations (chainNeutralConstructors.map (·.1))
      (chainWriteRegistry.map (·.1)) chainNeutralConstructors).isEmpty do
    throwError "reply-stack write census: a stated chain-neutral constructor was refused"
  if (primitiveCoverageViolations []
      (chainWriteRegistry.map (·.1)) [(`SeLe4n.Kernel.thisIsNotACandidate, "stale")]).isEmpty then
    throwError "reply-stack write census: a STALE chain-neutral exemption was accepted -- an \
      exemption for a definition that no longer builds a chain-bearing record reads like \
      coverage"
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
  unless (reconciliationViolations [`a, `b] [] [`a, `b]).isEmpty do
    throwError "reply-stack write census: agreeing derived/registry sets were reported as \
      disagreeing"
  if (reconciliationViolations [`a, `b] [] [`a]).isEmpty then
    throwError "reply-stack write census: an UNREGISTERED write site was accepted — the \
      shape this gate exists to catch"
  if (reconciliationViolations [`a] [] [`a, `b]).isEmpty then
    throwError "reply-stack write census: a stale registry entry was accepted"
  unless (reconciliationViolations [] [] []).isEmpty do
    throwError "reply-stack write census: two empty sets were reported as disagreeing"
  -- The census.  The set is derived; the registry is reconciled against it in
  -- both directions; the witnesses above are excluded by name, since they are
  -- planted write sites rather than kernel ones.
  let witnesses : List Name :=
    [``censusWitnessBareConsume, ``censusWitnessDirectLinkWrite,
     ``censusWitnessSplitWriter, ``censusWitnessSplitHelper,
     ``censusWitnessDelegatedStoreWriter, ``censusWitnessDelegatedStoreHelper,
     ``eq_censusWitnessUserNamed, ``eq_1, ``censusWitnessRawTableWrite]
  let mut derived : List Name := []
  for n in directWriteCandidates env do
    if witnesses.contains n then continue
    let some info := env.find? n | continue
    if (← Meta.isProp info.type) then continue
    derived := n :: derived
  -- The primitive list itself, held to what the code does.  `derived` above is
  -- read off `chainWritePrimitives`, so it can only ever confirm that list; this
  -- is the independent half, and it is what stops the nine names from becoming
  -- an enumeration standing in for a derivation.
  let mut candidates : List Name := []
  for n in recordConstructingStoreCandidates env do
    if witnesses.contains n then continue
    let some info := env.find? n | continue
    if (← Meta.isProp info.type) then continue
    candidates := n :: candidates
  let recorded : List Name := chainWriteRegistry.map (·.1)
  let mismatches := reconciliationViolations derived candidates recorded
  unless mismatches.isEmpty do
    throwError "reply-stack write census: {mismatches}"
  let coverage := primitiveCoverageViolations candidates recorded chainNeutralConstructors
  unless coverage.isEmpty do
    throwError "reply-stack write census: {coverage}"
  for (n, d) in chainWriteRegistry do
    let violations := disciplineViolations env chainWriteRegistry n d
    unless violations.isEmpty do
      throwError "reply-stack write census: {violations}"
  let stating := chainWriteRegistry.filter
    (fun (_, d) => match d with | .states _ => true | _ => false)
  let mirroring := chainWriteRegistry.filter
    (fun (_, d) => match d with | .mirrors _ => true | _ => false)
  -- The count and the frontier it is taken over, together.  `chainWriteFrontier`
  -- existed as a `def` whose docstring promised it was printed here and nothing
  -- referenced it, so the bound was stated in prose and not in the output -- the
  -- shape this census exists to refuse, inside the cut that added it.  The
  -- summary is therefore built as a value and checked to carry the frontier
  -- before it is logged: a reword that drops it fails elaboration rather than
  -- silently returning the number to reading as a proof of absence.
  let halfSteps := chainWriteRegistry.filter
    (fun (_, d) => match d with | .halfStep _ => true | _ => false)
  -- **The total is the registry, and it must equal the sum of its own rows.**
  -- The count used to be `derived.length` — the primitive-reaching frontier
  -- alone — while `stating` and `mirroring` were counted over the registry, so
  -- once a site entered through the record-constructing frontier the three
  -- numbers stopped adding up and the headline understated the surface
  -- (PR #895 review round 7).  A gate whose own arithmetic does not close is
  -- the shape this file exists to refuse, so the closure is asserted rather
  -- than assumed.
  unless stating.length + mirroring.length + halfSteps.length == recorded.length do
    throwError "reply-stack write census: the registry has {recorded.length} entries and \
      {stating.length} + {mirroring.length} + {halfSteps.length} disciplines — a total that \
      is not the sum of its rows describes no set"
  let summary := s!"reply-stack write census: {recorded.length} write sites \
({derived.length} reached through a chain-write primitive, \
{recorded.length - derived.length} found only by the record-constructing frontier), \
{stating.length} of them stating their own chain result, {mirroring.length} on the \
frozen surface mirroring a live site that does; the remaining {halfSteps.length} are \
half-steps of a composite that does\n      frontier: {chainWriteFrontier}"
  unless (summary.splitOn chainWriteFrontier).length > 1 do
    throwError "reply-stack write census: the summary does not carry \
      `chainWriteFrontier`, so the site count would read as a proof of absence"
  logInfo summary

end SeLe4n.Testing.ReplyStackWriteCensus
