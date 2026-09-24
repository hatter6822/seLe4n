/-
  SeLe4n — the kernel-transition reachability census.

  Copyright (C) 2025 seLe4n contributors
  SPDX-License-Identifier: GPL-3.0-or-later
-/
import Lean.Elab.Command
import SeLe4n
import SeLe4n.Platform.Staged
import SeLe4n.Testing.DeclarationKind
import SeLe4n.Testing.ExportCommitDisciplineCensus
import SeLe4n.Testing.ReplyStackWriteCensus

/-!
# Which kernel transitions are on an executed path

`ExportCommitDisciplineCensus` walks *outward* from each state-committing
`@[export]` and asks how it commits.  This census walks the same graph the other
way: it derives every definition that **transforms kernel state**, partitions
that domain by whether a committing export can reach it, and reconciles the
unreachable half against a pin in both directions.

## Why the tree needs it

WS-RR RR8.12 (`v0.35.90`) found two verified behavioural steps — WS-OD OD1.7's
aborted-donation-holder wake and WS-RR RR7.22/RR8.11's replenishment migration —
sitting in `cancelIpcBlockingOnCore`, a composite **no production path calls**,
while the live `.tcbSuspend` arm re-composed that composite's parts and so
carried neither.  The consequence was a permanent denial of service against a
passive server.  Nothing in the tree could say that the composite was not on an
executed path: the fact was true, checkable and unstated.

## What this census claims, and what it does not

It claims: **every state-transforming definition is either reachable from a
committing export, or recorded in the pin below** — and the pin is reconciled
both ways, so a new non-executed transition fails and so does an entry that has
become live.  The pin carries no per-entry prose, deliberately: a few hundred
shallow reasons would read as justification while asserting nothing, and the
obligation that does the work falls on whoever adds the next entry, who must
either wire it or say there why it exists.  The census prints its own sizes; a
count restated here is a hand-kept figure beside a derivation.

It does **not** claim that a recorded surface agrees with whatever live code
re-composes it.  A bare reachability partition cannot: the offending composite
already existed before the step was added to it, so its entry would have
predated the defect and no reconciliation would have moved.  The mechanism for
*that* is `standsBesideLive` below, whose rows name the live counterpart **and a
pin theorem relating the two**; a step added to one side and not the other
breaks the pin.  A recorded surface with no such row makes no agreement claim at
all, and extending the pinned set is what closes the class rather than the
instance.

This distinction is why `docs/REGISTERED_DEBT.md`'s row registering this census
was corrected in the same cut that landed it: the row said a reachability census
"would have failed on the day" the step was introduced, and that is only true of
the pinned category, not of reachability alone.
-/

namespace SeLe4n.Testing.KernelTransitionReachabilityCensus

open Lean Elab Command Meta
open SeLe4n.Testing.ExportCommitDisciplineCensus (isProjectConstant commitsState)
open SeLe4n.Testing.ReplyStackWriteCensus (privateIn conclusionOf)
open SeLe4n.Testing.DeclarationKind (bodyBearing)

/-- The state this kernel transforms.  A definition whose **result** mentions it
is a transition, a resolver over it, or a step of one; a definition that merely
*takes* one is a reader or a predicate and is not this census's subject. -/
def kernelStateType : Name := `SeLe4n.Model.SystemState

/-- The components the compiler appends to a declaration it mints.

A *suffix*, in every case: `Foo.bar._flat_ctor`, `Foo._sizeOf_inst`,
`Foo.bar._cstage1`.  Each was measured when it was added -- `_flat_ctor` 279,
`_sunfold` 92, `_unsafe_rec` 98 and `_sizeOf_inst` 355 members, none of them
reached by the derived predicates -- and `_cstage1` / `_cstage2` have **0** members
in this build, kept because their absence is a code-generation configuration fact
rather than a design one: a release build that emits them must not turn this census
red. -/
def reservedFinalComponents : List String :=
  ["_cstage1", "_cstage2", "_flat_ctor", "_sunfold", "_unsafe_rec", "_sizeOf_inst"]

/-- Does this name END in a component the compiler reserves?

The FINAL component and not any of them, because a reserved spelling is a suffix
the compiler appends: asking `components.any` also excludes every declaration
nested beneath a namespace of that name, whatever the declaration is called.
Measured: all 830 of this environment's reserved-component constants carry it
finally, so the narrowing excludes nothing that is really generated. -/
def hasReservedFinalComponent (n : Name) : Bool :=
  match n.components.getLast? with
  | some c => reservedFinalComponents.contains c.toString
  | none => false

/-- The compiler's own generated declarations, which are not definitions anyone
wrote.

The general answer is `ReplyStackWriteCensus.isAuxiliary`, which asks the
environment (macro scopes, `isAuxRecursor`, `isRecCore`, `Meta.isMatcherCore`)
rather than matching name shapes, and whose docstring records why a name list
was retired in favour of it.  Reusing it is deliberate: a second auxiliary
filter beside a derived one is this project's one-question-two-answers hazard,
and the two would diverge on the next compiler change.

What that predicate does **not** reach is the generated shapes whose result type
mentions a state-carrying type and which therefore land in *this* census's domain
but not in its sibling's: the compiler's own lowering stages (`_cstage1` /
`_cstage2`, and the `_sunfold` / `_unsafe_rec` pair a `partial` or well-founded
definition gets), the flat constructor a structure gets, and the `SizeOf` instance
every structure and inductive gets.

**Every clause is an EXACT component match, and that is the fix rather than an
incidental style** (PR #897 review, `v0.35.125`).  What stood here was
`s.startsWith "initFn"`, a name RESEMBLANCE: a project transition called
`initFnCleanup` is an ordinary name a contributor may write, and the prefix
excluded it from the domain **before** its result type was ever inspected — so a
definition returning `SystemState` could sit unreachable from every committing
export and appear on neither side of the reconciliation.  That is
`ReplyStackWriteCensus`'s own retired `eq_` prefix, one census over, and
*narrowing a resemblance produces a smaller resemblance, not a relation*.

It is not narrowed here; it is **deleted**, because the environment already
answers it.  Measured on this environment: of the 4 project constants carrying an
`initFn` component, **0** are outside `isAuxiliary` — a module's `initFn` is
macro-scoped (`initFn._@.M._hyg.N`), which `n.eraseMacroScopes != n` decides — so
the clause excluded nothing the derived predicate did not already exclude, while
admitting a user name it should not have.  The surviving clauses are whole
components the compiler reserves, not prefixes of user names, and each was
measured: `_flat_ctor` 279, `_sunfold` 92, `_unsafe_rec` 98 and `_sizeOf_inst`
355 members, **none** of them reached by `isAuxiliary`; `_cstage1` / `_cstage2`
have **0** members in this build, and are kept because their absence is a
code-generation configuration fact rather than a design one — a release build that
emits them must not turn this census red.

**And three more questions the environment answers, added at `v0.35.128`** (PR #897
review).  `Lean.isAuxRecursor`, `Lean.isNoConfusion` and `Meta.isMatcherCore` are the
compiler's own predicates for the recursors, the injectivity helpers and the match
auxiliaries it mints, so asking them is *ask the environment* rather than another
resemblance.  They were needed because `typeCarries` now reduces reducible aliases
(see below), which brings a `T.noConfusion` into the domain: its result is
`T.noConfusionType P x y`, an `abbrev` whose unfolding mentions the constructor
fields' types and so mentions `SystemState` for any state-carrying `T`.

**The two filters are complementary, and that is measured rather than assumed** —
the reason the component list is not deleted with the addition.  Of this
environment's project constants, the LIST catches `_flat_ctor`, `_sizeOf_inst` and
`_unsafe_rec` members the three predicates do not, and the PREDICATES catch every
`*.noConfusion` (and the matchers and aux recursors) the list does not.  So this is
*derive what the environment can answer, and keep the list as a pin for what it
cannot* — neither half subsumes the other, and claiming redundancy in either
direction would have shrunk the filter.

**And a name is still not a fact, twice over** (PR #897 review, `v0.35.130`).  The
component list survived the `initFn` deletion because its members are *whole*
components the compiler reserves rather than prefixes of user names.  That is true
and it was not enough, in two independent ways.  Lean accepts `_flat_ctor` as an
ordinary identifier, so a contributor's `SeLe4n.Kernel._flat_ctor : SystemState →
SystemState` was excluded before its result type was ever read; and the test was
`components.any`, which excludes every declaration **nested beneath a namespace**
of one of those names, whatever the declaration itself is called.  Both are the
silent direction — the constant is never examined, no pin moves, and the
reconciliation goes on reporting that its whole domain is accounted for.

So the name narrows and the ENVIRONMENT decides.  A reserved spelling is a
*suffix* the compiler appends, so the question is the **final** component, and a
declaration the compiler minted carries **no declaration range**: the elaborator
records a source position for what a contributor wrote, and an auxiliary added
without `addDeclarationRanges` has none.  Measured on this environment: of the
**830** project constants carrying a reserved component, **830** carry it as the
final one (so the `any` reading excluded nothing extra *today* while admitting a
whole namespace), and **all 830** have no range — while a planted user-written
`_flat_ctor` and a planted definition nested under a `_cstage1` namespace each
have one, and each was classified compiler-generated by the superseded reading.

What this deliberately does NOT claim: a declaration a future macro mints with a
source range, or a user declaration some elaborator records without one.  The
first stays in the domain (where a spurious member must be explained, which is the
loud direction) and the second stays out, which is exactly the superseded
behaviour — so the narrowing is a strict improvement rather than a new
approximation. -/
def isCompilerGenerated [Monad m] [MonadEnv m] (n : Name) : m Bool := do
  let env ← getEnv
  if SeLe4n.Testing.ReplyStackWriteCensus.isAuxiliary env n
      || Lean.isAuxRecursor env n || Lean.isNoConfusion env n
      || Lean.Meta.isMatcherCore env n then
    return true
  if !hasReservedFinalComponent n then return false
  return (← Lean.findDeclarationRangesCore? n).isNone

/-- How many rounds `stateCarryingTypes` may take before it gives up.

The fixpoint is monotone in a finite set so it terminates on its own; the bound is
what keeps a `partial` walk from becoming a hang if a future Lean makes the
environment cyclic.

**Reaching it is an ERROR, not a smaller answer** (PR #897 review, `v0.35.128`).
This docstring already said that exhaustion "would under-approximate the carriers,
which makes the domain SMALLER, so a new bound must be checked rather than assumed"
— and the loop then returned the partial set as though it were complete, so a
transition returning an omitted wrapper was in neither the reachable nor the
unreachable set and the wire-or-record gate passed silently.  *A rule stated is not a
rule enforced*: `stateCarryingTypes` throws now, and takes the bound as an argument so
the throw has a witness (`carrierFixpointRefusesExhaustion`, which runs the
derivation at a bound of 1 and requires it to fail).

Measured on this environment: the fixpoint converges after **2** rounds — this
docstring said 3, which was the previous cut counting the convergence-detecting pass
that does not run. -/
def carrierFixpointBound : Nat := 12

/-- `true` when a type's own telescoped RESULT mentions one of `carriers`.

The same question the domain asks of a definition, asked of a field, so "this
returns kernel state" has one answer: a field of type `SystemState → Prop` reads a
state and holds none, and `Option SystemState` holds one. -/
def typeCarries (carriers : NameSet) (ty : Expr) : MetaM Bool :=
  forallTelescopeReducing ty fun _ body => do
    -- **A REDUCIBLE ALIAS IS NOT A DIFFERENT TYPE** (PR #897 review, `v0.35.128`).
    -- `forallTelescopeReducing` reduces only far enough to expose a `∀`, so a result
    -- spelled through `abbrev StateResult := Option SystemState` arrives as the alias
    -- constant, which `stateCarryingTypes` never adds (it adds inductives), and the
    -- transition is then in NEITHER the reachable nor the unreachable set -- a
    -- domain miss, silent by construction.  One `whnf` at REDUCIBLE transparency
    -- unfolds an `abbrev` and leaves a plain `def` alone, which is the exact
    -- boundary: `abbrev` is what Lean makes reducible, and reducing further would
    -- pull a dependent projection like `id.evidenceProp` open and file three proof
    -- bundles as state transformers.  Nesting needs no recursion here: an alias
    -- whose unfolding is a function type is already stripped by the telescope, and
    -- one whose unfolding names another alias is reduced by the same `whnf`.
    --
    -- Measured on this environment: with `isCompilerGenerated` asking the
    -- environment as well (above), the domain gains **0** declarations -- so the fix
    -- costs nothing today and the class it closes is one the tree does not yet
    -- exhibit.  Without that filter it would gain 2, both `T.noConfusion`.
    let body ← withReducible (whnf body)
    pure (body.find? fun e => match e with
      | .const c _ => carriers.contains c
      | _ => false).isSome

/-- **Does this type DECLARE a non-`Prop` sort**, up to reducible transparency?

The question `stateCarryingTypes` asks of a candidate type alias, asked once so
the whole type and a telescoped body cannot answer it differently.  PR #897's
review found it asked of the raw expression, where a declared sort that is itself
reducibly aliased is a `.const` and so neither a sort nor a `∀`.

`whnfR`, not `whnf`: reducible transparency unfolds an `abbrev` and leaves a plain
`def` alone, which is the boundary `v0.35.128` measured for the *result* of a
declaration and which this asks of its *sort*.  `Prop` is a sort and is excluded,
because a proposition's inhabitants are proofs and hold no state. -/
private def declaresNonPropSort (ty : Expr) : MetaM Bool := do
  let ty' ← whnfR ty
  pure (ty'.isSort && !ty'.isProp)

/-- Every project type that **carries** kernel state: `SystemState` itself, and
every non-propositional project inductive one of whose constructor FIELDS holds
one, transitively.

**A result type that carries state is not the same as one that mentions it**
(PR #897 review, `v0.35.125`).  The domain test below asked whether the telescoped
result *mentions* `SystemState` as a constant, so `Option SystemState` and
`Except KernelError SystemState` were in and a named wrapper was not:
`TlbCacheJointState.pageTableUpdate : TlbCacheJointState → … → TlbCacheJointState`
rewrites that structure's `sysState` field and appeared on **neither** side of the
reconciliation, so another unreachable transition could use the same wrapper and
bypass the gate entirely.  The projection `TlbCacheJointState.sysState` *was* in the
domain, which is the shape of the miss: the census could see the field and not the
record.

Three things this derivation decides, each of which the first measurement got
wrong and the second corrected — *a measurement that licenses a conclusion gets
checked as hard as the conclusion*.

**A FIELD, not a parameter.**  A constructor's telescope opens the inductive's own
parameters first, so `structure P (st : SystemState) : Prop` reads as "a field of
type `SystemState`" unless the first `numParams` arguments are dropped.  Without
that drop the carrier set is **64** types, almost all of them propositions —
`syscallDispatchQuiescence`, `donationChainWellFormed`, every `.below` motive.

**A field CARRIES state when its own telescoped result does.**  A field of type
`SystemState → Prop` *reads* state; it does not hold one.  Judging a field by
whether its type mentions a carrier anywhere admits `PlatformBinding` and both
boundary contracts, and with them every platform binding and contract constant in
the tree — 13 carriers and 24 configuration records that transform nothing.  The
rule here is the one the domain already applies to definitions, which is also why
the two cannot disagree about what "returns state" means.

**A proposition carries nothing.**  An inductive whose sort is `Prop` is excluded
outright: its parameters are states it is *about*.

Measured on this environment: **10** carrier types besides `SystemState`, and the
domain grows by **39** definitions no committing export reaches — the boot builder
and the whole boot path (unreachable because `lean_kernel_main` is not written
until SM10.1/WS-BP), the revocation traversals that are already a registered
residue, the lock-bracket machinery, and the reviewer's own
`TlbCacheJointState` pair.  Every one of them is a definition that produces a value
holding kernel state, which is precisely this census's subject. -/
partial def stateCarryingTypes (env : Environment)
    (bound : Nat := carrierFixpointBound) : MetaM NameSet := do
  -- **A TYPE ALIAS IS A CARRIER WHEN WHAT IT ABBREVIATES IS** (PR #897 review,
  -- `v0.35.131`).  `typeCarries` normalises the telescoped result at reducible
  -- transparency, which unfolds an alias that IS the whole result and cannot reach
  -- one nested under a constructor: `Option StateAlias` is already in weak-head
  -- normal form, so `whnf` stops at `Option` and only `StateAlias` remains for the
  -- search -- a constant the carrier set never held, so the transformer was in
  -- NEITHER the reachable nor the unreachable set.  Recursing the normalisation
  -- through the expression would be one more partial analysis; adding the alias to
  -- the carrier SET answers both shapes with the mechanism already here, and the
  -- fixpoint closes a chain of aliases for free.
  --
  -- Collected once, outside the loop: whether a definition is a type alias is a
  -- property of its own signature and no round can change it.  Only the carrier
  -- test below is re-run.
  let mut aliases : Array (Name × Expr) := #[]
  for (n, ci) in env.constants.toList do
    if !isProjectConstant n then continue
    -- "Does this declaration carry a body" has ONE owner, and matching `.defnInfo`
    -- here would be a sixth asker re-deciding it -- and would miss an `opaque` type
    -- alias exactly as the five `v0.35.114` found did.  `bodyBearing` answers, and
    -- `value?` with its flag hands back the body it says is there.
    if !bodyBearing ci then continue
    let some value := ci.value? (allowOpaque := true) | continue
    -- A type alias' telescoped TYPE is a sort -- **up to reducible transparency**,
    -- which is the correction PR #897's review made at `v0.35.135`.  The test read
    -- `ci.type` raw, so a declared sort that is ITSELF reducibly aliased --
    -- `abbrev CarrierSort : Type 1 := Type` and then
    -- `abbrev StateAlias : CarrierSort := SystemState` -- is a `.const`, neither
    -- `isSort` nor `isForall`, and the alias never entered this array.  A
    -- transformer returning `Option StateAlias` was then in NEITHER reconciliation
    -- set, which is the silent direction: the constant is never examined and the
    -- pin never moves.  That is `v0.35.128`'s own finding one level up -- there the
    -- RESULT needed one reducible `whnf` and here the declared SORT does -- so
    -- `declaresNonPropSort` asks the question once, of the whole type and of the
    -- telescoped body, and the branch on the raw shape is gone with it.
    --
    -- **Reducible is the exact boundary, for the reason `v0.35.128` measured**:
    -- `abbrev` is what Lean makes reducible, while DEFAULT transparency opens a
    -- dependent projection like `id.evidenceProp` and files four records of proofs
    -- as carriers.
    --
    -- `Prop` IS a sort, so the `isProp` half stays: without it every
    -- `SystemState → Prop` predicate in the tree reads as an alias of a
    -- state-carrying type, and its value mentions `SystemState`, so the carrier set
    -- swallows them.  Measured at **30** spurious domain members -- the `Decidable`
    -- instances and the four evidence records `v0.35.128` identified.  The `isProp`
    -- skip is the same one the inductive arm below makes, for the same reason.
    let isAlias ← forallTelescopeReducing ci.type fun _ body => declaresNonPropSort body
    if isAlias then
      aliases := aliases.push (n, value)
  let mut carriers : NameSet := ({} : NameSet).insert kernelStateType
  let mut changed := true
  let mut rounds := 0
  while changed && rounds < bound do
    changed := false
    rounds := rounds + 1
    for (n, value) in aliases do
      if carriers.contains n then continue
      -- ...judged by the SAME question a field is judged by, so "does this carry
      -- kernel state" keeps one answer across the alias, the field and the result.
      -- The value's own PARAMETERS are stripped first, so a parameterised alias is
      -- judged by what it abbreviates rather than by what its binders mention.
      if ← lambdaTelescope value fun _ body => typeCarries carriers body then
        carriers := carriers.insert n
        changed := true
    for (n, ci) in env.constants.toList do
      if !isProjectConstant n || carriers.contains n then continue
      match ci with
      | .inductInfo iv =>
        if ← forallTelescopeReducing iv.type fun _ body => pure body.isProp then
          continue
        let mut hit := false
        for ctor in iv.ctors do
          match env.find? ctor with
          | some (.ctorInfo cv) =>
            let holds ← forallTelescopeReducing cv.type fun args _ => do
              let mut found := false
              for a in args.toList.drop iv.numParams do
                if ← typeCarries carriers (← inferType a) then found := true
              pure found
            if holds then hit := true
          | _ => pure ()
        if hit then
          carriers := carriers.insert n
          changed := true
      | _ => pure ()
  -- **THE DEFAULT BRANCH IS A DECISION.**  Exiting with `changed` still set means a
  -- carrier chain was longer than `bound`, so the set returned is a strict subset of
  -- the carriers and every transition whose result holds an omitted wrapper drops out
  -- of BOTH sides of the reconciliation -- which is the one failure mode this census
  -- cannot report, because a domain miss is silent by construction.  Refusing is the
  -- only answer that is not a false green.
  if changed then
    throwError "carrier fixpoint did not converge within {bound} round(s): the \
      derived set of state-carrying types is a strict UNDER-approximation, so a \
      transition returning an omitted wrapper would be in neither the reachable nor \
      the unreachable set and this census would pass over it silently.  Raise \
      `carrierFixpointBound` and re-measure the convergence round count in its \
      docstring."
  return carriers


/-- `true` when `n` is a declaration with a body whose result type mentions
`SystemState`.

`typeCarries` strips the binders, so a predicate `SystemState → Prop` has body
`Prop` and is **not** in the domain, while `SystemState → Except KernelError
SystemState` is.  Since `v0.35.125` it asks whether the result **carries** state
rather than whether it mentions `SystemState`, so a named wrapper —
`TlbCacheJointState`, `IntermediateState`, `LockBracketOutcome` — counts; see
`stateCarryingTypes` for the derivation and for what the first two measurements of
it got wrong.  The test over-approximates — an `Option SystemState` resolver and a
pure reader that returns its argument both qualify — and that is the safe direction
for a *domain*: a member wrongly included must be explained, a member wrongly
excluded is never looked at.

**Which declarations have a body is `DeclarationKind.bodyBearing`'s question, not
this function's** (PR #897's review).  What stood here was a `match` on
`.defnInfo` with a `| _ => return false` wildcard, so an `opaque` — which is
executable, and whose body `liveClosure` below reads through
`value? (allowOpaque := true)` precisely because this tree has such declarations
— was silently outside this **domain**.  A domain miss is silent by
construction: the constant is never examined, the pin never moves, and the
reconciliation goes on reporting that every non-executed transformer is
recorded.  The same wildcard stood at four sites across three censuses while a
fifth had the right answer, which is why the question has one owner now rather
than four patches.

**The widening is not vacuous on this tree.**  It brought in exactly one real
constant: `Platform.FFI.kernelStateRef`, an `opaque IO.Ref SystemState` — the
state cell this census is *defined over*, since "commits state" means "reaches a
write to it".  It is not a transition, and the domain says as much by
over-approximating; it is **reachable** from every committing seam, so it needs
no pin entry and demands nothing.  Carving it out by name would be the
enumeration this census exists to retire, so it stays in and is explained here.
The other new member is the planted witness below. -/
def isStateTransformer (carriers : NameSet) (n : Name)
    (ci : ConstantInfo) : MetaM Bool := do
  if !bodyBearing ci then return false
  if !isProjectConstant n || (← isCompilerGenerated n) then return false
  typeCarries carriers ci.type

/-! ## Witnesses for the `opaque` arm of the domain

`DeclarationKind` witnesses the *predicate*; these two witness the **pipeline**,
which is the part that was broken: a transformer the classifier does not
recognise never reaches the reachability partition or the reconciliation at all.
They make the arm decisive in **both** directions through the reconciliation
itself rather than through a second check:

* the transformer is a state transformer no committing export reaches, so it must
  appear in the pin below; **measured** — delete that pin entry and the
  reconciliation reports it as a non-executed transformer nobody recorded, which
  is what says the witness reaches the reconciliation rather than merely
  elaborating;
* the control only *takes* a `SystemState`, so it must **not** appear: what keeps
  it out is that the type test reads the **telescoped result** rather than the
  whole type.  **Measured** — replace `forallTelescopeReducing`'s body with
  `ci.type` and the control becomes an unrecorded non-executed transformer, so
  the pair decides the domain in both directions.  (Narrowing `bodyBearing` back
  to `.defnInfo` is caught one module earlier, by `DeclarationKind`'s own
  `opaque` witness, which names the arm and the reason.)

They are `opaque` rather than `def` deliberately: a `def` exercises the arm that
already worked.  Each carries a value, because the finding is about an
*executable* opaque transition rather than a declared-and-unimplemented one. -/

private opaque censusWitnessOpaqueTransformer : Model.SystemState → Model.SystemState :=
  fun st => st

private opaque censusWitnessOpaqueNonTransformer : Model.SystemState → Nat :=
  fun _ => 0

/-- `true` when a constant's own body is ERASED — a theorem, a proof, or a
predicate.

Lean compiles no code for any of them, so a transformer that one of their terms
mentions is not on an executed path because of that mention.  The walk below
records such a constant as seen and does not expand it.

**The test is the TELESCOPED result, not the type** — `ReplyStackWriteCensus`'s
`isPredicate`, reused rather than re-spelled, so the two censuses cannot disagree
about what a proposition is.  `Expr.isProp` asks whether the type *is* `Prop`,
which is true of a proof and false of `SystemState → Prop`; a predicate is erased
just as a proof is, and it is also how a proof reaches this walk in practice, since
the proposition a root supplies appears as an implicit argument at the call site. -/
def isErasedConstant (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.thmInfo _) => true
  | some _ => SeLe4n.Testing.ReplyStackWriteCensus.isPredicate env n
  | none => false

/-- How much worklist the live closure may consume before it gives up.

Far above the closure of this kernel's seams — measured at **3477** constants
against a bound of 400000 — so nothing in production can reach the refusal, which
is why `liveClosureRefusalViolations` exercises it at a bound of 1.  *A check that
cannot fire and carries no witness is indistinguishable from one that is wrong.* -/
def liveClosureFuel : Nat := 400000

/-- Every constant a committing export can reach **computationally**, following
project constants transitively.

Fuel-bounded, and an exhausted walk is an **error** (PR #897 review, `v0.35.131`).

It used to return what it had, on the stated ground that a smaller *reachable* set
makes the census demand more.  That reads one of the reconciliation's two
directions and not the other.  A transformer already recorded in
`nonExecutedTransitions` that becomes reachable only beyond the cutoff stays in
`unreachable`, still matches its entry, and the reconciliation **passes** — instead
of reporting that a pin entry is now live, which is the regression this census
exists to catch.  Exhaustion is not conservative here; it is a false green on the
stale-entry half.

That docstring also called the behaviour "like its sibling", and the sibling does
the opposite: `ExportCommitDisciplineCensus.reachesAny` answers **`true`** on
exhaustion, because for *that* predicate — does this export reach a state write? —
`true` is what demands more.  Two walks, two conservative directions, and the
comparison was false in the direction that mattered.  Measured over this tree's four
bounded walks: `reachesAny` answers `true`,
`IpcDethreadingEnvironmentCensus.entailedTargets` answers the empty entailment set,
`stateCarryingTypes` throws since `v0.35.128` — three fail closed, and this was the
fourth.

An empty worklist and an exhausted fuel are therefore distinguished rather than
collapsed: completion is `some seen` whatever the fuel is, exhaustion is `none`,
and the fuel is an ARGUMENT so `liveClosureRefusalViolations` can exercise the
refusal on a tree where the real bound is never reached.

**An erased dependency is not a call** (PR #897 review, `v0.35.125`).  An
unrestricted `getUsedConstants` walk follows a proof: a committing path that
supplies a proof argument, or calls a theorem whose proof mentions an otherwise
unwired transformer, marked that transformer **live** although Lean erases the
dependency and no runtime path executes it — so it escaped `nonExecutedTransitions`
and the wire-or-record gate saw nothing.  That is *occurrence is not execution*,
one artefact over from where `BootEntryContract` records it.

Measured before tightening: the permissive closure is **4231** constants and the
erasure-respecting one **3477**, so 754 constants were reachable only through a
proof — and **zero** of them are state transformers, which is why the pin is
byte-identical across this change.  The tightening is therefore free *today* and
closes the path a single proof-carrying committing body would have opened.

What it does **not** close, stated rather than approximated: a proof term written
*inline* in a committing definition's own body is part of that body, so the
constants it mentions are still followed.  Deciding that needs `Meta.isProof` at
every argument of every application in the closure, which is a type inference per
node over thousands of constants; the residue is an over-approximation of *live*,
which makes the census demand **less**, and it is named here rather than left for a
reader to find. -/
partial def liveClosure (env : Environment) (roots : List Name)
    (fuel : Nat := liveClosureFuel) : Option NameSet :=
  go roots {} fuel
where
  go (worklist : List Name) (seen : NameSet) (fuel : Nat) : Option NameSet :=
    -- The worklist is matched FIRST and the fuel only inside the non-empty arm, so
    -- "finished" strictly dominates "exhausted" by NESTING rather than by arm order.
    -- Written as one `match worklist, fuel` the two are peers, and swapping them
    -- makes a walk that empties the worklist on its last unit of fuel report as
    -- exhausted -- a spurious refusal on a correct run, at a boundary no witness on
    -- this tree can reach.  *Prefer making the property structural over checking
    -- it*: nested, there is no order to get wrong.
    match worklist with
    | [] => some seen
    | c :: rest =>
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      if seen.contains c || !isProjectConstant c then go rest seen fuel'
      else
        let seen := seen.insert c
        if isErasedConstant env c then go rest seen fuel'
        else
          match (env.find? c).bind (·.value? (allowOpaque := true)) with
          | none => go rest seen fuel'
          | some v => go (v.getUsedConstants.toList ++ rest) seen fuel'

/-- An alias for the state itself, used NESTED under a result constructor.

`v0.35.128`'s `CensusWitnessAliasedState` is the alias as the WHOLE result, which
`typeCarries`' weak-head reduction unfolds.  This one is `Option
CensusWitnessNestedAlias`: already in weak-head normal form, so `whnf` stops at
`Option` and only the alias constant reaches the search.  Without the alias arm of
`stateCarryingTypes` the transformer below is in NEITHER the reachable nor the
unreachable set, and its pin entry reads as stale. -/
private abbrev CensusWitnessNestedAlias := Model.SystemState

/-- The transformer that must be in the domain, and so in the pin. -/
private def censusWitnessNestedAliasTransformer (st : Model.SystemState) :
    Option CensusWitnessNestedAlias := some st

/-- A `Prop`-valued definition whose statement quantifies over the state.

`Prop` IS a sort, so without the `isProp` half of the alias test every proposition
in the tree reads as a type alias, and `typeCarries` of its statement finds the
state it quantifies over -- measured at **30** spurious domain members, the
`Decidable` instances and the four evidence records `v0.35.128` identified as what
DEFAULT transparency would file.  Its inhabitants are proofs and hold no state.
This one has NO parameters, so it exercises the `dv.type.isSort` branch; the
parameterised branch is exercised by the tree's own predicates. -/
private def CensusWitnessPropAlias : Prop := ∀ st : Model.SystemState, st = st

/-- Its producer must NOT be in the domain.  `PLift` because `Option` takes a
`Type` and a proposition is `Sort 0`; the wrapper keeps the alias NESTED, which is
what stops the reducible unfolding from answering before the carrier test does. -/
private def censusWitnessPropAliasProducer (_st : Model.SystemState) :
    Option (PLift CensusWitnessPropAlias) := none

/-- A PARAMETERISED alias whose binder mentions the state and whose body does not.

The control for how an alias is judged: `stateCarryingTypes` strips the value's own
parameters before asking whether what it abbreviates carries state, so this one does
not.  Asking `typeCarries` of the whole value instead searches the lambda *including
its binder types*, finds `SystemState` there, and files the alias as a carrier --
which is judging a type by what its parameters read rather than by what it holds.
Used NESTED below, so the reducible unfolding cannot answer the question first. -/
private abbrev CensusWitnessParameterisedAlias
    (_reader : Model.SystemState → Nat) : Type := Nat

/-- The argument is a NAMED constant rather than a lambda: an inline `fun _ => 0`
carries its own binder type, so the result expression would mention `SystemState`
outright and the control would pass for a reason that has nothing to do with the
alias. -/
private def censusWitnessParameterReader : Model.SystemState → Nat := fun _ => 0

/-- Its producer must NOT be in the domain. -/
private def censusWitnessParameterisedAliasProducer (_st : Model.SystemState) :
    Option (CensusWitnessParameterisedAlias censusWitnessParameterReader) := some 0

/-- The CONTROL, and what makes the pair decide *the alias names a carrier* rather
than *the result is nested*: the same shape over an alias that carries nothing. -/
private abbrev CensusWitnessNestedAliasCount := Nat

/-- Its producer must NOT be in the domain. -/
private def censusWitnessNestedAliasCounter (_st : Model.SystemState) :
    Option CensusWitnessNestedAliasCount := some 0

/-- A sort that is **itself** a reducible alias.

PR #897's review, at `v0.35.135`: the alias test read `ci.type` raw, so an alias
whose DECLARED SORT is spelled through an `abbrev` is a `.const` -- neither
`isSort` nor `isForall` -- and never entered the candidate array at all.  This is
`v0.35.128`'s *a reducible alias is not a different type* one level up: there the
declaration's RESULT needed one reducible `whnf`, here its SORT does.  Planted
because the tree spells no sort this way, so the widening admits nothing on it and
this pair is the whole measurement. -/
private abbrev CensusWitnessCarrierSort : Type 1 := Type

/-- The alias the census must see: its declared sort is the one above, and what it
abbreviates is the state.  Used NESTED below, so the reducible unfolding of the
RESULT cannot answer before the carrier set is consulted -- which is what makes
this decide the SORT test rather than `v0.35.128`'s result test. -/
private abbrev CensusWitnessAliasedSortState : CensusWitnessCarrierSort :=
  Model.SystemState

/-- The transformer that must be in the domain, and so in the pin.  Before the fix
it was in NEITHER reconciliation set, so its pin entry read as stale -- the silent
direction, since a constant the domain never examines moves no number. -/
private def censusWitnessAliasedSortTransformer (st : Model.SystemState) :
    Option CensusWitnessAliasedSortState := some st

/-- The CONTROL, and what makes the pair decide *the aliased sort is normalised*
rather than *anything declared through this sort is a carrier*: the same shape over
an alias that abbreviates something holding no state. -/
private abbrev CensusWitnessAliasedSortCount : CensusWitnessCarrierSort := Nat

/-- Its producer must NOT be in the domain. -/
private def censusWitnessAliasedSortCounter (_st : Model.SystemState) :
    Option CensusWitnessAliasedSortCount := some 0

/-! ## Witnesses for the domain's two widenings

Each is planted, because the property each states is one the tree does not
currently exhibit — and a check that cannot fire on the current tree and carries
no witness is indistinguishable from one that is wrong.  Each comes with the
CONTROL that keeps its arm from being decided by the wrong thing.
-/

/-- A structure that **carries** kernel state in a field. -/
private structure CensusWitnessWrapper where
  carried : Model.SystemState
  tag : Nat

/-- ...and one that only **reads** it.  Its field is a function *of* a state, so
the wrapper holds no state: this is the distinction that keeps `PlatformBinding`
and both boundary contracts — and with them every platform binding in the tree —
out of the carrier set. -/
private structure CensusWitnessReader where
  readsState : Model.SystemState → Nat

/-- A transformer returning a WRAPPER, which mentions `SystemState` nowhere in its
own type.  It must be in the domain and, being reachable from no committing export,
in the pin below: delete its pin entry and the reconciliation reports it. -/
private def censusWitnessWrapperTransformer (st : Model.SystemState) :
    CensusWitnessWrapper :=
  { carried := st, tag := 0 }

/-- ...and the control that must NOT be, since `CensusWitnessReader` carries
nothing.  It is the wrapper witness with one field type changed, so the pair
decides the *field* rule rather than the existence of the walk. -/
private def censusWitnessReaderProducer : CensusWitnessReader :=
  { readsState := fun _ => 0 }

/-- A reducible ALIAS of a state-carrying result — `abbrev`, which is what Lean makes
reducible, so this is the exact shape `typeCarries`' `whnfR` is about.

PR #897 review (`v0.35.128`): `forallTelescopeReducing` reduces only far enough to
expose a `∀`, so a transformer whose result is spelled through an alias that is **not**
a function type arrives as the alias constant — which the carrier set never contains,
since that set is built from inductives — and the transformer is then in NEITHER the
reachable nor the unreachable set.  A domain miss, silent by construction.  The tree
exhibits no such alias today, which is why this is planted: on the real tree the fix
gains zero declarations, so the plants are the whole measurement. -/
private abbrev CensusWitnessAliasedState := Option Model.SystemState

/-- ...and the CONTROL: an alias that reduces to something carrying no state.  It keeps
the arm from being decided by "the result is an alias" rather than by "the alias names a
type that carries state" — a reduction that accepted any alias would pull this in too. -/
private abbrev CensusWitnessAliasedCount := Option Nat

/-- A transformer whose result type is a reducible alias.  It must be in the domain and,
being reachable from no committing export, in the pin below: delete its pin entry and
the reconciliation reports it, and drop the `whnfR` and it leaves the domain and the
reconciliation reports the entry as stale. -/
private def censusWitnessAliasedTransformer (st : Model.SystemState) :
    CensusWitnessAliasedState := some st

/-- ...and the control that must NOT be in the pin, being the transformer above with
the alias swapped for one that carries nothing. -/
private def censusWitnessAliasedCounter (_st : Model.SystemState) :
    CensusWitnessAliasedCount := some 0

/-- A PROPOSITION carrying a state in a data field — legal Lean, and the one
shape the carrier walk's `Prop` skip is about.

Its own sort is `Prop`, so Lean erases it and a definition returning it transforms
nothing observable; without the skip it would become a carrier and
`censusWitnessPropositionProducer` a state transformer.  Planted because the tree
has no such inductive: the skip was measured to exclude **nothing** here, and a
filter with no member is one whose deletion changes no number — so it needs a
witness or it is indistinguishable from dead code. -/
private inductive CensusWitnessPropCarrier : Prop where
  | mk (carried : Model.SystemState)

/-- ...and the producer that must NOT be in the domain. -/
private def censusWitnessPropositionProducer (st : Model.SystemState) :
    CensusWitnessPropCarrier :=
  .mk st

/-- A transformer whose name begins with the compiler's `initFn`, which the
retired prefix clause excluded from the domain **before** its result type was
read.  It is an ordinary project definition, so it must be in the domain and in
the pin; the real generated init is macro-scoped and `isAuxiliary` still excludes
it, which is what makes this witness decide the *prefix* rather than the filter. -/
private def initFnCensusWitnessTransformer (st : Model.SystemState) :
    Model.SystemState := st

/-- A user-written transformer whose FINAL component is a spelling the compiler
reserves.  Lean accepts `_flat_ctor` as an ordinary identifier, so the superseded
name test excluded it from the domain before its result type was ever read.  It is
a definition a contributor wrote, so the environment records a declaration range
for it and it must be in the domain and in the pin; the 830 real reserved-name
constants have no range and stay excluded, which is what makes this witness decide
the RANGE rather than the list. -/
private def _flat_ctor (st : Model.SystemState) : Model.SystemState := st

/-- A user-written transformer NESTED beneath a namespace whose name is a reserved
spelling.  Its own final component is ordinary, so only `components.any` excluded
it -- and that reading excludes every declaration under such a namespace, whatever
it is called.  It must be in the domain and in the pin, which is what makes this
witness decide `any` against `getLast?` independently of the range. -/
private def _cstage1.censusWitnessNestedTransformer (st : Model.SystemState) :
    Model.SystemState := st

/-! ### A transformer MINTED with no declaration range, under a namespace whose name
is a reserved spelling and with an ordinary final component of its own.

It is the witness for the two conjuncts `_flat_ctor` cannot reach, and it needs
both of its unusual properties to be one.  `Lean.addDecl` records no source
position, so this declaration has no range -- which is what a *dropped name test*
would then take as proof that the compiler minted it, excluding an ordinary
transformer from the domain.  And its own final component is ordinary, so only the
superseded `components.any` reading excluded it for the namespace it sits under.
Under the live test it is in the domain and so must be in the pin; under either
mutation it drops out and the reconciliation reports its entry as stale.

Minted rather than written because a `def` cannot lack a range: the property being
witnessed is precisely the absence the elaborator always supplies. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let stateTy := Lean.mkConst kernelStateType
  Lean.addDecl (.defnDecl {
    name := `SeLe4n.Testing.KernelTransitionReachabilityCensus._cstage1.censusWitnessMintedTransformer
    levelParams := []
    type := .forallE `st stateTy stateTy .default
    value := .lam `st stateTy (.bvar 0) .default
    hints := .abbrev
    safety := .safe })

/-- A transformer nothing calls, reachable from `censusWitnessErasedRoot` only
through a PROOF. -/
private def censusWitnessErasedTransformer (st : Model.SystemState) :
    Model.SystemState := st

/-- The proof that mentions it.  Proved by `unfold` rather than by `rfl`, because
what an erasure-blind walk follows is this theorem's **value**, and `rfl`'s
elaborated term need not name the constant its type mentions — a witness whose
proof term does not carry the transformer is inert, and an inert witness reads as
coverage while asserting nothing.  `erasureWitnessViolations` asserts it rather
than trusting it. -/
private def censusWitnessErasedProp (st : Model.SystemState) : Prop :=
  censusWitnessErasedTransformer st = st

private theorem censusWitnessErasedLemma (st : Model.SystemState) :
    censusWitnessErasedProp st := by
  unfold censusWitnessErasedProp censusWitnessErasedTransformer
  rfl

/-- A function that CONSUMES a proof, generically in the proposition.

Generic on purpose, and it is the second thing this witness had to get right:
`Expr.getUsedConstants` walks binder **types** as well as bodies, so a consumer
whose argument is typed `censusWitnessErasedTransformer st = st` reaches the
transformer through its own signature — a type-level mention, which is not
execution either, but is not the *erased* route the witness is about.  With `P`
abstract, the only route from the root below to the transformer runs through the
theorem's proof term.  It is not a state transformer, so it needs no pin entry: its
result is a variable. -/
private def censusWitnessProofConsumer {α : Sort u} {P : Prop} (a : α) (_h : P) :
    α := a

/-- A root whose elaborated body carries the lemma as an argument, and therefore
reaches the transformer through an erased dependency and through nothing else.
`liveClosure` must not follow it. -/
private def censusWitnessErasedRoot (st : Model.SystemState) : Model.SystemState :=
  censusWitnessProofConsumer st (censusWitnessErasedLemma st)

/-- **WS-RR / PR #897 review (`v0.35.128`): the carrier fixpoint's exhaustion refusal
FIRES.**

`stateCarryingTypes` throws when it exits with work outstanding, because returning a
partial carrier set certifies an under-approximated domain and every transition holding
an omitted wrapper then sits in neither the reachable nor the unreachable set.  On this
tree the fixpoint converges after 2 rounds against a bound of 12, so the throw is
unreachable in production — and *a check that cannot fire and carries no witness is
indistinguishable from one that is wrong*, which is why the bound is an argument.

At a bound of **1** the derivation cannot converge (`SystemState` alone is round one's
input, and the wrappers that hold it are found in round two), so the call must fail.
The witness reports a problem when it **succeeds**, which is the only direction that
can be silent: a refusal deleted, or a bound raised past the point where it binds, both
leave this returning a violation. -/
def carrierFixpointRefusalViolations (env : Environment) : MetaM (List String) := do
  let converged ← tryCatch
    (do let _ ← stateCarryingTypes env 1; pure true)
    (fun _ => pure false)
  if converged then
    pure ["carrier fixpoint at a bound of 1 SUCCEEDED: `stateCarryingTypes` no \
      longer refuses exhaustion, so a carrier chain longer than the bound would be \
      returned as a complete set and this census would pass over every transition \
      holding an omitted wrapper."]
  else
    pure []

/-- The erasure claim, decided against the walk itself rather than against the
whole pipeline: no committing export reaches these witnesses, so the pipeline
could not exercise the arm.  Both directions, because a walk that followed
nothing would satisfy the first clause vacuously. -/
def erasureWitnessViolations (env : Environment) : List String := Id.run do
  let mut out : List String := []
  let some live := liveClosure env [``censusWitnessErasedRoot]
    | return out ++ ["`liveClosure` exhausted its fuel on the erasure \
        witness's own root, so both clauses below decide nothing."]
  if live.contains ``censusWitnessErasedTransformer then
    out := out ++ ["`liveClosure` followed an ERASED dependency: \
      `censusWitnessErasedRoot` reaches `censusWitnessErasedTransformer` only \
      through `censusWitnessErasedLemma`, whose body Lean compiles away."]
  if !live.contains ``censusWitnessErasedRoot then
    out := out ++ ["`liveClosure` does not contain its own root, so the erasure \
      witness above holds vacuously and decides nothing."]
  match (env.find? ``censusWitnessErasedLemma).bind (·.value? (allowOpaque := true)) with
  | none =>
    out := out ++ ["`censusWitnessErasedLemma` has no value, so the erasure \
      witness carries no erased reference and asserts nothing."]
  | some v =>
    if !v.getUsedConstants.contains ``censusWitnessErasedTransformer then
      out := out ++ ["`censusWitnessErasedLemma`'s proof term does not mention \
        `censusWitnessErasedTransformer`, so the erasure witness is INERT: the \
        permissive walk it is meant to refute would not have followed it either."]
  return out

/-- The refusal above, exercised on a tree where the real bound is never reached.

`liveClosureFuel` is two orders of magnitude above this kernel's closure, so nothing
in production can make the walk answer `none` — and a refusal no input reaches is
indistinguishable from one that is wrong.  The witness drives the same walk at a fuel
of **1**, where it provably cannot complete (one pop leaves the root's own used
constants on the worklist), and reports a violation when the call **succeeds**.

That is the only direction that can go silent: delete the `none` arm, or reverse the
two match arms so exhaustion is read as completion, and this returns a violation.
The root is the planted erasure witness rather than the census's own export list, so
the claim does not depend on how many committing seams the tree happens to have. -/
def liveClosureRefusalViolations (env : Environment) : List String :=
  match liveClosure env [``censusWitnessErasedRoot] (fuel := 1) with
  | some _ => ["`liveClosure` at a fuel of 1 SUCCEEDED, so its exhaustion arm is \
      unreachable and the refusal it reports is untested: an exhausted walk would \
      hand back a partial `live` set, and a pin entry that has become live would \
      still look unreachable."]
  | none => []

/-- The committing exports, derived exactly as `ExportCommitDisciplineCensus`
derives them — through that census's own `commitsState`, so the two cannot
disagree about what installs kernel state. -/
def committingExports (env : Environment) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for (n, _) in env.constants.toList do
    if isProjectConstant n && (getExportNameFor? env n).isSome && commitsState env n then
      out := out.push n
  return out

/-- Every state transformer the live closure does not reach, as of this cut.

A **pin**, in the shape `scripts/identifier_naming_baseline.json` uses for the
same reason: the set is derived above, and this list is what makes a *change* to
it visible.  It carries no per-entry prose, deliberately — a few hundred shallow
reasons would read as justification while asserting nothing, and the obligation
that does the work falls on whoever adds the next entry, who must either wire it
or say here why it exists.

**The four-member residue this list named closed at `v0.35.192`**, and the
judgement went both ways, which is why it was a decision rather than a line.
`cleanupActiveDonation` and `endpointCallWithDonation` are **deleted**: the first
was Z7-E's alias for `returnDonatedSchedContext` whose scenario the live
`cleanupPreReceiveDonation{,Checked,Migrated}` family implements, the second Z7's
single-core donation-aware Call that `endpointCallCrossCoreDispatch` superseded,
tied to it by no equivalence theorem.  `timerTickChecked` and
`switchDomainChecked` are **kept**, because they are two of the four X2-I
API-boundary wrappers and deleting half of a symmetric family is the asymmetry
this project's implement-the-improvement rule forbids — so they gained the
witnesses their two driven siblings have (`tests/NegativeStateSuite.lean`), which
closes *"no suite drives them"* while leaving *"outside the live closure"* true
and recorded **here**, where it belongs.

**The revocation family's residue closed at `v0.35.190` (WS-RR RR8.16)**, and
what is left of it here is a *narrower* claim than the one that was registered.
`API.lean` gained the `.cspaceRevoke` arm, so `cspaceRevoke`, `cspaceRevokeCdt`,
`revokeCdtScaffold`, `revokeCdtMaterializedTraversal`, `revokeCdtFoldBody`,
`processRevokeNode` and the in-flight sweep are all in the live closure and have
left this list.  What remains are the three **reporting variants**
(`cspaceRevokeCdtStrict`, `cspaceRevokeCdtStreaming`,
`cspaceRevokeCdtTransactional`) with their traversals, the streaming BFS and the
reporting fold step: each is the same scaffold at a different traversal, offered
to *in-kernel* callers that want a structured failure report or an
`O(branching-factor)` walk, and the syscall arm dispatches the materialized
variant because a userspace invocation has no channel to receive a report
through.  A variant with no in-kernel caller either gains one or is retired;
that is a smaller question than the one the register row asked, and it is what
the row was closed down to.

**And the local `cspaceRevoke` is back on this list since `v0.36.1`** (PR #900
review), for the opposite reason from the variants: it was in the live closure
only as `revokeCdtScaffold`'s prologue, and that prologue is a read of the source
slot now, because the local sweep matched on the **target** and so destroyed
capabilities that were not derivations — an independently rooted capability to
the same object, and the revoked capability's own parent.  What still runs it is
`lifecycleRevokeDeleteRetype`, an internal proof helper already on this list, and
the non-interference operation catalogue, where it is an operation in its own
right; no syscall reaches it. -/
def nonExecutedTransitionsPlain : List Name :=
  [ `SeLe4n.Kernel.Architecture.TlbCacheJointState.empty
  , `SeLe4n.Kernel.Architecture.TlbCacheJointState.pageTableUpdate
  , `SeLe4n.Kernel.Architecture.TlbCacheJointState.sysState
  , `SeLe4n.Kernel.Architecture.ackInterruptAudit
  , `SeLe4n.Kernel.Architecture.adapterAdvanceTimer
  , `SeLe4n.Kernel.Architecture.adapterContextSwitch
  , `SeLe4n.Kernel.Architecture.adapterFlushTlbByAsidHw
  , `SeLe4n.Kernel.Architecture.adapterFlushTlbByVAddrHw
  , `SeLe4n.Kernel.Architecture.adapterFlushTlbHw
  , `SeLe4n.Kernel.Architecture.adapterReadMemory
  , `SeLe4n.Kernel.Architecture.adapterWriteRegister
  , `SeLe4n.Kernel.Architecture.advanceTimerState
  , `SeLe4n.Kernel.Architecture.asidAllocateWithShootdown
  , `SeLe4n.Kernel.Architecture.contextSwitchState
  , `SeLe4n.Kernel.Architecture.dispatchException
  , `SeLe4n.Kernel.Architecture.dispatchSynchronousException
  , `SeLe4n.Kernel.Architecture.endOfInterrupt
  , `SeLe4n.Kernel.Architecture.handleInterrupt
  , `SeLe4n.Kernel.Architecture.handleTlbShootdownReqOnCore
  , `SeLe4n.Kernel.Architecture.handleTlbShootdownReqOnCorePerCore
  , `SeLe4n.Kernel.Architecture.icFetchOnCore
  , `SeLe4n.Kernel.Architecture.icInvalidateOnCore
  , `SeLe4n.Kernel.Architecture.interruptDispatchSequence
  , `SeLe4n.Kernel.Architecture.markTlbBarriered
  , `SeLe4n.Kernel.Architecture.markTlbDirty
  , `SeLe4n.Kernel.Architecture.setIcacheOnCore
  , `SeLe4n.Kernel.Architecture.shootdownCatchUpPerCore
  , `SeLe4n.Kernel.Architecture.shootdownRound
  , `SeLe4n.Kernel.Architecture.shootdownRoundPerCore
  , `SeLe4n.Kernel.Architecture.stageCancelledIpcFrame
  , `SeLe4n.Kernel.Architecture.stageTimeoutFrame
  , `SeLe4n.Kernel.Architecture.timerInterruptHandler
  , `SeLe4n.Kernel.Architecture.tlbFlushByPage
  , `SeLe4n.Kernel.Architecture.tlbFlushByPageWithShootdown
  , `SeLe4n.Kernel.Architecture.tlbInvalidateOnAllCores
  , `SeLe4n.Kernel.Architecture.tlbInvalidateOnAllCoresCoalescing
  , `SeLe4n.Kernel.Architecture.tlbInvalidateOnCore
  , `SeLe4n.Kernel.Architecture.tlbShootdownBroadcast
  , `SeLe4n.Kernel.Architecture.tlbShootdownBroadcastIn
  , `SeLe4n.Kernel.Architecture.tlbShootdownDrainOnCore
  , `SeLe4n.Kernel.Architecture.tlbShootdownLocal
  , `SeLe4n.Kernel.Architecture.tlbShootdownLocalPerCore
  , `SeLe4n.Kernel.Architecture.vspaceLookup
  , `SeLe4n.Kernel.Architecture.vspaceLookupFull
  , `SeLe4n.Kernel.Architecture.vspaceMapPageChecked
  , `SeLe4n.Kernel.Architecture.vspaceMapPageCheckedWithFlush
  , `SeLe4n.Kernel.Architecture.vspaceMapPageCheckedWithFlushPlatform
  , `SeLe4n.Kernel.Architecture.writeRegisterState
  , `SeLe4n.Kernel.Architecture.writeRestartFrameToTcb
  , `SeLe4n.Kernel.Concurrency.KernelTransitionInstance.action
  , `SeLe4n.Kernel.Concurrency.KernelTransitionInstance.ofWithLockSet
  , `SeLe4n.Kernel.Concurrency.applySequential
  , `SeLe4n.Kernel.Concurrency.applySequentialWithLockSet
  , `SeLe4n.Kernel.Concurrency.commitSort
  , `SeLe4n.Kernel.Concurrency.insertByCommitTime
  , `SeLe4n.Kernel.Concurrency.objStoreWriteInstance
  -- WS-RR RR8.12 Cut C6h (`v0.35.181`): the OBJECT domain's bracket instance.
  -- The syscall seam moved to `schedulerLockBracketDomain` over the unified
  -- footprint, so nothing a committing `@[export]` reaches acquires through this
  -- one any more.  Not retired: it is the domain `runUnderDeclaredLockSet` is an
  -- instance of, and the CSpace-walk bracket that still reads it is STAGED, so
  -- no runtime path executes it.  It becomes live again when that surface is
  -- promoted, or when a second object-domain seam is bracketed.
  , `SeLe4n.Kernel.Concurrency.objectLockBracketDomain
  , `SeLe4n.Kernel.Concurrency.readOnlyInstance
  , `SeLe4n.Kernel.Concurrency.runChainExtension
  , `SeLe4n.Kernel.Concurrency.setObjStoreLockAction
  , `SeLe4n.Kernel.Concurrency.setSchedulerAction
  , `SeLe4n.Kernel.Concurrency.withDynamicChainExtension
  , `SeLe4n.Kernel.Internal.lifecycleRetypeObject
  , `SeLe4n.Kernel.Lifecycle.Suspend.cancelBoundDonation
  , `SeLe4n.Kernel.Lifecycle.Suspend.cancelDonatedDonation
  , `SeLe4n.Kernel.Lifecycle.Suspend.cancelDonation
  , `SeLe4n.Kernel.Lifecycle.Suspend.cancelDonationValid
  , `SeLe4n.Kernel.Lifecycle.Suspend.cancelIpcBlockingValid
  , `SeLe4n.Kernel.Lifecycle.Suspend.restoreToReadyMidState
  , `SeLe4n.Kernel.Lifecycle.Suspend.restoreToReadyOnCore
  , `SeLe4n.Kernel.Lifecycle.Suspend.restoreToReadyWithWake
  , `SeLe4n.Kernel.Lifecycle.Suspend.resumeThread
  , `SeLe4n.Kernel.Lifecycle.Suspend.suspendThread
  , `SeLe4n.Kernel.Liveness.CanonicalDeploymentProgress.exitState
  , `SeLe4n.Kernel.Liveness.CanonicalDeploymentProgressOnCore.exitState
  , `SeLe4n.Kernel.Liveness.stepPost
  , `SeLe4n.Kernel.Liveness.traceStateAt
  , `SeLe4n.Kernel.PriorityInheritance.propagatePipChainCrossCoreState
  , `SeLe4n.Kernel.PriorityInheritance.propagatePriorityInheritance
  , `SeLe4n.Kernel.PriorityInheritance.withPipChainSchedExtension
  , `SeLe4n.Kernel.SchedContext.PriorityManagement.migrateRunQueueBucket
  , `SeLe4n.Kernel.SchedContext.PriorityManagement.setMCPriorityOp
  , `SeLe4n.Kernel.SchedContext.PriorityManagement.setPriorityOp
  , `SeLe4n.Kernel.SchedContextOps.schedContextYieldTo
  , `SeLe4n.Kernel.advanceDomainOnCore
  , `SeLe4n.Kernel.advanceDomainOnCoreN
  , `SeLe4n.Kernel.applyReplyDonation
  , `SeLe4n.Kernel.cancelDonationOnCore
  , `SeLe4n.Kernel.cancelIpcBlockingOnCore
  , `SeLe4n.Kernel.chooseThread
  , `SeLe4n.Kernel.chooseThreadEffective
  , `SeLe4n.Kernel.chooseThreadInDomain
  , `SeLe4n.Kernel.cleanupPreReceiveDonation
  , `SeLe4n.Kernel.cleanupPreReceiveDonation_never_errors_under_ipcInvariantFull
  , `SeLe4n.Kernel.commitKernelAction
  , `SeLe4n.Kernel.continueFromAcquired
  , `SeLe4n.Kernel.cspaceLookupMultiLevel
  , `SeLe4n.Kernel.cspaceLookupPath
  , `SeLe4n.Kernel.cspaceMutate
  , `SeLe4n.Kernel.cspaceResolvePath
  , `SeLe4n.Kernel.cspaceRevoke
  , `SeLe4n.Kernel.cspaceRevokeCdtStreaming
  , `SeLe4n.Kernel.cspaceRevokeCdtStrict
  , `SeLe4n.Kernel.cspaceRevokeCdtTransactional
  , `SeLe4n.Kernel.declassifyRun
  , `SeLe4n.Kernel.declassifyStore
  , `SeLe4n.Kernel.declassifyStoreFromCore
  , `SeLe4n.Kernel.declassifyStoreOnCore
  , `SeLe4n.Kernel.descheduleThread
  , `SeLe4n.Kernel.dispatchSyscall
  , `SeLe4n.Kernel.dispatchWithCap
  , `SeLe4n.Kernel.donationChainWitness
  , `SeLe4n.Kernel.endpointCall
  , `SeLe4n.Kernel.endpointCallChecked
  , `SeLe4n.Kernel.endpointCallWithCaps
  , `SeLe4n.Kernel.endpointReceiveDual
  , `SeLe4n.Kernel.endpointReceiveDualChecked
  , `SeLe4n.Kernel.endpointReceiveDualWithCaps
  , `SeLe4n.Kernel.endpointReply
  , `SeLe4n.Kernel.endpointReplyChecked
  , `SeLe4n.Kernel.endpointReplyRecv
  , `SeLe4n.Kernel.endpointReplyRecvChecked
  , `SeLe4n.Kernel.endpointReplyRecvOnCore
  , `SeLe4n.Kernel.endpointReplyRecvWithDonation
  , `SeLe4n.Kernel.endpointReplyWithDonation
  , `SeLe4n.Kernel.endpointSendDual
  , `SeLe4n.Kernel.endpointSendDualChecked
  , `SeLe4n.Kernel.endpointSendDualWithCaps
  , `SeLe4n.Kernel.endpointSweepBody
  , `SeLe4n.Kernel.enqueueIdleThreadOnCore
  , `SeLe4n.Kernel.ensureRunnable
  , `SeLe4n.Kernel.faultAbandon
  , `SeLe4n.Kernel.faultSuspend
  , `SeLe4n.Kernel.handleYield
  , `SeLe4n.Kernel.handleYieldChecked
  , `SeLe4n.Kernel.handleYieldWithBudget
  , `SeLe4n.Kernel.lifecycleCleanupPipeline
  , `SeLe4n.Kernel.lifecyclePreRetypeCleanupWithToken
  , `SeLe4n.Kernel.lifecycleRetypeWithCleanup
  , `SeLe4n.Kernel.lifecycleRetypeWithCleanupShootdown
  , `SeLe4n.Kernel.lifecycleRetypeWithCleanupShootdownPerCore
  , `SeLe4n.Kernel.lifecycleRetypeWithCleanupShootdownPerCoreIcache
  , `SeLe4n.Kernel.lifecycleRevokeDeleteRetype
  , `SeLe4n.Kernel.lockSetAcquiredState
  , `SeLe4n.Kernel.notificationPurgeBody
  , `SeLe4n.Kernel.notificationSignal
  , `SeLe4n.Kernel.notificationSignalBound
  , `SeLe4n.Kernel.notificationSignalBoundCrossCoreDispatch
  , `SeLe4n.Kernel.notificationSignalChecked
  , `SeLe4n.Kernel.notificationWait
  , `SeLe4n.Kernel.notificationWaitChecked
  , `SeLe4n.Kernel.notificationWaitCrossCoreDispatch
  , `SeLe4n.Kernel.processReplenishmentsDue
  , `SeLe4n.Kernel.purgedAndRestored
  , `SeLe4n.Kernel.registerInterface
  -- WS-RR RR8.12 Cut C6h (`v0.35.181`): RR7.12's object-domain bracket at the
  -- ABI seam, superseded there by `Concurrency.runBracketed schedulerLock\
  -- BracketDomain` over `declaredUnifiedLockSetForAbiEntry` — the two domains
  -- write the same lock words, so nesting two brackets would take the
  -- object-store table lock twice.  Its remaining reader is the STAGED CSpace
  -- walk (`withCSpaceWalkLocks`), which no committing seam runs; the
  -- export-commit census still names it a bracket form, so a body that reaches
  -- it counts as bracketed.
  , `SeLe4n.Kernel.runUnderDeclaredLockSet
  , `SeLe4n.Kernel.removeRunnable
  , `SeLe4n.Kernel.removeRunnableValid
  , `SeLe4n.Kernel.replenishScOnCore
  , `SeLe4n.Kernel.replyRecvPostPopState
  , `SeLe4n.Kernel.replyTransferOnCore
  , `SeLe4n.Kernel.resolveCapAddressUnderWalkLocks
  , `SeLe4n.Kernel.restoreIncomingContext
  , `SeLe4n.Kernel.restoreIncomingContextChecked
  , `SeLe4n.Kernel.restoredAndConsumed
  , `SeLe4n.Kernel.returnDonatedSchedContextValid
  , `SeLe4n.Kernel.retypeAsidRoundFold
  , `SeLe4n.Kernel.retypeAsidRoundStep
  , `SeLe4n.Kernel.retypeFromUntyped
  , `SeLe4n.Kernel.revokeCdtReportingOutcome
  , `SeLe4n.Kernel.revokeCdtReportingStep
  , `SeLe4n.Kernel.revokeCdtStreamingTraversal
  , `SeLe4n.Kernel.revokeCdtStrictTraversal
  , `SeLe4n.Kernel.revokeCdtTransactionalTraversal
  , `SeLe4n.Kernel.saveOutgoingContext
  , `SeLe4n.Kernel.saveOutgoingContextChecked
  , `SeLe4n.Kernel.schedule
  , `SeLe4n.Kernel.scheduleChecked
  , `SeLe4n.Kernel.scheduleDomain
  , `SeLe4n.Kernel.scheduleEffective
  , `SeLe4n.Kernel.scheduleOrIdleOnCore
  , `SeLe4n.Kernel.serviceRegisterDependency
  , `SeLe4n.Kernel.setObjectLockAt
  , `SeLe4n.Kernel.setThreadCpuAffinityOp
  , `SeLe4n.Kernel.storeServiceEntry
  , `SeLe4n.Kernel.storeTcbIpcState_fromTcb
  , `SeLe4n.Kernel.storeTcbPendingMessage
  , `SeLe4n.Kernel.streamingRevokeBFS
  , `SeLe4n.Kernel.sweptAndRestored
  , `SeLe4n.Kernel.switchDomain
  , `SeLe4n.Kernel.switchDomainChecked
  , `SeLe4n.Kernel.syncThreadStates
  , `SeLe4n.Kernel.syscallEntry
  , `SeLe4n.Kernel.syscallEntryFromAcquired
  , `SeLe4n.Kernel.syscallEntryUnderDeclaredLockSet
  , `SeLe4n.Kernel.syscallEntryUnderLockSet
  , `SeLe4n.Kernel.syscallEntryUnderRevalidatedLockSet
  , `SeLe4n.Kernel.syscallEntryUnderRevalidatedLockSetModel
  , `SeLe4n.Kernel.syscallLookupReplyId
  , `SeLe4n.Kernel.timeoutAwareReceive
  , `SeLe4n.Kernel.timerTick
  , `SeLe4n.Kernel.timerTickBudget
  , `SeLe4n.Kernel.timerTickChecked
  , `SeLe4n.Kernel.timerTickOnCorePreDomain
  , `SeLe4n.Kernel.timerTickOnCorePrepared
  , `SeLe4n.Kernel.timerTickWithBudget
  , `SeLe4n.Kernel.withObjects
  , `SeLe4n.Model.Builder.createObject
  , `SeLe4n.Model.Builder.insertCap
  , `SeLe4n.Model.Builder.mapPage
  , `SeLe4n.Model.Builder.markRunnable
  , `SeLe4n.Model.Builder.registerIrq
  , `SeLe4n.Model.Builder.registerService
  , `SeLe4n.Model.Builder.withTaint
  , `SeLe4n.Model.IntermediateState.state
  , `SeLe4n.Model.SystemState.withObjectStored
  , `SeLe4n.Model.lookupObject
  , `SeLe4n.Model.lookupVSpaceRoot
  , `SeLe4n.Model.mkEmptyIntermediateState
  , `SeLe4n.Model.setCurrentThread
  , `SeLe4n.Model.setDomainScheduleChecked
  , `SeLe4n.Model.storeObjectChecked
  , `SeLe4n.Model.storeObjectKindChecked
  , `SeLe4n.Model.storeServiceState
  , `SeLe4n.Platform.Boot.applyMachineConfig
  , `SeLe4n.Platform.Boot.applyMachineConfigChecked
  , `SeLe4n.Platform.Boot.bootEnableInterruptsOp
  , `SeLe4n.Platform.Boot.bootFromPlatform
  , `SeLe4n.Platform.Boot.bootFromPlatformChecked
  , `SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreads
  , `SeLe4n.Platform.Boot.bootFromPlatformCheckedWithIdleThreadsFor
  , `SeLe4n.Platform.Boot.bootFromPlatformUnchecked
  , `SeLe4n.Platform.Boot.bootFromPlatformWithIdleThreads
  , `SeLe4n.Platform.Boot.bootFromPlatformWithInterrupts
  , `SeLe4n.Platform.Boot.bootFromPlatformWithWarnings
  , `SeLe4n.Platform.Boot.createBootObject
  , `SeLe4n.Platform.Boot.enqueueIdleThread
  , `SeLe4n.Platform.Boot.foldIrqs
  , `SeLe4n.Platform.Boot.foldObjects
  , `SeLe4n.Platform.Boot.installBootVSpaceRoot
  , `SeLe4n.Platform.Boot.installIdleThread
  , `SeLe4n.Platform.FFI.bootAndInitialiseFromPlatform
  , `SeLe4n.Platform.FFI.bootAndInitialiseFromPlatformOn
  , `SeLe4n.Platform.FFI.bootAndInitialisePlatform
  , `SeLe4n.Platform.FFI.bootAndInitialiseRPi5
  , `SeLe4n.Platform.FFI.getKernelState
  , `SeLe4n.Platform.RPi5.mmioRead
  , `SeLe4n.Platform.RPi5.mmioRead32
  , `SeLe4n.Platform.RPi5.mmioRead64
  , `SeLe4n.Platform.RPi5.mmioReadByte
  , `SeLe4n.Platform.RPi5.mmioWrite
  , `SeLe4n.Platform.RPi5.mmioWrite32
  , `SeLe4n.Platform.RPi5.mmioWrite32W1C
  , `SeLe4n.Platform.RPi5.mmioWrite64
  , `SeLe4n.Platform.RPi5.rpi5DeploymentBootState
  , `SeLe4n.Testing.KernelTransitionReachabilityCensus._cstage1.censusWitnessMintedTransformer
  ]

/-- The `private` members of the same set.

Lean mangles a `private def` to `_private.<Module>.0.<userName>`, which no name
literal can spell, so each is built with the compiler's own mangling through
`ReplyStackWriteCensus.privateIn`.  Eight of these are that census's own planted
witnesses, which enter this domain because this module imports it for
`isAuxiliary`; they are deliberately not executed, and their presence here is
the derivation working rather than noise to carve out.  One more is **this**
census's own, planted above so the `opaque` arm of its domain is decided by
something on this tree; the control beside it is deliberately absent, since its
result type is not `SystemState` and a widening that admitted it would fail
here. -/
def nonExecutedTransitionsPrivate : List Name :=
  [ privateIn `SeLe4n.Kernel.API `SeLe4n.Kernel.resolveExtraCapsDetailed
  , privateIn `SeLe4n.Kernel.API `SeLe4n.Kernel.resolveExtraCapsGated
  , privateIn `SeLe4n.Kernel.Capability.Invariant.Defs `SeLe4n.Kernel.ScrubTokenImpl.stPre
  , privateIn `SeLe4n.Kernel.IPC.Invariant.DispatchPayoff `SeLe4n.Kernel.witnessSt1
  , privateIn `SeLe4n.Kernel.IPC.Invariant.DispatchPayoff `SeLe4n.Kernel.witnessSt2
  , privateIn `SeLe4n.Kernel.IPC.Invariant.DispatchPayoff `SeLe4n.Kernel.witnessSt3
  , privateIn `SeLe4n.Kernel.IPC.Invariant.DispatchPayoff `SeLe4n.Kernel.witnessSt4
  , privateIn `SeLe4n.Kernel.IPC.Invariant.Reachability `SeLe4n.Kernel.chainWitnessSt1
  , privateIn `SeLe4n.Kernel.IPC.Invariant.Reachability `SeLe4n.Kernel.chainWitnessSt2
  , privateIn `SeLe4n.Testing.ReplyStackWriteCensus `SeLe4n.Testing.ReplyStackWriteCensus.censusWitnessBareConsume
  , privateIn `SeLe4n.Testing.ReplyStackWriteCensus `SeLe4n.Testing.ReplyStackWriteCensus.censusWitnessDelegatedStoreHelper
  , privateIn `SeLe4n.Testing.ReplyStackWriteCensus `SeLe4n.Testing.ReplyStackWriteCensus.censusWitnessDelegatedStoreWriter
  , privateIn `SeLe4n.Testing.ReplyStackWriteCensus `SeLe4n.Testing.ReplyStackWriteCensus.censusWitnessDirectLinkWrite
  , privateIn `SeLe4n.Testing.ReplyStackWriteCensus `SeLe4n.Testing.ReplyStackWriteCensus.censusWitnessRawTableWrite
  , privateIn `SeLe4n.Testing.ReplyStackWriteCensus `SeLe4n.Testing.ReplyStackWriteCensus.censusWitnessSplitWriter
  , privateIn `SeLe4n.Testing.ReplyStackWriteCensus `SeLe4n.Testing.ReplyStackWriteCensus.eq_1
  , privateIn `SeLe4n.Testing.ReplyStackWriteCensus `SeLe4n.Testing.ReplyStackWriteCensus.eq_censusWitnessUserNamed
  , privateIn `SeLe4n.Testing.KernelTransitionReachabilityCensus
      `SeLe4n.Testing.KernelTransitionReachabilityCensus.censusWitnessAliasedTransformer
  , privateIn `SeLe4n.Testing.KernelTransitionReachabilityCensus
      `SeLe4n.Testing.KernelTransitionReachabilityCensus.censusWitnessOpaqueTransformer
  , privateIn `SeLe4n.Testing.KernelTransitionReachabilityCensus
      `SeLe4n.Testing.KernelTransitionReachabilityCensus.CensusWitnessWrapper.carried
  , privateIn `SeLe4n.Testing.KernelTransitionReachabilityCensus
      `SeLe4n.Testing.KernelTransitionReachabilityCensus.censusWitnessErasedRoot
  , privateIn `SeLe4n.Testing.KernelTransitionReachabilityCensus
      `SeLe4n.Testing.KernelTransitionReachabilityCensus.censusWitnessErasedTransformer
  , privateIn `SeLe4n.Testing.KernelTransitionReachabilityCensus
      `SeLe4n.Testing.KernelTransitionReachabilityCensus.censusWitnessWrapperTransformer
  , privateIn `SeLe4n.Testing.KernelTransitionReachabilityCensus
      `SeLe4n.Testing.KernelTransitionReachabilityCensus.initFnCensusWitnessTransformer
  , privateIn `SeLe4n.Testing.KernelTransitionReachabilityCensus
      `SeLe4n.Testing.KernelTransitionReachabilityCensus.censusWitnessNestedAliasTransformer
  , privateIn `SeLe4n.Testing.KernelTransitionReachabilityCensus
      `SeLe4n.Testing.KernelTransitionReachabilityCensus.censusWitnessAliasedSortTransformer
  , privateIn `SeLe4n.Testing.KernelTransitionReachabilityCensus
      `SeLe4n.Testing.KernelTransitionReachabilityCensus._flat_ctor
  , privateIn `SeLe4n.Testing.KernelTransitionReachabilityCensus
      `SeLe4n.Testing.KernelTransitionReachabilityCensus._cstage1.censusWitnessNestedTransformer
  ]

/-- The whole pin. -/
def nonExecutedTransitions : List Name :=
  nonExecutedTransitionsPlain ++ nonExecutedTransitionsPrivate

/-! ## The surfaces that stand beside a live re-composition

The category that carries an obligation.  A **non-executed composite** whose
parts the live path re-composes is the shape WS-RR RR8.12 found: the composite
reads as the transition — its name says `OnCore`, its theorems are the
transition's theorems — while a syscall runs something else built from the same
pieces.  A step added to one side and not the other is then invisible, which is
how a permanent denial of service against a passive server survived two cuts.

Reachability alone cannot see that: the composite existed before the step, so
its entry in the pin above would not have moved.  What sees it is a **theorem
relating the two**, which this list requires: each row names the non-executed
surface, the live definition that re-composes it, and the pin.  Adding a step to
the surface and not to the live path breaks the pin at build time.

A row claims that `pin` relates `surface` to code the live path actually runs,
and the checks below are exactly that: the surface is outside the live closure,
the counterpart is inside it, and the pin's *statement* mentions both.  The
counterpart need not be the whole live program — the second row's pin relates
the surface to the arm functions the suspend pipeline's G3 inlines, and naming
one of them is what makes "the live side of this pin" checkable rather than
asserted.  The list is short because the claim is strong; a composite with no
such pin belongs in the pin above instead. -/
def standsBesideLive : List (Name × Name × Name) :=
  [ -- WS-RR RR8.12 (second cut): `cancelIpcBlockingOnCore` is the teardown, its
    -- reclaim and the victim's deschedule; the live `.tcbSuspend` pipeline runs
    -- the reclaim as its G2 and descheduls at G4.  This pin is what the cut
    -- that found the defect added.
    (`SeLe4n.Kernel.cancelIpcBlockingOnCore,
     `SeLe4n.Kernel.cancelIpcBlockingReclaimed,
     `SeLe4n.Kernel.cancelIpcBlockingOnCore_eq_reclaimed_deschedule)
    -- WS-RR RR8.12 (second cut), the sweep's own finding one level down: the
    -- suspend pipeline's G3 re-spells the dispatcher rather than calling it.
  , (`SeLe4n.Kernel.cancelDonationOnCore,
     `SeLe4n.Kernel.cancelBoundDonationOnCore,
     `SeLe4n.Kernel.suspendDonationArm_eq_cancelDonationOnCore)
  ]

/-! ## Reconciliation -/

/-- Where the derived partition and the pin disagree.

Both directions, for the reason `ExportCommitDisciplineCensus` gives for its
own: a **new** non-executed transformer is the dangerous one, since it is a
transition nobody runs that nobody has had to explain; a **stale** entry is the
harmless one and is still a failure, because a pin that no longer describes the
tree understates coverage as silently as it overstates it. -/
def reconciliationViolations (live unreachable : NameSet)
    (recorded : List Name) : List String := Id.run do
  let recordedSet : NameSet := recorded.foldl (fun acc n => acc.insert n) {}
  let mut out : List String := []
  for n in unreachable.toList do
    if !recordedSet.contains n then
      out := out ++ [s!"`{n}` transforms kernel state and no committing `@[export]` can \
        reach it, and it is not in `nonExecutedTransitions`.  Either wire it to the seam \
        that should run it, or record it there — a transition nobody runs and nobody has \
        explained is the shape WS-RR RR8.12 found."]
  for n in recorded do
    if !unreachable.contains n then
      if live.contains n then
        out := out ++ [s!"`{n}` is recorded as not on an executed path and a committing \
          `@[export]` now reaches it; delete the entry, the pin understates what this \
          kernel runs."]
      else
        out := out ++ [s!"`{n}` is recorded in `nonExecutedTransitions` and is not a state \
          transformer in this environment — a stale entry, or a module this census no \
          longer imports."]
  return out

/-- The two sides of a two-sided relation, or `none` if the conclusion is not one.

`Eq` and `Iff` are the two shapes a pin between two programs can take; anything
else -- a conjunction, an implication, a bare predicate -- relates nothing that
this check can read.

The telescope is stripped by `ReplyStackWriteCensus.conclusionOf`, which this
module already imports and which strips `letE` and `mdata` as well as `forallE`:
*before writing a helper, find the one this tree already has.*  The binders are
not instantiated, which is exactly right here -- loose bound variables carry no
constants, and `getUsedConstants` is the only thing read. -/
def pinSides (ty : Expr) : Option (Expr × Expr) :=
  let concl := conclusionOf ty
  match concl.eq? with
  | some (_, l, r) => some (l, r)
  | none =>
    match concl with
    | .app (.app (.const ``Iff _) l) r => some (l, r)
    | _ => none

/-- **Is this pin a RELATION between the two programs?** (PR #897 review.)

The question this replaces was *does the statement mention both constants*, which
is this project's oldest rule failing in the gate written to enforce a different
one: **a presence check is not a relation check.**  A conjunction of reflexive
equations mentions both and says nothing; so does a reflexive equation over a
pair built from both; so does an equation with both programs on one side.  Each
of those satisfies "mentions both" and leaves a step free to be added to either
program alone, which is the whole content of the claim.

What is required instead: the conclusion is `Eq` or `Iff`, and **each program
occurs on exactly one side, on opposite sides**.  A statement of that shape has
one side built from the surface without naming the counterpart and the other
built from the counterpart without naming the surface, so it necessarily connects
the two.  The structural inequality of the sides falls out of it rather than
being asked for separately.

**What it still cannot decide**, stated rather than left to be rediscovered: that
the equation is about the *whole* program rather than a projection of it
(`(surface ..).1 = (counterpart ..).1` passes), and that the two sides are
applied at corresponding arguments.  Those are questions about what a proposition
*means*, and no reading of its syntax answers them; the check over-approximates
there, so it fails closed on shape and admits a narrow-but-real relation. -/
def pinRelatesPrograms (ty : Expr) (surface counterpart : Name) : Bool :=
  match pinSides ty with
  | none => false
  | some (l, r) =>
    let lc := l.getUsedConstants
    let rc := r.getUsedConstants
    -- Each program on exactly one side...
    (lc.contains surface != rc.contains surface)
      && (lc.contains counterpart != rc.contains counterpart)
      -- ...and not the same side.
      && (lc.contains surface != lc.contains counterpart)

/-- Where a `standsBesideLive` row does not hold up. -/
def pinViolations (env : Environment) (live unreachable : NameSet)
    (rows : List (Name × Name × Name)) : List String := Id.run do
  let mut out : List String := []
  for (surface, counterpart, pin) in rows do
    if !unreachable.contains surface then
      out := out ++ [s!"`{surface}` is recorded as standing beside a live re-composition \
        and is not itself outside the live closure; the row's subject has changed."]
    if !live.contains counterpart then
      out := out ++ [s!"`{surface}`'s recorded live counterpart `{counterpart}` is not \
        reachable from any committing `@[export]`, so the row relates two things neither \
        of which runs."]
    match env.find? pin with
    | none =>
        out := out ++ [s!"`{surface}`'s pin `{pin}` does not exist; without it nothing \
          relates the surface to `{counterpart}` and a step may be added to either alone."]
    | some ci =>
        match ci with
        | .thmInfo ti =>
            if !pinRelatesPrograms ti.type surface counterpart then
              out := out ++ [s!"`{pin}` does not RELATE `{surface}` to `{counterpart}`: a \
                pin's conclusion must be an `Eq` or an `Iff` with each program on exactly \
                one side and the two on opposite sides.  Merely mentioning both is a \
                presence check -- a conjunction of reflexive equations passes it -- and \
                leaves a step free to be added to either program alone."]
        | _ =>
            out := out ++ [s!"`{pin}` is not a theorem; a pin between two programs is a \
              proposition about both."]
  return out

/-! ### Witnesses that the pin check decides

Both live rows pass, so nothing on this tree exercises the refusal: a check that
cannot fire is indistinguishable from one that is wrong.  The three theorems
below are the shapes the superseded *presence* check accepted -- each mentions
both programs and relates nothing -- and the census asserts that all three are
refused, beside a control asserting the live pin is accepted, so the refusal is
known to be about the shape rather than about the row. -/

/-- Witness: a conjunction of reflexive equations.  Mentions both programs,
relates nothing; the shape the review named. -/
theorem pinWitnessConjunctionOfReflexivity :
    (@SeLe4n.Kernel.cancelIpcBlockingOnCore = @SeLe4n.Kernel.cancelIpcBlockingOnCore)
      ∧ (@SeLe4n.Kernel.cancelIpcBlockingReclaimed
          = @SeLe4n.Kernel.cancelIpcBlockingReclaimed) :=
  ⟨rfl, rfl⟩

/-- Witness: one equation, both programs on **both** sides.  `Eq`-headed, so a
head test alone admits it, and reflexive, so it asserts nothing. -/
theorem pinWitnessReflexiveOverBoth :
    (@SeLe4n.Kernel.cancelIpcBlockingOnCore, @SeLe4n.Kernel.cancelIpcBlockingReclaimed)
      = (@SeLe4n.Kernel.cancelIpcBlockingOnCore,
         @SeLe4n.Kernel.cancelIpcBlockingReclaimed) := rfl

/-- Witness: both programs on **one** side.  The sides differ structurally, so a
"not reflexive" test admits it, and the projection discards the counterpart. -/
theorem pinWitnessBothOnOneSide :
    (@SeLe4n.Kernel.cancelIpcBlockingOnCore, @SeLe4n.Kernel.cancelIpcBlockingReclaimed).1
      = @SeLe4n.Kernel.cancelIpcBlockingOnCore := rfl

/-- The three shapes above, each of which must be refused. -/
def pinCheckWitnesses : List Name :=
  [ ``pinWitnessConjunctionOfReflexivity
  , ``pinWitnessReflexiveOverBoth
  , ``pinWitnessBothOnOneSide ]

/-- Every witness shape is refused.

The **acceptance** direction needs no witness of its own: `pinViolations` runs
over `standsBesideLive` in the same block, and both live rows are real relations,
so a change that refused everything would fail there.  Keeping the rows a fix does
not change is what distinguishes a narrowing from a disabling, and those rows are
them. -/
def pinCheckWitnessViolations (env : Environment) : List String := Id.run do
  let surface := `SeLe4n.Kernel.cancelIpcBlockingOnCore
  let counterpart := `SeLe4n.Kernel.cancelIpcBlockingReclaimed
  let mut out : List String := []
  for w in pinCheckWitnesses do
    match env.find? w with
    | some (.thmInfo ti) =>
        if pinRelatesPrograms ti.type surface counterpart then
          out := out ++ [s!"the pin check ACCEPTS `{w}`, which mentions both programs and \
            relates nothing -- it has degenerated into the presence check PR #897's review \
            named, and a step may again be added to either program alone."]
    | _ =>
        out := out ++ [s!"pin-check witness `{w}` is missing or is not a theorem; without \
          it nothing on this tree exercises the refusal, and a check that cannot fire is \
          indistinguishable from one that is wrong."]
  return out

/-! ## The census -/

run_cmd Command.liftTermElabM do
  let env ← getEnv
  let roots := committingExports env
  let some live := liveClosure env roots.toList
    | throwError "the live closure exhausted its fuel of {liveClosureFuel}: the \
      reachable set is a strict UNDER-approximation, so a transformer recorded \
      in `nonExecutedTransitions` that has since been wired would still look \
      unreachable and its now-stale entry would pass.  Raise `liveClosureFuel` \
      and re-measure the closure size in its docstring."
  let carriers ← stateCarryingTypes env
  let mut domainSize : Nat := 0
  let mut unreachable : NameSet := {}
  for (n, ci) in env.constants.toList do
    if (← isStateTransformer carriers n ci) then
      domainSize := domainSize + 1
      if !live.contains n then unreachable := unreachable.insert n
  let recorded := nonExecutedTransitions
  let violations :=
    reconciliationViolations live unreachable recorded ++
    pinViolations env live unreachable standsBesideLive ++
    pinCheckWitnessViolations env ++
    erasureWitnessViolations env ++
    liveClosureRefusalViolations env ++
    (← carrierFixpointRefusalViolations env)
  if violations.isEmpty then
    let unreachableCount := unreachable.toList.length
    let carrierCount := carriers.toList.length - 1
    logInfo s!"kernel-transition reachability census: {domainSize} state transformers \
      over {carrierCount} state-carrying wrapper type(s) beside `SystemState`, \
      {domainSize - unreachableCount} reachable from one of {roots.size} committing \
      `@[export]`s by a COMPUTATIONAL path, {unreachableCount} not — every one of \
      them recorded, and {standsBesideLive.length} RELATED to code the live path \
      runs, with {pinCheckWitnesses.length} witness shapes refused."
  else
    throwError "kernel-transition reachability census failed:\n{
      String.intercalate "\n" (violations.map ("  - " ++ ·))}"

end SeLe4n.Testing.KernelTransitionReachabilityCensus
