import Lean.Elab.Command
import Lean.Meta.Basic
import SeLe4n.Platform.Staged

/-!
# The elaborator-backed de-threading census

The structural endpoint of the RR3.1 text gate
(`scripts/check_ipc_invariant_dethreading.py`), registered as WS-DT debt
and pulled forward by review evidence: eight review-round findings in two
rounds were each one more fragment of Lean's elaborator semantics — binder
telescopes, grouped binders, named-argument order, notation expansion,
structure entailment, `∨`-entailment — that a text approximation must
re-implement and can only approximate.  Here the environment answers
directly: binders arrive resolved, notation is long gone, structures have
fields, and definitional unfolding is a `MetaM` call.

**What it checks.**  For every constant whose *final name component*
carries a family marker (`_preserves_ipcInvariantFull` /
`_establishes_ipcInvariantFull`) and whose type is a proposition: no
hypothesis of its telescope may *entail* a measured conjunct — or any
`ipcInvariantFull`-family form — applied to a state its conclusion
concludes the family about.  Entailment descends conjunctions, structure
fields, and definitional unfoldings; it refuses `∨`, `∃`, `¬`, `↔` and
arrows, which do not prove their parts.  The conjunct set is derived by
unfolding the canonical root, closed over definitions, exactly as the
text gate derives it — but on expressions rather than text.

**What it deliberately does not check.**  Equality transport
(`hEq : st = st'` beside `ipcInvariantFull st`) stays the text gate's
layer: the payoff statement rules there tie step inputs to covered
states, and entailment through `Eq.mpr` is proof-level, not
hypothesis-level.  The text gate remains the fast pre-commit
approximation; this module is the semantic authority CI builds.

The checker is its own witness (the text gate's harness discipline):
locally declared threaded theorems — deliberately *not* family-named, so
the whole-environment census never counts them — must fail the single-
constant checker, and the clean twin must pass, before the census runs.

Runs at elaboration: `lake build SeLe4n.Testing.IpcDethreadingEnvironmentCensus`
(wired into `scripts/test_tier1_build.sh` beside the staged surface).
-/


namespace SeLe4n.Testing.IpcDethreadingEnvironmentCensus

open Lean Meta Elab

private def familyMarkers : List String :=
  ["_preserves_ipcInvariantFull", "_establishes_ipcInvariantFull"]

/-- The family marker lives in the final component: auxiliaries
    (`….proof_1`) and parents of dotted names never match.  Macro scopes
    are erased first (PR #886 review): a pinned command macro minting
    `theorem hidden_preserves_ipcInvariantFull …` records a hygienic
    name whose raw final components are scope markers, and a classifier
    reading them raw skipped exactly the generated statements this
    census exists to catch. -/
private def carriesFamilyMarker (n : Name) : Bool :=
  match n.eraseMacroScopes with
  | .str _ s => familyMarkers.any fun m => (s.splitOn m).length > 1
  | _ => false

/-- Conclusion-side family forms, derived from the environment: every
    constant whose final component *starts with* `ipcInvariantFull` — the
    root, `_smp`, `_perCore`, `ExceptDonationOwner` — and never
    `ipcInvariantCore`, which is pre-state vocabulary. -/
private def isFamilyForm (n : Name) : Bool :=
  match n with
  | .str _ s => "ipcInvariantFull".isPrefixOf s
  | _ => false

private def systemStateName : Name := `SeLe4n.Model.SystemState

/-- The leaves of a body's `∧`-tree, as application heads. -/
private partial def andLeafHeads (e : Expr) (acc : NameSet) : NameSet :=
  if e.isAppOfArity ``And 2 then
    andLeafHeads (e.getArg! 1) (andLeafHeads (e.getArg! 0) acc)
  else
    match e.getAppFn with
    | .const n _ => acc.insert n
    | _ => acc

/-- The measured conjunct set: every accepted family form's `∧`-tree,
    closed over definitional unfolding — `derive_conjuncts`, on
    expressions.  Every form seeds, not the root alone (PR #886 review):
    `ipcInvariantFullExceptDonationOwner` carries the variant-specific
    `donationOwnerValidExcept` the canonical root does not, and a
    root-only seed left a theorem free to assume precisely its variant's
    post-state conjunct unmeasured. -/
private def measuredConjuncts : MetaM NameSet := do
  let env ← getEnv
  let root := `SeLe4n.Kernel.ipcInvariantFull
  let some (.defnInfo _) := env.find? root
    | throwError "de-threading census: `{root}` is not a definition"
  let mut frontier : List Name := []
  for (n, info) in env.constants.toList do
    if isFamilyForm n then
      if let .defnInfo d := info then
        let heads ← lambdaTelescope d.value fun _ body =>
          pure (andLeafHeads body {})
        frontier := heads.toList ++ frontier
  let mut conjuncts : NameSet := {}
  while frontier ≠ [] do
    let name :: rest := frontier | break
    frontier := rest
    if conjuncts.contains name || isFamilyForm name then
      continue
    conjuncts := conjuncts.insert name
    if let some (.defnInfo nested) := env.find? name then
      let heads ← lambdaTelescope nested.value fun _ body =>
        pure (andLeafHeads body {})
      for h in heads.toList do
        if !conjuncts.contains h then
          frontier := h :: frontier
  return conjuncts

/-- The subset of `targets` that `e` entails applied to the state `s'`.

    Descends `∧` (union), `∨` (intersection of the arms' sets -- a
    disjunction provides only what *every* arm provides, and by
    *identity*: `A st' ∨ B st'` entails neither A nor B even though each
    arm entails something, which a boolean intersection mistook for a
    hit; PR #886 review, two rounds), `∃`-bodies (elimination hands the
    body over whatever the witness), structure fields (projection types,
    instantiated at the application's own arguments), and definitional
    unfoldings, to `fuel`.  Arrows, `¬` (an arrow after unfolding) and
    `↔` provide none of their parts and yield the empty set.  The state
    argument is found by *type*, never by position: the elaborator
    already knows which argument is the `SystemState`. -/
private partial def entailedTargets (targets : NameSet) (s' : Expr) :
    Nat → Expr → MetaM NameSet
  | 0, _ => return {}
  | fuel + 1, e => do
    if e.isAppOfArity ``And 2 then
      let left ← entailedTargets targets s' fuel (e.getArg! 0)
      let right ← entailedTargets targets s' fuel (e.getArg! 1)
      return right.toList.foldl (init := left) fun acc n => acc.insert n
    else if e.isAppOfArity ``Or 2 then
      let left ← entailedTargets targets s' fuel (e.getArg! 0)
      if left.isEmpty then
        return {}
      let right ← entailedTargets targets s' fuel (e.getArg! 1)
      return left.toList.foldl (init := ({} : NameSet)) fun acc n =>
        if right.contains n then acc.insert n else acc
    else if e.isAppOfArity ``Exists 2 then
      lambdaTelescope (e.getArg! 1) fun _ body =>
        entailedTargets targets s' fuel body
    else
      let fn := e.getAppFn
      let .const name us := fn | return {}
      if targets.contains name then
        for arg in e.getAppArgs do
          if arg == s' then
            let ty ← inferType arg
            if ty.isConstOf systemStateName then
              return ({} : NameSet).insert name
        return {}
      let env ← getEnv
      if isStructure env name then
        let info := getStructureInfo env name
        let args := e.getAppArgs
        let mut found : NameSet := {}
        for field in info.fieldNames do
          let some proj := env.find? (name ++ field) | continue
          let projType := proj.instantiateTypeLevelParams us
          let hits ← try
            withLocalDeclD `self e fun self => do
              let fieldTy ← instantiateForall projType (args.push self)
              entailedTargets targets s' fuel fieldTy
          catch _ =>
            pure {}
          found := hits.toList.foldl (init := found) fun acc n => acc.insert n
        return found
      match ← unfoldDefinition? e with
      | some unfolded => entailedTargets targets s' fuel unfolded
      | none => return {}

/-- The states a conclusion concludes family forms about: for each
    depth-0 `∧`-leaf headed by a family form, its `SystemState`-typed
    argument. -/
private partial def conclusionStates (e : Expr) (acc : List Expr) :
    MetaM (List Expr) := do
  if e.isAppOfArity ``And 2 then
    conclusionStates (e.getArg! 1) (← conclusionStates (e.getArg! 0) acc)
  else
    match e.getAppFn with
    | .const name _ =>
      if isFamilyForm name then
        let mut found := acc
        for arg in e.getAppArgs do
          let ty ← inferType arg
          if ty.isConstOf systemStateName then
            found := arg :: found
        return found
      return acc
    | _ => return acc

/-- Check one constant; the census loop and the witnesses both call this.
    Returns a violation description, or none. -/
private def checkStatement (targets : NameSet) (name : Name) :
    MetaM (Option MessageData) := do
  let env ← getEnv
  let some info := env.find? name | return none
  forallTelescope info.type fun fvars conclusion => do
    let states ← conclusionStates conclusion []
    for s' in states do
      for fvar in fvars do
        let hyp ← inferType fvar
        let entailed ← entailedTargets targets s' 128 hyp
        if !entailed.isEmpty then
          return some m!"`{name}` hypothesises measured conjunct(s) \
            {entailed.toList} of its own conclusion state {s'}: {hyp}"
    return none

/-- Fails elaboration when any family statement in the environment is
    threaded; prints the census when clean. -/
private def censusMain : MetaM Unit := do
  let env ← getEnv
  let targets := (← measuredConjuncts).insert `SeLe4n.Kernel.ipcInvariantFull
  let targets := env.constants.fold (init := targets) fun acc n _ =>
    if isFamilyForm n then acc.insert n else acc
  let mut statements := 0
  let mut generated := 0
  let mut violations : List MessageData := []
  for (n, info) in env.constants.toList do
    -- No macro-scope skip (PR #886 review, the round after the
    -- classifier fix): the loop guard was the *other half* of the same
    -- bypass -- a pinned macro's generated family theorem is exactly
    -- what must be counted and checked.  Auxiliaries stay excluded
    -- structurally, by the final-component marker test.
    if !carriesFamilyMarker n then
      continue
    if !(← isProp info.type) then
      continue
    statements := statements + 1
    if n.hasMacroScopes then
      generated := generated + 1
    if let some violation ← checkStatement targets n then
      violations := violation :: violations
  if !violations.isEmpty then
    throwError "ipc de-threading census ({statements} statements): \
      {violations.length} threaded:{MessageData.joinSep violations "\n"}"
  -- Generated (hygiene-scoped) statements are counted and checked like
  -- any other but reported apart, so the source-visible total stays
  -- comparable with the text census's.
  logInfo m!"ipc de-threading census: {statements - generated} family \
    statements ({generated} generated), 0 threaded"

section CheckerWitnesses

/-- A conjunct-carrying local structure: the field walk's witness rung.
    Not family-named, so the whole-environment census never counts the
    witnesses that bind it. -/
private structure censusWitnessPack (st : SeLe4n.Model.SystemState) : Prop where
  carried : SeLe4n.Kernel.blockedThreadsPendingMessageConsistent st

/-- A definition unfolding to the pack: the delta rung above it. -/
private def censusWitnessCarrier (st : SeLe4n.Model.SystemState) : Prop :=
  censusWitnessPack st

/-- Deliberately threaded, directly: the whole family assumed of the
    conclusion's own state.  Provable *because* it is vacuous, which is
    exactly what the invariant forbids. -/
private theorem censusWitnessThreaded (st' : SeLe4n.Model.SystemState)
    (hThreaded : SeLe4n.Kernel.ipcInvariantFull st') :
    SeLe4n.Kernel.ipcInvariantFull st' := hThreaded

/-- Deliberately threaded, through the def-and-structure chain: the
    entailment walk must unfold `censusWitnessCarrier`, walk the pack's
    field, and find the conjunct on the conclusion state. -/
private theorem censusWitnessChained (st st' : SeLe4n.Model.SystemState)
    (hInv : SeLe4n.Kernel.ipcInvariantFull st)
    (_hThreaded : censusWitnessCarrier st')
    (hStep : st = st') :
    SeLe4n.Kernel.ipcInvariantFull st' := hStep ▸ hInv

/-- Deliberately threaded through a both-arms disjunction: cases
    elimination provides the conjunct on the conclusion state. -/
private theorem censusWitnessOrCarried (st st' : SeLe4n.Model.SystemState)
    (hInv : SeLe4n.Kernel.ipcInvariantFull st)
    (_hThreaded : SeLe4n.Kernel.blockedThreadsPendingMessageConsistent st' ∨
      SeLe4n.Kernel.blockedThreadsPendingMessageConsistent st')
    (hStep : st = st') :
    SeLe4n.Kernel.ipcInvariantFull st' := hStep ▸ hInv

/-- Deliberately threaded through an existential: elimination hands the
    body over whatever the witness. -/
private theorem censusWitnessExistsCarried (st st' : SeLe4n.Model.SystemState)
    (hInv : SeLe4n.Kernel.ipcInvariantFull st)
    (_hThreaded : ∃ _u : Unit,
      SeLe4n.Kernel.blockedThreadsPendingMessageConsistent st')
    (hStep : st = st') :
    SeLe4n.Kernel.ipcInvariantFull st' := hStep ▸ hInv

/-- The `∨ True` twin stays clean: its right arm suffices, so nothing is
    provided — the reported false positive, pinned at this layer too. -/
private theorem censusWitnessOrTrue (st st' : SeLe4n.Model.SystemState)
    (hInv : SeLe4n.Kernel.ipcInvariantFull st)
    (_hIrrelevant : SeLe4n.Kernel.blockedThreadsPendingMessageConsistent st' ∨
      True)
    (hStep : st = st') :
    SeLe4n.Kernel.ipcInvariantFull st' := hStep ▸ hInv

/-- A mixed disjunction stays clean: each arm entails *something*, but
    no single conjunct is provided by both, so nothing is entailed --
    the identity-intersection pin (PR #886 review). -/
private theorem censusWitnessOrMixed (st st' : SeLe4n.Model.SystemState)
    (hInv : SeLe4n.Kernel.ipcInvariantFull st)
    (_hMixed : SeLe4n.Kernel.blockedThreadsPendingMessageConsistent st' ∨
      SeLe4n.Kernel.endpointQueueNoDup st')
    (hStep : st = st') :
    SeLe4n.Kernel.ipcInvariantFull st' := hStep ▸ hInv

/-- The clean twin: every hypothesis on the pre-state. -/
private theorem censusWitnessClean (st st' : SeLe4n.Model.SystemState)
    (hInv : SeLe4n.Kernel.ipcInvariantFull st)
    (hStep : st = st') :
    SeLe4n.Kernel.ipcInvariantFull st' := hStep ▸ hInv

/-- The witness harness: the checker must fire on both threaded witnesses
    and stay silent on the clean one -- the "keep the token, break the
    relation" discipline, machine-enforced like the text gate's. -/
private def checkWitness (name : Name) (expectThreaded : Bool) : MetaM Unit := do
  let targets := (← measuredConjuncts).insert `SeLe4n.Kernel.ipcInvariantFull
  match ← checkStatement targets name, expectThreaded with
  | some _, true | none, false => pure ()
  | some v, false => throwError "census witness: clean statement flagged: {v}"
  | none, true => throwError "census witness: a threaded witness was not \
      flagged -- the entailment walk has gone blind"

/-- The loop witness's minting macro: hygiene records scope markers
    after the template's name, which is the point -- the census loop
    must count and check the minted statement all the same (PR #886
    review: the classifier was fixed while the loop's own skip survived,
    and a classifier-only witness could not see the bypass). -/
local macro "censusMintGeneratedWitness" : command => `(
private theorem generatedWitness_preserves_ipcInvariantFull
    (st st' : SeLe4n.Model.SystemState)
    (hInv : SeLe4n.Kernel.ipcInvariantFull st)
    (hStep : st = st') :
    SeLe4n.Kernel.ipcInvariantFull st' := hStep ▸ hInv
)

censusMintGeneratedWitness

run_cmd Command.liftTermElabM do
  checkWitness ``censusWitnessThreaded true
  checkWitness ``censusWitnessChained true
  checkWitness ``censusWitnessOrCarried true
  checkWitness ``censusWitnessExistsCarried true
  checkWitness ``censusWitnessOrTrue false
  checkWitness ``censusWitnessOrMixed false
  checkWitness ``censusWitnessClean false
  -- The minted hygienic family theorem must be visible to the census --
  -- existence and classification together; the loop below counts it
  -- through the same predicate, with no macro-scope skip left to hide
  -- behind.
  let env ← getEnv
  let mut mintedSeen := false
  for (n, _) in env.constants.toList do
    if n.hasMacroScopes && carriesFamilyMarker n then
      mintedSeen := true
  unless mintedSeen do
    throwError "census witness: the minted hygienic family theorem is \
      not visible to the census classifier -- the generated-statement \
      channel has reopened"
  -- The classifier must see through hygiene (PR #886 review): a macro-
  -- minted family theorem records scope markers after its user-facing
  -- name, and a raw read skipped it.
  -- The synthetic name is *constructed*, not spelled: it deliberately
  -- names no declaration, and the text gate's `family_references`
  -- backstop rightly fires on any spelled family-shaped token that
  -- resolves to nothing -- which is also how generated names actually
  -- arise in minting machinery.
  let hygienic ← MonadQuotation.addMacroScope
    ((`fake).appendAfter "_preserves_ipcInvariantFull")
  unless hygienic.hasMacroScopes && carriesFamilyMarker hygienic do
    throwError "census witness: the classifier does not see a \
      hygiene-scoped family name -- generated statements would escape"
  censusMain

end CheckerWitnesses

end SeLe4n.Testing.IpcDethreadingEnvironmentCensus
