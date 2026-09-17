/-
# The store-read classifier, reconciled against the elaborator

`scripts/lean_store_read_census.py` decides two structural questions about every
raw object-store read — and, since `v0.35.76`, every raw object-table write —
it finds: **which declaration owns this line**, and **is that declaration
executable**.  It decides both by reading text, because it runs in Tier 0 —
before any build — and the metrics it produces (`STORE_READ_CODE` and
`STORE_WRITE_CODE`, both `ZERO_METRICS` entries) are consumed there.

Text is the wrong instrument for both questions, and this project has the
receipts: across three review rounds of one PR the classifier was taught a
hypothesis binder, a `where` equation body, an ASCII arrow, a `structure` field
default, a leading indentation, a defaulted binder and a per-field reset — seven
legal Lean spellings, each found by a reviewer rather than by the gate.
`CLAUDE.md` names both the class (*the set of valid spellings that defeat a
regex is unbounded while the set a gate has seen is finite*) and the exit (*a
Lean question goes to the Lean elaborator*).

The exit cannot be taken where the classifier lives, so it is taken **here**.
The elaborator knows each declaration's source span (`findDeclarationRanges?`)
and whether it is a proposition (`Meta.isProp`) — exactly, for every spelling,
with nothing to miss.  This module asks the classifier for its own per-line
answers (`--attribution`) and fails the build wherever the two disagree.

**What this does and does not close.**  It closes the *structural* half: an
unseen declaration form now fails Tier 1 on the day it is written instead of
silently misfiling a read.  It does **not** make the read *recogniser* complete
— "is this occurrence a read rather than a write" is a question about an API's
meaning, which the environment has no opinion on (`CLAUDE.md` records that a
result-type derivation classified `FrozenMap.set`, a write, as a read).  That
half stays a stated floor, and `STORE_READ_SCOPE` says so.

**And the domain is reconciled, not assumed** (`v0.35.76`).  The classifier's
domain is the filesystem — every `SeLe4n/**/*.lean` — while this check's is the
environment, and a declaration outside the import closure is indistinguishable
from one that does not exist.  Until `v0.35.76` a row in such a file was counted
as "outside any declaration" beside a `#eval` line, a diagnostic; and **every**
`SeLe4n/Testing/` module was outside the closure, so the first row the write
census produced there (the reply-stack census's planted witness) was the first
row this check silently could not judge.  A row in a file no module of the
environment declares anything in now FAILS the build, naming the module to
import (`orphanFiles`), and `SeLe4n.Testing.ReplyStackWriteCensus` is imported
for exactly that reason.
-/
import Lean
import SeLe4n
import SeLe4n.Platform.Staged
import SeLe4n.Testing.ReplyStackWriteCensus

open Lean Elab Command Meta

namespace SeLe4n.Testing.StoreReadClassificationCensus

/-- One line the classifier attributed: source file, line, owning declaration,
and whether it judged that declaration a proposition. -/
structure Attribution where
  file : String
  line : Nat
  decl : String
  isProp : Bool
  /-- `"sig"` for a binder type or the result type, `"default"` for a binder's
  default value, `"body"` otherwise.  A signature row is not judged — a
  hypothesis binder is a proposition whatever its declaration is — while a
  default is, since a default is elaborated and run exactly when its
  declaration is. -/
  region : String
  deriving Inhabited

/-- A declaration's source span, as the elaborator records it. -/
structure Span where
  start : Nat
  stop : Nat
  isProp : Bool
  name : Name
  deriving Inhabited

/-- The conclusion of a (possibly dependent) function type. -/
partial def conclusionOf : Expr → Expr
  | .forallE _ _ body _ => conclusionOf body
  | .letE _ _ _ body _ => conclusionOf body
  | .mdata _ e => conclusionOf e
  | e => e

/-- Is this declaration *specification* in the classifier's sense?

Two ways, and the second is the one a naive reading misses: a **proof** (its type
is a proposition) or a **predicate** (`def p : SystemState → Prop`, whose type is
a function into `Prop` and therefore lives in `Type`, so `Meta.isProp` says no).

Reading `Meta.isProp` alone reported 271 disagreements on the first run of this
census, every one a predicate the classifier had filed correctly — the check was
wrong, not the classifier.  `SeLe4n/Testing/ReplyStackWriteCensus.lean` had
already settled this question as `isPredicate`; asking it a second way here
would have been this project's *one question, two answers* shape inside the
reconciliation written to prevent exactly that. -/
def isSpecDeclaration (ci : ConstantInfo) : MetaM Bool := do
  if ← Meta.isProp ci.type then return true
  return conclusionOf ci.type == .sort .zero

/-- `SeLe4n.Model.State` ↦ `SeLe4n/Model/State.lean`. -/
def moduleRelPath (m : Name) : String :=
  String.intercalate "/" (m.components.map fun c => c.toString) ++ ".lean"

/-- Parse one `STORE_ACCESS_ATTRIB=<file>|<line>|<decl>|<0|1>|<region>` row.

One stream for the read and the write census since `v0.35.76`: the two
structural answers judged here — which declaration owns the line, and whether it
is executable — do not depend on which access the line carries, so a line
carrying both is one row and the reconciliation reads it once. -/
def parseRow (s : String) : Option Attribution := do
  let body ← if s.startsWith "STORE_ACCESS_ATTRIB=" then
      some (s.drop "STORE_ACCESS_ATTRIB=".length).toString else none
  match body.splitOn "|" with
  | [f, l, d, p, r] => do
      let n ← l.toNat?
      some { file := f, line := n, decl := d, isProp := p == "1", region := r }
  | _ => none

end SeLe4n.Testing.StoreReadClassificationCensus

namespace SeLe4n.Testing.StoreReadClassificationCensus

/-- The classifier's own per-line answers, read from the gate itself so the two
cannot drift: a second implementation of the census here would be this project's
*one question, two answers* shape inside the check written to close it. -/
def readAttribution : IO (Array Attribution) := do
  let out ← IO.Process.output
    { cmd := "python3", args := #["scripts/lean_store_read_census.py", "--attribution"] }
  if out.exitCode != 0 then
    throw <| IO.userError s!"store-read census failed (exit {out.exitCode}): {out.stderr}"
  let mut rows := #[]
  for line in out.stdout.splitOn "\n" do
    if let some a := parseRow line.trimAscii.toString then
      rows := rows.push a
  return rows

/-- What one reconciliation found.

A record rather than a tuple, because the counts are read positionally at nine
call sites and this file has watched a project pay for positional access before
(`PlatformConfig.wellFormed`'s projection paths).  A field added here is a
compile error at any site that needs it and invisible at the rest, where a sixth
`Nat` in a tuple silently renumbers the other five. -/
structure Reconciliation where
  /-- Lines where the classifier and the elaborator disagree.  Enforced. -/
  mismatches : Array String
  /-- Lines judged in both directions. -/
  checked : Nat
  /-- Lines the classifier placed in a declaration's SIGNATURE, which a
  declaration-level verdict structurally cannot adjudicate. -/
  signatureRows : Nat
  /-- ...and how many of those sit inside an **executable** declaration, which
  is the residue this skip genuinely cannot judge — and, until PR #895 review
  round 7, where every boundary defect landed: `sig` is SPEC, so a body misfiled
  as signature passed the enforced zero *and* this reconciliation.  Tier 0's own
  refusal (`classify`'s `unparsed` channel in
  `scripts/lean_store_read_census.py`) is what closes that direction; this number
  is what keeps the remaining, legitimately unjudgeable population visible rather
  than implied. -/
  signatureInExecutable : Nat
  /-- Lines outside every declaration the elaborator knows. -/
  unplaced : Nat
  /-- Lines whose narrowest enclosing spans disagree about `isProp`. -/
  ambiguous : Nat

/-- Every declaration span containing this row's line. -/
def enclosingSpans (spans : Std.HashMap String (Array Span)) (a : Attribution) : Array Span :=
  (spans.getD a.file #[]).filter fun sp => sp.start ≤ a.line && a.line ≤ sp.stop

/-- The narrowest of them — the declaration that owns the line.

One definition, because both the judged path and the signature-residue count ask
it, and two spellings of "which declaration owns this line" is the shape this
tree keeps paying for. -/
def narrowestSpan (cs : Array Span) : Option Span :=
  if cs.isEmpty then none
  else some (cs.foldl (init := cs[0]!) fun acc sp =>
    if sp.stop - sp.start < acc.stop - acc.start then sp else acc)

/-- The files the classifier attributed rows to and no declaration of which is in
the environment: the classifier's domain minus this check's.  Every such file is
a module outside the import closure, and a row there is one this reconciliation
cannot judge at all — so the caller fails on a non-empty answer rather than
counting it as diagnostic residue (`v0.35.76`).  A file with rows is the only
kind that matters: a scanned file holding no raw access has nothing to judge. -/
def orphanFiles (spans : Std.HashMap String (Array Span)) (rows : Array Attribution) :
    List String :=
  (rows.filter fun a => !spans.contains a.file).toList.map (·.file) |>.eraseDups

/-- The verdict, as a pure function of the two inventories, so it can be
exercised on synthetic input.

**It has to be, because on this tree it cannot fire.**  The enforced claim is
one-directional — a line filed SPEC, in a declaration's body, where the
elaborator says that declaration is executable — and `STORE_READ_CODE` and
`STORE_WRITE_CODE` are both **0**, so no such line exists to find.  A mutation of the classifier that makes `def`
bodies specification changes nothing, since no read sits in a `def` body at all.
That is the same position `SeLe4n/Testing/BootEntryContract.lean` is in, and it
takes the same remedy: the witnesses below make the check decisive *before* the
tree it governs can exhibit the defect. -/
def disagreements (spans : Std.HashMap String (Array Span)) (rows : Array Attribution)
    (structureLike : Name → Bool) : Reconciliation := Id.run do
  let mut checked := 0
  let mut unplaced := 0
  let mut ambiguous := 0
  let mut signatureRows := 0
  let mut signatureInExecutable := 0
  let mut mismatches : Array String := #[]
  for a in rows do
    let candidates := enclosingSpans spans a
    let best? := narrowestSpan candidates
    -- A `"sig"` row is a binder TYPE or the result type — a proposition inside
    -- a declaration that may itself be executable, which a declaration-level
    -- verdict structurally cannot adjudicate.  A `"default"` row is a binder's
    -- DEFAULT VALUE, which it can: a default runs exactly when its declaration
    -- does, so it is judged like a body.
    if a.region == "sig" then
      signatureRows := signatureRows + 1
      if let some b := best? then
        unless b.isProp do signatureInExecutable := signatureInExecutable + 1
      continue
    match best? with
    | none => unplaced := unplaced + 1
    | some best =>
      let tied := candidates.filter fun sp => sp.stop - sp.start == best.stop - best.start
      if tied.any (fun sp => sp.isProp != best.isProp) then
        ambiguous := ambiguous + 1
      else
        checked := checked + 1
        -- A `structure` is executable while its field TYPES are propositions,
        -- so the elaborator's declaration-level verdict cannot settle either
        -- direction for one; it is excused from both.
        if structureLike best.name then
          pure ()
        else if a.isProp then
          -- **Fail-open.**  The classifier called this specification and the
          -- elaborator says the line is in an executable declaration, so a read
          -- that should count toward the enforced zero does not.
          unless best.isProp do
            mismatches := mismatches.push
              s!"{a.file}:{a.line}: the classifier filed this read under `{a.decl}` as \
SPEC, but the elaborator places the line in the body of `{best.name}`, which is \
executable — a Lean declaration form the classifier does not recognise"
        else
          -- **Fail-strict, and judged for exactly that reason.**  The classifier
          -- called this executable and the elaborator says the declaration is a
          -- proposition, so Tier 0 refuses legitimate specification text against
          -- an enforced zero — a wall with no explanation unless something says
          -- this.  The case that motivated it is a result type that is an ALIAS
          -- of `Prop` (`abbrev Pred := Prop`), which `prop_aliases` resolves
          -- lexically and so incompletely (PR #895 review round 6).
          if best.isProp then
            mismatches := mismatches.push
              s!"{a.file}:{a.line}: the classifier filed this read under `{a.decl}` as \
CODE, but the elaborator says `{best.name}` is a proposition — Tier 0 would \
refuse valid specification text.  If the result type is an alias of `Prop`, \
teach `prop_aliases` in scripts/lean_store_read_census.py to resolve it"
  return { mismatches, checked, signatureRows, signatureInExecutable, unplaced, ambiguous }

run_cmd Command.liftTermElabM do
  let env ← getEnv
  -- The production root must be imported, or a declaration defined only in a
  -- module it pulls in would read as absent and every line of that file would
  -- reconcile against nothing.
  unless env.header.moduleNames.contains `SeLe4n do
    throwError "store-read classification census: the production library root `SeLe4n` \
      is not in this environment"

  -- The elaborator's side: every source declaration's span, per file.  Compiler
  -- auxiliaries are excluded by the environment's own predicates — an equation
  -- lemma that inherited its parent's span would be a `Prop` sharing an
  -- executable declaration's lines, which is a false disagreement rather than a
  -- real one.
  let mut spans : Std.HashMap String (Array Span) := {}
  for (n, _) in env.constants.toList do
    if n.eraseMacroScopes != n then continue
    if isAuxRecursor env n || isRecCore env n || Meta.isMatcherCore env n then continue
    let some idx := env.getModuleIdxFor? n | continue
    let modName := env.header.moduleNames[idx.toNat]!
    unless (`SeLe4n).isPrefixOf modName do continue
    let some r ← Lean.findDeclarationRanges? n | continue
    let rel := moduleRelPath modName
    let some ci := env.find? n | continue
    let sp : Span :=
      { start := r.range.pos.line, stop := r.range.endPos.line
      , isProp := ← isSpecDeclaration ci, name := n }
    spans := spans.insert rel ((spans.getD rel #[]).push sp)

  let rows ← readAttribution
  if rows.isEmpty then
    throwError "store-read classification census: the classifier emitted no attribution \
      rows, so this reconciliation would pass by measuring nothing"

  -- **The classifier's domain is reconciled against this check's.**  Witnessed
  -- first, on synthetic input, because on the tree as imported the check
  -- cannot fire: a row in a file the environment declares nothing in is an
  -- orphan, and a row in a file it does is not.
  let orphanSpans : Std.HashMap String (Array Span) :=
    Std.HashMap.emptyWithCapacity.insert "F.lean"
      #[{ start := 1, stop := 10, isProp := false, name := `aDef }]
  let orphanRow : Attribution :=
    { file := "G.lean", line := 3, decl := "d", isProp := false, region := "body" }
  let placedRow : Attribution :=
    { file := "F.lean", line := 3, decl := "d", isProp := false, region := "body" }
  unless orphanFiles orphanSpans #[orphanRow, placedRow] == ["G.lean"] do
    throwError "store-read classification census: a row in a file outside the \
      environment was not reported as an orphan, so a module outside the import \
      closure would be judged by being skipped"
  unless (orphanFiles orphanSpans #[placedRow]).isEmpty do
    throwError "store-read classification census: a row in a file the environment \
      declares in was reported as an orphan"
  let orphans := orphanFiles spans rows
  unless orphans.isEmpty do
    throwError "store-read classification census: the classifier attributed rows in \
      {orphans}, but no declaration of those modules is in this environment, so \
      their rows cannot be judged — import each module here (the module is outside \
      the closure of `SeLe4n` and `SeLe4n.Platform.Staged`), or the classifier's \
      domain is wider than this reconciliation's and the gap is silent"

  -- **The witnesses, on synthetic input, before the real comparison.**  A check
  -- that cannot fire on the current tree and carries no witness is
  -- indistinguishable from one that is simply wrong.
  let stub : Name → Bool := fun _ => false
  let mkRow (l : Nat) (isProp : Bool) (region : String) : Attribution :=
    { file := "F.lean", line := l, decl := "d", isProp := isProp, region := region }
  let spec : Span := { start := 1, stop := 10, isProp := true,  name := `aProp }
  let exec : Span := { start := 1, stop := 10, isProp := false, name := `aDef }

  -- THE SHAPE THIS EXISTS TO CATCH: a body read filed SPEC inside an executable
  -- declaration — what an unrecognised declaration form buys.
  let bad := (disagreements
    (Std.HashMap.emptyWithCapacity.insert "F.lean" #[exec])
    #[mkRow 5 true "body"] stub).mismatches
  if bad.isEmpty then
    throwError "store-read classification census: a SPEC-filed body read inside an \
      executable declaration was accepted — the one direction this check enforces"
  -- THE SECOND DIRECTION: a body read filed CODE inside a declaration the
  -- elaborator calls a proposition.  Over-counting is the *safe* direction for
  -- a zero floor, so this is not a soundness hole — it is Tier 0 refusing valid
  -- specification text, which a `Prop` ALIAS in a result type produces and
  -- which nothing reported until this direction was judged (round 6).
  let bad2 := (disagreements
    (Std.HashMap.emptyWithCapacity.insert "F.lean" #[spec])
    #[mkRow 5 false "body"] stub).mismatches
  if bad2.isEmpty then
    throwError "store-read classification census: a CODE-filed body read inside a \
      specification declaration was accepted — Tier 0 would refuse valid text with \
      nothing to explain it"
  -- A binder DEFAULT is executable exactly when its declaration is, so unlike a
  -- signature row it IS adjudicable — and it is judged in the same direction.
  let bad3 := (disagreements
    (Std.HashMap.emptyWithCapacity.insert "F.lean" #[exec])
    #[mkRow 5 true "default"] stub).mismatches
  if bad3.isEmpty then
    throwError "store-read classification census: a SPEC-filed binder DEFAULT inside an \
      executable declaration was accepted — a default runs when its declaration does"
  -- ...and the shapes that must NOT be reported, or the gate fires on correct
  -- input: the same read in a genuinely specification declaration, the same read
  -- in a SIGNATURE (a hypothesis binder is a proposition inside an executable
  -- declaration — `mkRetypeTarget` is the live instance), and a read filed CODE
  -- in a declaration that really is executable (the 24 accessor bodies).
  let ok1 := (disagreements
    (Std.HashMap.emptyWithCapacity.insert "F.lean" #[spec])
    #[mkRow 5 true "body"] stub).mismatches
  unless ok1.isEmpty do
    throwError "store-read classification census: a SPEC read in a specification \
      declaration was reported as a disagreement"
  let ok2 := (disagreements
    (Std.HashMap.emptyWithCapacity.insert "F.lean" #[exec])
    #[mkRow 5 true "sig"] stub).mismatches
  unless ok2.isEmpty do
    throwError "store-read classification census: a read in a declaration's SIGNATURE \
      was judged against the declaration — a hypothesis binder is a proposition \
      whatever the declaration is"
  -- ...and the residue that skip leaves is COUNTED rather than implied.  A
  -- signature row inside an executable declaration is both the legitimately
  -- unjudgeable case (a hypothesis binder) and the shape a boundary defect
  -- takes, so the number must move for it — and must stay still for a row
  -- inside a proposition, where nothing is being skipped over.
  let sigInExec := (disagreements
    (Std.HashMap.emptyWithCapacity.insert "F.lean" #[exec])
    #[mkRow 5 true "sig"] stub).signatureInExecutable
  unless sigInExec == 1 do
    throwError "store-read classification census: a SIGNATURE row inside an executable \
      declaration was not counted as unjudged residue, so the population this \
      reconciliation cannot reach would read as empty"
  let sigInSpec := (disagreements
    (Std.HashMap.emptyWithCapacity.insert "F.lean" #[spec])
    #[mkRow 5 true "sig"] stub).signatureInExecutable
  unless sigInSpec == 0 do
    throwError "store-read classification census: a SIGNATURE row inside a proposition \
      was counted as unjudged residue — nothing is being skipped over there"
  let ok3 := (disagreements
    (Std.HashMap.emptyWithCapacity.insert "F.lean" #[exec])
    #[mkRow 5 false "body"] stub).mismatches
  unless ok3.isEmpty do
    throwError "store-read classification census: a CODE-filed read in a genuinely \
      executable declaration was reported — that is the classifier agreeing"
  -- A structure excuses BOTH directions, not only the first: its field types are
  -- specification and its defaults are executable, and one declaration-level
  -- verdict cannot be right about both.
  let ok5 := (disagreements
    (Std.HashMap.emptyWithCapacity.insert "F.lean" #[spec])
    #[mkRow 5 false "body"]
      (fun n => n == `aProp)).mismatches
  unless ok5.isEmpty do
    throwError "store-read classification census: a CODE-filed read in a structure was \
      reported, but a structure cannot arbitrate either direction"
  -- A structure's field TYPES are specification while the structure itself is
  -- executable by this test, so it cannot arbitrate a body read either.
  let ok4 := (disagreements
    (Std.HashMap.emptyWithCapacity.insert "F.lean" #[exec])
    #[mkRow 5 true "body"]
      (fun n => n == `aDef)).mismatches
  unless ok4.isEmpty do
    throwError "store-read classification census: a body read in a structure was \
      reported, but a structure's field types are specification"

  let structureLike : Name → Bool := fun n =>
    (env.find? n).any fun ci => match ci with | .inductInfo _ => true | _ => false
  let result := disagreements spans rows structureLike

  unless result.mismatches.isEmpty do
    throwError "store-read classification census: {result.mismatches.size} line(s) where \
      the text classifier and the elaborator disagree — the classifier has met a Lean \
      spelling it does not know:\n  {String.intercalate "\n  " result.mismatches.toList}"

  if result.checked == 0 then
    throwError "store-read classification census: no body line was judged, so this \
      reconciliation passed by measuring nothing"

  logInfo m!"store-read classification census: {result.checked} body line(s) agree with \
the elaborator in BOTH directions ({result.signatureRows} in signatures, of which \
{result.signatureInExecutable} sit in executable declarations and are the residue no \
declaration-level verdict can judge; {result.unplaced} outside any declaration, \
{result.ambiguous} in tied spans; all diagnostic)"

end SeLe4n.Testing.StoreReadClassificationCensus
