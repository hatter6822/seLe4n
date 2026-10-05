# Key conventions — full text (agent reference)

> The full text of the project's key conventions and gate-writing rules, with the review history that earned each one.  Moved verbatim from `CLAUDE.md` (and its former `AGENTS.md`
> mirror) so the auto-loaded agent guidance stays small; only relative
> link targets were rewritten to resolve from this directory.  See
> [`CLAUDE.md`](../../CLAUDE.md) for the condensed, binding statement
> of each rule.
>
> **Tests are for code, not documentation** (`v0.36.42`).  No gate, test or
> anchor reads `.md` files, `docs/`, README or i18n text, or comment and
> docstring prose.  The worked examples below still name the documentation
> checks that were retired then (the plan, claim-evidence, deferral-registration,
> lock-ceiling-figure, line-citation, Markdown-link and fixture-index checks,
> and the Tier 3 prose anchors on comments); those names are the history of how
> each rule was earned, not live gates.

## Key conventions

- **Gates read code, prose reads prose.** No comment or docstring may
  decide whether a check passes. Every source-scanning gate matches
  against the *code view* — `scripts/lean_code_view.py --overlay`, a
  whole-repo overlay whose `.lean` files are comment-free and
  byte-aligned with the originals — so a docstring can neither satisfy
  an anchor (a symbol that survives only in a comment after its
  definition is deleted) nor trip one (a negative anchor firing on the
  sentence that explains what it forbids), and the AK7 counters measure
  code rather than the text discussing it. This is wired at the helper,
  not at the call site: `run_check` / `run_negative_check` route through
  the view automatically, because requiring an opt-in would mean the
  obvious way to write a new anchor is the wrong one. For code the view
  does not cover — a linker script, assembly, a fixture produced by code —
  declare the check with **`run_prose_check`** / **`run_prose_negative_check`**,
  which read the real tree; never point them at a comment or docstring,
  because comment prose is documentation and is not tested. Both mechanisms are pinned by witnesses in
  Tier 0 (`lean_code_view.py --self-test` for the stripper,
  `test_code_view_wiring.sh` for the routing), since a stripper that
  stops stripping and a helper that stops routing both fail silently.
  Never contort prose to satisfy a scanner — if a comment cannot say
  something plainly, the scanner is reading the wrong text.
  *Known duplication, tracked*: `generate_codebase_map.py` and
  `check_identifier_naming.py` each carry their own Lean comment
  stripper and were already doing the right thing — which is why the
  anchors and AK7 counters reading raw text was an oversight rather
  than a design choice. Three strippers is two too many; consolidating
  them onto `lean_code_view.strip` is a follow-up, deliberately not
  done in the same cut as the mechanism they would depend on.
  **The view is per-language, and a language absent from it is read
  raw** (WS-RR RR7.17). `test_lib.sh`'s classifier routes *every*
  `rg`/`grep` anchor through the overlay, not only the Lean ones, but
  the overlay linked `.rs` files whole — so 215 Tier-3 anchors over
  Rust matched comments, and "gates read code, prose reads prose" held
  for Lean only. It surfaced the way this class always does: the first
  negative written against a Rust construct was satisfied by the
  comment explaining what it forbids, and the project's own rule
  forbids the obvious escape (*never contort prose to satisfy a
  scanner*). The overlay's `_STRIPPERS` table now maps `.lean` to
  `lean_code_view.strip` and `.rs` to `rust_code_view.code` — the same
  view the Python gates read, so the tree has one Rust view rather than
  two that can disagree — and a suffix absent from the table is linked
  whole, which is a *decision* rather than a default: adding a language
  whose files gates scan means adding its stripper. The witness suite
  `test_code_view_wiring.sh` covers both languages on all three
  directions (a comment cannot satisfy a code anchor; a prose check
  still reads the real text; code anchors still match code), in both
  Rust comment forms, because a Lean-only witness is exactly what let
  the Rust hole stay open while the script reported PASS.
- **A presence check is not a relation check.**  Nearly every gate here
  is a text scanner, and the recurring way one fails is that it asserts a
  *token is present* when the property it means is a *relation*: that the
  flag reaches **this command**, that the guard precedes **this
  instruction**, that the artefact came from **this run**, that the
  reference is **this occurrence**.  Presence is necessary and almost
  never sufficient, and the gap is invisible because the token really is
  there.  **Seventeen instances** shipped across three review rounds of one
  cut (WS-RR RR1, `v0.34.41`), and the count is the point: each
  round fixed the instances it was shown and the next round found more, in
  the code written to fix the last.  Round 1 (`v0.34.41`): a workflow step
  *name* satisfying a check for an installed target; a two-profile script
  satisfying a `cargo build` check after one profile became a `check`;
  `CROSS_TARGET=`/`CROSS_FEATURES=` assignments satisfying flag checks
  while the builds passed something else; a stale archive satisfying "the
  sources assembled"; `body.contains(guard)` passing with the guard moved
  *below* the instruction it protects; a call-syntax regex missing
  `use … as alias`; a whole-file exemption set from a docstring — that one
  in the gate written to enforce *gates read code, prose reads prose*; and
  two self-inflicted, inside the fixes for the others (a shell expander
  taking the *first* assignment, so a re-assigned setting read at a value
  the command never receives; a divergence check testing for `fatal_halt()`
  **file-wide**).  Round 3 found eight more, six of them
  reported and two found while fixing those: a host `--release` build
  satisfying "the *cross* build is done in both profiles"; `cargo test
  --doc … --features host_tools` satisfying "the host lane tests with
  `host_tools`" while running none of the tests the feature gates; `run:
  echo ./script.sh` satisfying "a job runs the gate"; a nested
  `if has_feat_tlbios() { fatal_halt(); }` satisfying the
  *branch*-scoped divergence check written in round 2; a module-scope
  `static` inheriting the allowlist entry of the function textually above
  it; a `//` inside an `asm!` template deleting the emitted instruction
  from the view; a string literal `"require_feat_tlbios()"` standing in for
  the call that keeps an UNDEFINED instruction off a Cortex-A76; and a
  file-wide directive count read from a view that had blanked the templates
  holding them.

  What the third round changed is the response.  Patching instances was not
  converging, because every one of them substituted an *ad-hoc slice of
  text* for a question about a *program*, and the ways text can diverge
  from structure are unbounded.  So the slices were replaced by shared
  structural views: `scripts/rust_code_view.py` (comments blanked, with
  string contents kept or blanked as the question requires, brace-matched
  `fn` bodies, byte-aligned) for the Python-side gates, its counterpart
  `rust_code_views` in `rust/sele4n-hal/build.rs`, and a `shell_commands` /
  `argv_of` / `option_values` layer so a flag is read on a **command**
  rather than on a line — and, since PR #889 review round 2, a Lean view in
  `build.rs` (`lean_code_view`) so the export inventory that drives the
  readiness gate is derived from code rather than from the docstrings that
  cite retired seams, and a recursive shell view in
  `check_identifier_naming.py` so a `$( … )` body is lexed rather than copied — and, since the RR7 audit round, a here-document body is lexed as a document of its own, so an apostrophe in a fixture line cannot carry quote state past its terminator.  The rule is unchanged and now has a mechanism:
  **resolve the text into the structure it stands for before asserting** —
  expand the script's variables and check the command, take byte offsets
  and check the order, parse the array and check the element, lex the
  source and check the scope.  Where a scanner genuinely cannot
  (reachability, aliasing through a value), say so in its docstring and
  make it over-approximate, so it fails **closed**.
- **Test a gate by breaking the relation, not by deleting the token.**
  The corollary, and the reason every instance above passed its own
  self-test: the fixtures mutated by *removal*, which any presence check
  survives.  The mutation that finds this class **keeps the token and
  breaks the relation** — leave `hw_target` in the file but build another
  target; keep `--release` but put it on a *host* build; keep the guard but
  move it after the `asm!`; keep `fatal_halt()` but nest it under the
  negation of its own branch condition; keep the reference but move it out
  of the function whose allowlist entry covers it.

  **And having built the resolver, sweep every site that asks the same
  question.**  Round 4 of the same review failed differently from the first
  three: the resolvers were right, and each was wired into exactly the call
  site the review had named.  `job_runs_gate` required a command position
  while its neighbour `cargo_invocations` still scanned tokens anywhere, so
  `echo cargo build --target …` passed; `rust_code_view.enclosing_fn` got
  real brace-matched bodies while `enclosing_lean_decl`, four lines below,
  stayed last-declaration-wins, so an `initialize` block inherited the
  preceding `def`'s allowlist entry; the Rust view became quote-aware while
  the `.S` view kept a `//`-only stripper resting on an asserted claim about
  the tree's *content* ("the `.S` sources use `//` exclusively") rather than
  the preprocessor's grammar.  A fix applied at one site and not its
  siblings leaves the class open and reads as closed.

  A related shape, and the one worth looking for unprompted: **an
  enumeration standing in for a derivation**.  A hand-written list of the
  things a gate protects — local TLBI wrappers, `*OS` wrappers, `.S`
  sources, FFI bindings — cannot see the one that does not exist yet, so the
  gate is silent exactly when something new is added.  Derive the set from
  what the code actually does and keep the list as a pin that fails when the
  two diverge.  Three of the four such lists in these gates were found by
  sweeping for the shape after the fourth was reported.

  **And a cardinality is not a set** (WS-OD OD3.5, prompted).  The same
  substitution one dimension down, and the one this file had not written
  because the gate wearing it *reported numbers*, which reads as measurement.
  `scripts/check_store_reader_hygiene_monotonic.sh` held the residual raw
  `match st.objects[…]?` reads at a whole-tree floor per variant — nine
  endpoint reads, fifty-three TCB reads — and its own docstring says what the
  floor means: "a previously hygienized site re-introduced the raw pattern".
  That is a statement about **which** sites, and a total cannot make it: a
  change that hygienizes one raw read in file A and introduces a fresh one in
  file B leaves every number identical, so the gate passed on exactly the
  movement it exists to catch.  Demonstrated on the real tree, not on a
  fixture — `RAW_MATCH_ENDPOINT` and `RAW_MATCH_TOTAL` both unmoved, a raw
  endpoint discriminator newly resident in `Scheduler/RunQueue.lean`.

  The floor is now the per-(file, variant) inventory, which is the shape
  `scripts/identifier_naming_baseline.json` had already reached for the same
  reason and which nothing had swept onto its sibling: **a set of keys alone
  cannot see a second occurrence inside a file that already contains one, and
  a count alone cannot see the first occurrence in a file that did not**, so
  the floor has to be both.  Two corollaries fell out of the same reading.
  The should-*grow* direction had the plain form of the defect — adoption was
  `grep -c "getEndpoint?"`, so `getEndpoint?_eq_some_iff` and every theorem
  named `*_ok_getEndpoint?` counted as a read of the object store (29 of 210),
  and writing a lemma *about* a helper raised the floor for *using* it; it
  counts whole symbols now — and since `v0.35.202` it also excludes a line whose
  leading token is a tactic that **unfolds** the accessor, because
  `unfold SystemState.getCNode? at hStep` takes the accessor *out* of the goal to
  reach the raw store, which is the opposite of the migration the metric is named
  for.  That one was found by the metric *scoring an improvement as a regression*:
  collapsing eight inline re-derivations onto one shared decomposition lowered
  `GETCNODE_ADOPTION` from 147 to 129 and failed a should-grow floor, and 45 of
  its 172 lines turned out to be tactic references to the definition.  **The
  measurement is what makes the scope honest**: it is a floor over *recognised*
  uses, since whether an occurrence reads *through* an accessor is a question
  about elaboration; an unrecognised tactic spelling leaves the figure a little
  high rather than inverting its direction.  And the per-variant scan carried awk state across
  the file list with no `FNR == 1` reset, so a trailing `match … .objects[` at
  the end of one file could pair with a `some (.tcb …)` at the start of the
  next and report a site existing in neither.

  The mutation for this class keeps every total and moves the site — and the
  self-test's harness *asserts* that each rejecting case leaves every scalar
  metric byte-identical, because that assertion is precisely the statement
  that the superseded gate admitted the case.  A live floor also does not
  live in `docs/dev_history/`: this one did, in a directory the project
  reserves for material contributors are told not to read.

  Every check in a self-tested gate needs at least one such case, and
  **that requirement is now enforced rather than asserted**: each case in
  `check_aarch64_cross_target.py` and `check_tlbi_broadcast_discipline.py`
  declares the check it exercises and whether its mutation is `preserving`
  or `deleting`, and the harness fails when any check has no preserving
  case.  Writing the rule in this file did not stop the next round from
  shipping eight more instances; a harness that refuses to pass does.  The
  harness must also reject a mutation that leaves the fixture unchanged,
  since an inert mutation reads as coverage while asserting nothing.  A
  fixture must also be **no thinner than the file it stands for**: a
  `mod`-less, gate-less toy passes checks the real file would fail, which
  is how a missing `re.MULTILINE` and an unanchored `.file()` search both
  survived.

  **And a count over two populations measures neither** (`v0.35.7`, prompted).
  The same substitution again, and the one this file had not written because the
  gate wearing it was *already* an inventory: `RAW_LOOKUP_TID` held raw
  `st.objects[…]` reads at a whole-tree ceiling, and 96.9% of what it counted was
  **specification vocabulary** — 1490 of 1711 lines in `theorem`s, 168 more in
  `Prop`-valued `def`s, `structure` fields and `inductive` arguments — against 53
  lines of executable code.  A proposition about the store has no helper form
  (`getTcb? k = none` holds for an absent key and a wrong-kinded object alike, so
  a frame statement quantified over every key cannot be phrased through a variant
  accessor without weakening it), so the enforced number rose whenever anyone
  wrote an invariant, and it was re-anchored **upward four times in three days**
  (1609 → 1600 → 1678 → 1711).  A ceiling that every cut raises is a ratchet
  running backwards; it reads as measurement because it prints a number.
  Three further defects rode along, each a rule already in this file applied
  everywhere but here: the metric was named `_TID` while **four** types carry
  `.toObjId` (*a name is not the thing*); it was `grep -c`, so two reads on one
  line counted once and a reflow lowered it (*a cardinality is not a set*, one
  level down); and `RAW_LOOKUP_SITE` was keyed by `(file)` while its sibling
  `RAW_SITE` had been refined to `(file, declaration, variant)` for the stated
  reason that a per-file key cannot see a read moving between declarations —
  *when a fix names a relation, grep for every other place that asks it*, unrun.

  **Split the populations, enforce the one that can reach zero, and report the
  other.**  `scripts/lean_store_read_census.py` classifies each read by whether it
  sits in the *body* of a declaration whose result is not a `Prop` — a binder or a
  result type is a proposition whatever the declaration's kind — and emits
  `STORE_READ_CODE` beside `STORE_READ_SPEC` (diagnostic, the treatment
  `RAW_MATCH_UNCLASSIFIED` already had).  The mutation for this class **moves a
  read between the populations while holding their sum fixed**, which is all the
  superseded figure could see: the gate's self-test has that case in both
  directions, the spec→code one rejecting and the code→spec one passing, because
  the second is the migration working.

  **And a floor that reaches zero stops being a floor** (`v0.35.8`).  The split
  was shipped with `STORE_READ_CODE` held to a **ceiling** and a per-key
  inventory — which is the superseded metric's own shape, one population
  narrower, and it carried the superseded metric's own escape: a cut that
  exceeds a ceiling may re-anchor it, which is what happened four times in three
  days.  So the residue was finished rather than registered.  The whole
  executable population is **zero**: `SeLe4n/Kernel` and `SeLe4n/Platform` were
  already there at `v0.35.7`, and the 76 that remained — 65 trace-harness
  bodies, 10 runtime invariant helpers, and one proof case split whose enclosing
  `def` returns a record of proofs — went in this cut, with the golden fixture
  **byte-identical**, which is the measurement that retired the deferral's own
  stated reason (*migrating it risks a fixture churn*).  The last of them came
  out by restating two theorems' hypotheses in the accessor vocabulary rather
  than bridging at the call site, so no `def` body mentions the store at all.
  `STORE_READ_CODE` is now a `ZERO_METRICS` entry beside `SORRY_COUNT` and
  `AXIOM_COUNT`: **regenerating the baseline does not clear it**, only fixing
  the tree does, and the gate says so in its failure epilogue.  Since `v0.35.76`
  `STORE_WRITE_CODE` sits beside it: the same classifier run over the raw
  *write* spellings, with the bodies that write raw by design registered in
  `WRITE_PRIMITIVE_BODIES` and reconciled in both directions — and it was a
  zero floor from its first measurement, the raw-write migration having
  reached the primitives before the census existed.

  **Both zeros are over the DIRECT spellings, and `v0.35.117` is where that stops
  being implied and starts being printed.**  Until then this paragraph said the
  only raw reads left anywhere were the accessor bodies and propositions, and the
  §7's raw-write ledger said the only raw writes were the five primitives and one
  planted witness.  Both were **false**, and the reason is the rule this file
  states one item down (*a helper the scanner cannot see is a spelling that evades
  the metric*) read in the other direction: every pattern here keys on the
  receiver text `.objects`, so a declaration that holds the table through an
  **indirection** is invisible to all of them.  There are two spellings of that
  indirection and they are one question — a binding (`let objs := st.objects`,
  then `objs.insert k v`) and a parameter (`(objs : RHTable ObjId KernelObject)`)
  — and three executable declarations use them: `endpointQueueRemove` (four
  writes, two reads), `spliceOutMidQueueNode` (two and two) and
  `queueNeighbourPatch` (one and one).  Twelve keyed accesses, outside two
  enforced zeros, which is why the raw-write migration
  (`v0.35.64`..`v0.35.78`) passed over all three: *the population a census
  measures is the population its receiver can name.*

  `STORE_INDIRECT_CODE` is the number, `STORE_INDIRECT_SCOPE` the claim, and both
  zeros now print their own `_SCOPE` line saying *recognised spellings only; a
  floor, not a proof of absence*.  Four things new code must respect.  (1) **One
  classifier, both spellings**: `table_receivers` derives the identifiers that
  denote the table — from three binder positions, a signature binder, a lambda
  binder and an unbracketed ascription, all read over the *whole* declaration
  rather than its signature alone, and from a binding of the projection, closed
  **transitively**, so one extra `let` is not a hole — and the access alternation
  is `_TABLE_OPS`', the same one `READ` and `WRITE` are built from, so a newly
  classified operation reaches the direct and indirect censuses by construction.
  The table type itself has one definition (`_TABLE_TYPE`), so a binder and an
  ascription cannot disagree about what a table is.  Flooring one spelling and
  describing the other in prose would have been *a fix applied at one site and not
  its sibling*.  (2) **It is driven through
  `classify`**, via a `collect` hook, because the property is a relation between a
  declaration's signature and its body that no line pattern can express — so the
  declaration boundary, the `Prop` verdict and the region split stay ONE answer
  and a mutation of any of them fails both censuses.  (3) **The unit is the
  access, not the binding**: a binding count cannot see a second `objs.insert`
  added to a declaration that already aliases, which is *a cardinality is not a
  set* one level down and is exactly what the two zeros count.  (4) **It is a
  floor, not a zero, and that is the honest shape**: a `ZERO_METRICS` entry this
  project may not re-anchor would have had to be false on the day it landed.  The
  table's own operations are exempt, **derived** from `_TABLE_SOURCES` — a
  declaration named `RHTable.insert` in the table's own source *is* the primitive,
  so counting it would report the definition of the thing being measured — and
  reconciled both ways so a stale exemption cannot read as coverage.

  **Driving it to zero is registered, with its architecture named rather than
  left to be rediscovered** (`docs/REGISTERED_DEBT.md` table C).  The target is
  not a new primitive: `queueNeighbourPatch` becomes state-level, which is
  `Option.elim` over the `updateTcb` this tree has had since `v0.35.65`, and the
  two aliasing removals then compose it and `rewriteObject` with no table in
  scope.  What that costs is measured rather than estimated — nine theorems stated
  over the *table* in `CleanupPreservation.lean`, twenty-five over
  `spliceOutMidQueueNode` across fifteen files, and the two `_eq_patches` pins
  whose right-hand sides compose at the table level — which is why it is a cut of
  its own and not a rider on the census that found it.

  **And a spelling is not a write either — nor is a regex a classification**
  (PR #897 review, `v0.35.97`).  That zero was true of `objects.insert` and
  `objects.erase` and blind to `objects.set`, which the WRITE pattern named in
  its *qualified* branch and not in its *method* one — so `st.objects.set k v`,
  the frozen surface's ordinary store, walked around an **enforced zero**, and
  thirty-one executable raw writes sat behind it.  That is `v0.35.12`'s finding
  on the other census, one branch down, and patching the branch would have been
  the fourth telling of a rule this file already carries twice.

  So the *question* has one answer: `_TABLE_OPS` classifies every operation of
  either object table `read` / `write` / `sweep` / `other`, and `READ`, `WRITE`
  and `SWEEP` are built from **one alternation** over it, so a widening reaches
  both spellings by construction.  Two reconciliations run in every mode:
  `table_op_violations` derives the operation set from `RHTable`'s and
  `FrozenMap`'s own sources and fails in both directions — *an operation nobody
  classified is one neither pattern ever looks for*, which is precisely how
  `set` escaped — and `branch_symmetry_violations` asserts each kind is
  recognised in the method spelling *and* the qualified one.  The decisive
  self-test case keeps the write and changes only how it is written.

  Two things that widening measured, and both generalise.  **A helper the
  scanner cannot see is a spelling that evades the metric**: the frozen writes
  went onto `frozenWithObjectStored`, a *state*-level primitive, because a
  map-level one would carry its raw `set` on a bare `FrozenMap` parameter, which
  a census keyed on `.objects` is blind to — so a new store primitive takes the
  state, never the table.  And **a transition can wear a primitive's
  exemption**: `frozenUpdatePipBoost` was in `WRITE_PRIMITIVE_BODIES` because it
  spelled its write `st.objects.insert`, the one form the `set`-only branch
  could not see; it writes through `frozenRewriteObject` — the total mirror of
  the live `rewriteObject`, sound because `FrozenMap.insert` *is* `set` with an
  append fallback — and the registry names the primitive alone.  Whole-table
  traversals are now **reported** (`STORE_SWEEP_*`) rather than silently outside
  the population, because a fold is not a keyed access and a number beside the
  two zeros is what stops their silence reading as absence.

  **And the collapse surfaced twelve answers to one question.**  Moving the
  writes behind a primitive broke eleven proofs that each `unfold`ed a composite
  down to `FrozenMap.set` and case-split on it — plus a twelfth,
  `frozenStoreObject_extracts_state`, which said exactly that, `private`, in a
  module **downstream of every asker**: *when a question has one owner and an
  asker that cannot see it, the owner is in the wrong layer.*  The owner is now
  beside the write (`frozenWithObjectStored_ok`, `_only_modifies_objects`,
  `frozenRewriteObject_only_modifies_objects`, `frozenOnlyObjects_rfl` /
  `_trans`) and the duplicate is deleted with a tombstone.  The re-derivations
  were coupled to the wrong thing besides — each closed its leaves by
  `injection` on a literal `{ st with objects := _ }`, so it depended on how many
  branches a body had *and* on every write being spelled inline, which is why
  the migration broke them rather than leaving them redundant.
  `frozen_objects_frame` **searches** the branch for whatever store chain the
  split left in context, so a store added to a frozen operation costs its frame
  proof nothing.

  One mechanical note, because it corrected the author rather than the tree: a
  mutation run first read as showing the registry reconciliation passing a stale
  entry.  It was not stale — `frozenUpdatePipBoost` genuinely still held a raw
  write, in the `insert` spelling the fixing sweep had grepped past.  **The gate
  was right and the sweep was one spelling wide**, which is this cut's own
  finding arriving inside the work to fix it.

  **And the sweep's subject is the SET a cut retires, not the artefact the last
  red gate named.**  Four artefacts watched this one change and each reported
  separately: the de-threading gate (a `macro` is declaration-minting
  machinery), the reply-stack write census (a helper one hop past the frontier),
  and **two** Tier 3 anchors — one on the retired `WRITE` alternation, one on
  the retired `WRITE_PRIMITIVE_BODIES` key.  The fourth is the finding: after
  the third, this file's own *sweep what was pinning the thing you deleted* rule
  was run — and run against the retired **pattern**, which is what the red gate
  had pointed at, so the anchor naming a retired **registry key** stayed
  invisible until Tier 3 reached it.  A cut that deletes a pattern, a helper and
  a registry key has three sweeps to run.  Deriving that set is a mechanism
  `scripts/check_anchor_symbol_liveness.py` already has for Python *symbols* and
  does not have for the string-literal *keys* these registries are indexed by;
  extending it is registered in `docs/REGISTERED_DEBT.md` table C rather than
  restated here, because a rule this file has now stated three times is owed a
  check.

  **And a spelling is not a read** (PR #895 review, `v0.35.12`).  The zero above
  was true of `s.objects[k]?` and blind to `s.objects.get? k`, which is *the same
  read*: the `GetElem?` instance **is** `RHTable.get?`, and this tree proves it
  outright (`objects_getElem?_eq_get?`, by `rfl`).  So the census measured a
  spelling, and an enforced zero a rename walks around is worse than no zero,
  because the number reads like a measurement.  Not theoretical either: forty
  executable reads were hiding in the method form, and one of them —
  `Concurrency.updateObjectAt` — **said so in its own docstring**, *"so the
  AK7-cascade raw-match floor stays at its v0.31.2 baseline"*, which is choosing
  a spelling to evade a metric and is the mirror image of this file's own rule
  against contorting prose to satisfy a scanner.  Its second claim, that no typed
  accessor applied, was false besides: `getObject?` is the kind-agnostic one.
  `READ` reads both spellings now, and the self-test's decisive case keeps the
  read and changes only how it is written.

  Three things new code must respect.  (1) **The frozen surface is in scope, and
  always was.**  `FrozenKernelObject.reply` carries the live
  `SeLe4n.Kernel.Reply` and `Model.freeze` copies a live state's records
  verbatim, so a frozen transition discriminating a variant at the call site is
  the defect this census is named for — it had twenty-nine such reads, now zero,
  routed through a frozen accessor family (`Model/FrozenState.lean`) that mirrors
  the live one and which `FrozenOps.frozenLookup*` is stated over rather than
  beside.  (2) **Where a site distinguishes "wrong kind" from "absent" the typed
  accessor is the wrong tool**: it answers `none` to both, so collapsing the two
  would change an error code.  Those sites read `getObject?` and keep their arms
  — no raw table read, and the distinction that *is* the semantics survives.  (3)
  **The exemption is per declaration, not per file.**  `Model/State.lean` was
  skipped whole, which is a 4800-line module that is not only accessors, so a raw
  read added anywhere in it was invisible; `ACCESSOR_BODIES` names the twenty-one
  bodies that *are* the accessors and the store primitives, and is reconciled in
  both directions in **every** mode — `--rows` included, since that is the mode
  Tier 0 calls — so a stale exemption fails rather than reading like coverage.

  Two mechanical notes, both the *one question, two answers* rule at the point
  where the fix could have introduced it.  The per-key inventory for this metric
  was **deleted**, not kept beside the zero: at zero a cardinality and a set say
  the same thing, and carrying both would be this file's own duplication hazard
  inside the gate written to close it.  What replaced it is the *relation* — the
  gate asserts `STORE_READ_CODE` equals the sum of its own `STORE_READ_CODE_SITE`
  rows, in the baseline and in the current capture, so a hand-edited or truncated
  file claiming "none" beside a live site row is refused as a gate defect rather
  than passed on the strength of the total; the rows are still emitted, because
  when the zero breaks they are what names the offending declaration.  And the
  self-test grew a second case shape, because the two claims are token-preserving
  with respect to different things: the inventory cases hold every scalar fixed
  and the harness asserts it, while the census cases move the scalars and the
  harness asserts the fixture is internally consistent.  Its decisive case keeps
  the baseline and the current value **equal at one** — everything a ceiling
  asks, and exactly what a zero floor must still reject.

  **A region-scoped presence check is still a presence check** (PR #887
  review round 4).  Resolving the guard's block, the tail after a branch, or
  the body after a binding and then asking whether a token occurs inside it
  moves the haystack without changing the question: a divergence nested under
  `if retry { … }`, a halt nested under `if frame.x0() == 0 { … }`, and a
  routing `match` nested under a condition beside a second `match` all keep
  the token and break the relation, and `if lean_ready(c) == false { … }` is
  a condition without `||` that entails the *opposite* of readiness.  Ask the
  question of **statements** — `rust/sele4n-hal/build.rs`'s
  `top_level_statements` is the view: what a block does unconditionally is
  what its top-level statements say, a divergence is the block's *last*
  top-level statement, a routing construct is a top-level statement of the
  body, and a predicate entails readiness only in a structural form
  (`ready_condition_argument`: a conjunct that *is* the call).  The mutation
  for this class nests the token under a condition, or inverts the predicate
  around it.

  **Provenance, sole consumption and location are relations too** (PR #887
  review rounds 6 and 7).  A statement-level view answers "is this
  unconditional"; it does not answer *whose* value a guard reads, whether a
  bound name has a *second* consumer, or *which* of two matching arms is the
  live one — and a scanner that resolves the statement and then takes the
  token's first occurrence, or accepts any argument, is back to presence.
  `lean_ready(0)` on core 1, `let invoke = lean_x;`, a no-op `match`
  followed by an `if` on the same class, a `#[cfg(test)]` decode of tag 2
  beside the live one, and a decoy `Faulted` arm ahead of the real one all
  kept every token round 4 checked.  So: read the guard's **argument** back
  to the executing core through the statements that dominate it, with the
  last binding winning (`ready_argument_is_executing_core`); **count** a
  name's whole-word occurrences when the claim is "nothing else consumes
  it" (`word_occurrences`); and **locate** an arm by walking from the
  function's terminal statement through parsed arms
  (`terminal_routing_match`, `match_arm_spans`) rather than by its first
  textual match.  Round 4 applied the statement view to the three checks the
  review named and left their siblings on text slices; rounds 6 and 7 swept
  the siblings — the sweep rule above, failing in the way it says.  The
  mutation for this class keeps the token and changes its provenance, adds
  a second consumer, or puts a decoy ahead of the live occurrence.

  **A name is not a definition** (PR #889 review round 12).  The last
  relation in this family is the one a scanner performs implicitly every
  time it matches an identifier: that the spelling *denotes* the
  declaration it stands for.  It does not.  `let bootAndInitialiseRPi5 :=
  fun _ => pure (.ok default)` above the call satisfies every
  executed-call and branch-and-halt check written against the callee's
  name; `Fake.ffiFatalHalt` and a local `let ffiFatalHalt : BaseIO Unit
  := pure ()` both satisfy a halt pattern that allows an arbitrary
  qualifier; `@[inline, export lean_kernel_main]` is invisible to a
  `@\[export\s+…\]` regex, so the declaration carrying it is not
  recognised as the boot entry *at all* and its contract passes
  vacuously; and `#[link_name = "actual"] fn local();` names a symbol the
  Rust identifier never mentions.  So **resolve the reference before
  asserting about it**: `resolves_to` applied Lean's own suffix rule
  against fully-qualified names (`lean_qualified_declarations`) — that
  Lean-side machinery was retired at round 17, where the elaborator
  resolves references with no suffix rule to get wrong; the Rust and
  attribute halves below are live — the
  candidate set must contain nothing unapproved, a bare name is refused
  where the declaration binds it locally, the attribute list is parsed
  rather than matched (`lean_code_view.attribute_arguments`, shared with
  `build.rs`'s parser so the two inventories cannot disagree), and an
  `extern` declaration's symbol is its *effective linker name*.  Where
  resolution is beyond a scanner — an alias for a Lean upcall, which no
  gate can attribute to a readiness guard — refuse the alias
  (`lean_link_name_aliases`) rather than read past it.  The mutation for
  this class keeps the name and changes what it denotes: rebind it, put
  it in another namespace, spell the attribute a second legal way.

  **A nested construct is not a sibling** (PR #889 review round 13).  The
  same substitution one level down: a scanner that splits a multi-line
  construct into lines and treats them as peers has thrown away the
  nesting, and nesting is what says which construct a line belongs to.
  Stripping each continuation's indentation let a `match` *inside* an arm
  donate its `| .error _ => halt` to the arm list of the match that
  contains it, so a boot-result match with only a wildcard arm read as
  having a named, halting error handler; and "the arm's last non-empty
  line" is the arm's outcome only until the conditional is written across
  lines, where the halt in an `else` branch is the last line and runs
  only when the condition is false.  **Keep the depth and ask the
  question of the level you mean**: continuations retain their column
  relative to the block, arms are the `|`s at the match's own column, and
  a body's terminal statement is the last line at the body's *minimum*
  column.  The mutation for this class keeps the token at an accepted
  position and moves it one level in or out.

  Round 14 of the same review is that sweep rule failing four times at
  once, and is the clearest evidence for it: `let` was not every binder
  (`have` shadowed the value the boot-result match reads), an exit is not
  always the whole statement (`if skip then return ()` passed a check
  that asked whether the statement *begins* with `return`, while
  `build.rs`'s `statement_may_exit` had asked the right question since
  PR #887), the halt-alias closure resolved by suffix while
  `reference_failure` in the same file required a *unique* candidate
  (both retired at round 17 with the rest of the Lean scan), and
  the recursive shell view lexed `$( … )` while the legacy backtick
  spelling beside it was still copied verbatim.  The RR7 audit round found the third sibling: a here-document body was lexed as the enclosing script's text, so one apostrophe in a Lean fixture inside `check_physical_address_width.sh` inverted the quote state for the rest of the file and every double-quoted diagnostic below it counted as code.  None was a new class;
  each was a rule already written down, applied at one site and not at
  its sibling.  **When a fix names a relation, grep for every other place
  that asks it** — the same file, the other language, the other
  spelling.  Its fifth finding adds the one genuinely new point:
  **the view you read depends on the question, and one walk can need
  both** — a string literal supplied a `{` that a nesting walk read as an
  enclosing block *and* a `#[cfg]` that the verdict read as that block's
  header, because both were taken from the strings-kept view.  Structure
  (braces, attributes, statements) comes from the string-free view; only
  the text a predicate is *about* comes from the aligned kept one.

  **When the enumeration cannot be finished, state a contract instead**
  (PR #889 review round 16).  The four preceding rules all say *resolve
  the text into the structure it stands for* — and rounds 12, 14, 15 and
  16 showed the limit of doing that with regexes over a language you are
  not parsing: each round taught the binder scan one more Lean form
  (`have`, `for`, `let ⟨a, _⟩ :=`, the same pattern across lines) and
  the head-matching call scan one more way to discard what the head
  named (`f x |> fun _ => …`).  The fixes were right and the class
  stayed open, because the set of valid spellings that defeat a regex is
  unbounded while the set a gate has seen is finite.  Where the subject
  is code **this project writes** — and especially where it does not
  exist yet — the exit is to require a canonical spelling and refuse the
  rest: the boot entry names the checked boot and the halt by their
  *fully-qualified* names (Lean's local binders bind single-component
  identifiers, so nothing local can shadow one) and the accepted
  expression is the call *and its arguments*, never a prefix of a larger
  expression; the readiness guard is written `crate::lean_ready::lean_ready(..)`
  and the bare spelling never counts.  A contract on unwritten code
  costs nothing and makes the question decidable; keep parsing only
  where the subject is code you do not control.

  **A Lean question goes to the Lean elaborator, never to a regular
  expression** (PR #889 review round 17, and a standing instruction).  The
  rule above is the last patch this class accepts; the class itself ends
  here.  From PR #889 review round 3 to round 16 the boot-entry check in
  `scripts/check_kernel_entry_exports.py` grew into a Lean parser made of
  regexes, and eleven rounds of findings against it were one defect in
  eleven costumes — a name is not a definition, a nested construct is not
  a sibling, a prefix is not the expression, a constructor's head is not
  its coverage, a `renaming` binds a name no declaration mentions.  Each
  fix was correct and the next round found more, because the set of Lean
  spellings that defeat a regex is unbounded.

  So: **if the property is about elaboration — which declaration a name
  denotes, what an expression evaluates, which values a pattern matches,
  what a body transitively calls — ask the environment.**  A `run_cmd`
  over `Environment` that throws is a gate: `getExportNameFor?` finds an
  `@[export]` whatever its attribute list looks like,
  `Expr.getUsedConstants` returns *constants*, and a constant has one
  definition, so aliasing, shadowing, `renaming`, qualification and
  notation are not questions any more.  Building the module is the check
  (`scripts/test_tier1_build.sh`), and it carries witnesses so it is
  decisive before the code it governs exists.  The tree has three such
  gates: `SeLe4n/Testing/BootEntryContract.lean` (the hardware boot
  entry's contract), `SeLe4n/Testing/IpcDethreadingEnvironmentCensus.lean`,
  and the probe-driven `check_live_arm_per_core_routing.py` /
  `check_content_flow_coverage.py`.

  **And occurrence is not execution** (PR #889 review round 18).  Asking the
  environment answers *which declaration*, not *whether it runs*:
  `Expr.getUsedConstants` reports that a constant occurs in the elaborated
  term, so `if cond then bootAndInitialiseRPi5OrHalt config else pure ()`
  satisfies a used-constants test and boots nothing on the path a real
  configuration takes.  That is this file's oldest rule — a presence check is
  not a relation check — one level below text, and the resolution is the same
  in kind: **walk the structure that cannot branch** and ask the question of
  what it reaches.  `unconditionalActions` follows binders, `let`s, metadata
  and both action arguments of a monadic bind; a conditional or a `match`
  appears there as one action whose head is `ite` / `dite` / a matcher, which
  is not the call being required, so it satisfies nothing.  The mutation for
  this class keeps the call and nests it in a branch.  **And the walk's own
  assumptions are relations too** (PR #889 review round 19): a `Bind.bind`
  application sequences only under a lawful *instance*, which is an argument —
  a `Bind` on a type definitionally equal to `BaseIO Unit` may discard both of
  them, so the instance is compared against the one synthesis finds
  (`isCanonicalBaseIOBind`); and `ConstantInfo.value?` hides an `opaque` body
  by default, so a walk that does not pass `allowOpaque := true` reads
  `opaque overwrite := initialiseKernelState` as a harmless leaf.  Where the
  environment still cannot answer — an `@[extern]` body is foreign — say so in
  the docstring and state why the property survives, rather than assuming it
  away.  The same round's third finding is the *enumeration* rule again, and
  the second instance of it in the same place: `PlatformConfig.wellFormed`'s
  conjuncts and the `else if` chain reporting them were two lists that had to
  agree, and twice a conjunct was added to one and not the other, so a config
  was refused in the words of a fault it did not have.  **A diagnostic belongs
  with the predicate it reports**: `wellFormedConjuncts` pairs each conjunct
  with its message, `wellFormedDiagnostic` reads that list, and
  `wellFormed_eq_all_conjuncts` fails to elaborate if the two ever diverge.  A second relation the
  environment does not volunteer is the **type**: an `@[export]`ed declaration
  links under its C name whatever its Lean type, so a seam's contract states
  the type its `extern` declaration is called at
  (`expectedBootEntryType`, `UInt64 → BaseIO Unit`).  And the environment a
  contract reads is itself a relation — `SeLe4n/Testing/BootEntryContract.lean`
  imports the production root as well as `Platform.Staged`, and pins that with
  `env.header.moduleNames`, because a declaration outside the imported closure
  is indistinguishable from one that does not exist.

  Two corollaries.  **Prefer making the property structural over checking
  it at all**: `Platform.FFI.bootAndInitialiseRPi5OrHalt` is the checked
  boot with its failure handled, so "the entry's `.error` arm ends in a
  halt" — eight review rounds of parsing — became "the entry calls this
  constant", which `getUsedConstants` answers.  And **a lexical scan is
  still right where the question is lexical**: the `@[export]` inventory
  the archive reconciliation reads is deliberately taken from Lean
  *source*, because a module outside the import closure exports nothing
  into the environment and that drift is precisely what it must catch.
  The test is what the property is *about*, not which language the file
  is written in.  Where a Lean scan survives for that reason, say so in
  its docstring; `rust/sele4n-hal/build.rs` keeps one because it cannot
  depend on a Lean build, and it is pinned against the elaborated
  inventory rather than trusted.
  **And a hand-written analysis over `Expr` is not the elaborator** (PR #889
  review round 21, and the correction to round 17).  Round 17's instruction —
  *a Lean question goes to the Lean elaborator, never to a regular expression*
  — was applied to **names** and ended that sub-class outright, because
  `getExportNameFor?` and `getUsedConstants` return constants and a constant
  has one definition.  It was **not** applied to *behaviour*, and nothing in
  the environment answers "what does this program do": rounds 18, 19, 20 and 21
  are four consecutive findings against `unconditionalActions`, a hand-rolled
  abstract interpreter written in round 17 to decide whether an arbitrary
  `BaseIO` term boots.  A conditional (18), a lawless `Bind` instance (19), a
  hidden `opaque` body (19), a non-returning action (20), a `let`-bound head
  (21) — each fix correct, each round finding another form, for the reason
  round 16 had already written down about regexes: *the set of inputs that
  defeats a partial analysis is unbounded while the set it has seen is finite.*
  Substituting `Expr` for text moved the class down a level; it did not close
  it.

  The exit is the one round 16 named, applied to the **program** rather than to
  its names: **where the subject is code this project writes and does not exist
  yet, require a canonical spelling and refuse the rest.**
  `SeLe4n/Testing/BootEntryContract.lean` no longer analyses the boot entry —
  it requires the entry to *be* `Platform.FFI.bootAndInitialiseRPi5OrHalt`
  applied to a configuration, decided by reducing the entry's body **towards
  the approved call** (`Meta.whnfUntil`: beta, zeta, delta through aliases,
  until that constant is the head) and one reducible `isDefEq` against a
  metavariable on what remains (PR #892 review round 2 — round 21 used one
  unbounded `Meta.isDefEq`, which opens *both* sides: on a deviating entry the
  unifier unfolded the approved call through the whole checked boot and hit
  the recursion limit once the configuration binding reached the RPi5
  RAM-variant selection, and it would have accepted an inlined copy of the
  wrapper's body, which is exactly what naming the wrapper exists to refuse).
  Every question the walk approximated is then answered exactly
  or has no subject: the entry *is* the boot, so nothing precedes it, there is
  no bind whose instance could be lawless, the reduction zeta- and beta-reduces so
  a `let`-bound head is not a form to know about, and nothing else runs at all
  — which makes the contract **stronger** than the walk, not weaker, since that
  one admitted any extra action which happened not to write kernel state.  The
  argument carries the rest type-theoretically: `PlatformConfig` is *data*, so
  no term of that type can install state, diverge or sequence.  Thirteen
  witnesses pin it, and three of them are **acceptances** — the required
  program spelled with a `let`, through an alias, and directly — because a
  contract that refuses everything reads exactly like one that decides.  What
  it deliberately refuses is an entry needing *effects* to build its
  configuration; if SM10.1 needs one, the kernel supplies that wrapper as a
  definition and this contract names it, which is a reviewed one-line change
  rather than a return to analysing arbitrary programs.  Eleven analysis
  definitions and 253 lines went with the walk.

  The corollary for scanners that have no elaborator to ask — a shell lexer, a
  Rust foreign block — is unchanged and is the same rule: **fail closed on what
  you cannot decide.**  A macro invocation inside an `extern` block expands to
  declarations no `fn`-shaped search can see, so the gate refuses the input
  rather than reading past it.

  **And one question answered in two places will diverge** (PR #889 review
  round 22).  The sweep rule above is reactive — *when a fix names a relation,
  grep for every other place that asks it* — and round 22 is three findings
  where it had not been run, which is the signal that the reactive form is not
  enough.  All three were a question with two implementations and only one of
  them right: "which cores does this boot install idle threads on?" answered by
  `bootAndInitialisePlatform` from the binding and by
  `bootAndInitialiseFromPlatform` as a hardcoded `allCores`, so a narrow
  configuration booted a TCB pinned to a PE the machine it installed does not
  have; "how does a boot-fatal condition fail closed?" answered by
  `gic::halt_all()` at three sites and by the per-PE `cpu::fatal_halt()` at the
  handoff refusal, which parks the boot core while the secondaries that *did*
  start keep servicing interrupts; and "is this a function provider?" answered
  by `executable_definitions` (global **text** symbols, since round 8) for the
  archive and by an unqualified `.global` + label conjunction for the source
  fallback, so a `.section .data` object satisfied an `extern "C" fn`.

  **Derive both answers from one, or make the second impossible.**  The core
  list is now `declaredCoresOfConfig`, read off the configuration the machine
  will carry; the refusal calls the barrier the rest of the tree calls; the two
  provider paths both ask the section question (`executable_label_names`).
  Where a second implementation must exist — a source fallback for when the
  object code is not built — it answers the *same* question and
  under-approximates, so the divergence direction is a false missing symbol
  rather than a false provider.

  **And a proxy is not the fact** (PR #889 review round 23).  The corollary of
  the rule above, for the case where the second "implementation" is a
  *stand-in*: `bring_up_secondaries` returns how many PSCI `CPU_ON` calls were
  accepted, and the round-21 handoff compared that against the declared PE
  count — but the number is incremented before the secondary has executed any
  of its own init, so a PE that halts in MMU, GIC or timer setup, or an
  `AlreadyOn` PE that never reaches `secondary_entry`, still counts.  The fact
  is `smp::CORE_IRQ_READY[c]`, which core `c` publishes *itself* after
  `enable_irq` and which the shootdown protocol already reads as the
  IRQ-serviceable set.  `serving_core_count_within` (named `irq_ready_core_count_within` until WS-BP BP6.3, which added Lean-readiness to what it waits for) waits for it, **bounded**,
  so a PE that never publishes makes the boot *fail* rather than hang.  When a
  cheap number is available beside the expensive fact, check which one the
  property is about.

  **And a bound has two sides.**  Round 22's `declaredCoresOfConfig` clamped
  `declaredCoreCount` from above and said nothing about zero, where the
  derivation yields the *empty* core list: no idle thread on any core,
  `bootAffinitiesDeclared []` satisfied by any unpinned config, and a boot that
  returns `.ok` with nowhere to run.  `declaredCoreCountInRange` is
  `wellFormed`'s sixth conjunct.  Two mechanical notes from adding it, both
  earned twice now: projection paths into the `wellFormed` conjunction shift
  whenever a conjunct is added, so the accessors are `simp_all only [...]` and
  depend on no nesting; and a Tier 3 anchor written as `X config$` breaks the
  moment a conjunct follows `X`, so anchors name the conjunct-list pairing
  round 19 made canonical instead.

  **And a name is not a contract — read the docstring of what you reach for**
  (PR #889 review round 24).  Round 23's fix for *a proxy is not the fact* was
  paced with `cpu::wfe_bounded`, and its `max_ticks` is **informational**: the
  docstring says in terms that it "does not bound the actual `wfe`", and the
  body opens `let _ = max_ticks;`.  A bare `wfe` returns on an event and a
  secondary that dies in init sends none, so the first iteration could sleep
  forever, the elapsed count never advanced, and the caller's topology refusal
  was unreachable — *a wait that cannot time out cannot fail closed*.  The name
  was the only thing that said "bounded", and the name is not the contract.

  Worse, and this is the point: **`shootdown::wait_all_acked_bounded_in` had
  already reached that conclusion and written it down** — same hazard, same
  word ("asleep FOREVER"), same remedy ("a counted spin is strictly more
  robust"), with an injected clock so the bound is testable.  Writing a third
  bounded-wait instead of using it is the round-22 rule (*one question, two
  answers*) at the point where the tree had already answered.  **Before writing
  a wait, a barrier, a retry or a timeout, find the one this tree already has
  and read why it is shaped that way.**  The readiness wait is now that
  pattern, clocked by `crate::timer::read_counter`, with four host tests that
  the bound actually terminates — a timeout with a straggler, an immediate
  return costing no clock reads, a clamp above the flag array, and a zero
  budget.

  **And a scanner's default branch is a decision — refuse what you cannot
  read** (PR #889 review round 25).  Every rule above is about a scanner that
  asked the wrong question of input it *did* recognise.  This one is about the
  other branch: three separate scanners, asked something they could not parse,
  silently did nothing — and doing nothing is the fail-open answer in all
  three.  An `extern` item that was not a `fn` declared no link requirement, so
  `fn r#lean_real();` — a raw identifier, which names the very same symbol —
  asked the archive for nothing and Tier 1 passed with no provider.  A
  `.section` whose operand the code view had blanked (the quotes make it a
  string literal) matched no section-directive pattern at all, so the scanner
  stayed in whatever section preceded it.  An `@[export]` argument spelled with
  guillemets — `@[export «suspend_generated»]`, which Lean accepts and emits —
  left the export inventory, and with it the readiness-gate seam set, one entry
  short.  In each case the artefact is real and *present*: the symbol links,
  the label is emitted, the export compiles.  Only the gate is silent.

  This is the presence-check family's dual, and it is why they keep appearing
  together: a presence check asserts too little about a token it *found*; a
  silent skip asserts nothing at all about input it did not recognise.  Round
  21 had already established the right shape — an item macro inside an `extern`
  block is refused, not read past, because "where a scanner cannot decide, it
  fails closed" — and applied it to that one case, which is the sweep rule
  failing exactly as it says.  **So make the default branch explicit: enumerate
  the inputs that legitimately produce nothing, and stop the build on anything
  else.**  A spelling the language accepts and the gate does not is a gate
  defect; it should say so, on the day it is introduced, rather than quietly
  checking less.

  **And which direction is closed depends on what the scanner produces.**  A
  scanner that builds a set of **requirements** fails closed by *refusing*
  unreadable input — a requirement it drops is a check nobody runs.  A scanner
  that builds a set of **providers** fails closed by *dropping* it — a provider
  it invents satisfies a requirement that was never met.  So the same
  unreadable `.section` operand makes `executable_label_names` treat the
  section as unknown and therefore **not** executable (a symbol reported
  missing, the gate failing), while it makes `extern_declarations_in` and both
  `@[export]` inventories stop outright.  Choosing the wrong direction is
  indistinguishable from not choosing.  A new mechanism brings its own edge, so
  check it: reading assembler *statements* rather than lines (AArch64 GAS
  separates them with `;`) would have split a `#define ENTRY(x) .text;
  .global x; x:` — a cpp **template**, whose directives and label exist where it
  is invoked — setting the section from a body that never executes there and
  registering the parameter as a provider.  That is round 16's `.macro` hazard
  arriving through the fix for a different one; a preprocessor line is not split
  and contributes nothing.

  **And a FAILED derivation is not an EMPTY one — the same rule at the point
  where a gate learns its own domain** (PR #897 review, `v0.35.147`).  The rule
  above is about *input* a scanner cannot read.  This is about the *question it
  asks the outside world*: four Tier 0 gates derive their whole domain by running
  git, and every one of them answered a failed run with an **empty** one —
  `except (CalledProcessError, FileNotFoundError): return []` and its `{}` twin.
  `[]` is also what a clean scan of a tree with nothing in it returns, so the
  caller iterates over nothing, finds nothing, and the gate prints PASS.

  **The review reported one site; the sweep found seven**, and the sweep is the
  point.  Its first form keyed on `subprocess.` and so missed the *reported*
  one, which runs git through a helper — *a helper the scanner cannot see is a
  spelling that evades the metric*, inside the measurement written to size the
  class — so the domain is closed **transitively** over intra-module calls.  The
  test that separates a defect from a deliberate sentinel is sharp and needs no
  registry: **a failure branch is a defect when its value is one the SUCCESS path
  can also return.**  `-> list[str]` returning `[]` is indistinguishable;
  `-> str | None` returning `None` is a sentinel the caller reads.  Measured over
  every tracked `scripts/*.py`: 10 failure branches in the git-derivation domain,
  **8 indistinguishable and 2 sentinels, with nothing undecidable**.

  Three things this cut records.  **The consequence is measured per site, not
  asserted**: only `check_deferral_registration.tracked_files` was run to ground,
  and what it produced was not a silent pass but a **misdiagnosis** — 35 false
  "row cites a path the index does not track" findings, naming the register
  instead of git, which is *answering in the words of a fault it does not have*;
  the rest are the same wrong shape at lower or unmeasured reachability, and the
  fix is the shape.  Claiming seven silent passes would have been the overstatement
  the measurement exists to prevent.  **The shared answer is
  `scripts/indexed_source.py`**, because `check_deferral_registration.indexed_contents`
  and `generate_smp_theorem_manifest.indexed_text` were the same `cat-file --batch`
  parser — same loop, same header split, same `i += size + 1`, same trailing
  comment — under two names; collapsing them found a **third** instance inside
  the body itself, since both `break` on an unreadable header and return the
  **prefix** they had parsed, which is a truncated domain indistinguishable from
  a complete one.  And **not everything that runs git should raise**:
  `select_changed_anchors._git` stays status-returning because three of its
  callers ask git a question whose answer IS the exit status (`rev-parse
  --verify`; `diff --no-index`, where 1 means "they differ"), so only the two for
  which a nonzero status is a *failure* raise.  A raise cannot be mistaken for an
  answer, which is why the shared module raises and that helper must not be folded
  into it.

  The fifth instance is the same rule one artefact over, and it is the one that
  says where to look next: `check_anchor_consistency`'s `filtered` bucket means
  *composed*, and its **membership** was a fall-through from every other arm — so
  `LC_ALL=C rg PATTERN FILE` inside a `bash -lc`, which heads no option table and
  is not a `SEARCH_TOOLS` head either, landed in the EXCLUDED bucket on a stated
  ground that is false of it, while the bare-argv sibling answered `unparsed`.
  `_is_composed` decides that bucket positively now and everything else that
  searches and does not reduce is `unparsed`, whatever its head.  **When a
  category has a stated reason, its membership test must BE that relation** — and
  a bucket reached by falling through is not one.  The widening admits nothing on
  the live tree (5211 / 827 / 38, byte-identical), so every witness is planted,
  and the two new fixtures are decided by *different* conditions: restoring the
  fall-through flips both, while opening the assignment set flips only one — which
  is what keeps either from being inert.

  **And the shell has the same defect with a second failure mode: the fallback
  APPENDS** (WS-RR RR8.15, `v0.35.186`).  The rule above is about Python calling
  git; every shell gate in this tree counts with `grep -c`, which *prints its
  count on the failing path too* — so `n=$(grep -c PAT F || echo 0)` does not
  substitute a default, it **adds a second line**.  On a clean run `grep -c`
  prints `0` and exits 1 (no matches), so `n` holds `0\n0`, every later
  `[ "$n" -gt … ]` dies with `integer expression expected`, and the `if` takes
  the else arm.  `test_tier5_cross_language.sh` did exactly that: **the one
  comparison the whole gate exists for did not decide**, and agreed with the
  truth by accident of which arm a failing `[` takes, while an *unreadable*
  mismatch log — `grep -c` exits 1 for "no matches" and above 1 for an I/O
  failure — produced the same verdict as a clean one.  Read the status
  (`n=$(grep -c …) || rc=$?`), make `rc > 1` a named gate failure, and refuse an
  unreadable input rather than defaulting it.  The sweep off that one found
  **three** more, all latent — `store_reader_hygiene_baseline.sh` twice and the commit
  hook once — and a Tier 3 negative refuses a fifth.
  **And a FOURTH sat two lines above the helper that sweep wrote** (`v0.35.204`,
  found while re-anchoring the metric it produces): the baseline script's
  `SENTINEL_CHECK_DISPATCH` kept the idiom with its `grep -c` on one line and the
  fallback on the next, behind a backslash continuation, and the tree-wide
  negative was single-line — so *a line is not the command*, and a sweep that
  reads lines misses exactly the instance a contributor wrapped.  The anchor
  reads the continued command now, and its mutation set has the two-line shape
  beside the one-line one.  Two things this cut
  measured about its own method.  `shellcheck` passes every one of them, and the
  shell's error line sat *above* the gate's `PASS`, so only **running** the gate
  found it; this is the second consecutive cut where running an artefact found
  what auditing it did not.  And the mutation harness written to judge the fix's
  anchors re-implemented `test_lib.sh`'s own view routing, always using the
  overlay — where `rg` skips the symlinks the overlay is made of on a *recursive*
  scan, and where a `bash -lc … scripts/…` anchor does not run at all — so a
  decisive anchor read as MISSED.  **A harness that re-implements the gate's
  routing answers a different question from the gate**; it sources
  `_run_with_view` now, with `set +e` after the source, because under `set -e`
  the failing command a negative anchor *expects* kills the harness at the first
  one and truncates the run.

  **And a default branch over a closed inductive is a decision five artefacts got
  wrong** (PR #897 review, `v0.35.114` and `v0.35.115`).  The rule above is about
  input a scanner cannot *read*; this is the same rule where the scanner reads the
  input perfectly and answers a wildcard.  `ConstantInfo` has exactly eight
  constructors, and "which declarations carry a body" is the first question every
  environment-derived **domain** in this tree has to settle.  It had **six
  answers** — this paragraph said five for one cut, because `v0.35.114`'s
  enumeration was of the *censuses* and two embedded Lean probes ask the same
  question; the sixth was found by sweeping the tree for the eight constructor
  names, which is the measurement that produced the check below.
  `ReplyStackWriteCensus` was the one that was right (`.defnInfo` *or*
  `.opaqueInfo`), and five sites across three censuses and two probes matched
  `.defnInfo` alone, or read `value?` without `allowOpaque := true`, and
  wildcarded the rest — so an `opaque`, which is executable, which this tree's FFI
  surface has seventy-odd of, and whose body
  `ConstantInfo.value? (allowOpaque := true)` hands back, was silently outside
  **five** derived domains at once.  What each one then stopped asking: an
  unreachable `opaque` transition owed no wire-or-record judgement
  (`KernelTransitionReachabilityCensus`), an `opaque` lock-set footprint owed no
  `_size_le` bound — so `boundedWait_under_2pl` and the whole WCRT surface would
  be **silent** about it — an `opaque` invariant conjunct dropped out of
  `measuredConjuncts`, making the de-threading census demand less, an `opaque`
  writer of `SystemState.declassificationTaint` passed a check whose claim is "one
  live writer", and an `opaque` helper in a syscall arm's chain stopped the
  per-core routing reach there, so the arm beyond it reached no slot at all.  The
  review reported one of the five.

  Three things follow, and the first is why this was not four patches.  **A domain
  miss is silent by construction** — the constant is never examined, the pin never
  moves, and each census goes on reporting that its whole domain is accounted for
  — so the class cannot be found by reading a failure; it is found by sweeping
  every asker of the question.  **The right answer was already in the tree and
  unreachable from two of the askers**, which is `v0.35.59`'s rule verbatim: the
  owner was in the wrong layer.  It is
  `SeLe4n/Testing/DeclarationKind.lean`'s `bodyBearing` now, upstream of every
  census, matching all eight constructors with **no `_` case at all**, so a ninth
  in a future toolchain is a *build error* naming the function rather than a silent
  exclusion.  And **two of the six exclusions are necessary rather than
  incidental**, which is precisely why folding them back under a wildcard reads as
  harmless: a `.thmInfo` carries a value, and a result-type test still matches one
  — `theorem f : step st = st'` elaborates to `@Eq SystemState (step st) st'`,
  whose implicit type argument *is* the constant a `SystemState` domain looks for —
  and `.ctorInfo` covers `SystemState.mk`, whose result type is `SystemState`
  itself.  `scripts/check_module_axioms.py` had enumerated all eight, case for
  case, since it was written; that was the precedent, unswept onto the censuses.

  **The widening is not vacuous, and the witnesses are the measurement.**  On the
  real tree it admitted exactly one constant: `Platform.FFI.kernelStateRef`, an
  `opaque IO.Ref SystemState` — the state cell the reachability census is
  *defined over*, since "commits state" means "reaches a write to it", and which
  was outside its own census's domain.  It is reachable from every committing
  seam, so it needs no pin entry; carving it out by name would be the enumeration
  the census exists to retire.  Beyond that the arms needed planting, since a
  check that cannot fire and carries no witness is indistinguishable from one that
  is wrong: the owner carries a `def`, an `opaque` and a `theorem` control, and
  the reachability census carries an `opaque` transformer that must be in its pin
  and a control that only *takes* a `SystemState` and must not be.  Both census
  witnesses were decided by **building**: deleting the pin entry makes the
  reconciliation report the transformer as unrecorded, and reading the whole type
  instead of the telescoped result makes it report the control as unrecorded — so
  the pair pins the domain in both directions, and the first draft's claim that
  the control witnesses "any declaration" was corrected by the mutation that
  refused to produce it.


  **And the question a resemblance stands in for may have THREE answers, not
  one** (PR #897 review, `v0.35.148`).  `check_content_flow_coverage.py` decided
  *"is this constant a compiler auxiliary"* by a **substring** over the qualified
  name, so `SeLe4n.Kernel.congruentTaintWriter` matched `.congr` and left a gate
  whose whole claim is *one live taint writer*.  The obvious remedy — repoint it
  at the environment-based answer this tree already has — is wrong, and the
  measurement says so: asked of this tree, the substring test and
  `KernelTransitionReachabilityCensus.isCompilerGenerated` disagree in **both**
  directions, **1156** constants one way and **2814** the other.  They are not
  two answers to one question.  *Before collapsing two predicates onto one owner,
  measure whether they agree; two that disagree in both directions are two
  questions, and naming one of them the owner silently changes what the other
  asker asks.*

  What licensed deleting it instead was a different measurement: the filter
  discarded **nothing** (disabling it left the gate byte-identical), and
  everything it *could* discard is a name a human wrote — the probe reports every
  writer through its owner-resolution, so the names reaching the filter have
  already been mapped to a human-written definition.  **A filter positioned where
  it can only ever be wrong is not a filter**; the two answers upstream of it
  (the owner resolution, and "a theorem is not a program") were already doing the
  work.

  And writing the witness found the real cause one layer down, which is the part
  worth keeping: the owner resolution itself stripped any component with a
  reserved prefix, so a contributor's `eq_foo` was attributed to its **parent
  namespace**.  Same class, better unit — the final component rather than a
  substring — and still a resemblance.  `v0.35.130`'s rule closes it: *the name
  narrows and the environment decides*, a declaration the compiler minted
  carrying no source range (`Lean.declRangeExt`, pure).  Two things that fix had
  to get right.  The range is asked of the constant **as the environment holds
  it**, never of its un-mangled user name — `privateToUserName?` maps
  `_private.M.0.foo` to `M.foo`, which is not a registered constant, so asking
  there answers "no range" for every private declaration and strips them all,
  re-creating the private-blindness the gate was fixed for two cuts earlier.  And
  the un-mangling was **folded into** the owner resolution rather than left as a
  helper beside it, because the two are one step and splitting them is precisely
  how the wrong name gets asked.

  The witness is the measurement here, as it is in every cut whose widening
  admits nothing: every existing plant in that gate is named `cfPlanted…`, so not
  one of them could show either defect.  The plant that decides is named the way
  a contributor would name a real definition (`eq_cfPlantedUserNamedTaintWriter`),
  and it is asserted on **both** sweeps.  *A witness drawn from the naming
  convention the fixtures already use cannot see a defect about naming.*

  **And the answer to "who else asks this" is a SWEEP, and once the sweep has run
  twice the third response is a check** (PR #897 review, `v0.35.115`).  `v0.35.114`
  gave the question one owner, repointed four askers and wrote the paragraph above.
  It named a fifth asker rather than omitting it — `check_content_flow_coverage.py`'s
  embedded Lean probe, whose `cfExecutableValue` both matched on the kind *and*
  called `value?` with no flag, with four sweeps beside it that bypassed even that.
  Then the *sweep* — every tracked file, for each of the eight constructor names —
  found a **sixth**: `check_live_arm_per_core_routing.py`'s `routeExecutableValue`,
  byte-for-byte the function `cfExecutableValue` had been, feeding a **reachability**
  question, so an `opaque` helper anywhere in a syscall arm's chain made the walk
  stop there and the arm beyond it was reported as touching no per-core slot.  The
  enumeration that opened this cut said *five*; the count was six, and nothing but
  running the search over the whole tree would have said so.

  So the response is not a seventh paragraph.
  `scripts/check_declaration_kind_askers.py` (Tier 0) refuses any subject that
  matches a `ConstantInfo` constructor and is not a recorded asker, keyed
  `(subject, constructor)` with a **count** and reconciled in both directions — the
  floor shape `identifier_naming_baseline.json` already has, because a set of keys
  alone cannot see a second occurrence inside a subject that already has one and a
  count alone cannot see the first in a subject that had none.  **Its domain is
  derived over both places this tree writes Lean**: `.lean` files, and a probe
  string a Python gate hands to `lake env lean`, located by `ast` — so the three
  such gates are found without any of them being named, and a fourth is found the
  day it is written.  A file whose import markers the located constants do not
  account for is **refused** rather than skipped, since "could not read" must not
  answer the same as "read and clean".  Both views are the ones this tree already
  owns, because several subjects document in their docstrings exactly which
  constructors they retired and a check that counted those would force them to stop
  explaining themselves.

  Three things that cut measured.  **The widening admits nothing on the live tree**
  — both gates' whole inventories and both production verdicts are byte-identical
  before and after — which is the opposite of `v0.35.114`, where one real constant
  (`kernelStateRef`) came in; so here the *plants* are the entire measurement, and
  each is its neighbour with one keyword changed: `cfPlantedOpaqueTaintWriter` is
  the first plant's body spelled `opaque`, and `routeSelfTestOpaque` is
  `routeSelfTestAlias` spelled `opaque`.  **Neither could have been an older
  witness**: all four existing plants and all three older routing witnesses are
  definitions, so every one of them passes both halves of the defect, which is
  exactly why four review rounds and a sweep were needed to see it.  And **the new
  check earned its keep on its first run**, twice: its own reconciliation reported
  two guessed probe-variable names that do not exist, and the mutation set confirms
  it reports each pre-fix probe, a census re-deciding the question, a stale entry, a
  moved count in either direction and an unlocatable probe.

  **And the answer to "who else asks this" had a THIRD dimension: the census's own
  domain and closure** (PR #897 review, `v0.35.125`).  `v0.35.115` derived which
  *files* hold a Lean probe and gave the question one owner; it left
  `KernelTransitionReachabilityCensus`'s own three questions to resemblances, and a
  review found all three at once.  A **name prefix** stood for "generated"
  (`startsWith "initFn"`, which an ordinary `initFnCleanup` trips — this file's own
  retired `eq_` prefix, one census over); a **constant occurrence** stood for
  "reachable", so a transformer mentioned only inside a proof was marked live and
  escaped the wire-or-record pin; and a **mention** of `SystemState` stood for
  "returns state", so `TlbCacheJointState.pageTableUpdate` — which rewrites that
  record's `sysState` field — was on neither side of the reconciliation while the
  projection `TlbCacheJointState.sysState` was.

  Each remedy is the environment answering, and each was **measured before it was
  chosen**.  The prefix is *deleted* rather than narrowed: of the 4 `initFn`
  constants here, **0** are outside `isAuxiliary`, a module's init being
  macro-scoped, so the clause excluded nothing while admitting a user name.  The
  closure skips an **erased** constant, decided on the telescoped result through
  the sibling census's `isPredicate`, since `Expr.isProp` is true of a proof and
  false of `SystemState → Prop` and a proposition reaches the walk as an implicit
  argument at a call site: the permissive closure is 4231 constants and the
  erasure-respecting one 3477, and **zero** of the 754 are transformers, so the
  tightening is free today and closes the path one proof-carrying body would open.
  And the domain asks whether a result **carries** state — `SystemState`, or a
  non-propositional project inductive holding one in a constructor field,
  transitively — which is 10 carrier types and 39 more pinned definitions, the boot
  path among them.

  Two rules the carrier derivation cost, both about the measurement rather than the
  code.  **A constructor's telescope opens the inductive's own parameters**, so
  without dropping `numParams` a `Prop` structure over a state reads as holding
  one — 64 carriers, almost all propositions, which is a measurement that would
  have licensed a much larger claim than the tree supports.  And **a field carries
  state when its own telescoped result does**, the same question the domain asks of
  a definition: judging by a mention anywhere admits `PlatformBinding` and both
  boundary contracts, and with them every configuration record in the tree.  *A
  measurement that licenses a conclusion gets checked as hard as the conclusion* —
  twice here, and the third reading is the one that shipped.

  One thing the erasure witness had to get right, and it generalises: **`Expr`
  traversal walks binder TYPES**, so a helper whose argument is typed with the
  proposition reaches the subject through its own signature rather than through the
  proof — a type-level mention, which is not execution either but is not the route
  the witness is about.  The consumer is generic in the proposition, and the check
  asserts that the theorem's own proof term mentions the transformer, because a
  proof term that does not makes the whole witness **inert**.

  **And a REDUCIBLE ALIAS is not a different type, nor is an exhausted fixpoint a
  smaller answer** (PR #897 review, `v0.35.128`).  Two more misses in that same
  derivation one cut later, and both are the *domain* half of this family rather than
  the predicate half — so both fail in the one direction this census structurally
  cannot report: a constant it never examines moves no pin, and the reconciliation goes
  on stating that every non-executed transformer is recorded.

  `forallTelescopeReducing` reduces only far enough to expose a `∀`, so a result spelled
  through `abbrev StateResult := Option SystemState` arrives as the alias **constant** —
  which the carrier set never contains, that set being built from inductives — and the
  transformer is then in neither the reachable nor the unreachable set.  One `whnf` at
  **reducible** transparency is the exact boundary, and *exact* is measured rather than
  argued: `abbrev` is what Lean makes reducible, so it unfolds, while **default**
  transparency opens a dependent projection like `id.evidenceProp` and files **four**
  records of proofs (`covertChannelEvidence`, `fineLockClaimEvidence`,
  `declassificationRuleEvidence`, `crossCoreLiveArmEvidence`) as state transformers.
  The negative anchor on the unrestricted spelling is what keeps that boundary.

  Two things the fix records.  **The widening needed the environment's own answer to
  "did you generate this"**: reducing a `T.noConfusion`'s result mentions the
  constructor fields' types, so `Lean.isAuxRecursor`, `Lean.isNoConfusion` and
  `Meta.isMatcherCore` join the filter — and they are **complementary** to the
  hand-written component list rather than a replacement, measured both ways (the list
  catches `_flat_ctor` / `_sizeOf_inst` / `_unsafe_rec` members the predicates do not;
  the predicates catch every `*.noConfusion` the list does not).  *Derive what the
  environment can answer and keep the list as a pin for what it cannot* — claiming
  redundancy in either direction would have shrunk the filter.  And **the real tree
  gains zero declarations**, so the plants are the entire measurement: an `abbrev`
  naming a state-carrying type (which must be in the pin) beside the control naming one
  that carries nothing (which must not), so the pair decides *the alias names a carrier*
  rather than *the result is an alias*.

  The second miss is *a rule stated is not a rule enforced*, and the rule was stated in
  the very docstring that failed to enforce it: `carrierFixpointBound`'s own text said
  exhaustion "would under-approximate the carriers, which makes the domain SMALLER, so
  a new bound must be checked rather than assumed" — and the loop then **returned the
  partial set as though it were complete**.  It throws now.  The bound is an *argument*
  so the refusal has a witness, because on this tree the fixpoint converges in **two**
  rounds against a bound of twelve and nothing in production can reach the throw:
  `carrierFixpointRefusalViolations` runs the derivation at a bound of **1** and reports
  a violation when it *succeeds*, which is the only direction that can be silent.  (The
  two-round figure also corrects the previous cut's docstring, which said three — it had
  counted the convergence-detecting pass that does not run.)

  **And the sort the alias DECLARES is normalised too** (PR #897 review,
  `v0.35.135`).  The same miss four lines above, in the same derivation, unswept by
  the cut that wrote the paragraph above: the alias test read `ci.type` **raw**, so a
  declared sort that is itself reducibly aliased — `abbrev CarrierSort : Type 1 :=
  Type`, then `abbrev StateAlias : CarrierSort := SystemState` — is a `.const`,
  neither `isSort` nor `isForall`, and the alias never entered the candidate array at
  all.  A transformer over it is then in neither reconciliation set, which is the same
  silent direction one level further out.  *When a fix names a relation, grep for every
  other place that asks it* — here the other place was the **next test in the same
  function**, and asking it is what shows that the whole type and a telescoped body
  were two spellings of one question: `declaresNonPropSort` is the one owner and the
  branch on the raw shape is deleted, since `forallTelescopeReducing` over a non-`∀`
  type calls its continuation on that type.  Both boundaries above carry over
  unchanged — reducible unfolds an `abbrev` while default files the four evidence
  records, and `Prop` is a sort — so the plants are again the entire measurement (585
  over 19 before and after the fix; 586 over 20 with the pair), and the **control** is
  what makes them decide *the aliased sort is normalised* rather than *anything
  declared through this sort is a carrier*.

  **And a domain written as a NODE KIND is the same defect one grammar down**
  (PR #897 review, `v0.35.124`).  `v0.35.115` derived *which files* hold a Lean
  probe and left *which expressions* to one `ast` node kind: `embedded_lean` read
  the value of an `Assign`/`AnnAssign` and nothing else, with an explicit `else:
  continue`.  So a probe handed straight to its runner —
  `run_probe(<a literal>)` — was located by no shape at all, and the fail-closed
  refusal beside it asked whether **anything** had been found, which one assigned
  probe in the same file answers for every marker in it.  Measured on the fixture:
  the capture read the assigned probe alone and refused nothing, so an inline probe
  could re-decide the body-bearing question with the inventory unchanged and Tier 0
  green — *invisible in both directions at once*, which is what makes a domain miss
  unfindable by reading a failure.

  Four things follow, and each is a rule this file already carries arriving at a
  smaller unit.  **The domain is every string constant**, plus every expression that
  *assembles* one (`A + B`, an f-string, a `.join`/`.format`), because an assembled
  probe's import marker and its `ConstantInfo` match sit in different fragments and
  neither is a probe on its own evidence — measured at **zero** admitted on the
  tracked tree, against **1060** for the statement-level grouping first tried, so
  the widening costs nothing and every witness is planted.  **The refusal is a
  count** (`markers_located < markers_in_text`), since *a cardinality is what sees
  the second occurrence*; its witness is therefore an unlocatable marker **beside** a
  located probe, because a fixture whose only marker is the unlocatable one is
  refused by the superseded reading too and would pass with the count reverted.  It
  counts markers in located TEXT and not in the rows reported, because one constant
  bound to two names is reported twice and that surplus would pay for a marker nobody
  read — found by re-reading this cut's own diff, not by a review.  **A
  subject key must identify a subject**: an assembled probe takes its assignment's
  name rather than its scope, or two of them in one module collapse into one key
  where the counts add — and two probes that bind *no* name in one scope are
  **refused**, not bucketed, since an ordinal key churns when an earlier probe is
  deleted and *refuse, name the scope, state the remedy* is what this project does
  wherever a scanner cannot decide.  And **the reassembly is in SOURCE order**:
  `ast.walk` is breadth-first, so `A + B + C` yields `C, A, B`, and a join in that
  order destroys a constructor name straddling the last boundary — two fragments
  cannot witness it, which is why the fixture the defect arrived with could not have
  caught it.

  One mechanical note, and it is the *fail-fast harness* hazard rather than a new
  class: a `UnreadableProbe` raised inside a self-test case escaped as a traceback,
  which is not the gate's voice and which skips every case after it — so one
  mutation could mask another, and two of this cut's eleven mutations were
  mis-attributed until the direct reads went through a helper that reports a refusal
  the way `violations` already did.  **A harness that crashes where it should report
  hides the second defect**, and a mutation run is the only thing that shows it.

  **And the located subject's TEXT and its IDENTITY are each something the program
  computes** (PR #897 review, `v0.35.127`).  Two fail-open defects in that same
  locator, one cut later, and they are one class: it asked *what shape is this* where
  the question was *what value does this have*, and *what is this called* where the
  question was *which subject is this*.

  The text half is `a spelling is not the text` at the one place the text is
  assembled rather than written.  `_is_concatenation` asked whether an expression
  builds a string from parts, and the callers then **joined its literals in source
  order** — which is the string `"a" + "b"` builds and is *not* the one
  `"… .{}Info …".format("opaque")` builds: joining yields `… .{}Info … opaque`, so the
  constructor pattern matches nothing while the template's own import marker **is**
  accounted for, so the fail-closed marker count passes too and the asker is invisible
  in both directions at once.  `_reconstruct` returns the string or `None`, and four
  forms are determined by literals — a literal, `+` over two determined operands, an
  f-string with no interpolation, and `<literal>.join([<determined>, …])`.  Narrowing
  the reader is **not enough on its own**, and that is the load-bearing part: with
  `.format` no longer forming an assembly its template would fall through to the
  bare-constant branch and be *located*, reopening the hole one branch over — so
  `_unreadable_assemblies` **refuses** a string assembly that carries a marker and
  does not reconstruct, which is *a scanner's default branch is a decision* applied to
  the one branch a narrowing creates.  The shape set excludes a call on a plain
  **name**, because a probe handed straight to a helper is this tree's commonest idiom
  and its literal is the call's *argument* rather than a part of a string the call
  builds; a `.replace` on a named `@SENTINEL@` template — how all four real probes are
  built — is likewise not a subject, its marker living in the template's own
  assignment.  Measured before choosing: **zero** such expressions on the tracked
  tree, so the refusal is entirely planted today.

  The identity half is this file's own rule inside the cut that wrote it.  A named
  probe's key was the bare target name, so two probes assigning `PROBE` in two
  functions shared one subject and their counts **added**: change one from `.defnInfo`
  to `.opaqueInfo` and the other the inverse, and every number in the inventory is
  unchanged while *both* askers have re-decided the question.  `v0.35.124` had already
  refused exactly that for probes binding **no** name, one branch over, under a
  comment stating the reason — *a fix applied at one site and not its sibling*, for the
  third time in this file.  `_qualified` keys a named probe by scope-and-name, the
  scope itself is now a **qualified path** rather than the nearest declaration name (a
  bare name is a resemblance two methods in two classes share), and two probes that
  still land on one key are **refused** — by OCCURRENCE, not by distinct text, because
  two identical rebindings double every constructor in them and a set cannot see the
  second one.  Free on the tree: all 17 located probes are at module scope, so every
  key is byte-identical and the pin does not move.

  Two things the cut records about its own witnesses.  **The axis came from Python's
  grammar, not from the reported spelling**: the review named `.format`, and `%` was
  not even *grouped* by the superseded reader — so its template was read as a bare
  inline probe and the constructor was lost the same way, one branch further over —
  while an interpolating f-string has `FormattedValue` parts that are not literals at
  all.  All three are cases, with **two controls** (a literal f-string, which
  reconstructs and is read; a `@SENTINEL@` template, which is the tree's own idiom),
  because a fix that banned the node type would pass a case list drawn from the
  finding.  And **a mutation must revert the defect, not merely edit the code**: the
  first mutation written against the `.format` refusal widened a branch whose other
  conditions still rejected the input, so the self-test passed and the case read as
  unverified; the mutation that decides restores the *superseded reading* — a
  `.format` branch returning the source-order join — and is caught immediately.

  **And a TRANSFORM of located text is a third thing, beside its shape and its
  value** (PR #897 review, `v0.35.129`).  `v0.35.127` replaced *what shape is this*
  with *what value does this have*, and the case that survived is the one where the
  answer is **almost** the value.  A named template holding a constructor spelling
  with a hole in it is a **located** subject: its import marker is accounted for, the
  fail-closed marker count is satisfied, and its constructor count is **zero**, while
  the probe handed to Lean decides the question.  Invisible in both directions at
  once — the shape that makes a domain miss unfindable by reading a failure — and
  reached by the tree's own commonest probe idiom, a `@SENTINEL@` template consumed
  by `.replace`.

  **So the reconstruction is PARTIAL: determined text with holes.**  Not the
  all-or-nothing string, and not a shape — `_reconstruct_holed` returns the text the
  expression builds with one non-word `_HOLE` wherever text the scanner cannot read
  enters it, and "determined" is that with no holes left.  Four things follow, and
  each is a rule already in this file arriving at a smaller unit.  **A name resolves,
  fail-closed at both ends** — a template is reached *through* its name, so a scanner
  that cannot resolve the name cannot see the text a substitution applies to, and a
  name bound more than once resolves to nothing because two bindings are two texts
  and no occurrence says which is live.  **The refusal asks COMPLETION, not the
  presence of a hole**: `_constructor_completing_holes` is derived from the
  constructor tuple and inherits its `\b` bounds, so a hole is refused exactly where
  the template has written part of a constructor against it — measured at
  **thirteen** substitution sites on the tree, every one undetermined and **zero**
  writing a constructor against its hole, so refusing every hole would refuse the
  tree and the mutation that does fails the control *and* the live gate.  **The
  default branch is taken per CALL SITE rather than per spelling** — an unmodelled
  form is unreadable when applied to determined probe text and an ordinary value
  fragment otherwise, which is what keeps the recognised set from having to be
  complete.  And **the admission test moves with the text**: the marker is asked of
  the assembled text in *both* branches, because a template reached through its name
  puts the marker in no literal fragment of the expression that substitutes into it.

  Two things that cut records about its own witnesses.  **The widening admits nothing
  and refuses nothing on the live tree** — 25 subjects, byte-identical counts, zero
  refusals — so the plants are the entire measurement, as at `v0.35.115`.  And **two
  of the ten mutations were MISSED on the first run**, which is the part worth
  keeping: the word-boundary guards and the named branch's admission test each passed
  every case that existed, because every fixture reached them through the other
  branch.  *An unwitnessed condition is indistinguishable from a wrong one*, so the
  answer is not to reason about it but to plant the case that separates it — a
  fixture with **two** holes, so a mutation dropping one guard is caught by its own
  half; a substitution **assigned** to a name beside the one that is returned; and an
  ambiguous name that is *not* probe text, since the ambiguous-probe refusal fires
  first for every name that is.  **Run the mutations before believing the cases.**


  **And a PREFILTER is not the SIGNAL — and asking one with the other's predicate
  skipped two whole gates** (PR #897 review, `v0.35.132`).  Every rule above is about
  what a scanner asserts of input it examined.  This is the cheapest way not to
  examine any: `embedded_lean` returned early unless `_probe_signal(text)` held, and
  that predicate is written for a probe's OWN text, where the import begins a line.
  Asked of a whole Python file it is a different question, false for one of the
  commonest spellings there is — `PROBE = """import SeLe4n ...` opens the literal on
  the assignment line, so no line of the file begins with the import.

  **Measured, and the measurement is why this is a rule rather than a patch**: that
  skipped `check_ipc_invariant_dethreading.py` (11 markers) and
  `check_tlbi_broadcast_discipline.py` (4) — two real Tier 0 gates, every embedded
  Lean probe outside the inventory, with the gate reporting the tree clean.  Not
  fixtures; the plants in the six preceding cuts admitted nothing, and this widening
  admits exactly those two files.  **A prefilter must be strictly WIDER than the
  predicate it stands in for**, and where a scanner has both, the narrow one is kept
  for the questions that genuinely are about a line start.

  Its sibling finding is the resolution residue reached by an extra HOP: `ALIAS =
  PROBE` resolves to no literal, so a transform through it substitutes into a hole
  whose result carries no marker, and the template is still located carrying the
  constructors its *unsubstituted* text spells.  **The refusal is the remedy, not
  resolution** — a probe has one name, deleting an alias is a one-line change, and
  chasing a chain whose depth nothing bounds is the partial-analysis shape this file
  retires twice over; the probe SET is closed transitively all the same, so `B = A`
  over `A = PROBE` is seen.

  One correction this cut records about its own plan, because the plan was wrong and
  the measurement said so before any code was written.  The first design deleted the
  hole machinery outright, on the ground that no probe in the tree assembles text.
  That is true of the 41 probe **assignments** and false of their **uses**: three
  `@SENTINEL@` `.replace` sites substitute *computed* values, so a canonical
  "substitute with literals or refuse" rule would have refused every real probe in
  the repository.  *Measure the uses, not only the definitions* — and when a
  measurement kills the plan, that is the measurement working.

  **And when TWO conditions guard one question, each needs a witness the other
  cannot rescue** (PR #897 review, `v0.35.130`).  `v0.35.125` deleted the `initFn`
  prefix and kept the component list on the stated ground that its members are
  *whole* components the compiler reserves rather than prefixes of user names.  True,
  and not enough twice over: Lean accepts `_flat_ctor` as an ordinary identifier, so
  a contributor's transformer with that name was excluded before its result type was
  read; and `components.any` excludes every declaration **nested beneath a namespace**
  of such a name, whatever it is called.  So the remedy is the one this section keeps
  arriving at — the name *narrows* and the **environment decides**: a reserved
  spelling is a suffix, so the question is the FINAL component, and a declaration the
  compiler minted carries **no declaration range**, which
  `Lean.findDeclarationRangesCore?` answers.

  What is new is what the mutation run then showed.  With the range test in place,
  **neither** the `any`→`last` narrowing nor the name test itself was observable:
  every user-written plant carries a range, so restoring `components.any` and
  deleting the name test each passed every case.  Two conjuncts, one of them
  witnessed.  *A condition no case can reach is indistinguishable from a wrong one*,
  and the pair rescuing each other is how a two-condition guard hides a dead half —
  so the witness has to be the shape **neither** existing plant can take: a
  transformer **minted** through `Lean.addDecl`, with no declaration range, an
  ordinary final component, under a reserved namespace.  It decides both mutations at
  once, because it is the only input on which the two conjuncts disagree.

  Generalising: when a guard is a conjunction, ask of each conjunct *what input does
  this one alone reject?* — and if every fixture is rejected by its partner too, the
  conjunct is unwitnessed however plausible it reads.  The plant will usually have to
  be constructed rather than written, because the property being witnessed is
  precisely the one the ordinary way of writing code cannot produce.

  **And when a cut fixes an exhaustion, SWEEP every other bounded walk — the
  conservative direction is different for each** (PR #897 review, `v0.35.131`).
  `v0.35.128` made an exhausted carrier fixpoint an error and wrote down why; the
  question was never asked of its siblings.  Asking it found the tree has **four**
  bounded walks and that three of them fail closed for three *different* reasons —
  `reachesAny` answers `true` (does this export reach a state write? `true` demands
  more), `entailedTargets` answers the empty entailment set (fewer entailments
  demand more), `stateCarryingTypes` throws — while `liveClosure` returned its
  partial set.  A bound is not conservative in itself; **which** answer is
  conservative depends on what the predicate means, so every walk needs the question
  asked separately and the answer recorded at the walk.

  Two things that cut records.  **A docstring that compares itself to a sibling is a
  claim about the sibling**: `liveClosure`'s said it was "fuel-bounded like its
  sibling", and the sibling does the opposite — the comparison was false in exactly
  the direction that mattered, and it read as having been checked.  And **a
  precedence you would otherwise have to witness is better removed**: distinguishing
  "finished" from "exhausted" by arm order in one `match a, b` is a property no
  witness on this tree can reach (it bites only when the worklist empties on the last
  unit of fuel), so the arms are *nested* instead and there is nothing left to get
  wrong.  *Prefer making the property structural over checking it at all.*

  The same cut's second finding is the recursion rule one level down: a normalisation
  that reaches only the HEAD is a partial answer too.  `whnf` on `Option StateAlias`
  stops at `Option`, so an alias nested under a constructor never unfolds — and the
  answer is not to recurse the normalisation, which is one more partial analysis, but
  to add the alias to the **set** the search consults, where the existing fixpoint
  closes a chain of them for free.  *When a reduction cannot reach the thing, widen
  what the question is asked about rather than deepening the reduction.*

  Two corollaries about the plants it needed, both earned by a mutation run that
  found three of five conditions unwitnessed.  **A control that mentions the subject
  for an unrelated reason decides nothing**: the parameterised-alias plant first
  passed its argument as an inline `fun _ => 0`, whose own binder type put
  `SystemState` in the result expression outright, so the plant was in the domain
  whatever the code did.  And **`Prop` is a sort** — the one place this cut's first
  draft had to be told twice, because dropping that half admitted 30 spurious domain
  members and the mutation that proves it must target the branch the tree's own
  predicates actually take.

  **And a recognised set is not a derived set — so a count over one is a floor,
  not a measurement** (PR #895 review, rounds 1 and 2, `v0.35.13`).  Every rule
  above polices the **predicate**: what a scanner asserts of an element it
  found.  None of them polices the **domain**: whether it found them all.  That
  asymmetry is why this family keeps reappearing, because the two fail
  differently — a predicate miss can fire on a real element, while a domain miss
  is *silent by construction*: the element is never examined, the count stays
  clean, and the gate reports a number that reads as a measurement of absence.

  Six of the eight findings across two review rounds of one PR were that one
  defect.  `.objects.get?`, then `RHTable.get? st.objects k`, then a `where`
  equation body whose signature never closed — three spellings of one read.
  `pub unsafe extern "C" fn`, skipped entirely rather than judged.  `FrozenOps`,
  outside both library roots, so *every reply-stack write* meant every one in
  the modules the census imported.  A frontier that asked "constructs **and**
  stores" of one body, which a writer defeats by delegating the construction to
  a helper.  Each fix was right and the next round found another, because the
  boundary was being probed rather than the property.

  **Two kinds of gate, and only one of them can be closed.**  Where the domain
  is *derivable* — which constants a term uses, which modules an environment
  imports, what a definition transitively calls — derive it and reconcile both
  directions, and the class really does end there: the reply-stack write census
  now follows construction through helpers (`reachesChainConstructor`, walked
  backwards from the storing definitions and memoised, since nearly everything
  reaches a constructor forwards), and asks the *environment* which constants it
  generated rather than matching name prefixes.  Where the domain is a **coding
  convention over unbounded syntax** — "obtain objects through an accessor",
  "justify every unsafe site" — there is no closed formulation, in text *or* in
  the environment: round 17's instruction sends questions about **elaboration**
  to the elaborator, and "is this occurrence a read rather than a write" is a
  question about an API's meaning, which the environment has no opinion on.
  Measured rather than assumed: 245 hand-written executable definitions mention
  the object-table projection, because writing the store is what a transition
  does — so "never mention it" is not a stateable contract either, and the
  attempt to derive a read-set from result types promptly classified
  `FrozenMap.set`, a *write*, as a read.

  So for the second kind, **fix the claim**: report the number as a floor over
  recognised forms, in the gate's own output and in the prose that cites it
  (`STORE_READ_SCOPE`, and the unsafe gate's `scope:` line).  The enforcement is
  unchanged — a recognised violation still fails Tier 0 outright — but a
  widening of the recogniser becomes an improvement to a diagnostic rather than
  the closing of a hole that was claimed shut, which is the only way the reports
  stop being findings.  And keep the other half of round 25's rule, which is
  what bounds the gap: an input the scanner does not recognise **fails the
  gate**, so the unrecognised set is visible rather than assumed empty.

  One mechanical note, earned twice in this round: a fix for a domain defect can
  introduce one.  `Name.isInternal` looked like the environment's own answer to
  "did Lean generate this" and is true of the `_private.…` mangling, so adding
  it to the auxiliary filter would have excluded **every `private def` in the
  kernel** — the same class, inside its own remedy.  The census's planted
  witness caught it, which is what witnesses are for.

  **And a domain written as an exclusion is the same defect wearing a filter**
  (PR #895 review round 3, `v0.35.15`).  Round 2 named the class and fixed it at
  the four sites the review pointed at; round 3 found four more, and every one
  was the gate's *domain* spelled as a hand-written exclusion rather than
  derived: a glob naming `src` (so integration tests, `build.rs`, examples and
  benches were never scanned), a prefix list naming `eq_` (so a contributor's
  `eq_clearReply` was filtered out as a compiler auxiliary before its constants
  were read), a regex naming `: Prop` that matched a *binder* (so
  `def step (proof : Prop) … : SystemState` filed its raw store reads as
  specification and walked around an enforced zero), and a `usesDirectly` naming
  "direct" (so a writer that hands a built record to a store helper was in
  neither derivation).  None was a new class; each was the round-2 rule applied
  at one site and not swept onto its siblings, which is the failure mode this
  file already documents.

  The remedies are all the same shape — **derive the set, or name the shape
  rather than the resemblance**: every tracked `.rs` file that is not build
  output; the result type is what follows the first depth-zero `:`; and the
  frontier pairs a transitive side with a direct one on each disjunct.  That
  last is the point at which derivation stops being possible: chasing stores
  transitively makes every IPC composite a candidate, measured at 22, so the
  census states its frontier (`chainWriteFrontier`) in its own output instead of
  letting the number read as a proof of absence — the second-kind treatment this
  section already prescribes.  **A predicate over a domain you filtered is a
  measurement of the filter.**

  **And an exclusion's stated reason is a claim about its MEMBERS, re-measured or
  not** (`v0.35.120`).  `check_anchor_consistency.py` leaves an invocation it
  cannot reduce to one `(pattern, target)` out of the satisfiability comparison,
  with the reason written at the category: such an invocation *"pins a property of
  the composition rather than of a pattern, so it has no counterpart to
  contradict"*.  True of a pipeline.  But the *membership* test was not that
  relation — it was *the script inside a `bash -lc` is not one of two recognised
  **wrapper** forms*, a syntactic accident — so a bare `rg PATTERN FILE` that
  happens to be quoted through a shell landed in the bucket, and that is the form
  **every** bounded-gap anchor in this tree must take, the gap carrying a `\n`.
  Measured: **976 of 987** excluded invocations reduced to exactly one
  `(pattern, target)` and 11 were genuinely composed; the compared set was **4579**
  records where it is now **5573**, and the *negative* half **470** of **742**, so
  over a third of the tree's absence pins — the *must not come back* negatives a
  deletion's correctness rests on — were compared against nothing while the gate's
  PASS line read as coverage of the anchor set.  It failed silently by
  construction: an excluded member is never examined, so no count moved.

  Three things follow.  **Make the membership test the relation the reason names**,
  not a shape that usually implies it — the reduction is now the same one a bare
  argv gets, and `_is_composed` decides what a composition is, so the 11 keep an
  exclusion that is true of them.  **Re-measure a category's reason against its
  members when either changes**, because this bucket was correct when it held only
  the two wrapper forms and became wrong as the tree's anchor style moved.  And
  **state what the gate still cannot decide at the gate**: *two positives* over one
  subject are jointly satisfiable in the abstract — a file may hold two matching
  lines — and unsatisfiable only given a fact no scanner has (*this file declares
  that name once*), which is why `v0.35.118`'s defect is the changed-file sweep's
  question and not this one's.  One mechanical note, from this cut's own mutation
  set: the first anchor over the new fail-closed branch pinned its **condition and
  explanatory comment**, so a mutation keeping both and changing `unparsed` to
  `filtered` left it green — *a presence check is not a relation check*, inside an
  anchor written for the cut that closes one.

  **And a narrower resemblance is not a relation** (PR #895 review round 4,
  `v0.35.17`).  The fourth remedy in that list was *a generated component is the
  prefix plus a numeral*, and it is the one that did not hold: `eq_1` is as legal
  a definition name as `eq_clearReply`, so the rule narrowed the set of user
  names a contributor must avoid without making the test a fact about the
  declaration.  Round 4 found six more instances of the round-2/round-3 class, and
  five of the six are the *scanner's own default* rather than its predicate —
  which is this file's `a scanner's default branch is a decision` rule meeting its
  domain rule, since a default that silently answers is a domain written as an
  omission.  A missing metric read as `0`, so **deleting a measurement satisfied
  an enforced zero** (`check_store_reader_hygiene_monotonic.sh`: `SORRY_COUNT`,
  `AXIOM_COUNT` and `STORE_READ_CODE` all rode on it); `structure`/`class` bodies
  were spec whole, so an executable field **default** filed as specification (the
  remedy carried an over-approximation — a default ran to the end of its
  declaration — which that cut called harmless and `v0.35.18` had to retire: it
  filed a later field's *type* as executable, which is fail-strict, not
  harmless); a result-type parser that knew only `→` rejected the ASCII `->`
  that Lean equally accepts; inner rustdoc (`//!`, `/*!`, `#![doc]`) documents the *enclosing*
  module and justified the function below it; and `r#unsafe` — an identifier, not
  the keyword — failed a file outright.

  What closes the name half is not a sixth narrowing but the environment:
  `Meta.isMatcherCore` is pure, every `eq_N`/`proof_N` constant is `Prop`-typed
  and so excluded structurally, and with those two facts the whole name list is
  **redundant** — measured at zero definition-shaped, non-`Prop` writers kept only
  by a name test — so `isGeneratedComponent` was deleted rather than narrowed a
  third time.  **Where a resemblance keeps needing another exception, the
  question belongs to something that knows the answer.**

  **And a parser for a language you are not parsing is a list of the spellings
  you have seen** (PR #895 review round 5, `v0.35.18`).  Round 5 found seven more,
  three of them in code written hours earlier to fix round 4, whose findings were
  in code written to fix round 3.  The through-line is not any one of them: it is
  that `scripts/lean_store_read_census.py` decides two **structural** questions —
  which declaration owns a line, and whether that declaration is executable — by
  reading text.  Over three rounds it was taught seven legal Lean spellings it had
  not seen (a hypothesis binder, a `where` equation body, an ASCII arrow, a
  `structure` field default, a leading indentation, a defaulted binder, a
  per-field reset), which is this file's own regex rule arriving at a gate written
  after it.

  The exit is round 17's — *a Lean question goes to the Lean elaborator* — and the
  obstacle is that the classifier runs in **Tier 0**, before any build, because
  the `ZERO_METRICS` entry it produces is consumed there.  So the exit is taken at
  the tier that can take it: `SeLe4n/Testing/StoreReadClassificationCensus.lean`
  (Tier 1) asks `findDeclarationRanges?` which declaration owns each line and the
  conclusion of its type whether that declaration is specification, and fails the
  build wherever the classifier disagrees.  **And its domain is reconciled
  against the classifier's** (`v0.35.76`): the classifier scans the filesystem
  and the reconciliation reads the environment, and no `SeLe4n/Testing/` module
  was in that environment — invisible while the read census produced no row
  there, and exposed by the write census's first, the reply-stack census's
  planted witness, which the check counted as "outside any declaration" and
  moved on.  A row in a file the environment declares nothing in now fails the
  build naming the module to import (`orphanFiles`), because a declaration
  outside the import closure is indistinguishable from one that does not exist
  and a count of what could not be judged reads as a diagnostic.  Its first run
  named a **kernel** module, not a test one — `ChainFootprint`, outside both
  library roots since RR7.40 — which is how the five-modules finding recorded
  under *a surface outside every derived domain* above was made.  **Where the authoritative answer is
  out of reach at the tier that needs it, derive it at a tier that can and
  reconcile** — the *derive the set, keep the list as a pin* rule, one tier apart.

  Three things that cut records, each found by running the reconciliation rather
  than reading it.  Its first run reported **271** disagreements and every one was
  the *check* being wrong: `Meta.isProp` asks whether a declaration is a **proof**,
  and a predicate (`def p : SystemState → Prop`) is not one — a question
  `ReplyStackWriteCensus` had already answered as `isPredicate`, so asking it a
  second way was the one-question-two-answers shape inside the remedy for it.  Its
  second reported **5**, all hypothesis binders inside executable declarations,
  which a declaration-level verdict structurally *cannot* adjudicate — so the
  classifier reports the region and signature reads are counted, not judged.  And
  the enforced direction **cannot fire while `STORE_READ_CODE` is zero**: there is
  no misfiled executable read to find, so it carries synthetic witnesses, as
  `BootEntryContract` does for the same reason.  **A check that cannot fire on the
  current tree and carries no witness is indistinguishable from one that is
  wrong.**

  **And a reconciliation only closes the direction it judges** (PR #895 review
  round 6, `v0.35.19`).  Round 5 took the structural exit for the Lean
  classifier and wrote the caveat above; round 6 found **seven** more — six
  reported, one self-inflicted — and the useful result is *which* of them the
  round-5 mechanism already covered, because that is the measure of whether the
  exit was the right one.

  It covered one.  `opaque` was missing from the classifier's declaration
  keywords, so an executable `opaque` body following a `theorem` was attributed
  to the theorem and filed `SPEC`, past the enforced zero — and the elaborator
  reconciliation's mismatch message *already named that case* ("a Lean
  declaration form the classifier does not recognise"), because asking
  `findDeclarationRanges?` who owns a line is spelling-independent.  It could
  not fire only because no `opaque` body in the tree holds a read.  **A
  mechanism that would have caught a finding it never saw is the evidence that
  it is the right mechanism**, and the keyword was still added: Tier 0 is where
  the metric is read, and a gate that needs its sibling to notice every miss is
  a worse gate.

  It did **not** cover the other two, and each for a reason worth keeping.  A
  binder's *default value* was emitted in the signature region, which the
  reconciliation skips — correctly, since a declaration-level verdict cannot
  adjudicate a hypothesis binder.  But a default is not a hypothesis: it is
  elaborated and evaluated exactly when its declaration is, so it *is*
  adjudicable, and lumping the two into one region hid an executable read from
  both tiers at once.  **A region is a claim about what a verdict can decide;
  two constructs that differ in that are two regions.**  And a result type that
  is an *alias* of `Prop` was filed `CODE`, which the reconciliation also
  skipped — deliberately, on the reasoning that over-filing `CODE` cannot bypass
  a zero.  True, and it is not the only thing that matters: over-filing makes
  Tier 0 refuse valid specification text, and the tier that knows better was
  staying silent about it.  **Judge both directions: the safe direction is still
  a direction, and a wall with no explanation is a defect too.**

  Two more from the same round, on the Rust side, are the nesting and
  same-line rules one level down — a doc marker nested inside another comment
  publishes nothing, and a preceding *item* on the site's own line does not
  donate its documentation — and the second carries a distinction worth
  stating: the two site kinds ask different questions of that line.  A **block**
  is evaluated inside the statement it sits in, so a binding prefix is not
  something that executed in between; a **declaration** preceded by another item
  is a different item.  Applying one rule to both is wrong in whichever
  direction it is applied, measured: the strict rule over blocks fails 18 live
  sites.

  Finally, the round's own mechanical lesson, earned by nearly shipping a false
  green: **a mutation must revert the defect, not exchange one sound rule for
  another.**  The first mutation written against the same-line fix substituted
  the *block* rule for the *declaration* rule, and the fixture passed under it —
  not because the fixture was weak but because both rules reject that input.
  The mutation that decides is the pre-fix behaviour itself.

  **And a skip is a sink** (PR #895 review round 7, `v0.35.20`).  Round 5 sent
  the classifier's *verdict* to the elaborator and round 6 made that
  reconciliation judge both directions; neither touched the **region boundary**
  — where a declaration's signature ends and its body begins — which stayed a
  two-token regex, and whose failures all landed in `sig`, the one region the
  reconciliation deliberately does not judge.  So the parser's unknown-input
  behaviour drained into the bucket nothing checks.  Measured on the tree:
  Lean's direct equation syntax (`def f : A → B` followed by `| p => rhs`)
  carries neither `:=` nor `where`, so **4778 lines of body across 263
  declarations** were filed as signature — SPEC, unjudged, past an enforced
  zero, in the gate this PR spent four rounds hardening.

  **When a judged direction is split from an unjudged one, every parse failure
  migrates into the unjudged one.**  A skip is never neutral: it attracts
  exactly the defects the judge exists to find, and the size of what it
  attracted is invisible because the rows look ordinary.  Three things follow,
  and all three are now mechanism rather than advice.  Teach the boundary the
  form (a depth-zero clause bar, with `||`, `|||`, `|>.` and `<|>` excluded by
  shape rather than by a list).  **Refuse** what it still cannot close — every
  declaration form has a body except `opaque` and `axiom`, so an unterminated
  signature is a named Tier 0 failure instead of a silent SPEC filing, which is
  this file's *a scanner's default branch is a decision* applied to a region
  boundary.  And **report the residue the skip legitimately leaves**: the Tier 1
  census now counts signature rows sitting inside *executable* declarations —
  five, against the 4778 that were hiding there — so the population no
  declaration-level verdict can reach is a number rather than an implication.

  The round's other two findings are the same meta-shape one level up, and they
  are why this entry is about the class rather than the instances: **a fix
  landed where the review pointed and the question's other askers were left.**
  `CLAUDE.md` recorded *an item macro inside an `extern` block is refused, not
  read past* as implemented — true of `check_kernel_entry_exports.py`, and false
  of `check_unsafe_block_justifications.py`, which parses foreign blocks for the
  same items and scanned them for `fn` alone, so a macro declared an unsafe
  obligation no site, count or baseline could see.  And the reply-stack write
  census named the **frozen** table primitive (`FrozenMap.set`) while omitting
  the **live** one (`RHTable.insert`), so a definition that builds a `Reply` and
  writes `{ st with objects := st.objects.insert … }` — which is how
  `Lifecycle/Suspend.lean` writes a consumed Reply — was in neither derivation.
  That is round 1 of this same PR (*a spelling is not a read*) on the same two
  tables in the opposite direction, with the sweep unrun.

  Stating the sweep rule has now failed often enough to be the finding.  **Give
  it an artefact: derive both answers from one place, or make the second
  implementation impossible.**  The foreign-block walk — ABI-literal resolution,
  brace matching, the item split, and the classification `fn` / `macro` /
  `non-fn` / `unknown` — is `rust_code_view.extern_blocks` /
  `extern_block_items` / `classify_extern_item`, read by both gates, so one
  mutation now fails both self-tests; only what an item *means* stays per gate
  (a linker symbol there, an unsafe obligation here).  The store frontier names
  the two table **primitives** and keeps the wrapper helpers as a *pin* each of
  which must itself reach a primitive — and that pin found two more defects on
  its first run: a fourth entry (`SystemState.storeObject`) that names no
  declaration at all, and a live helper (`storeObjectChecked`) the list had
  never mentioned.  A list nothing reconciles is a list nobody reads.  **And a
  pin's reach is a relation too** (`v0.35.66`): the frontier recognises a store
  one hop from a pinned name, so a helper *over* a pinned helper sits two hops
  out — `refillSchedContext`'s `updateSchedContext` over `rewriteObject` over
  the insert — and the census reported its exemption as stale the moment the
  definition migrated.  The `v0.35.64` cut had met the same report for
  `suspendThread` and deleted the entry, which is the fail-open direction (a
  writer setting `scReply` through the unpinned helper would have been
  invisible); the rewrite family is pinned now and the entry is back.

  The sweep was then **run**, not just written down, and its value is the two
  sites it left alone.  `check_ipc_invariant_dethreading.py` has its own Lean
  `signature_end`, and its fall-through is already a stated decision — with no
  `:=` the signature runs to the next declaration, which over-captures and can
  only make the gate stricter — so it is the sink's opposite and correct as it
  stands.  `build.rs`'s `blank_extern_blocks` is a Rust twin that *blanks* a
  block rather than enumerating its items, so the macro question does not arise
  there, and it already shares the ABI-literal resolution.  A sweep that changes
  nothing at a site is the sweep working; a sweep not run is how all three of
  this round's findings got here.

  **And a conjunct whose antecedent is the property you want enforces nothing**
  (PR #895 review round 8, `v0.35.21`).  This round's sharpest finding is not in
  a scanner at all — it is in the kernel, and it is the invariant-level form of
  *a presence check is not a relation check*.  `passiveServerIdle` reads "an
  unbound thread that is **not queued and not current** is in one of these
  `ipcState`s".  The property the tree wants at a donation pop is *an unbound
  thread is not queued*, and that is precisely the conjunct's own **hypothesis**
  — so a thread left `.unbound` **and still runnable** satisfies it vacuously,
  and every bundle theorem over it stays true while the defect is live.

  The defect it hid: `replyRecvPostReceiveDonation`'s Call arm donates the newly
  dequeued client's context to the **receiver** `tid` and descheduled nobody,
  which is right exactly when `tid` *is* the recorded server — the non-delegated
  steady state — and wrong on a **delegated** reply, where the recorded server
  gave its context back in the pop and receives none.  It then stays on its run
  queue and is selected at its legacy TCB priority charged to no reservation,
  which is WS-OD OD3.6's defect on the path OD3.5 had just made live.  The arm's
  own comment names the distinction two lines above the bug (*"not the (possibly
  delegated) recorded server"*) and its justification sentence ignores it, so:
  **a justification that holds on one side of a distinction the code already
  makes is not a justification — say which side, or make the code not care.**
  `replyRecvServerDeschedule` is the named answer, with the write set, the
  confinement and both bundle proofs carrying it (renamed
  `replyRecvHolderDeschedule` at `v0.35.149`, when its argument stopped being the
  recorded server), and the witness pair in
  `tests/SmpIpcSuite.lean` §3.9b is delegated *and* non-delegated, because a
  deschedule that fires unconditionally passes the first and breaks the second.

  The round's three gate findings are all rules this file already carries, each
  unswept by exactly one step.  `#+\s*Safety` accepts `/// #Safety`, which
  CommonMark renders as a paragraph — the gate whose whole subject is *what a
  caller is told* accepting text that tells the caller nothing.  The upward
  justification walk decided a multi-line `#[cfg(all( … ))]` one physical line at
  a time and stopped at its `))]`, which is *a nested construct is not a sibling*
  applied to Lean and never to Rust attributes; the remedy consumes the closer's
  pending run and requires the balancing line to open an attribute, because a
  multi-line *expression* ending in `]` is code and extending a run across it is
  the fail-open direction.  And `\bextern\b` matches inside `r#extern`, so
  `mod r#extern { … }` parsed as a foreign block — the `r#` exclusion sitting on
  `UNSAFE_KEYWORD` eight lines away in the file this scanner was *moved out of*,
  one round earlier.

  That last one is the measurement worth keeping.  Round 7's remedy was **give
  the sweep an artefact** — two gates consolidated onto one shared view so a
  single mutation fails both.  It worked, and it did not stop the very cut that
  performed the consolidation from writing a fresh regex missing a rule the same
  file states.  **Sharing the answer stops two answers from diverging; it does
  not make a new answer inherit what the old one learned.**  When you move a
  scanner, carry its neighbours' exclusions with it — or, better, reach for the
  existing pattern instead of writing one that looks like it.

  Two mechanical notes.  A census whose headline is one derivation while its
  breakdown is another describes no set: the reply-stack summary counted
  `derived.length` beside disciplines counted over the registry, so the figures
  stopped adding up the moment a site entered through the second frontier, and
  the closure `stating + mirrors + halfSteps = registry` is asserted now.  And a
  registry cannot name a `private def` with a name literal — Lean mangles one to
  `_private.<Module>.0.<name>` and a numeric component is not an identifier — so
  the entry is built with Lean's own `mkPrivateNameCore` rather than with a
  resemblance to it.


  **And a rule stated is not a rule enforced — give it a check, not a third
  telling** (PR #895 review round 9, `v0.35.22`; a rule about *code* — checks
  are for code, not documentation).  Round 8 closed with *sharing
  an answer stops two answers from diverging; it does not make a new answer
  inherit what the old one learned*, and recorded it in this file.  Round 9 found
  **six more** bare keyword spellings in the very file whose one correct pattern
  carries the rule, ten lines below the comment explaining it.  Measured:
  `check_unsafe_block_justifications.py` held **seven** `\bunsafe` regex literals
  and exactly one had the raw-identifier exclusion, so `struct r#unsafe { … }`
  read as an unsafe block and Tier 0 demanded a justification of safe Rust.

  That is this file's own enumeration-versus-derivation rule at the level of a
  **regex fragment**, and the two previous remedies could not reach it: fixing a
  site does not reach the site nobody has written yet, and consolidating a *walk*
  does not constrain a *new pattern* written beside it.  Writing the lesson down
  a third time would have been the move that had already failed twice.

  **So the remedy is a mechanism.**  `rust_code_view.keyword(word)` is the one
  fragment every keyword pattern composes, and `bare_keyword_literals()` reads
  the gate sources and refuses any bare word-boundary keyword spelling written
  outside it, wired into the view's self-test.  The next such pattern fails on
  the day it is written.  Two things make it honest: it reads **code, not
  prose** — `python_code_view` blanks `#` comments and, via `ast`, docstrings,
  because `keyword`'s own docstring quotes the bad spelling in order to explain
  it and a check that counted it would force the file to stop explaining itself
  — and it is mutation-tested in all three directions, since a discipline check
  that cannot fire is indistinguishable from one that is wrong.  **When a rule
  has been restated twice, the third response is not prose.**

  Two corollaries this round paid for.  **An inert witness reads as coverage
  while asserting nothing**: the first case written for the unsafe-attribute
  classification was a *site* case, and a file whose only `unsafe` is an
  attribute produces no sites, so it passed vacuously with the fix reverted —
  the mutation harness caught it by **not** failing, and the witness moved to the
  scan the fix actually lives on.  And **a fix can reopen a closed finding**: the
  new doc-attribute scan was first written `#!?\[`, accepting the *inner*
  `#![doc]` form, which is round 4's *inner rustdoc documents the enclosing
  module* — round 4's own witness failed immediately, which is what witnesses are
  for.

  The round's other three findings are each a question this file already answers,
  asked of the wrong artefact.  Rust 2024's `#[unsafe(no_mangle)]` is the only
  spelling a 2024 crate may use for those attributes and matched no known form,
  so the explicit default branch failed the whole file — classified now, with
  **no** per-site obligation, because it attaches to an item and asserts
  something about the linker namespace that two other gates already enforce.  A
  `///` attaches to the item that *follows*, so the comment after a scope opener
  documents the first item inside it; the run takes the trailing portion after
  the last code character, which is the other side of round 6's rule rather than
  a widening of it, since that one was documentation sitting *before* an
  intervening item.  And `#[doc = r"…\n# Safety"]` is a **raw** literal whose
  `\n` is two characters, so rustdoc publishes no heading: two rounds had
  narrowed that regex and the question itself was wrong, so the value is
  **decoded** by its literal kind and a real line-start question asked of the
  result — *a spelling is not the text*, which is *a spelling is not a read* one
  artefact over.


  **And when two rounds' findings land in each other's fixes, the fix's SHAPE is
  the defect** (PR #895 review round 10, `v0.35.23`).  Round 9 closed with *a
  rule stated is not a rule enforced — give it a check, not a third telling*, and
  built one.  Round 10 then found five more, **two of them inside round 9's own
  fixes**, and the useful reading is not the instances: it is that both were the
  same *kind* of mistake, made at the point where a fix chooses what to trust.

  **A proxy is not the fact, at the scheduler.**  `replyRecvServerDeschedule`
  (`replyRecvHolderDeschedule` since `v0.35.149`)
  accepted the core its caller had already computed — `determineExecutingCore`,
  which finds a core the thread is *current* on and otherwise answers
  `bootCoreId`.  A **queued** server matches nothing there, so the deschedule
  edited the boot core's queue while the server sat on another and the
  temporal-isolation defect the step exists to close survived on the preempted
  path.  `determineTargetCore` is no better and the measurement says why:
  `affinityAdmitsCore` is `true` on *every* core for an unpinned thread, so
  `runQueueAffinityConsistentOnCore` does not pin one to that answer either.
  Both are proxies; the fact is **placement**, and `removeRunnableOnCore` writes
  the run queue *and* the current slot of whatever core it is handed.
  `placedCoreOf?` is the witness, tied to `runnableOnSomeCore ||
  runningOnSomeCore` by theorem so a third answer cannot appear.  The sites
  round 10 named and did not sweep — the cancellation path's `descheduleThread`
  and `cancelIpcBlockingOnCore` — and a third the sweep found, the live
  suspend's own home-then-running-core removal pair, closed at WS-RR RR8.6
  (`v0.35.79`); the standing constraint is recorded below.

  Two things generalise.  **A parameter is a place for a caller to be wrong**:
  the fix is not a better argument at the call site but *no argument* — the step
  resolves its own core, and its footprint reads the same call, so the transition
  and the declaration cannot name different cores.  And **a witness that supplies
  the answer tests the fixture, not the code**: §3.9b passed `serverCore` by hand
  and so asserted nothing about the resolver production actually used, which is
  why a green suite sat over a live defect for a whole cut.  With the parameter
  gone there is nothing left to supply.  Ask of any witness: *could this have
  failed if the production path computed its input differently?*

  **And the view you read depends on the question** — the same rule this file
  states for Lean structure, arriving at a gate that had deliberately chosen raw
  text.  The justification run is raw because what matters is what a reviewer
  reads, and that is right for *reading* a comment and wrong for *deciding
  whether something is one*: an ordinary `// #[doc = "# Safety"]` was decoded as a
  real attribute and a `"// SAFETY: …"` inside `#[allow(reason = …)]` counted as
  a real comment.  Both fail open.  Comment spans are now *derived from the code
  view* rather than re-lexed — a maximal run of blanked bytes holding a byte the
  raw text did not blank **is** a comment — because a second Rust lexer is this
  file's one-question-two-answers hazard.

  Two more corollaries about witnesses, both earned rather than reasoned.  **A
  fix whose revert breaks nothing is indistinguishable from no fix**: the domain
  correction here was first shipped with no witness at all, and the mutation
  harness caught it by reporting `MISSED` — the case lists could not reach it,
  because the function reads the real workspace, so it needed a synthetic tree.
  And **bounding a negative is not automatically safe**: the two Tier 3 anchors
  on the deschedule were mutation-tested in both directions, silent on the clean
  tree and firing on a mutation that keeps every token and moves the pre-fix
  spelling back inside the declaration.

  **And a witness drawn from a finding tests the finding** (PR #895 review round
  11, `v0.35.24`).  Round 10's reading was that a fix's *shape* is the defect
  when two rounds land in each other's fixes; round 11 makes it three, with
  three of its four findings inside round 10's own code, and names where the
  shape comes from.  Every case list in these gates had been grown the same way:
  a round reports a spelling, the fix adds a witness for **that spelling** plus a
  control, and the next round supplies one nobody enumerated — a raw doc
  literal, a `#[unsafe(…)]` attribute, a scope opener, a `*`-decorated block
  comment, attribute-shaped text inside a string.  That is this file's own *a
  recognised set is not a derived set*, applied to a gate's **test cases** rather
  than to its input, and it fails the same way: silently, because the cases that
  exist all pass.

  **So enumerate the space instead of the findings.**  The remedy already existed
  one file over — `per_core_state_matrix` pins the lock by classifying every
  entry point in every per-core state — and it is a *matrix*, not a list: every
  marker FORM crossed with every ENCLOSURE, with the verdict a property of the
  enclosure alone (a real comment justifies; a literal or a commented-out
  spelling never does).  A spelling the gate has not considered is then a missing
  **row** — visible, and addable without waiting for a review round to supply
  it.  Its first run on `check_unsafe_block_justifications.py` found **five**
  defects no round had reported: one fail-closed (an undecorated `/*\nSAFETY: …*/`
  refused), and four fail-open — a `/**` inside a line comment, inside a string,
  or nested in another block comment each publishing a `# Safety` section; a
  `///` heading at the start of a line *inside a string literal* satisfying the
  line-anchored scan; and `UnterminatedLiteral` in no handler, so a file the
  shared lexer cannot finish reached the operator as a traceback rather than as
  the refusal the gate's own "one failure channel" claims.

  Three things fall out of running it.  **Keep the tables symmetric**: the
  declaration side omitted the plain string-literal enclosure the block side had
  carried since round 10, and that asymmetry is what hid the `///` cell — the
  same defect one level up, inside the matrix meant to close it.  **A
  declaration-bounded negative is a statement about that declaration**: round
  10's Tier 3 anchor was scoped to `replyRecvServerDeschedule`
  (`replyRecvHolderDeschedule` since `v0.35.149`) while the relation
  is about *every* deschedule of the thread the pop unbound, so the sibling arm
  twenty-five lines away kept the retired spelling and the anchor's silence read
  as coverage.  And **a harness that re-spells the gate's own decision absorbs
  the defect it is there to find**: the refusal handler was written out three
  times, `UnterminatedLiteral` was missing from two of them, and the self-test's
  private copy caught what the scanner would have crashed on — one `REFUSALS`
  constant now, which is also what makes dropping a member *detectable*.

  **And a matrix enumerates the dimensions you thought of** (PR #895 review
  round 12, `v0.35.25`).  Round 11's remedy was to stop drawing witnesses from
  findings and enumerate the space instead — every marker FORM crossed with
  every ENCLOSURE.  Round 12 then found three more in the same gate, and the
  useful reading is *where* they landed: not in a cell, but **off the grid**.  A
  `# Safety` inside a fenced code block is a markdown enclosure; `#/* c */[doc
  = …]` is a token-separation form; `pub unsafe fn λ()` is a *name* form, a
  dimension of the site scanner the justification matrix does not reach at all.
  The matrix worked exactly as designed — each is now a row — and the lesson is
  that its **axes** were themselves a recognised set.

  **So take the axes from the artefact's grammar, not from the findings.**  The
  question a gate asks has a small number of dimensions, and they are readable
  off the language rather than off a review: for a doc comment they are *which
  marker*, *what encloses it lexically*, *what encloses it in the rendered
  markup*, and *how the item is named*.  Each round-12 finding added an axis and
  then all of its values at once, which is why one cut closed six defects
  including two the review did not report.

  **And when the property is about the whole artefact, build the artefact.**
  That is the sharper half.  A fence is a property of the *rendered document*,
  and three separate line-oriented patterns — a `///` scan, a doc-block scan, a
  decoded-attribute scan — structurally could not see it, however many spellings
  each one learned.  rustdoc concatenates every doc source on an item into one
  markdown input, so `rendered_doc_markdown` now does too and
  `publishes_safety_heading` asks the single question of it.  Three patterns
  became one, a cross-form fence (opened in a `///`, closing after a `#[doc]`)
  became answerable at all, and every rule about which markers attach to the
  item moved to the one place that builds the document.  **Reconstructing what
  the real tool consumes is not a bigger scanner; it is the end of a class of
  scanner defect** — and it is the same payoff shape as round 7's *give the
  sweep an artefact*, one level up.

  Two corollaries this round paid for.  **A field name is not a receiver
  type**: the store census matched `.objects[…]?` by spelling, so an executable
  definition over any other type with an `objects` field was counted as a
  kernel-state read and refused by an enforced zero.  Resolving the receiver is
  an elaborator question and this gate runs before any build, so the *ambiguity*
  is bounded instead — `OBJECTS_FIELD_OWNERS` is derived from the sources and
  reconciled both ways, making a new owner a **named** Tier 0 failure rather
  than a mystery rejection.  Running that derivation found six owners where the
  first guess named four, one of them (`BootstrapBuilder.objects : List`)
  already indexable: the ambiguity was live, not hypothetical.  And **a name is
  not a definition, in Lean too**: `Prop`-alias resolution accepted any alias
  with the same final component, so `B.Pred := Nat` read as specification
  because some other namespace declared a `Pred := Prop`.  Aliases carry
  qualified identities now and resolve against the use site's enclosing
  namespaces, longest prefix first — which is what the elaborator does, and the
  third case in its witness set is the one that stops the fix from degrading
  into *a bare alias never resolves*, since refusing valid specification text is
  a defect in its own right.

  Finally, the round's own mechanical lesson, and the second time this PR has
  paid for it: **an inline mutation with no assertion is an inert mutation.**
  Two of this round's mutation checks reported the fix as unverified and one
  reported it as verified when the edit had silently matched nothing — the
  difference being a `assert s.count(old) == 1` the throwaway script omitted.
  The harness asserts it; a one-off mutation run by hand must too.  And **a
  mutation must revert the whole defect**: the alias fix has two halves, and
  reverting either alone left a witness passing, while reverting both — the
  actual pre-fix state — failed immediately.

  **And a mirror of a part is not a mirror of the whole — sharing an
  implementation transfers its preconditions** (PR #895 review round 13,
  `v0.35.26`).  Round 12 said *when the property is about the whole artefact,
  build the artefact*, and meant a rendered document.  Round 13 is that rule
  meeting three different units, two of its three findings inside round 12's own
  fixes — the fourth consecutive round where findings land in the previous
  round's code.

  The one worth keeping is not a scanner.  `Reply.consumed` keeps a stack head's
  links, and its docstring says why in terms: *the pop that follows clears
  them*.  That sentence is a **precondition on the caller**, not a description —
  and `FrozenOps` adopted the record without it.  Sharing `consumed` between the
  live and frozen surfaces was *right*, by this file's own one-question-one-answer
  rule; what the sharing also moved, invisibly, was an obligation the frozen
  surface could not discharge, because it models no donation pop.  So a frozen
  state captured mid-chain left the answered Reply failing `Reply.isFree`
  forever: never re-linkable, never retypeable, and no passive server could
  complete a second call/reply cycle on it.  **When you reach for a shared
  answer, read what it requires of you, not only what it returns** — a function
  whose correctness depends on what runs *after* it is a contract, and adopting
  it is accepting that contract.

  Where the fix goes carries the second half.  `frozenEndpointReply` is refined
  against the **bare** `endpointReply`, which also leaves a head linked, and the
  differential scenario compares exactly that — so putting the pop inside it
  would have broken the refinement the surface exists to check, while fixing the
  symptom.  The frozen `.reply` *operation* is the reply leg **then** the
  donation return, as the live one is, so the composite is where the pop belongs
  and the refined mirror is left alone.  **Ask which unit the property is about
  before choosing where to fix it**: the leg refines, the operation composes, and
  a fix at the wrong level trades a visible defect for an invisible one.

  The two scanner findings are the same rule at smaller units, and both are the
  *unit* being smaller than the property.  A binder-default scan asked its
  question of the enclosing group's whole span, so a `let` in a nested group that
  had already closed suppressed a real default — filing an executable read as
  `SPEC region=sig`, the one region the Tier 1 reconciliation does not judge, so
  it bypassed **both** tiers rather than one; the span is walked at depth now,
  through the depth-zero walk every other top-level-token question in that file
  already used.  And the markdown enclosure axis round 12 created had one value —
  fenced code — where CommonMark's grammar has several: **HTML blocks hold raw
  text**, so a `# Safety` heading inside `<!-- ... -->` published nothing and
  satisfied the gate.  The axis is taken from the grammar rather than from the
  reported spelling: all seven block types, both end conditions, an unterminated
  block running to the end of the document, and type 7's inability to interrupt a
  paragraph.  **A new axis is enumerated at all of its values on the day it is
  added**, or the next round supplies the ones that were skipped.

  One mechanical note, and it is the *witness* rule again rather than a new one:
  each hidden matrix row is paired with a control that ends the enclosure, so the
  row is known to fail on the enclosure and not on the marker; and the census
  case for the binder fix is decisive only because round 12's own case keeps
  passing under the mutation — a fix that narrows a rule must be shown to narrow
  it rather than to disable it.

  **And six rules did not close this class, which is itself the finding**
  (PR #895 review round 14, `v0.35.27`).  Rounds 9 through 14 each added a rule
  to this section — *give it a check not a third telling*, *a witness drawn from
  a finding tests the finding*, *take the axes from the grammar*, *build the
  artefact*, *sharing an implementation transfers its preconditions* — and each
  round after it found more.  Do not read that as six failures of nerve; read
  the **distribution**.  Every one of those six rounds found at least one defect
  in `check_unsafe_block_justifications.py` or its shared view, and rounds 10,
  11, 13 and 14 each found one in the frozen surface.  Two artefacts, six
  rounds.  The rules were locally right and structurally beside the point.

  **Cause one: a gate that hand-implements a language front-end will be fed a
  construct it has not seen, forever.**  Those two files are 3,591 lines
  implementing Rust lexing, Rust item parsing and CommonMark; the store census
  implements Lean declaration parsing.  This is round 16's own observation —
  *the set of valid spellings that defeats a regex is unbounded while the set a
  gate has seen is finite* — arriving at the level of the whole gate rather than
  of one pattern.  The exit is round 17's, and it was taken **once**: the Lean
  classifier's verdict is reconciled against `findDeclarationRanges?` at Tier 1,
  and round 6 then confirmed the mechanism by finding it would have caught a
  defect it never saw.  It was never generalised, and the generalisation is not
  subtle: **Rust's front-end is `rustc`, and the `# Safety` question's front-end
  is `rustdoc`** — the tool whose output the property is defined by.  Round 12
  wrote *build the artefact* and then hand-rolled a markdown renderer instead of
  asking the renderer.

  **Cause two: a hand-written second implementation whose fidelity is checked by
  a hand-written list.**  `FrozenOps` mirrors live transitions and
  `frozenRunAgrees` would catch a divergence, but which pairs are driven through
  both sides is a handful of scenarios and the pairing itself is a Markdown
  table.  Rounds 10, 11, 13 and 14 are one shape — a *part* of a live operation
  reproduced with a step omitted that the live code pairs with it — and 13 and
  14 are the same defect twice, the second inside the first's fix.  That is this
  section's own strongest rule (*one question answered in two places will
  diverge*) meeting the artefact deliberately built to be two places.

  **And that artefact is not a test double** (the maintainer's correction,
  `v0.35.102`).  `FrozenOps` is the *execute* phase of this project's
  build → freeze → execute architecture: `Model.freeze` takes the **builder**'s
  `IntermediateState` to a `FrozenSystemState`, and `Platform/Boot.lean`'s
  `bootToRuntime_invariantBridge_empty` — *boot to runtime* — carries the
  invariant bundle across the freeze into `apiInvariantBundle_frozen`, which is
  a bridge worth proving only if the runtime is meant to run on the frozen
  representation.  What is missing is the dispatch: `API.lean` contains no
  occurrence of `FrozenOps`, `kernelStateRef` holds a `SystemState`, the boot
  installs `ist.state` rather than `freeze ist`, and `Model.freeze` has no
  executable caller anywhere under `SeLe4n/` — every occurrence in `Boot.lean`
  is inside a theorem statement.  So the duplication is an **interim**, the
  differential is the evidence that would license ending it, and every
  divergence found is a *deferred kernel defect* rather than a model one.
  Calling it a second implementation *kept so the live one can be compared
  against it* names the interim method and not the purpose, which reads the
  severity down; the register row says so since `v0.35.102`, and C.1 row 14 —
  the dispatch switch — gated on *benchmarks* and named no correctness gate at
  all, so the two preconditions lived in neither row.

  **What changed, and what did not.**  Both causes are now rows in
  `docs/REGISTERED_DEBT.md` table C with closure targets before v1.0.0, because
  the remedies are a reconciliation against the real tools and a derived
  differential coverage set — work, not wording.  What this cut *does* do is
  narrow cause two at its own site: a frozen mirror names the live function that
  **completes** a step (`frozenApplyReplyDonation` pairs the donation return with
  the deschedule) rather than the one nested inside it, so the pairing is
  structural.  **When a rule has been restated six times, stop restating it and
  write down what the restating measured.**

  **And a claim made at the wrong UNIT is a claim about something else** (PR #895
  review round 15, `v0.35.28`).  Round 13 said *ask which unit the property is
  about* and applied it to where a fix goes.  Round 15 is the same question asked
  of where a *verdict* is taken, in two artefacts that share nothing else, and
  the two together are why this is a class rather than two bugs.

  A Setext heading's content is the **whole** preceding paragraph (CommonMark
  4.3), and the round-14 check read the line directly above the underline — so
  `/// This is not a contract`, `/// Safety`, `/// ===` satisfied a gate whose
  subject is what a caller is told, while rustdoc titles that heading "This is
  not a contract Safety".  Fail-open, on the gate with an empty baseline.  And
  the frozen surface's differential coverage table said `.reply` was checked
  against `endpointReply` — the **bare** reply, a *leg*.  The live `.reply`
  *operation* is that leg plus the donation return plus a priority-inheritance
  revert, and nothing compared the frozen composite against it, so "reply:
  checked" stood through **four consecutive review rounds** in which that
  composite was found to be missing the donation pop, then the server's
  deschedule, then the inheritance revert, then a missing-server refusal.
  (Round 22 corrected the *counterpart* this round chose: the leg differential
  runs against `endpointReplyOnCore` and the operation one against
  `endpointReplyCrossCoreDispatch`, both read out of `frozenBranchLiveLeg` /
  `frozenBranchLiveOperation` rather than named in a comment.  Do not cite this
  paragraph for either name.)  In
  both cases the check ran, reported truthfully about the unit it examined, and
  that unit was not the one the claim was read as being about.

  **So name the unit in the claim, and make the smaller claim unable to stand in
  for the larger.**  The heading verdict is taken from the paragraph's first
  line, where its content begins.  The coverage table gained a second, separate
  claim (`frozenBranchOperationChecked`) with its own scenario list reconciled in
  both directions, three `decide` interlocks, and — the load-bearing part — a
  *stated reason* on every branch that has only a leg check, so the next step
  composed onto a live operation is a row somebody has to write.  Merging the two
  lists would have re-created the defect inside its own remedy.

  Two corollaries, both earned.  **A new unit changes which leaf blocks matter**:
  carrying the paragraph's first line means a thematic break and an ATX heading
  must now end the paragraph, one in each direction — the break so `Safety` /
  `***` / `===` is refused, the heading so `# Overview` / `Safety` / `===` is
  *accepted* — and each needs its own mutation, since a case that survives the
  pre-fix code tests nothing.  And **a mechanism worth building finds something
  on its first run**: the operation-level differential immediately failed, on a
  bug in the same cut's own fix — `frozenUpdatePipBoost` looked for the thread in
  the bucket its *old effective priority* names, where the live `updatePipBoost`
  asks whether the thread is in the queue at all and removes it from wherever it
  is.  The divergence is visible only on a state where a thread's bucket and its
  effective priority have already drifted apart, which is precisely the state a
  reversion exists to repair.  A mechanism that passes everything on the day it
  lands has not yet been shown to measure anything.

  **And when a real front-end exists, the scanner is not the authority — hand it
  the question** (the maintainer's instruction, `v0.35.28`).  The rule above
  fixes a verdict taken at the wrong unit; this one retires the artefact that
  kept taking them.  Round 14 registered the generalisation as debt and round
  15's P1 was the **seventh consecutive round** to find a defect in the same
  hand-written front-end, which is the measurement that registering it again was
  not the move.

  *The `unsafe` question's front-end is rustc; the `# Safety` question's is
  rustdoc.*  `sele4n-hal` and `sele4n-abi` deny
  `clippy::undocumented_unsafe_blocks` and `clippy::missing_safety_doc` at their
  crate roots.  The first is rustc's own parse of the block and of the comment
  run above it — no `//` versus `/*` versus `r#unsafe` versus attribute-nesting
  question can be got wrong, because there is no second parser to get it wrong
  in.  The second renders the item's documentation with the parser rustdoc uses,
  so fences, HTML blocks, Setext underlines and raw doc literals — four of the
  last seven rounds' findings — are decided by the tool whose output the caller
  actually reads.

  **Two things about turning a lint on were established by mutation, and either
  would have shipped a false green.**  `cargo clippy -- -W <lint>` reaches only
  the final compilation unit and is **silent** for every workspace member: the
  first run reported zero findings and deleting a real `// SAFETY:` comment
  still reported zero.  And the host lane cannot see the
  `#[cfg(target_arch = "aarch64")]` majority of a HAL: the same deletion yields
  **0** findings on the host and **2** on `aarch64-unknown-none`.  *A lint that
  is not running is indistinguishable from a lint that passes*, which is this
  file's inert-witness rule arriving at a tool nobody thinks to test.  Delete a
  real justification and watch the lane you rely on fail before believing it.

  **The scanner stays, and says what it now owns.**  Tier 0 runs before any
  build, so the fast approximation is still worth having; and three things
  structurally escape the lints — a non-`pub` `unsafe fn`, an `unsafe fn`
  declared inside an `extern` block (no lint requires a contract of a *foreign*
  declaration, and this tree has ten Lean upcalls that need one), and the ARM ARM
  citation census.  Its output prints its authority and its residue beside its
  ratio, because a number that implies an authority it does not have is the
  defect this section keeps recording.

  **And the same instruction applied inwards: a mirror must not re-answer a
  question that has a live answer.**  The round-15 frozen fix added five
  hand-written counterparts of live functions, which is more of the duplication
  that produced the churn.  Two were pure questions about a `TCB` record — and
  the frozen store holds the **live** `TCB` — so they are the live accessors
  now: `TCB.boostedPriority` and `TCB.blockingServer?`
  (`Model/Object/Types.lean`).  Under them sits `Priority.raisedBy`
  (`Prelude.lean`), "a base raised by an inherited boost", which was written
  inline at **eleven** sites across the scheduler, the IPC wake path, the
  priority-setting path and the frozen run queue.  Its base is a **parameter**
  because it is not always the thread's own: a `.bound` thread's base is its
  reservation's.  Fixing it at the TCB would have covered ten of eleven and left
  the eleventh spelling its own `match` — *an abstraction that does not fit its
  subject is how a duplicate survives a de-duplication.*

  Three things that cut records.  **An accessor ships with its frame**:
  `TCB.blockingServer?_congr` and `TCB.boostedPriority_congr` say which fields
  each reads, because a consumer that instead unfolds the accessor inside a
  `filterMap` also rewrites the tail's *bound* occurrences and desynchronises the
  induction hypothesis — a hazard one proof in `Compute.lean` had already
  documented one level up, and which reappeared the moment the accessor was
  introduced.  **A pin is not a substitute for an upstream answer, and a pin whose subject is
  gone is deleted, not kept**: `effectiveRunQueuePriority` and
  `ipcEffectiveRunQueuePriority` were two bodies because importing the scheduler
  from the IPC module would close an import cycle, held together by a `rfl`
  obligation stated in the first module that sees both names.  That pin is
  exactly what this project prescribes when a second implementation must exist —
  and it need not have existed, because the shared answer belongs in the
  **model**, upstream of both, where the cycle objection never applied.  *Look
  for the upstream home before reaching for the pin.*  Both names are now gone
  and every site calls `TCB.boostedPriority`; the pin went with them, because
  once one side is deleted it has no subject, and a theorem that can only be
  `rfl` asserts nothing while reading like a check — this file's own
  inert-witness defect, arriving as the *residue of a de-duplication*.  A pin is
  worth exactly the divergence it can still see.  And
  **the de-duplication's own grep missed a copy**: `effectiveBucketPriority`
  binds its base with a `let`, so a search for `Nat.max tcb.priority.val` did not
  see it; it surfaced only when a proof stopped closing.

  **And a fix retires more than it changes — sweep what was PINNING the thing
  you deleted** (PR #895 review round 16, `v0.35.29`).  Three findings, and the
  honest reading of them is that two were rules already in this file applied at
  one site and not at its sibling: `classify_extern_item` decided a foreign
  item's kind by *searching its interior*, which is round 15's wrong-unit rule
  one artefact over (the question is what the item **starts** with, so
  `decl!(#[doc = "…"] fn fake());` read as a plain `fn` and the macro was
  consumed rather than refused); and `lean_store_read_census.py` classified over
  raw bytes while its own `_SIGNATURE_END` comment asserted the view had blanked
  strings, which is *gates read code, prose reads prose* — the shared overlay
  keeps string contents **deliberately**, because a Tier 3 anchor may be about
  what an `asm!` template puts in the symbol table, and this census's question
  needs them gone.  The third is round 13's *a new axis is enumerated at all of
  its values*: the fence axis knew that a fence hides a heading and not
  CommonMark 4.5's rule that a **backtick** fence's info string may hold no
  backtick, so ```` ```rust`x ```` opened a fence that does not exist.

  The one worth writing down is the fourth, which no review reported and which
  the first fix *created*.  Replacing the interior search retired
  `_EXTERN_FN_ITEM`, `_MACRO_INVOCATION` and `_EXTERN_NON_FN_ITEM` — and a Tier
  3 anchor named the third, so it went on reporting PASS over a definition the
  classifier no longer consulted.  **A pin on a dead symbol is a tautology**: it
  says nothing about the live code while reading in the report exactly like a
  check that decides something.  And the way one is made is not by writing a bad
  anchor — the anchor was correct when written — but by **deleting the thing it
  watched**.  So a fix's blast radius includes the artefacts that watch what it
  changed, and those fail *silently by construction*, since reporting PASS is
  their ordinary output.  When a cut retires a definition, sweep every anchor,
  baseline, registry and census that names it.

  Two mechanical consequences.  The anchor is repointed at the symbol's **read**
  rather than its definition, because a pin on a definition is a presence check
  even when the symbol is live — the set can be defined here and consulted
  nowhere, which is the same tautology one step later.  And, this being the
  second tautological pin this PR has been shown, the response is the round-9
  one rather than a third telling: `scripts/check_anchor_symbol_liveness.py`
  (Tier 0) refuses any Tier 3 anchor naming a Python symbol its target binds and
  the tracked tree never reads.  Its domain is derived on both sides, a target
  that is missing or unparseable **fails** rather than being skipped, and its
  decisive case keeps the anchor and the definition and adds only a reader.


  And the same reading applied to the fix itself: `_skip_item_prelude` first
  re-derived the `[` position from a raw regex match and carried its own
  bracket-matching loop, while `attribute_opens_at` already answered the first
  and `attribute_spans` already inlined the second.  Both are one answer now,
  and the payoff is measured rather than asserted — one token-preserving
  mutation of `_matching_square` fails the self-tests of `rust_code_view`,
  `check_unsafe_block_justifications.py` **and** `check_kernel_entry_exports.py`.
  *Before writing a helper, find the one this tree already has.*

  Finally, the evidence for preferring a sweep to a count.  `v0.35.28` recorded
  `Priority.raisedBy` as collapsing **eleven** inline spellings; re-running the
  search over the landed cut found a **twelfth**, in
  `schedContextConfigureBoundPropagate`, which computed the bucket a reconfigured
  thread moves to from its `priority` argument while storing the record beside
  it.  It reads the stored record now, and the collapse is definitionally
  identical.  *A number in a changelog is what one search found; it is not the
  set.*

  **And a proxy can be the LENIENT side — check which tool the property is
  about** (PR #895 review round 17, `v0.35.30`).  Two findings, both in code
  written for round 16, which is five consecutive rounds landing in the previous
  round's fixes.  The first is this file's own *a recognised set is not a derived
  set* applied to a gate's **domain**, in the gate written last cut to close that
  shape one level up: `check_anchor_symbol_liveness.py` unioned every name read
  in any tracked module, so an unrelated `def helper(_DEAD)` kept a dead anchor
  green.  A read is **resolved** to the anchored module's symbol now — the
  target's own scope, an attribute on the imported module (plain or aliased), or
  a `from` import — with intra-module scope decided by **`symtable`**, CPython's
  own analysis, so shadowing by a parameter, comprehension target or nested `def`
  is not a form to enumerate.  *Round 17's instruction — ask the language's own
  front-end — applies to Python too, and `symtable` is it.*

  The second is why this entry exists.  `MD_SAFETY_HEADING` matched `Safety`
  case-insensitively on a word boundary, accepting four spellings
  `clippy::missing_safety_doc` rejects — and clippy does not examine a **private**
  `unsafe fn`, so there this scanner is the only enforcement.  The accepted set
  was then **measured** rather than recalled, with one `pub unsafe fn` per
  spelling compiled under the workspace's own clippy: `Safety`, `SAFETY`,
  `Implementation safety`, `Implementation Safety`.  That mattered in both
  directions — the review proposed restricting to the first two, which would have
  refused the two clippy accepts.

  **And the measurement found the two authorities disagreeing.**  For a Setext
  heading whose underlined paragraph spans lines, `cargo doc` renders
  `id="safetyand-more-text"` and `id="this-is-not-a-contractsafety"` — neither
  publishes a Safety section — while clippy **accepts both**, comparing each Text
  event of the heading rather than the heading's text.  On this shape the lint is
  the *lenient* one.  `v0.35.28` said the `# Safety` question's front-end is
  rustdoc and then reached for the lint that approximates it; the gate follows the
  **rendering**, because that is what a caller reads, and requires the paragraph
  to be a single line.  *So "hand the question to the real front-end" is not
  finished by naming a tool: when two tools answer, the one the property is
  defined by wins, and which that is has to be checked rather than assumed.*

  Two mechanical notes.  A previous round's recorded expectation is evidence, not
  authority: round 15's control asserted `True` for the multi-line Setext form on
  the strength of the first-line rule it had just introduced, and measurement
  corrected it while **vindicating** that round's actual finding.  And a
  hand-kept figure beside a derivation drifts on contact — the liveness gate's
  self-test printed `len(_CASES) + 3`, already wrong by two; it counts the checks
  that ran.

  **And an approximation is not the oracle — check whether the exact answer is
  already in reach** (PR #895 review round 18).  Three findings, all three in
  code this PR wrote, and all three the same thing: a gate deciding a question
  about a *language* with a pattern written by hand.  Round 14 named that class
  and registered it as debt on the reasoning that the remedy is "a reconciliation
  against the real tools — work, not wording".  Round 18 is the evidence that the
  deferral was partly wrong: **two of the three had an exact oracle in the
  standard library the whole time**, and the reason nobody used it is that nobody
  asked whether one existed.

  The identifier case is the clearest.  `[^\W\d]` is Python's *word* class and
  the question was `XID_Start`; rustc accepts `pub unsafe fn \u2118()` (Sm),
  `\u212e()` (So) and `\u1885()` (Mn), and `\w` matches none of them, so a
  declaration spelled with one raised **no obligation at all** and then failed
  its file as an unrecognised form.  Round 12 had already widened this class once
  for the same reason, which is the signal: *a class that needs widening a second
  time is not a class, it is a table someone is guessing at.*  **Python's
  identifier grammar is UAX#31 — the same one Rust uses** — so `str.isidentifier()`
  answers it, and the agreement is measured rather than assumed: over 28
  codepoints spanning every plausible category, 27 agree and the sole divergence
  is a lone `_`, which Python accepts as a whole identifier and Rust reserves as
  the wildcard.

  **That reading was half right, and round 21 supplies the other half.**  The
  rule really is shared; the *table* is not, and the 28-codepoint probe could
  not see that because every one of its codepoints was assigned in both
  editions.  `str.isidentifier()` was retired one round later — see **an oracle
  is exact only up to the version of the data it reads** below — so do not cite
  this paragraph as licence to reach for it.

  Two corollaries.  **The reach of a fix is the question, not the finding**: the
  reported site was one gate's declaration scanner, and the same question was
  being asked by seven hand-written classes across five files — so the remedy is
  round 9's, not a seventh patch.  One fragment derived from the oracle, and
  `bare_ident_literals` refusing a new ASCII class in any gate source, with
  `NON_RUST_IDENT_SOURCES` naming the files that legitimately ask a *different*
  language's question (a POSIX shell variable, a GAS label and a Lean identifier
  are all ASCII by their own grammars) and reconciled in both directions, so a
  stale classification fails as loudly as an unclassified pattern.  And **a
  measurement can carry the defect it is sizing**: the first scan for rebound
  import aliases reported three, all false, because it counted
  `os.environ["X"] = "y"` as rebinding `os` — a `Subscript` target mutates an
  object and binds no name.  The real count is zero, which is what makes the
  fail-closed fix free; had the false three been believed, the fix would have
  been weakened to accommodate them.

  **And when two authorities disagree, the accepted set is their INTERSECTION —
  and which one is strict can flip** (PR #895 review round 19).  Round 17 found
  `clippy::missing_safety_doc` and rustdoc disagreeing on a multi-line Setext
  heading and took the *rendering*, on the reasoning that the property is what a
  caller reads.  Round 19 is the same axis one level in — **inline markup inside
  the heading** — and it shows that reasoning was half the rule.  Measured on
  fifteen forms under this workspace's own toolchain: they disagree in **both**
  directions.  `` `Safety` ``, `&#83;afety`, `**Saf**ety` and `Saf<!-- c -->ety`
  all render `Safety` and clippy **refuses** each (a code span is a `Code` event;
  the other three split the title across two `Text` events); `[Safety]` clippy
  accepts while rustdoc renders `[Safety]` and warns `broken_intra_doc_links`.
  Following the rendering alone would let Tier 0 green a file the crate's own
  `-D warnings` lint then rejects — so *neither tool is "the" authority*, and
  naming one is not the end of the question even after you have measured it.
  The measurement stands and is what the gate's own output reports; what this
  round *did* with it — accept the intersection, by rendering the heading — was
  superseded one round later, for the reason its own closing paragraph gives.
  See **a rule stated in a docstring is not a rule in the code** below.

  The finding itself was the **fail-closed** direction — `/// # **Safety**`
  refused, a correctly documented `unsafe fn` rejected — which round 6 recorded
  as a defect in its own right and which this section otherwise spends its time
  on the opposite of.  *A spelling is not the text*: a heading's content is
  markup that renders to something else, which is *a spelling is not a read* one
  artefact over, at the one place round 12's "build the artefact" had stopped
  short — it built the markdown document and then matched the heading's raw
  bytes.

  **Two things about this round are worth more than the fix.**  First, round 18
  narrowed the debt row to "Rust item parsing and the CommonMark residue", and
  round 19 landed *inside the residue that row had just named*, one cut later.
  That is the narrowing working as a measurement and **not** working as a
  remedy: **predicting where the next finding will be is not preventing it**, so
  a narrowed row is evidence the analysis is right and no evidence at all that
  the gap is closing.  Second, round 18's own rule was applied *before* writing
  anything — *is an exact oracle in reach?* — and the answer here was **no**: no
  CommonMark implementation is available at Tier 0, which runs before any build.
  Recording the `no` is what makes the bounded reader honest rather than lazy;
  it refuses every inline form it cannot render, which keeps the site in the
  violation set (a visible failure) rather than clearing it silently.

  **And a rule stated in a docstring is not a rule in the code — the narrowest
  gap in this whole section** (PR #895 review round 20).  Round 19 closed by
  applying round 18's rule before writing anything and recording the answer:
  *is an exact oracle in reach?* — **no**, no CommonMark implementation is
  available at Tier 0 — and therefore "it refuses every inline form it cannot
  render".  That sentence is right, it is the correct engineering call, and it
  went into the docstring and into this file.  The code shipped in the same cut
  peeled emphasis runs and extracted link labels by hand.

  Round 20 is the two cells that gap produces, and they are worth naming because
  neither is exotic.  `# ** Safety **` is **inactive** emphasis — CommonMark 6.2:
  a left-flanking delimiter run may not be followed by whitespace — so rustdoc
  renders the asterisks literally and publishes no Safety section, while a
  peeler that strips a matched `**`/`**` pair reads `Safety`.  And
  an ATX heading whose content is a bracketed `Safety` label, an inline
  destination and a trailing `junk)` renders `Safetyjunk)`, while a label
  extractor anchored on the brackets reads `Safety`.  Both were accepted; both are the fail-open
  direction on the gate whose baseline is empty.

  **The distance between a stated rule and an implemented one is where this
  section's findings now live.**  Nine of the last twelve rounds found a defect
  in a hand-written front-end, and this file has said so since round 14 and
  registered it as debt; round 19 went further and *derived the right rule from
  first principles* — and then the hand-written renderer was written anyway,
  because refusing markup felt like it would reject valid documentation.  It
  does not: **measured before choosing**, every Safety heading in this tree is
  already written plainly (26 `/// # Safety`, 3 `/// ## Safety`, 3 `//! #
  Safety`, 2 `//! ## Safety`, zero carrying inline markup), so requiring the
  canonical spelling costs the tree nothing.  *Take the measurement that tells
  you the strict option is free, and the temptation to approximate disappears.*
  The heading's content must now **be** one of the four measured titles; every
  inline form is refused, including the seven both authorities accept, and the
  gate says which kind of refusal each is.  That is round 16's exit —
  **where the subject is code this project writes, require a canonical spelling
  and refuse the rest** — reaching the last construct in this file that was
  still being parsed.

  The round's second finding is the **enumeration** rule meeting a language that
  grew.  `rebound_import_names` was a hand-written `ast` walk over binding
  constructs, and the review reported one it missed: a `match` capture.
  Measuring the walk rather than patching the reported cell found the shape — it
  handled *every* binder Python had before PEP 634 and **none** of structural
  pattern matching's, which is four forms, not one.  An enumeration of a
  language's binders is a list of the ones that existed when it was written, so
  the next grammar addition empties it silently.  The exit is round 18's, and
  the oracle was already imported in the very cut that wrote the walk:
  **`symtable` is CPython's own binding analysis**, and `is_assigned()` is False
  for a name bound only by an import and True the moment anything else binds it.
  The enumeration is deleted; all eleven forms and both non-binding controls
  (`x.k[i] = v`, `x.attr = v`) are answered without the oracle being told they
  exist.

  Two mechanical notes, both earned.  **Measure the walk, not the cell**: fixing
  the reported `match` capture alone would have left three siblings live and the
  next round would have supplied one — and the same measurement corrected this
  file's own first draft of this entry, which claimed the walk had missed the
  walrus and `except ... as` too.  It had not; it handled both, and saying
  otherwise would have overstated the finding.  And **a conservative answer is
  defensible only when you have measured what it costs**: the whole-module
  binding query over-refuses a receiver shadowed only in an unrelated function,
  which the docstring declares — and across all 31 tracked `.py` files, zero
  import-bound names are assigned at module scope and zero at nested scope, so
  the conservative query and the exact one agree on the entire tree.  The
  alternative (ask the module scope alone) is fail-**open** for a shadowed read,
  which is the thing the gate exists to catch.

  **And an oracle is exact only up to the version of the data it reads**
  (PR #895 review round 21).  Round 18's instruction — *check whether the exact
  answer is already in reach* — is right, and this is the question to ask
  immediately after it: **what edition of what table is that answer computed
  from, and does the other side read the same one?**

  Three P2s, all three fail-**closed**, all three on valid Rust this tree would
  refuse.  `str.isidentifier()` and rustc both implement UAX#31 — the *rule* is
  genuinely shared, which is what made round 18's reasoning sound — but they
  read different editions of the Unicode table it ranges over.  Measured on this
  environment: CPython 3.11 carries Unicode **14.0**, where U+1C89 is
  *unassigned*, while rustc **1.94.1** compiles `pub unsafe fn Ᲊ() {}` with
  nothing worse than an `uncommon_codepoints` warning.  So a documented
  `unsafe fn` named with it raised no obligation and the explicit default branch
  then refused the whole file; and `\b`, defined against `\w`, saw a boundary
  *inside* the valid identifier `unsafeᲉ`, so `\bunsafe\b` matched its first six
  characters and Tier 0 demanded a justification of safe Rust.

  **Round 18's measurement was itself a recognised set** — this file's oldest
  domain rule, arriving inside the evidence that justified an oracle.  Twenty-
  eight codepoints spanning every plausible *category*, and category was the
  wrong axis: every one of them was assigned in both editions, so the probe was
  structurally blind to skew and would have reported 27/28 however far the two
  tables had drifted.  *When a measurement licenses a dependency, ask what it
  could not have seen.*

  The exit is **not** a third table.  Pinning rustc's XID data into a Python
  gate is the enumeration this project keeps retiring, and it goes stale at the
  next toolchain bump.  Instead the *question* changes to one no Unicode release
  can move: **every delimiter, operator and piece of punctuation in Rust source
  is ASCII** — rustc rejects non-ASCII punctuation outright — so outside
  comments and literals a non-ASCII character is part of an identifier.  That
  gives *a character may continue an identifier unless it is ASCII and neither
  alphanumeric nor `_`*, a fact about Rust's **grammar** rather than about a
  codepoint table, and for the two questions this tree actually asks it is
  **exact rather than merely safe**: a keyword adjacent to an identifier
  character is not a keyword but one longer identifier, and a name is only ever
  terminated by ASCII punctuation.  Where it does over-approximate — `×` and `·`
  are admitted and rustc refuses them — the self-test *asserts the
  over-approximation* rather than leaving a reader to rediscover it, because
  neither can stand beside a name in code that compiles.

  Two things the fix records.  **A retired oracle takes its dead API with it**:
  `is_rust_identifier` existed only to state round 18's `_` divergence, its sole
  readers were its own self-test rows, and its body was the retired call — a pin
  on a question nothing asks, which this file already names a tautology, so it
  is deleted rather than rewritten.  And **free exactness is still worth
  taking**: `ident_start` excludes ASCII digits, because `0-9` is a fact about
  ASCII and costs no table, even though the class beyond ASCII stays generous.

  The round's third finding is the same *whose question is this* shape in a
  different artefact.  `CARGO_TARGET_DIR` is **cargo's** setting, so a relative
  value resolves from the **invocation** directory; the gate joined it onto
  whatever root its scan had narrowed to, so `CARGO_TARGET_DIR=rust/target` run
  from the repository root excluded `rust/rust/target` — which does not exist —
  while cargo wrote to `rust/target`, which was therefore scanned.  Generated
  `.rs` under a build script's `OUT_DIR` is code no contributor wrote, so an
  unsafe site there would have failed Tier 0 against a file nobody can edit.
  *When you honour another tool's setting, resolve it the way that tool does.*

  **And the sweep found a fourth, in the check written to make sweeps
  unnecessary.**  Running this round's own rule — *when a fix names a relation,
  grep for every other place that asks it* — over Python's `\b` turned up two
  more Rust-keyword boundaries, and the reason `bare_keyword_literals` had not
  reported them is that it recognised **one shape**: `\b<keyword>\b`, a single
  keyword with a boundary on each side.  A keyword inside an alternation with a
  `\s+` tail (`check_claim_evidence_citations.py`'s Rust declaration head) and
  a one-sided boundary (`check_tlbi_broadcast_discipline.py`'s FFI export
  pattern) were both invisible.  Round 9 built that check so "the next such
  pattern fails on the day it is written"; **a discipline check that enumerates
  the shapes it has seen is the defect it exists to close, one level down.**

  The question is widened to the one being asked — *does this regex literal use
  a word boundary while naming a scanned keyword as a whole word?* — which
  over-approximates deliberately, because the remedy for a false positive is to
  compose `keyword()`, which is what the author wanted anyway; a literal
  genuinely asking another language's question goes in
  `NON_RUST_KEYWORD_SOURCES`, reconciled in both directions like every other
  classification here.

  One mechanical note, and it is this file's own rule repaying its cost
  immediately.  The widened question was first written to search the raw line,
  and the `b` of `\b` is an identifier character — so the whole-word lookbehind
  failed on `\bunsafe\b` and the derived question **missed the very spelling it
  subsumes**.  Nothing on the live tree would have caught that, because the
  plain pattern still ran beside it; what caught it was the witness asserting
  the *unchanged* row next to the new ones. **Keep the rows a fix does not
  change** — that is what distinguishes a fix that generalises from one that
  merely moves. A two-character regex escape is one token, so escapes are
  blanked before the keyword question is asked.
  **And the name a claim cites is its load-bearing half, so it cannot live in a
  comment** (PR #895 review round 22).  Four findings, and the pattern across
  them is one this file has been circling: three are *my own previous rounds'
  fixes*, and the fourth is a coverage claim whose counterpart was prose.

  The narrow one first, because it is the sweep rule failing at the smallest
  possible distance.  Round 14 found that **an angle bracket is not always a
  delimiter** — an array length and a const-generic argument are const
  *expressions*, so `[u8; 1 << 2]` in a signature raises a `<`-counting depth
  twice with nothing to lower it — and fixed it in `extern_block_items`, writing
  the reasoning into that function's docstring.  Round 18 then wrote
  `_body_open_brace` **one function above it**, counting `<` unconditionally,
  under a docstring asserting the opposite of the grammar (*"a comparison or a
  shift cannot appear in a type"*).  Both directions shipped: `-> [u8; 1 << 2]`
  never finds the body, and `-> [u8; 8 >> 1]` clamps the shared counter at zero
  and then lets the closing `]` drive it negative.  Each answers `FILE_SCOPE`,
  which no allowlist entry matches — so a **justified** site inside such a
  function is reported unjustified, Tier 0 refusing valid Rust.

  The remedy is not round 14's, and the difference is the point: dropping angle
  brackets is right when the subject is a `;` (which `[` and `{` already cover)
  and wrong when the subject **is** a brace, since `-> Foo<{ 1 }> { .. }` would
  answer with the const-generic block.  Two counters, with `<`/`>` read **only
  outside every bracket group**, is *exact* rather than merely safe, and for the
  reason round 14 gave: Rust requires a non-trivial const argument to be braced
  and an array length to sit inside `[` … `]`, so an operator `<` is always
  inside a bracket group and a delimiter `<` never is.  **The same grammatical
  fact answers both questions; only the direction differs.**

  **And the remedy for F1 is not the patch — it is that the question now has one
  owner.**  Two scans in that file asked *where does a Rust signature end*: one
  for the `;` that terminates a foreign item, one for the `{` that opens a body.
  The nesting rule is identical for both and was written twice, and the second
  copy reintroduced the defect the first had removed.  Patching the second would
  have left the file in exactly the state that produced the finding, so
  `signature_terminator` states the rule once — brackets nest, angles nest only
  at bracket depth zero, `->` is one token, a terminator counts only at zero on
  both counters — and both scans read it, differing only in which characters they
  pass as terminators.  The payoff is measured rather than asserted: **one**
  token-preserving mutation of that function now fails **four** witnesses across
  *both* questions, where before it would have failed only the body rows.

  That is the round-7 remedy (*give the sweep an artefact*), and round 9's lesson
  says it is not sufficient — sharing an answer stops two implementations from
  diverging and does not stop a **third** from being written beside them.  So the
  discipline is enforced too: `hand_rolled_angle_nesting()` refuses an
  angle-bracket *character* test anywhere in that file outside the owner, which
  is the shape such a scan is written in.  **The scope was measured before it was
  chosen** — the file holds exactly two such tests and both are in the owner,
  while every other one under `scripts/` asks a different language's question
  (Lean notation, a Lean arrow, a Markdown autolink, a CommonMark HTML-block end
  condition, a regex group name), so a whole-repository check would be mostly
  classification and this one costs nothing.  It is pinned in **both**
  directions, because a discipline check that cannot fire is indistinguishable
  from one that is wrong: removing the owner's exemption makes it report the
  owner's own two tests, and a probe appends a second implementation to a copy of
  the file and requires a hit.  Two things that probe records — a fixture must
  not be **self-referential** (the first version anchored on a `def` line whose
  text the probe's own source also contained, so the splice landed inside a
  string literal and the copy would not parse) and it builds its `<` from
  `chr(60)`, because a literal there would be a hit in the probe's own source and
  exempting the probe by location is the hole the check exists to refuse.

  The two other scanner findings are the same shape at their own level.  A
  foreign declaration may mark itself `unsafe` (RFC 3484's per-item marker,
  whose `safe fn` opt-out the gate already read), so the keyword pass **and**
  the foreign-item pass both yielded it: one declaration, two rows, every total
  and any baseline doubled — and invisible to a case list that only asks
  *"is each site found justified?"*, since both rows carry the same good
  justification.  A cardinality defect needs a cardinality witness, so the
  gate grew `_SITE_INVENTORY_CASES`, which name the declarations a fixture must
  produce and fail on a repeat.  The region now belongs to exactly one pass, and
  the direction is forced: the foreign walk is *derived* from the item structure
  and refuses a form it cannot read, so nothing inside the braces escapes it,
  while the keyword pass sees only what carries the token.  And
  `check_anchor_symbol_liveness.py` — the gate written last round to retire
  tautological pins — asked *"does this name occur as a global read"* where its
  question is *"does anything else read it"*, so `def _dead(n): return
  _dead(n - 1)` kept its own anchor alive.  That is this file's oldest rule
  inside the gate built to close one instance of it; reads are **attributed** to
  the declaration they occur in now, nesting carried, with the cycle residue
  stated rather than assumed away.

  The fourth is the one worth the entry's title.  Round 15 fixed *a claim made
  at the wrong UNIT* — leg versus operation — and left **which instance** of the
  unit, in a **comment**: `frozenBranchOperationChecked`'s only `true` row said
  it was checked against `endpointReplyWithDonation`.  That is the *single-core*
  composite, with no production caller, and it opens with the bare
  `endpointReply`, which keeps the `replier == expected` gate the cross-core
  spelling dropped (PR #822 review 6J-lYm: authority is the presented reply
  capability, and seL4-MCS reply caps are delegatable).  The live `.reply` arm
  dispatches `endpointReplyCrossCoreDispatch`, which accepts a delegate — and so
  does `frozenEndpointReply`.  So on a delegated input the frozen composite
  agrees with the **kernel** and disagrees with the named counterpart, and the
  row's `true` was read as the former.  Latent only because every fixture made
  the replier *be* the recorded server, where the two counterparts coincide.

  **A counterpart named in prose is a claim nothing reconciles**, so both
  counterparts are data now (`frozenBranchLiveOperation`,
  `frozenBranchLiveLeg`), each with a both-directions interlock — and the leg
  table is the sweep this round owed, because it asked the identical question
  with the identical answer wrong, which is round 11's *keep the tables
  symmetric* one artefact over.  A string is not a check and does not pretend to
  be: what pins the counterpart is a theorem **pair**,
  `endpointReplyCrossCoreDispatch_independent_of_replier` and
  `endpointReplyWithDonation_refuses_delegated_replier`, which together say the
  two are not interchangeable — the lesson `API.lean`'s `syscallDelegates`
  records from its own review round 11, that a *name* establishes a declaration
  exists and not that it says anything about the claim citing it.  The scenarios
  carry the delegated shape and assert the superseded composite **refuses** it,
  so the choice is measured at the point of use.  And the live steps the
  differential does not reach — the fault branch and the WS-RA delivered-message
  staging that `replyTransferOnCore` wraps the spine in — are **stated**
  (`frozenBranchOperationFrontier`) rather than implied, because a claim that
  stops at "checked" implies an authority over the whole arm it does not have.

  **And a bare NAME is not a declaration either — a suffix rename defeats it**
  (WS-RR RR8.16, `v0.35.197`–`v0.35.198`).  The same substitution at the
  smallest unit an anchor has: `rg '^theorem foo'` matches `theorem fooX`, so an
  anchor over a declaration with **no other consumer** — which is exactly what
  these anchors exist for — goes on reporting PASS once the name it pins is
  gone.  That is the tautological pin this file already retires, reached by a
  *rename* rather than by a deletion.  Cut C3b-iv (`v0.35.170`) recorded the
  rule, fixed the one anchor it was written for, and left the class; measured
  at **2543** of the tree's positive anchors.  Three things follow.  **Bound the
  name** with the delimiters a declaration name can be followed by — a class
  containing no alphanumeric, so the identifier-naming gate does not read a
  workstream code in it, and one both `rg` and the PCRE `grep` shim accept.
  **Negatives are out of scope**, and that is a decision rather than an
  omission: bounding a positive is strictly stricter, while bounding a negative
  can stop it firing on a name it was catching, so each of the tree's 27 is a
  judgement.  And **the sweep is driven by the gate's own anchor parser, not by
  a second regex** — a hand-rolled pattern is a recognised set and the parser is
  the derived one, which is what found the last 41 sites the hand-rolled sweep
  missed.  `unbounded_declaration_anchors`
  (`scripts/check_anchor_consistency.py`, Tier 0) refuses a new bare positive,
  with a deliberate FAMILY count — an `rg -c` against a threshold, where the
  prefix **is** the question — registered and reconciled both ways.  The sweep's
  own measurement is the argument for it: **eight anchors pinned nothing they
  name**, six naming the prefix `_preserves_ipcInvariant` where the declaration
  is `_preserves_ipcInvariantFull`, and one naming a file whose bare match was a
  different declaration entirely.
  **And an unbounded gap is not a region** (WS-OD OD3).  The region-scoped rule
  above assumes the scanner *has* a region; the cheapest way to write an anchor
  of the form "declaration `X` has property `Y`" is `X(.|\n)*Y`, and that gap runs
  to the end of the file.  The anchor then asserts only that `X` occurs somewhere
  before `Y` occurs somewhere — a presence check wearing the relation's comment —
  and it fails **open** in a positive check and fires spuriously in a negative
  one.  Both directions were live in `test_tier3_invariant_surface.sh`: a
  negative fired on a clean tree because it reached an unrelated theorem's
  hypothesis, and **eight positives were satisfied by text spanning a declaration
  boundary**, one of them crossing 43 declarations, so a lock footprint could have
  lost the member its anchor exists to pin with the gate still reporting PASS.
  Write the gap as `[^\n]*(\n([ \t][^\n]*)?)*` — the rest of the line, then any
  run of indented or blank lines — which cannot leave the declaration it started
  in, because a Lean declaration header sits at column 0.  Two earlier rounds had
  found this and abandoned the wildcard at the one site each was shown; the
  comments recording both were still in the file beside forty-nine live
  instances, which is the sweep rule failing in the way it describes.  **Bounding
  a positive is always safe** (strictly stricter, so it can only fail closed);
  bounding a negative is not, so each negative bounded in that sweep was
  mutation-tested in both directions — silent on the clean tree, firing on a
  mutation that keeps the token and moves it into the target declaration.

  **Three mechanical facts about writing one, two earned at `v0.35.140` and one
  at `v0.35.173`.**  The
  gap stops at the *first* column-0 line, so it cannot cross a **multi-line
  signature's own closing line** — a Python `) -> set[tuple[str, int]]:` or the
  equivalent sits at column 0 and is not a continuation.  That is the bound
  working rather than a defect, and the answer is to anchor from a line that is
  *inside* the declaration and unique to it (its docstring's first line), never to
  widen the gap.  And a `\"` inside a double-quoted `rg` argument inside single
  shell quotes **ends the argument early**, so an anchor over a Python or Lean
  docstring marker writes the quote `\x22`: the shell-quoting failure does not
  error, it silently decides nothing, which is the one outcome
  `check_anchor_consistency.py` exists to refuse.  And **a Lean `Name` literal's
  `` `` `` inside a double-quoted `bash -lc` argument is an EMPTY command
  substitution**, so it deletes itself from the pattern: five anchors written that
  way at `v0.35.173` searched for `whnfUntil applied SeLe4n.Kernel.…` — a string
  the file does not contain — and the changed-file sweep *deferred* all five as
  "substitutes a command" while printing PASS, so a mutation run over them reported
  every mutation as missed.  An anchor over a Lean name is written as bare argv
  with a single-quoted pattern (`run_check "INVARIANT" rg -F -n '``X.Y' file`),
  never through `bash -lc`; and the deferral **count** in a sweep's own epilogue is
  part of its verdict, not decoration.

  **And a DELIMITER that can occur in the data is not a delimiter** (PR #897's
  review, `v0.35.150`).  Six findings, one class, and it is this family's
  *domain* half rather than its predicate half: each gate answered "nothing
  here" for input it could not determine, which is silent by construction — the
  element is never examined, no count moves, and the report reads as a
  measurement of absence.

  The sharpest is in **shared infrastructure**.  `indexed_source.indexed_contents`
  wrote one `cat-file --batch` request per LINE and read one header per line, and
  a tracked path is a byte string that may hold a newline — which `listed_at`
  deliberately preserves, `-z` being exactly what it buys.  Measured: a two-file
  index in which one name holds a newline returned `{}`, **both** files absent
  and no exception, so every gate reading the staged domain through that helper
  reported a clean tree.  Three things the fix records.  `-Z` frames both
  directions, and git documents `-z` as deprecated *because the output stays
  ambiguous* — a framing fixed on one side only is half a framing.  The declared
  size is **checked against its terminator** rather than trusted, since `find`ing
  the next NUL re-synchronises after any drift and an off-by-one is absorbed at
  every entry.  And the walk must **consume the whole stream**: one response per
  request, which is precisely what the original defect violated (git answered
  three times for two wanted entries) and which no per-entry check can see.

  Five rules generalise from the six.  **A recorded failure must FAIL** — the
  changed-file anchor sweep's epilogue called `record_failure`, which only
  counts, on a path that never reaches `finalize_report`, so an anchor ending in
  `exit 0` printed the failure and the gate exited 0; the existing
  fatal-expansion control could not see it, because `set -u` exits 1 and the two
  agreed by accident.  **A rebinding is not a use** — crediting a bound fixture
  path when its name "occurs again" is satisfied by a second *assignment*, so a
  consumer that spells a path, overwrites the name and opens nothing passed the
  claim that the row names a gate which reads it.  **A call is not classifiable**
  — whether a call alters its argument before `lake` sees it is not a question a
  source scanner answers, so the probe locator's builder/consumer split (is the
  result used?  is the argument a `Name`?) was two proxies for an undecidable
  fact, and both were defeated within two review rounds; the exit is round 16's,
  *require a canonical spelling and refuse the rest* — probe text reaches Lean
  through a named template and `.replace` over literals, never as a call
  argument, with one structurally-incapable sink (`ast.parse` returns an AST)
  exempt by **resolution** rather than by spelling and reconciled both ways.
  **Every binding TARGET is seen** — a walk that skips any target which is not a
  bare `ast.Name` leaves `(PROBE,) = (<probe text>,)` binding nothing, so the
  name denotes no text and a transform through it builds a string carrying no
  marker: invisible in both directions at once.  And **the sweep is run, not
  stated** — `check_identifier_naming`'s own module docs record NUL-delimited
  discovery as its item 8, and seven sibling listings across five gates were
  still splitting on whitespace; the same sweep found a **third** copy of the
  `cat-file` loop that `v0.35.147` had collapsed two of.

  Two things about witnessing this class.  A mutation that keeps every token and
  changes the framing is caught only by a case whose *input* carries the
  delimiter — a fixture built from well-formed bytes proves nothing about a path
  with a newline in it, and the decisive cases here are git-driven because what
  was wrong is the REQUEST, which no parser fixture can exercise.  And **a
  harness that crashes where it should report hides the second defect**: a
  refusal raised on a success-path call escaped `indexed_source`'s self-test as a
  traceback and skipped every case after it, so one mutation masked another until
  the harness started reporting exceptions as case failures.

  **And the sweep found five more, one of them in the gate that blocks
  commits — so the rule gets a CHECK** (PR #897's review, `v0.35.154`).
  `v0.35.150` swept seven sibling listings for this class; the review then
  reported two it had missed, and sweeping the *question* rather than the
  reported spelling found three more.  The worst is
  `scripts/pre-commit-lean-build.sh`, whose `sorry` check reads three
  `mapfile -t` listings: staging `$'a\nb.lean'` holding
  `theorem bad : True := by sorry` produced **no finding**, because
  `git show ":\"a\\nb.lean\""` resolves to no object, so the gate whose stated
  job is to block a `sorry` passed it silently.  `select_changed_anchors` fails
  the same way in the other direction — a path that does not exist matches no
  anchor target, and the sweep reports **clean** while running nothing the real
  change invalidates.

  This file already said *the sweep is run, not stated*, and restating it a third
  time is the move that had failed twice.  `indexed_source.unframed_path_listings`
  is the check, in the module that already owns "run git correctly", wired into
  the self-test Tier 0 runs.  Three things it records.  **A NUL-framed stream
  cannot be piped through a line filter**, so the hook's `.lake/` exclusion became
  a path test rather than a `grep`; the framing is undone by the first consumer
  that splits on newlines.  **A path byte that is not valid UTF-8 must
  round-trip**, so the Python reader decodes with `surrogateescape` rather than
  raising on the one input the framing exists for.  And **the check resolves each
  line into the structure it stands for**, because two drafts of it cried wolf on
  this tree's own text: matching lines reported a diagnostic string, a Tier 3
  anchor quoting the call and a membership predicate, and matching every string
  argument of a call then reported six fixture builders whose arguments merely
  *include* an unrelated `"diff"` and an unrelated `"--cached"` — **a set standing
  in for a sequence, which is this file's own presence-for-relation defect inside
  the check written to close one.**  An argv is contiguous and identified
  structurally: a list whose first element is `"git"`, a callee whose name ends in
  `git`, or a shell command whose *head* word is `git`.  `--error-unmatch` is
  deliberately not a listing option — it prints nothing and is a predicate whose
  answer is the exit status.

  **And the check's OWN domain was a name resemblance, found by this cut's
  anchor sweep rather than by a review.**  `_python_git_argvs` recognised an
  invocation as a list argument whose first element is `"git"` **or a callee
  whose name ends in `git`** — and the second is a resemblance.  Measured over
  the tracked `scripts/*.py`: **30** functions run git, and **6** unframed
  listing call sites reach one through a helper named `g`, every one reported
  clean.  That is *a helper the scanner cannot see is a spelling that evades the
  metric*, inside the check written to close a domain miss, on its first day.
  `_git_wrapper_names` is the relation — a function whose body starts a process
  whose argv begins with the literal `"git"` IS a git wrapper, whatever it is
  called — resolved **intra-module**, because that is what `ast` can decide, with
  the name test **kept beside it** as a pin for the cross-module case rather than
  replaced.  The six sites are **fixed, not exempted**: an exemption is the
  enumeration the check exists to retire, so the harness asks git for paths the
  way the readers it tests do.  And the control is what keeps the derivation from
  becoming *any helper* — a same-shaped function running `hg` is not a wrapper,
  so dropping the `argv[0] == "git"` test fails a case rather than passing
  silently.

  **And the fail-closed fix's CALLER was admitting what it could not read**
  (`v0.35.150`, found by CI rather than by review).  Making a derivation raise
  moves the question to whoever decided it was available, and
  `check_workstream_plan.baseline_refs` decided it with `git rev-parse --verify
  -q <cand>` — an existence check for a ref NAME and a pure **syntax** check for
  a full hex sha, since git turns forty hex digits into a raw object id without
  consulting the object database.  Measured, on a sha this tree does not
  contain: `rev-parse --verify -q <sha>` exits **0**, `<sha>^{commit}` exits 1,
  `ls-tree` exits 128 with `fatal: not a tree object`.  A full hex sha is
  exactly what CI passes, so the guard was exact for every candidate except the
  one that matters, and both CI workflows already peeled — *one question, three
  askers, and the odd one out was the gate*.  `revision_is_readable` is the
  owner; an unreadable candidate is skipped and `baseline_is_complete` says so.

  Three things that cut records, each a rule already in this file arriving at a
  smaller unit.  **A fixture that inherits ambient configuration is not a
  witness**: three of four fixture cases pinned `SELE4N_PLAN_BASE_REF` and one
  did not, so under CI it listed a revision the fixture cannot contain;
  `_fixture_repo` is the one owner and it *pins* rather than pops, since popping
  sends the resolver to its `origin/main` fallback — the ambient repository
  again, one indirection out.  **Two halves can rescue each other**: with the
  peel in place, reverting the fixture leak leaves the suite green, because the
  unreadable sha is skipped and the case silently runs HEAD-only — which a
  *staged* deletion does not need a base for, though a *committed* one does, so
  the same leak one case over is a vacuous pass.  Hermeticity is therefore
  asserted directly, through the resolver inside the fixture, with a hostile
  ambient value by construction.  And **a negative anchor over a retired
  SPELLING is defeated by a reformatting revert**: the first one here kept the
  relation and MISSED its own mutation, because re-inlining the unpeeled call
  across two lines keeps every token and matches no single-line pattern.  Scope
  such a negative to the **location** — `baseline_refs` must not ask git at all
  — which is what makes extracting the owner the fix rather than a tidy-up; it
  then catches the inlined, the reformatted and the renamed-local revert alike.
  The explanatory measurement moves to the owner's docstring in the same step,
  since leaving it behind both duplicates the fact and trips that negative on
  prose.

  **And a RECEIVER may be parenthesised, which is the same substitution at the
  smallest unit a scanner has** (PR #897 review, `v0.35.151`).  The rule above
  polices the *question* a gate asks; this is the one where the question is
  right and the **text** it is asked of has a legal second form.  Lean permits
  redundant brackets around any expression, so `(st.objects)[k]?` *is*
  `st.objects[k]?` — the same access, on the same table — and every store-census
  pattern keys on the receiver's text.  Seven positions ask *which text denotes
  the object table*, the review reported one, and **all seven** keyed on the
  unparenthesised spelling.

  **Measured, and the measurement is what makes it a class rather than a
  nit**: four keyed reads in `Scheduler/Invariant.lean` are already spelled
  `({ st with objects := … }.objects)[tid.toObjId]?`, which `READ` could not
  see.  They sit in a `theorem`, so `STORE_READ_CODE`'s **enforced zero** was
  untouched — by accident, not by construction; the same expression in a `def`
  body walks around it.  That is `v0.35.12`'s *a spelling is not a read* and
  `v0.35.97`'s *a spelling is not a write* at the one position neither cut
  swept, and the qualified branch's second sub-shape
  (`RHTable.erase (spliceOutMidQueueNode st tid).objects k`, which `[\w'.]*`
  structurally cannot span) is a rename away from the same hole, the tree
  already writing that shape at five sites for theorem helpers.

  Three things follow.  **One owner, not seven patches**: `_RECV_OPEN` /
  `_RECV_CLOSE` are composed by every receiver position, so a widening reaches
  all of them by construction — a fix at whichever branch a review names leaves
  the other six open.  **Exact beats safe where the language decides it**:
  `_RECV_CLOSE` admits whitespace only INSIDE the bracket group and never
  between the last `)` and the accessor, because Lean's own lexer separates
  `x[i]` (a subscript) from `x [i]` (an application to a list literal), so
  `f (st.objects) [a, b]` is correctly refused — and that refusal is
  *asserted*, since the widening that admits the one is a whitespace class away
  from admitting the other.  And **the reconciliation is derived**:
  `branch_symmetry_violations` crosses `_TABLE_OPS` with `_OPERATION_SPELLINGS`
  rather than naming two spellings inline, so classifying an operation checks
  it in every spelling and adding a spelling checks it for every operation.

  Two mechanical notes, both earned by running the mutations rather than
  reasoning about them.  **Asking "was anything reported" is satisfied by a
  neighbouring assertion**: dropping the PARENTHESISED SUBSCRIPT check left the
  suite green because no case could reach it, so each reconciliation case now
  names the substring its violation must carry, and the two subscript cases are
  each other's controls — one requires a bracket where Lean does not, the other
  admits none where Lean does.  And **a negative over a spelling the fixtures
  deliberately carry must be scoped to its owner**: `self_test` holds the
  retired patterns as mutation inputs, so a tree-wide negative would fire on
  them; each is bounded to the declaration that must not ask the question the
  retired way, and verified by restoring the pre-fix reading inside it.

  **And a canonical-spelling contract is exactly as strong as its narrowest
  escape** (PR #897 review, `v0.35.152`).  Round 16's exit — *where the subject
  is code this project writes, require a canonical spelling and refuse the rest*
  — is the remedy this section arrives at twice, and `v0.35.150` applied it to
  probe text: *a probe reaches Lean through a named template and a `.replace`
  over literals, never as a call argument*, with one structurally-incapable sink
  (`ast.parse`) exempt "by RESOLUTION rather than by spelling".  Both escapes
  were then keyed on a **resemblance**: the exemption resolved that the receiver
  is *some* import rather than *which module*, so `import probe_builder as ast`
  satisfied it; and the unmodelled-form fallback answered "ordinary value" for a
  `Subscript`, so `[TEMPLATE][0].replace(…)` carried no marker and was not
  refused.  Both measured invisible in both directions at once.  So: **write the
  contract, then audit every branch that lets something past it** — an
  exemption resolves what its table NAMES (a module path, not a binding), and a
  default branch that cannot read its input answers *refuse* when the input
  reaches the thing the contract is about.

  Two corollaries the mutation run produced rather than the review.  **A third
  escape existed and no case reached it**: reverting the `FormattedValue` branch
  left the suite green, and measuring what it alone decides showed
  `f"{TEMPLATE}".replace(…)` passing without it — so the branch was right and
  unwitnessed, which is indistinguishable from wrong until a case is planted.
  And **a fourth clause measured the other way**: a marker-bearing literal
  written inline inside an unmodelled form is refused either way across five
  spellings, because an upstream reconciliation already catches it, so it is
  deleted with its measurement rather than kept for symmetry — *a filter
  positioned where it can only ever be wrong is not a filter*.

  **And "the view you read depends on the question" cuts both ways** (same
  round).  This file states that rule for *structure versus text*; the fixture
  catalogue needed it for *two code views of one language*.  `.sh` and `.py`
  consumers were read RAW under a docstring calling the over-approximation a
  loss of "precision on the diagnostic", and it was not: a shell gate containing
  only `# open("foo.expected")` satisfied the consumer claim, so a fixture could
  be indexed, hashed and opened by no executable code.  Both views already
  existed here, and the reason they are not in the shared overlay stands — a
  Tier 3 anchor may legitimately match a `.sh` or `.py` comment — so the remedy
  is a second table with a **stated** question and a reconciliation refusing the
  two to answer for one suffix, not a third lexer.  Where the existing view
  answers a *different* question, make the difference a **parameter**:
  `strip_shell` blanks a double-quoted span's message text, which is right for
  "which tokens are identifiers" and wrong for "does this script open that
  fixture", so the policy is the caller's and the lexing stays one answer.

  **And an anchor's inputs are not always in its own command.**  `test
  "${CIBUNDLE_CONJUNCTS}" -ge 5` names no path; the file it is about is named by
  the assignment above it.  Relating changed paths to the command alone dropped
  such an anchor from the changed-file selection **entirely** — not deferred,
  not reported, absent — so deleting conjuncts left that sweep green while
  direct Tier 3 failed.  *Resolve the text into the structure it stands for*: a
  variable reference is a reference to its producer, taken as the **last**
  assignment of that name before the anchor, and the relation, the disposition
  and the executed text are one answer.  An unbound name resolves to nothing at
  all rather than to a partial prelude.

  **And a new AXIS is only as good as the values you enumerate on it** (PR #897
  review, `v0.35.153`).  `v0.35.151` gave the store census's symmetry matrix a
  *receiver* axis and enumerated three of its five values; the two it skipped —
  a doubly parenthesised receiver and a NESTED application — were a live hole in
  the qualified branch, whose receiver was a FLAT paren group, so
  `RHTable.erase (f (g st)).objects k` was outside an enforced zero.  That is
  this file's own *a new axis is enumerated at all of its values on the day it is
  added* rule, unrun by the cut that created the axis.  **Take the axis's values
  from the grammar**: a Lean term in projection position is an identifier chain
  or a parenthesised term, which may nest or hold an application that nests, so
  the axis has five values and no others.  The same review found the same
  substitution one derivation over — `_TABLE_TYPE` wrote `(?:SeLe4n\.)?` on one
  of the type's three identifiers, at one of its qualifications, so a binder
  spelled `SeLe4n.Kernel.RobinHood.RHTable …` bound no receiver and its keyed
  accesses were in **neither** census.  A qualified Lean name denotes the same
  constant, so the qualifier is per identifier and bounded by a
  name-continuation lookahead.

  Three things that cut records.  **A regex cannot balance parentheses, so the
  qualified branch over-approximates to the LINE** and says so — a bounded
  nesting depth is the enumeration this file retires, and over-reporting a
  violation stops Tier 0 and names the declaration where under-reporting passes
  silently (measured: zero lines admitted on the live tree).  **The operation
  name's end is not `\b`** — Lean admits `?` in an identifier, so after `get?`
  there is no word boundary, and the crossing reported all three of its qualified
  spellings unrecognised before the branch ever ran against the tree.  And **a
  widening that admits a live site is a finding, not a failure**: the type
  widening surfaced `collectQueueMembers`, whose migration to the state accessor
  was *implemented and then reverted* — the walk and its six theorems port
  cleanly and two proofs shrink, but seven bundle transports in one module stop
  being definitional, against 320+ mentions across twelve files, because taking
  the table is what keeps the predicate unable to mention a non-object field.
  It is recorded in the indirect floor with that measurement.  *When a
  measurement kills the plan, that is the measurement working.*

  **And the view you read depends on the QUESTION, so one function that asks two
  needs two** (PR #897's review, `v0.35.154`).  The rule above is about a *value*
  a scanner could not read; this is about a scanner that read the right value
  through the wrong policy.  `check_fixture_consumers` asks a consumer *where is
  the fixture path mentioned*, which needs string contents **kept** because a
  path IS a string literal, and *is this occurrence of the bound name a read*,
  which needs them **gone** because a name inside a string is not a read.  One
  view answered both, so a consumer spelling `FIXTURE="foo.expected"` and then
  nothing but `echo "FIXTURE"` credited the literal as a use — a fixture could be
  listed in the README, hashed, named in a gate that never opens it, and still
  validate its `Used by` row, which is `v0.35.109`'s own *a checksum is not a
  comparison* one column over, in the check written to close it.

  **`v0.35.152` had already established that the two policies differ** — it gave
  `strip_shell` a `keep_quoted` parameter for exactly this reason — and used only
  one of them; this is that cut's own distinction applied at the second asker.
  Three things follow.  The blanking policy is a **parameter of the caller's
  question, not a second lexer**: `python_code_view` gained `blank_strings`, the
  shape `strip_shell` took two cuts earlier and the one `code_no_strings` has
  carried for Rust all along, so the tree keeps one Python lexer.  The two views
  are **byte-aligned**, which is what lets the mention be located in one and the
  read counted in the other at the same offsets.  And **the reconciliation's
  domain is derived, not the union of the two tables**: the first draft iterated
  `set(A) | set(B)`, so a suffix missing from *both* was in neither set and the
  check was silent about exactly the drop it exists to catch — deleting `.lean`
  from the identifier table was reported by **nothing**, which the mutation run
  said and no amount of reading it would have.  The domain is now what
  `consumer_code_view` can *answer* (`CONSUMER_VIEWS` plus the shared overlay's
  own `_STRIPPERS`), so "is this suffix answerable at all" has one owner.

  **And a LINE is not the declaration, nor is ONE decision drawn from two
  subjects** (PR #897's review, `v0.35.155`).  Two more of this family, and both
  are *the view you read depends on the question* at the level of the SPAN a gate
  reads.  `v0.35.153` over-approximated the store census's qualified branch to the
  LINE — correct reasoning, wrong unit: Lean wraps a long call, so
  `RHTable.insert\n  st.objects k v` matched **nothing** and an executable raw
  write could sit outside `STORE_WRITE_CODE = 0` while the gate printed the zero,
  with `READ` holding the same hole.  The unit is the **declaration**, spelled as
  the bounded gap this tree's anchors already use — a run of characters none of
  which begins a column-0 line, which a Lean declaration header always does — and
  written as one lazy alternation so it is linear rather than a nested quantifier.
  Measured before taking it: over all 405 tracked `.lean` files it admits **zero**
  matches the line bound did not, so the widening is free and every witness is
  planted.  `_WHITESPACE_PLACEMENTS` is the axis at all three of its values with
  `_DECLARATION_CROSSING` as its negative, because a gap that reaches a
  continuation line is one whitespace class away from reaching the next
  declaration's.

  The sibling is the same substitution in a *disposition*:
  `select_changed_anchors` computed `kind` from the anchor ALONE and compared it
  against `SEARCHING_KINDS`, while `missing` and `substitutes` beside it were
  computed from the command WITH its prelude — so a fully resolved threshold
  `test "${N}" -ge 5` reached `defer:tool`, and deleting bundle conjuncts left the
  changed-file sweep green while direct Tier 3 failed.  `v0.35.152` had fixed that
  split for `related`, the *provenance* question, and not for `kind`, the
  *executability* one.  **Recomputing `kind` is not the remedy and the measurement
  says so**: a compound `NAME=$( … ); run_check …` is not a line the classifier
  parses, so every such anchor would become `fail:unparsed` and fail Tier 0 on ten
  anchors that are correctly deferred.  Of eleven anchors with a resolved producer
  exactly **two** are runnable; the nine others are an array assignment the fold
  truncates, an EMPTY array (where the tool would run with no arguments and
  *pass*), a side-effecting `mktemp` feeding a build, or a redirection into the
  tree.  So round 16's exit again — **require a canonical spelling and refuse the
  rest** — with two details the measurement corrected: the substitution's closing
  parenthesis is the LAST character, since a `sed` pattern holds
  `\(theorem\|def\)` and a `[^)]*` bound stopped inside it, refusing one of the
  two anchors the contract exists for; and the pipeline is split on a **lexed
  word** through the module's own `_shell_words`, because a `sed` pattern holds
  `\|` and a `grep` pattern holds `| ` inside quotes.  **And the predicate needs a
  WIRING case of its own**: cases that exercise it directly leave a disposition
  branch which never consults it passing, which is *an unwitnessed condition is
  indistinguishable from a wrong one* at the point where a fix is plugged in.

- **Retired code is removed, not left to pollute the tree.**  When a cut
  supersedes a definition, a theorem, a resolver or a policy, the superseded
  thing is **deleted in the same workstream**, not kept beside its replacement.
  Two readings of one question is the duplication hazard this file spends most
  of its length on; a *retired* reading kept "for reference" is that hazard with
  a note attached, and it reads in a bundle, a footprint or a search result
  exactly like the live one.  The rule is unconditional — a superseded
  declaration has no grace period, and "it might be useful later" is what
  version control is for.

  Six things the WS-HP HP7 sweep (`v0.35.46`) established about doing this
  safely, each of which cost a measurement:

  1. **"Unused" is measured over the code view, and textual reference is not the
     only kind of use.**  A `lockSet_*_size_le` bound has *zero* textual
     consumers and is required **by name** by a Tier 1 census
     (`LockFootprintBoundCensus`, which derives the obligation from each
     footprint's own telescope and decides it by `isDefEq`); Tier 3 anchors
     consume symbols the same way.  A sweep that counted references and deleted
     the zeroes would have removed eleven live bounds.  So: count references over
     `scripts/lean_code_view.py --overlay`, then subtract what a **gate**
     consults — and where a declaration is genuinely consumed by nothing at all,
     anchor it rather than orphan it (next item) or delete it.
  2. **The derivations that replace a retired hypothesis are not retired.**
     HP7's whole content is that three *stated* coherence facts became
     consequences of the head-driven trigger; the theorems that say so
     (`answeredFrameHeadContext?_head_is_answered_reply`, `_donationHeadOf`,
     `_boundThread`) had no consumer either, and deleting them would have left
     the claim "derivable" with nothing behind it.  They are **anchored in Tier
     3** instead, because a derivation nothing consults reads exactly like one
     nobody checked.
  3. **A retired reading a witness needs moves into the witness, private, and
     nowhere else.**  A test that cannot name what it replaced cannot show that
     the replacement changed anything.  So the superseded spelling lives as a
     `private def` in the suite that refutes it —
     `bindingDrivenReplyServerDonation?` in `tests/SmpCrossCoreReplySuite.lean`,
     `bindingDrivenCancelledCallerDonation?` in `tests/SmpCancellationSuite.lean`,
     and `FrozenOpsSuite`'s `FO-042` for the frozen surface — computed beside the
     live one so the assertions are known to discriminate rather than merely to
     pass.  That keeps the *evidence* and deletes the *code*.
  4. **A positive anchor on a deleted symbol becomes a negative.**  `run_check`
     on a name a cut removed fails outright; worse, a `run_negative_check` on one
     silently passes forever, which is the tautological pin this file already
     retires.  Convert each positive to a negative that refuses the symbol
     tree-wide (*it must not come back*), and add a positive on whatever now
     carries the property.
  5. **Deleting a symbol means sweeping every citation of it.**  Prose naming a
     declaration that no longer exists reads exactly like prose naming one that
     does, and the deletion's blast radius includes docstrings, `CLAUDE.md` /
     `AGENTS.md`, the spec, the claim index, GitBook, the debt register and the
     plan.  Leave a **tombstone** where
     the symbol was, naming what replaced it: a reader arriving from a citation
     you missed needs somewhere to land, and the tombstone is what makes the
     miss recoverable instead of mystifying.
  6. **A declaration's own docstring is not authority on its fate — and check
     that the gates which would catch the miss are running.**  Two things this
     sweep found, and neither was in the deletion's plan.  The predicate WS-HP
     HP7 was scheduled to retire turned out to be **live**, with twelve
     consumers, while **five** docstrings across `API.lean`,
     `DispatchPayoff.lean`, `DonationPreservation.lean`, `Endpoint.lean` and the
     plan itself said the phase retires it — a forward-looking claim written
     three phases earlier, propagated by every later cut that touched those
     files, and false.  So a sweep resolves what a symbol's *consumers* say, not
     what its docstring predicts, and it sweeps the **forward-looking** prose
     (`until X retires it`, `X is what retires this`) as well as the citations:
     a stale prediction reads exactly like a scheduled obligation.  And the
     sweep's own instruments need checking, because both of this tree's citation
     gates failed here in opposite directions: `check_workstream_plan.py` was
     **red at HEAD** and had been since the previous cut, on landing notes that
     cite a later sibling narratively where the gate — correctly, no scanner
     being able to tell a mention from a consumption — reads a forward
     dependency; and `check_claim_evidence_citations.py` matches a citation as
     `` `<ident>_<ident>` ``, at least one underscore, so **every Lean `def`**
     (lowerCamelCase) is outside its domain and a deleted one cited as evidence
     reports PASS.  That is fail-open, it is registered in
     `docs/REGISTERED_DEBT.md` §C with its measurement, and until it closes a cut
     that deletes a `def` sweeps the index by hand.  *A green gate you did not
     run, and a gate whose domain excludes what you deleted, are the same
     silence.*

- **Invariant/Operations split**: each kernel subsystem has
  `Operations.lean` (transitions) and `Invariant.lean` (proofs). Keep
  this separation.
- **No axiom/sorry**: forbidden in production proof surface. Tracked
  exceptions must carry a `TPI-D*` annotation.
- **Deterministic semantics**: all transitions return explicit
  success/failure. Never introduce non-deterministic branches.
- **Fixture-backed evidence**: `Main.lean` output must match
  `tests/fixtures/main_trace_smoke.expected`. Update fixture only with
  rationale.

  **And a checksum is not a comparison** (`v0.35.109`).  Every fixture carries
  a `.sha256` companion and the Tier 2 gate sweeps all of them, reporting
  "Fixture hashes verified (14 files)" — which reads as a measurement of
  agreement with the program and is a measurement of agreement with *itself*.
  A checksum's job is to force a fixture edit to be paired with a hash refresh
  in the same commit; it says nothing about whether the fixture still describes
  what the code does, and it is the fixture's *producer* that must be run to
  ask that.  This file's oldest rule, arriving at an artefact none of its
  instances had reached: *a presence check is not a relation check*, where the
  presence is a hash of the file by itself.

  Measured on the whole directory: **twelve of fourteen** fixtures were also
  compared against live output — by `test_tier2_trace.sh` for the main trace, by
  a `fixturePath` read inside the producing suite for ten more, and by
  `include_str!` in `rust/sele4n-abi/tests/conformance.rs` for the return-shape
  table, which is asserted on both sides of the ABI — and all twelve matched, so
  the sweep's value is entirely in the two it could not reach.  Those two are the
  ones nothing compared, and their drift was **total**: `robin_hood_smoke.expected` and `two_phase_arch_smoke.expected`
  are not golden output at all but `SCENARIO_ID | SUBSYSTEM |
  expected_trace_fragment` manifests, and **19 of 19** fragments named lines no
  suite printed.  The cause is the shape this file keeps recording: the only
  consumer, `scenario_catalog.py validate-registry`, parses `parts[0]` — the ID
  column — so the *fragment* column was read by nothing, and when the suites'
  `expect` labels lost the scenario-id prefix the manifests presuppose, every
  row went stale in silence.  `RobinHoodSuite.lean` carried **both**
  conventions, 19 labels with an id and 36 without, in one file.

  Four things new code must respect.  (1) **A fixture needs a gate that runs its
  producer, and the comparison is of SEQUENCES.**  Which gate it is belongs in
  `tests/fixtures/README.md`'s "Used by" column — where it was *false* for both
  manifests, naming suites that do not read their file.  And the main trace's own
  gate asked only the forward direction (every fixture fragment occurs in the
  output), computing the converse *inside the failure branch*, so a passing run
  never asked whether every output line is accounted for: a trace line **added**
  to the output left the fixture no longer enumerating the trace, while this file
  said "must match".  Both directions were asserted at `v0.35.110`, and the
  measurement is what licensed taking the strict one — 239 fragments, 239
  non-empty output lines, zero unaccounted, so it cost the tree nothing.  The
  mutation that decided there drops **one** fixture line and touches nothing else:
  the forward direction still passes at 238/238, and the pre-`v0.35.110` gate
  reported `Fixture comparison passed` on it.

  **And a set is not a sequence** (PR #897 review, `v0.35.113`).  Both of those
  directions are substring **containment**, so what the pair decides is set
  membership and nothing more — which is this file's oldest rule one level below
  the cut that added the second one, and it leaves three token-preserving
  mutations passing: a fixture line **duplicated** (the forward pass finds it
  twice, the reverse pass accounts for every output line), two fixture lines
  **transposed** (identical multiset, and neither direction reads order), and an
  output line **duplicated** (both copies independently find the same fragment, so
  the trace gained a line and the gate reported that both directions held).
  Measured against the superseded gate, the transposition passed and the
  duplication passed *reporting `240/240`* against a 239-line trace — a fixture
  claiming one more expectation than the program prints, called a pass.  What
  licenses the strict form here is the artefact's own contract rather than a
  judgement: `tests/fixtures/README.md` regenerates this fixture by redirecting
  the producer's stdout over it, so it **is** golden output, and the expectation
  sequence and the output sequence are byte-identical at 239 lines with no
  duplicate on either side.  The two loops are kept as *diagnostics* — a 239-line
  diff does not say which scenario id is missing, and which direction moved is
  what tells a maintainer whether the code or the fixture changed — and the
  sequence equality is the verdict.  (2) **The improvement direction is the code, not the
  fixture.**  The manifests were right and the labels had drifted, so the fix
  relabels 94 assertions rather than rewriting 19 rows — and it costs no fixture
  churn, because a manifest nobody edits keeps its checksum.  Rewriting the rows
  would also have made them *ambiguous*: `size correct` and `timer advanced` each
  name two assertions, so a fragment without its id identifies no scenario, which
  is the presence-versus-relation defect one level down.  (3) **The swept set is
  derived**: `list-manifests` classifies a fixture as a manifest by its row shape
  and reads its producer from the manifest's own `# Suite:` header, so a manifest
  added later is checked with no gate edit, and one that declares no producer
  **fails discovery** rather than dropping out of the domain while the gate
  prints PASS.  (4) **A regeneration recipe is a claim too**: the README told you
  to redirect each suite's stdout over its manifest, which replaces an ID table
  with raw output and breaks the Tier 0 registry gate (measured: 74 and 79
  differing lines).  A documented workflow that corrupts the artefact it
  maintains is worse than none, and a Tier 3 negative refuses its return.

  **And a table that claims to enumerate a directory is an enumeration standing
  in for a derivation.**  The same README's `## Files` table is where a reader
  learns which gate compares a given fixture, and it had omitted
  `syscall_return_shape.expected` and `qemu_boot_expected.txt` — the second found
  by `check-fixture-index` (Tier 0) on its first run, which is the criterion this
  file sets for a mechanism worth building.  Membership is a **row**, never a
  mention: a fixture named in passing in the prose names no gate, so accepting one
  would be the presence-for-relation substitution one artefact over.  The
  exemption set is reconciled in both directions, because an exemption nobody
  reconciles reads exactly like coverage.

  **And the machinery that closes a class is written by the same hands** (`v0.35.111`).
  The three paragraphs above are one rule — *a presence check is not a relation
  check* — applied to fixtures.  A review of the code that applies it found **three
  instances of it inside that code**, all fail-open, and the measurement worth
  keeping is not the instances but *where the witnesses were*: all twenty cases had
  been drawn from the drift that had already been observed, so they probed the
  boundary and never asked the property.  That is this file's own *a witness drawn
  from a finding tests the finding*, arriving in the cut written to obey it.

  The three, each a presence check standing in for the relation the function's own
  name asserts.  `check_fixture_index` joined the table's `|` lines into one blob
  and asked whether the filename occurred in it, so an **unlisted fixture passed
  whenever any cell quoted a longer name containing it** — its own `.sha256`
  companion, which every row in that table names — and the loop ran over the
  *directory*, so a row naming a **deleted** file was never inspected.
  `discover_manifests` skipped a file it could not parse, so one carrying a valid
  `# Suite:` header and a single malformed row was swept as golden output with
  `manifest_count` still nonzero and the gate still printing PASS — the exact
  silence the machinery exists to end, arriving through the classifier instead of
  through a stale row.  And `check_fragments` bound a fragment to nothing, so a row
  reading `RH-001 | … | [RH-002a insert then get]` **passed**: the fragment is
  emitted, by the wrong assertion, and `RH-001` could have been deleted from the
  suite outright with the gate green.

  Four things the remedies decide rather than inherit.  **Membership is a parsed
  CELL of a named section**: `fixture_table_filenames` reads the `Fixture` and
  `Hash` cells of the `## Files` table, scoped to that heading — so a filename
  backticked in a second table cannot satisfy a fixture's membership, which is the
  derived-domain rule applied to *which table the claim is about* — and only those
  two cells declare, because the real table's third column quotes
  `scenario_registry.yaml` in prose and would otherwise have declared it.  **Intent
  is what makes a skip reportable**: `classify_fixture` treats a `# Suite:`
  declaration *or* all-row content as manifest intent, and given intent anything
  short of well-formed is an error — with the control mattering as much as the case,
  since the same content without the declaration must stay a trace fixture or golden
  output would be run against a producer it never named.  **A binding is a relation,
  not a containment**: the id must be followed by an optional sub-case letter and
  then a character that cannot continue an id, so `RH-001` does not match
  `RH-0010a …`, which is the same defect one character down.  And **two
  classifications are none**: a file both exempt and named by a row now fails, as a
  missing `## Files` heading does — answering "nothing to check" is a silent pass
  and answering "every fixture is unlisted" names the wrong cause.

  One mechanical point that is genuinely new, and it corrected this cut rather than
  the tree.  **A negative anchor on a retired variable name is satisfied by a revert
  that renames it.**  The first negative written here forbade the retired membership
  expression verbatim; the mutation that reintroduces the joined-blob reading under
  any other local name left it silent, and the mutation run is what said so.  What
  the claim is about is *where the README's text is read*, so the anchor is scoped
  to `check_fixture_index` and forbids the read itself — the declaration-bounded
  form this file otherwise warns about, correct here because the claim really is
  about that declaration.  Ask of any negative: *what renames or relocations
  survive it?*

  **And a gate's own control must be identified by the REASON it fires**
  (`v0.35.113`, found while fixing the paragraph above).  The one artefact that
  claimed to exercise the comparison above was
  `scripts/audit_testing_framework.sh`, whose header says in as many words that
  it "synthesises a deliberately-broken trace fixture and asserts that
  `test_tier2_trace.sh` correctly rejects it (catching a class of *fixture
  compare silently passing* bugs)".  It copied the fixture to a `mktemp` path and
  asserted a non-zero exit — and `TRACE_FIXTURE_PATH` must name a **git-tracked**
  file, an injection guard that refuses any path outside the index, so the
  control was refused before the gate read a single line and would have reported
  success with the comparison deleted outright.  The script written to catch
  "fixture compare silently passing" was passing silently, and the class it names
  is the one the review then found.

  **"The gate could not read it" and "the gate checked it and it differs" must
  never produce the same verdict** — the rule this file already states for
  `check_anchor_consistency.py`, there in the PASS direction and here in the FAIL
  one.  So a control asserts the *message*, not the exit status, and a control
  whose claim is that one check decides asserts the others stayed **silent**: the
  five now in that script mutate the real fixture (with its `.sha256` refreshed,
  since the checksum sweep runs first and the mutation is exactly the consistent
  fixture edit a maintainer makes) and are each decided by their own subject — an
  appended expectation by the forward direction, a deleted one by the reverse, a
  **transposed** and a **duplicated** one by the sequence comparison alone, and an
  untracked path by the guard and by nothing else.  Two further things that cut
  measured.  A control that cannot be run **on its own** is a control nobody
  re-runs after touching the gate it is about, which is how this one stayed inert
  behind a tier stack it runs first: `--controls-only` is eleven seconds against
  tens of minutes.  And the mutated fixture is restored from the index after every
  control **and the restoration is verified**, because a crashed run that leaves a
  golden fixture edited is worse than a control that never ran.
  **And a prose COLUMN is a claim nothing reconciles — while a gate that repairs
  shared state must own it first** (`v0.35.116`).  The rule above says a fixture
  needs a gate that runs its producer and that *which gate it is belongs in*
  `tests/fixtures/README.md`'s "Used by" column.  That sentence had two readers
  and no checker: `check_fixture_index` parses the `Fixture` and `Hash` cells and
  ignores the third, so the column a reader is told is "the only place a reader
  learns which gate compares a given fixture" was read by nothing — and the same
  cut that wrote it *measured* the column false for two fixtures.  A new golden
  fixture could therefore be listed, hashed and compared by no gate at all with
  every fixture gate green, which is `v0.35.109`'s own finding one column over,
  and it is the *a counterpart named in prose* rule (PR #895 round 22) applied to
  a documentation table rather than to a Lean comment.

  `check_fixture_consumers` validates it per fixture **kind**, because what "its
  consumer" means differs: a scenario-traceability manifest is found by a glob
  that names no file, so its cell must name that gate and nothing else is
  checkable; every other fixture is opened by name, so a repository path its cell
  names must exist and must mention the fixture in its **code view** — the tree's
  own per-suffix table, hoisted out of `lean_code_view.overlay`'s local so the
  question "what is this file's code view" keeps one owner rather than two.  A
  suffix with no view is read raw and the docstring says so, since narrowing it
  would mean a third shell lexer.  Its first run caught the row the enumeration
  could not: `two_phase_arch_smoke.expected`'s cell read *"same two gates"*, a
  back-reference to the row above that a reader resolves by eye and a check
  cannot resolve at all.

  The second half is the audit harness, and it is a class this file had not
  written down.  `audit_testing_framework.sh` mutates the real trace fixture in
  place — the only way to reach the comparison, since the fixture-path guard
  refuses anything outside the index — and restores it with `git checkout --`
  before the first control and again on EXIT.  That **permanently discards an
  unstaged edit**, and a maintainer editing a fixture is exactly who runs
  `--controls-only`, which this file advertises as eleven seconds against tens of
  minutes.  **A gate that repairs shared state takes ownership of it first, and
  refuses rather than repairing what it does not own**: the check is fail-closed
  (a non-zero exit naming the files, never a skip), it runs *before* the tier
  stack rather than before the controls — a full run would otherwise spend tens
  of minutes and then discard the edits, and a legitimately regenerated fixture
  makes that stack **pass** — and the restore reads an ownership flag, because the
  trap is installed before the check can run and would otherwise fire the very
  restore it exists to prevent.  A *staged* edit is not dirty and is preserved,
  which is what makes `git diff --quiet` the right question: it asks precisely the
  unstaged one, and the index is what the restore puts back.
- **Typed identifiers**: `ThreadId`, `ObjId`, `CPtr`, `Slot`,
  `DomainId`, etc. are wrapper structures, not `Nat` aliases. Use
  explicit `.toNat`/`.ofNat`.
- **Internal-first naming**: every identifier — theorems, functions,
  definitions, structures, fields, test runners, file names, directory
  names — must describe the semantics of what it is (state update
  shape, preserved invariant, transition path, test subject).
  Workstream IDs, audit IDs, phase codes, and sub-task numbers
  (`WS-*`, `AN3-*`, `AK7-*`, `ak9ce_01`, `I-H01`, etc.) **must not**
  appear in any identifier or file name. Example: rename a test from
  `an3b_02_projection_typing` to
  `ipc_invariant_full_projection_signatures`. Workstream IDs are
  commit-time labels and age out as soon as a workstream closes —
  encoding them in identifiers creates documentation debt and hides
  what the code actually means. Legitimate places to reference a
  workstream ID: docstrings, commit messages, CHANGELOG entries, and
  `CLAUDE.md` / `docs/REGISTERED_DEBT.md` prose. Historical
  identifiers that already encode workstream IDs stay as-is until
  touched by a workstream that can rename them in the same commit;
  new code must comply from day one.  Enforced by
  `scripts/check_identifier_naming.py` (Tier 0), which scans every
  identifier token — and every path component — over every tracked
  non-documentation file rather than enumerating declaration forms,
  globs, or suffixes: Rust is held at zero, and every other code
  surface (Lean, Python, shell, config, assembly, data) is pinned by a
  baseline in `scripts/identifier_naming_baseline.json` counting
  occurrences per (identifier, file), so a grandfathered name's count
  may fall but never rise — a set of pairs alone cannot see a second
  use inside a file that already contains the name.  Prose is
  exempt, as are documentation paths — an audit report or workstream
  plan is *named after* the workstream it records, and CLAUDE.md and
  the website link manifest both cite those paths.  The exemption is
  by location, never by suffix: a `.json`, `.txt`, `.sha256` or
  `.expected` file outside `docs/` is code as far as this gate is
  concerned.  Within a file the prose exemption stops at any literal
  that supplies a linker-visible name — `#[export_name = "…"]`, an
  assembly `.global`, a linker-script `PROVIDE`, an `asm!` template —
  since each of those puts its string in the symbol table.  Paths and
  contents are both read from the git index, so the gate checks what is
  being committed rather than the working tree.  The gate's own
  mechanisms are pinned by `scripts/test_identifier_naming_gate.py`
  (Tier 0), since a scanner that under-reaches fails silently.
