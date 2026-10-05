#!/usr/bin/env python3
"""Validate and query WS-B11 scenario catalog metadata.

Two artefact shapes live under `tests/fixtures/`.  A **trace fixture** is golden
output compared byte-for-byte against a suite's stdout.  A **scenario-
traceability manifest** is a table of `SCENARIO_ID | SUBSYSTEM |
expected_trace_fragment` rows: its ID column is reconciled against
`tests/fixtures/scenario_registry.yaml` by `validate-registry`, and its fragment
column names a line the suite emits.

The fragment column was read by nothing until `v0.35.109`, so a suite that
renamed an assertion label staled its manifest silently — measured then at
**19 of 19** fragments absent from live output across the two manifests, because
an `expect` label's scenario-id prefix had been dropped and the only consumer
parsed `parts[0]`.  A `.sha256` companion cannot see that: it pins a fixture
against itself, not against the program.  `check-fragments` is that relation, run
from `scripts/test_tier2_trace.sh`, which is where this tree answers "does a
fixture agree with the program"; `list-manifests` derives its domain and is run
from Tier 0 as well, because manifest well-formedness needs no build.

`v0.35.111` corrected presence-for-relation defects in that machinery, each
the class it was written to close.  `discover_manifests` skipped a file it could not
parse, so one carrying a valid `# Suite:` header and a single malformed row was
swept as golden output with `manifest_count` still nonzero; manifest INTENT now
makes that an error.  And the fragment relation bound nothing to its own row, so
a cross-wired row witnessed a different scenario and passed against real output;
`fragment_names_scenario` is the binding.
"""

from __future__ import annotations

import argparse
import json
from json import JSONDecodeError
from pathlib import Path
import re
import sys

ALLOWED_TIERS = {"smoke", "nightly"}

# A manifest row: `SCENARIO_ID | SUBSYSTEM | expected_trace_fragment`.
MANIFEST_ROW = re.compile(
    r"^([A-Z][A-Za-z0-9-]*)\s*\|\s*([A-Za-z][A-Za-z0-9_]*)\s*\|\s*(\S.*)$"
)
# A manifest declares the executable whose output its fragments must appear in.
# The declaration lives in the manifest so the gate's domain is DERIVED from the
# fixtures rather than listed in the gate: a manifest added later is swept with
# no edit anywhere else, and one that declares no producer fails the gate rather
# than dropping out of the domain unnoticed.
SUITE_DECL = re.compile(r"^#\s*Suite:\s*([a-z][a-z0-9_]*)\s*$")
# The bracket form a trace fixture uses for its scenario ids: `[RH-001] ...`.
BRACKET_ID = re.compile(r"^\[([A-Z]+-\d+)\]")
#: A scenario id's canonical shape: an upper-case family prefix and a number.
#: Both manifests use it for EVERY row, and requiring it of a row is what keeps a
#: manifest's declared set comparable with what the reverse reconciliation reads
#: out of its producer -- that scan reports every label-position id of this shape
#: (`emitted_scenario_ids`), so a row spelled outside it would be declared and
#: never matched.  Until `v0.35.142` the family also *bounded* that scan's domain,
#: which is why this shape was required; the bound is gone (it was derived from
#: the manifest, so a NEW family defined itself out of the scan) and the shape
#: requirement stays for the reason above.
SCENARIO_ID = re.compile(r"^([A-Z]+)-\d+$")
#: **Where a scenario id may appear to be a LABEL**, written once because two
#: questions ask it: whether a manifest row's fragment names its own scenario
#: (`fragment_names_scenario`) and which scenarios a producer's output claims to
#: trace (`emitted_scenario_ids`).  A second spelling would be free to disagree
#: about what a label position is, and the two directions would then reconcile
#: different relations.  `{id}` is substituted with an escaped id or with a
#: capturing group for the family.
LABEL_POSITION = r"(?:^|\[){id}[a-z]?(?![0-9A-Za-z-])"


class Manifest:
    """A parsed scenario-traceability manifest."""

    def __init__(self, path: Path, suite: str | None,
                 rows: list[tuple[str, str, str]]) -> None:
        self.path = path
        self.suite = suite
        self.rows = rows


class FixtureShape:
    """Which of the two artefact shapes a `tests/fixtures/*.expected` file is.

    `manifest` is set when the file is a well-formed scenario-traceability
    manifest; `error` when it DECLARES manifest intent and is not one.  Both
    unset means a trace fixture: golden suite output, whose lines are not rows
    and which claims no producer.

    The intent flag is what makes the error case reachable at all.  Classifying
    by content alone answers "not a manifest" for a file carrying a valid
    `# Suite:` header and one malformed row, so such a file was swept as a trace
    fixture -- silently, with `manifest_count` still nonzero and the gate still
    reporting PASS.  That is a scanner's default branch answering a question it
    could not read, which this project's rules call a decision: an input a
    scanner does not recognise fails the gate rather than dropping out of its
    domain.
    """

    def __init__(self, path: Path, manifest: Manifest | None = None,
                 error: str | None = None) -> None:
        self.path = path
        self.manifest = manifest
        self.error = error

    @property
    def is_trace_fixture(self) -> bool:
        return self.manifest is None and self.error is None


def fragment_names_scenario(scenario_id: str, fragment: str) -> bool:
    """Does `fragment` carry `scenario_id` as an assertion label's own id?

    A row asserts that ITS scenario is traced, and the fragment is the evidence,
    so a fragment naming a DIFFERENT scenario witnesses the wrong thing while
    passing a containment test against the suite's output -- the row's claim and
    the check's subject come apart, which is a presence check standing in for a
    relation.

    The id must occur **at a label position** -- the start of the fragment, or
    immediately inside a `[` -- followed by an optional lowercase sub-case letter
    and then a character that cannot continue an id.  So `RH-001` matches
    `RH-001a insert` and `... passed [RH-001a empty get? returns none]`, and does
    NOT match `RH-0010a ...` (a longer id that merely has this one as a prefix,
    the same defect one character down) or `[RH-002] insert (covers RH-001)`.

    **A region-scoped presence check is still a presence check** (`v0.35.116`).
    The first cut of this function searched the WHOLE fragment, so the second
    example passed: the row claims `RH-001` is traced, the evidence is a line
    labelled `RH-002`, and `check_fragments` then passed whenever that RH-002 line
    was emitted -- while `validate-registry` sees only the id SET and the checksum
    pins the manifest to itself.  Narrowing the id's spelling (the previous fix)
    made a prefix collision impossible and left the position unasked.

    The two label forms are the ones this tree's manifests use, measured rather
    than guessed: `TPH-001a empty builder valid` (the label is the fragment) and
    `robin-hood check passed [RH-001a ...]` (the label is bracketed).  Requiring
    one of them is this project's *require a canonical spelling and refuse the
    rest* rule, and it costs the tree nothing -- every live fragment sits at a
    label position -- so a suite that emits `PASS: TPH-001a ...` spells the
    fragment as the label rather than the gate widening to a third position.
    """
    pattern = re.compile(LABEL_POSITION.format(id=re.escape(scenario_id)))
    return pattern.search(fragment) is not None


#: The reverse of `fragment_names_scenario`: every id a producer's output puts at
#: a label position, for the families given.  Built from `LABEL_POSITION`, so the
#: two directions cannot disagree about where a label sits.
#:
#: `re.MULTILINE` is what makes that sharing real, because the two directions ask
#: the pattern at different SCOPES.  The forward direction is handed ONE LINE (see
#: `check_fragments`), so its `^` means the start of a line; this is handed a whole
#: output, where an unflagged `^` would mean the start of the DOCUMENT -- a
#: different relation, at the one point this cut exists to make single.  Measured:
#: it admits nothing on this tree, since `Testing.expectCond` prints
#: `<tag> check passed [<label>]` and both producers use it, so every live label is
#: bracketed.  `test_the_emitted_extractor_reads_every_family` is therefore what
#: pins it, with a line-start label no suite emits today.
EMITTED_LABEL = re.compile(LABEL_POSITION.format(id=r"([A-Z]+-\d+)"), re.MULTILINE)


def emitted_scenario_ids(output_text: str) -> set[str]:
    """Every scenario id `output_text` labels, whatever family it names.

    **The domain is the output, not the manifest** (PR #897's review,
    `v0.35.142`).  `v0.35.139` bounded this by the families the manifest's own
    rows declare, on the ground that an ordinary output line may carry anything.
    That bound is derived from the very thing the scan exists to contradict: a
    producer that adds its FIRST scenario in a new family -- an `RH-*` suite that
    starts emitting `[NEW-001a ...]` -- names a family no row declares, so the
    filter discarded it and the reconciliation passed over a scenario with no row
    and no registry entry.  A domain derived from the answer is the enumeration
    this reconciliation was written to retire, one level up.

    **What the bound was guarding against is measured at zero.**  Over both live
    producers the label-position scan finds 12 and 8 ids and the family filter
    drops **none** of them, because `Testing.expectCond` brackets every label and
    every bracketed label is a scenario id.  So the bound cost the tree nothing
    and bought it nothing but the hole.

    It remains an over-approximation in the safe direction: a line that happens to
    bracket `XX-999` is reported, which is a false MISSING ROW rather than a false
    pass, and a suite that means it should add the row.
    """
    return {scenario_id
            for scenario_id in EMITTED_LABEL.findall(output_text)
            if SCENARIO_ID.match(scenario_id)}


def classify_fixture(path: Path) -> FixtureShape:
    """Read `path` once and decide which artefact shape it is.

    Manifest INTENT is either signal: a `# Suite:` declaration (the author says
    so) or content that is entirely rows (the file is one).  Given intent, the
    file must be a well-formed manifest -- every non-comment line a row, every
    row's fragment naming its own scenario, at least one row, and a declared
    producer -- or it is an error.  Absent intent it is a trace fixture, which is
    the only silent skip and the only correct one.
    """
    rows: list[tuple[str, str, str]] = []
    seen_ids: dict[str, int] = {}
    suite: str | None = None
    suite_lineno = 0
    malformed: list[str] = []
    for lineno, line in enumerate(
            path.read_text(encoding="utf-8").splitlines(), start=1):
        stripped = line.strip()
        if not stripped:
            continue
        if stripped.startswith("#"):
            decl = SUITE_DECL.match(stripped)
            if decl:
                # A manifest declares ONE producer, and `suite is not None` is a
                # presence check where the property is "exactly one".  Taking the
                # last silently redirects every fragment check: a copied or
                # merge-conflicted header points the gate at another suite, which
                # passes whenever that suite happens to emit the listed
                # fragments, while the real producer is never run.  Two
                # declarations classify the file two ways, and "two
                # classifications are none".
                if suite is not None:
                    malformed.append(
                        f"line {lineno} is a second `# Suite:` declaration "
                        f"({decl.group(1)!r}); line {suite_lineno} already "
                        f"declared {suite!r}, and a manifest has one producer"
                    )
                    continue
                suite = decl.group(1)
                suite_lineno = lineno
            continue
        match = MANIFEST_ROW.match(stripped)
        if match is None:
            malformed.append(f"line {lineno} is not a row: {stripped!r}")
            continue
        scenario_id, subsystem, fragment = match.groups()
        if SCENARIO_ID.match(scenario_id) is None:
            # `v0.35.139`: the FAMILY is what bounds the reverse reconciliation's
            # scan of the producer's output, so an id without one would take this
            # manifest out of that scan's domain silently -- the shape of defect
            # the reverse direction exists to close, arriving through its own
            # domain.  Every live row already matches, so requiring it is free.
            malformed.append(
                f"line {lineno}: scenario id {scenario_id!r} is not "
                f"`<FAMILY>-<number>` — the family is what bounds the scan that "
                f"reconciles the producer's emitted scenarios back to this "
                f"manifest, so an id without one leaves the manifest out of it"
            )
            continue
        if not fragment_names_scenario(scenario_id, fragment):
            malformed.append(
                f"line {lineno}: row {scenario_id}'s expected_trace_fragment "
                f"does not name {scenario_id}: {fragment!r}"
            )
            continue
        if scenario_id in seen_ids:
            # PR #897's review, `v0.35.139`: a repeated id is not a harmless
            # duplicate row.  The registry is keyed by id and can supply ONE
            # metadata entry, `scenario_ids_in` returns a SET so the repetition
            # is invisible to `validate-registry`, and `check_fragments` loops
            # rows, so two rows can both be credited to the same emitted line --
            # two declarations, one scenario, and nothing that could report it.
            malformed.append(
                f"line {lineno} repeats scenario id {scenario_id}, first "
                f"declared on line {seen_ids[scenario_id]} — the registry is "
                f"keyed by id and can describe one scenario per id, and the id "
                f"set both later checks read collapses the two"
            )
            continue
        seen_ids[scenario_id] = lineno
        rows.append((scenario_id, subsystem, fragment))

    declares = suite is not None
    content_is_rows = bool(rows) and not malformed
    if not declares and not content_is_rows:
        return FixtureShape(path)
    if not declares:
        return FixtureShape(path, error=(
            f"{path}: scenario-traceability manifest declares no producer; "
            f"add a `# Suite: <lake exe target>` header line so "
            f"scripts/test_tier2_trace.sh can check its "
            f"expected_trace_fragment column"
        ))
    if malformed:
        detail = "; ".join(malformed)
        return FixtureShape(path, error=(
            f"{path}: declares `# Suite: {suite}` but is not a well-formed "
            f"scenario-traceability manifest -- {detail}.  Fix the row (or the "
            f"header, if this is golden trace output); a file that declares a "
            f"producer is never swept as a trace fixture"
        ))
    if not rows:
        return FixtureShape(path, error=(
            f"{path}: declares `# Suite: {suite}` but has no "
            f"`SCENARIO_ID | SUBSYSTEM | expected_trace_fragment` rows, so "
            f"check-fragments would pass vacuously"
        ))
    return FixtureShape(path, manifest=Manifest(path, suite, rows))


def scenario_ids_in(path: Path) -> tuple[set[str], str | None]:
    """The scenario ids a fixture declares, DECIDED BY ITS SHAPE.

    The two forms are a manifest's pipe-delimited rows (`ID | SUBSYSTEM |
    fragment`) and the bracket form a trace fixture uses (`[ID] ...`), and which
    one a file is in is `classify_fixture`'s question.  This asked neither: it
    split **every** line on `|` and took `parts[0]` whenever there were three or
    more, so a golden output line such as `cap | badge | ok` put `cap` in
    `fixture_ids` and `validate-registry` failed against a registry that
    correctly has no such scenario.  Tier 0 passes `main_trace_smoke.expected`
    through here, so that is a live path rather than a hypothesis, and the
    direction -- a spurious failure -- makes a legitimate golden fixture
    unmaintainable rather than letting a bad one through.

    A manifest's ids come from `shape.manifest.rows`, which `classify_fixture`
    has **already parsed**, so this is also a de-duplication: re-splitting the
    rows here was one question with two answers, free to disagree about what a
    row is.

    Returns `(ids, error)`.  A file that DECLARES manifest intent and is not a
    well-formed manifest yields no ids and the classifier's own error, because
    reading it as golden output would silently take its rows' first fields as
    scenario ids -- the same fail-open one field over, and the reason
    `discover_manifests` treats that case as an error rather than a skip.
    """
    shape = classify_fixture(path)
    if shape.error is not None:
        return set(), shape.error
    if shape.manifest is not None:
        return {row[0] for row in shape.manifest.rows}, None
    ids: set[str] = set()
    for line in path.read_text(encoding="utf-8").splitlines():
        match = BRACKET_ID.match(line.strip())
        if match:
            ids.add(match.group(1))
    return ids, None


def fixture_ids_and_errors(paths: list[Path]) -> tuple[set[str], list[str]]:
    """The union of the scenario ids `paths` declare, and any classification errors.

    One helper because `validate-registry` and `generate-registry-stub` ask the
    same question and had two copies of the loop; the errors are returned rather
    than swallowed so both commands fail closed on a file neither shape fits.
    """
    ids: set[str] = set()
    errors: list[str] = []
    declared_by: dict[str, Path] = {}
    for path in paths:
        if not path.exists():
            continue
        found, error = scenario_ids_in(path)
        if error is not None:
            errors.append(error)
            continue
        # `|=` is where a CROSS-fixture repeat disappears (PR #897's review,
        # `v0.35.139`).  `classify_fixture` refuses a repeat within one manifest;
        # two fixtures declaring one id collapse here instead, and the registry
        # -- keyed by id -- then describes one of the two scenarios while
        # `validate-registry` compares sets and reports agreement.
        for scenario_id in sorted(found):
            first = declared_by.get(scenario_id)
            if first is not None:
                errors.append(
                    f"{path}: scenario id {scenario_id} is already declared by "
                    f"{first} — the registry is keyed by id and can describe "
                    f"one scenario per id, and the union both commands read "
                    f"collapses the two"
                )
                continue
            declared_by[scenario_id] = path
        ids |= found
    return ids, errors


def discover_manifests(directory: Path) -> tuple[list[Manifest], list[str]]:
    """Every `*.expected` under `directory` that is a manifest, plus errors.

    A file that declares manifest intent and is not a well-formed manifest is an
    ERROR, not a skip: the gate cannot ask whether its fragments are emitted, and
    silently dropping it would make the swept set smaller than the manifest set
    while the gate still reported PASS.  `classify_fixture` decides which case a
    file is in; this function only routes.
    """
    manifests: list[Manifest] = []
    errors: list[str] = []
    for path in sorted(directory.glob("*.expected")):
        shape = classify_fixture(path)
        if shape.error is not None:
            errors.append(shape.error)
        elif shape.manifest is not None:
            manifests.append(shape.manifest)
    return manifests, errors


def check_fragments(manifest: Manifest, output_text: str) -> list[str]:
    """Every row's fragment must be emitted ON A LINE THAT NAMES ITS SCENARIO.

    Containment rather than equality *within the line*, because the two manifests
    quote their fragments at different widths: one carries the whole emitted line
    (`robin-hood check passed [RH-001a ...]`) and the other only the label
    (`TPH-001a ...`).

    **Containment alone is not the relation** (PR #897 Codex review, `v0.35.119`).
    The row's claim is "*my* scenario was traced", and a bare `fragment in
    output_text` credits it to whichever line happens to contain those bytes.  A
    row whose fragment is short enough to be a prefix of another id -- `RH-001`
    against an emitted `[RH-0010a insert then get]` -- passes while scenario
    `RH-001` emitted nothing and could be deleted from the suite outright.  That is
    `v0.35.111`'s *a binding is a relation, not a containment* on the very same
    ids, one artefact over: `fragment_names_scenario` was written for exactly this
    relation, applied to the FRAGMENT at `v0.35.116`, and never swept onto the
    OUTPUT -- *when a fix names a relation, grep for every other place that asks
    it*.

    So the evidence is a line that carries the fragment **and** names this
    scenario at a label position, asked through the one function that owns the
    question rather than through a second spelling of it.  It costs the tree
    nothing, measured: `expectCond` emits `{tag} check passed [{label}]`, so the
    id sits immediately inside a `[` on every live row's line.

    That a row's fragment names its own scenario is still `classify_fixture`'s
    question and is asked before any suite runs -- a cross-wired row is a
    malformed manifest, not a failed comparison.  This check asks the same
    relation of the *producer's output*, which is a different subject.
    """
    errors: list[str] = []
    if not manifest.rows:
        errors.append(f"{manifest.path}: no manifest rows — the check would pass vacuously")
        return errors
    lines = output_text.splitlines()
    declared = {row[0] for row in manifest.rows}
    for scenario_id, _subsystem, fragment in manifest.rows:
        if not any(fragment in line and fragment_names_scenario(scenario_id, line)
                   for line in lines):
            errors.append(
                f"{manifest.path}: {scenario_id} expected_trace_fragment not emitted "
                f"by `lake exe {manifest.suite}` on a line naming {scenario_id} at a "
                f"label position: {fragment!r}"
            )
    # ...AND THE OTHER DIRECTION (PR #897's review, `v0.35.139`).  The loop above
    # asks only whether every ROW is traced, so a suite that adds a labelled
    # scenario without adding its row passes: every old fragment still matches,
    # and `validate-registry` sees only the id set the manifest itself declares.
    # The manifest claims to enumerate its producer's scenarios, and that claim
    # was made by nothing -- measured on the live tree, where
    # `two_phase_arch_suite` had emitted `TPH-015` under thirteen sub-case labels
    # and no row since it was written.
    for scenario_id in sorted(emitted_scenario_ids(output_text) - declared):
        errors.append(
            f"{manifest.path}: `lake exe {manifest.suite}` labels scenario "
            f"{scenario_id}, which this manifest does not declare — the manifest "
            f"is what the scenario registry enumerates, so an emitted scenario "
            f"with no row is one the registry silently stops describing"
        )
    return errors


def load_catalog(path: Path) -> dict:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def validate_catalog(catalog: dict, fixture_path: Path) -> list[str]:
    errors: list[str] = []

    for key in ("schema_version", "owner", "review_cadence", "scenarios"):
        if key not in catalog:
            errors.append(f"missing top-level key: {key}")

    scenarios = catalog.get("scenarios")
    if not isinstance(scenarios, list) or not scenarios:
        errors.append("scenarios must be a non-empty list")
        return errors

    fixture_text = fixture_path.read_text(encoding="utf-8")
    ids: set[str] = set()

    for index, scenario in enumerate(scenarios, start=1):
        prefix = f"scenario[{index}]"
        if not isinstance(scenario, dict):
            errors.append(f"{prefix} must be an object")
            continue

        for key in ("id", "subsystem", "risk_tags", "replay_tier", "expected_trace_fragment"):
            if key not in scenario:
                errors.append(f"{prefix} missing key: {key}")

        scenario_id = scenario.get("id")
        if not isinstance(scenario_id, str) or not scenario_id.strip():
            errors.append(f"{prefix} has invalid id")
        elif scenario_id in ids:
            errors.append(f"duplicate scenario id: {scenario_id}")
        else:
            ids.add(scenario_id)

        subsystem = scenario.get("subsystem")
        if not isinstance(subsystem, str) or not subsystem.strip():
            errors.append(f"{prefix} has invalid subsystem")

        risk_tags = scenario.get("risk_tags")
        if not isinstance(risk_tags, list) or not risk_tags:
            errors.append(f"{prefix} risk_tags must be non-empty list")
        elif any((not isinstance(tag, str) or not tag.strip()) for tag in risk_tags):
            errors.append(f"{prefix} has invalid risk tag entry")

        replay_tier = scenario.get("replay_tier")
        if replay_tier not in ALLOWED_TIERS:
            errors.append(f"{prefix} replay_tier must be one of: {sorted(ALLOWED_TIERS)}")

        seed = scenario.get("deterministic_seed")
        if replay_tier == "nightly":
            if not isinstance(seed, int) or seed < 0:
                errors.append(f"{prefix} nightly scenario requires non-negative deterministic_seed")
        elif seed is not None:
            errors.append(f"{prefix} non-nightly scenario must not include deterministic_seed")

        fragment = scenario.get("expected_trace_fragment")
        if not isinstance(fragment, str) or not fragment.strip():
            errors.append(f"{prefix} has invalid expected_trace_fragment")
        elif fragment not in fixture_text:
            errors.append(f"{prefix} expected_trace_fragment missing in fixture: {fragment}")

    return errors


def nightly_seeds(catalog: dict) -> list[int]:
    seeds = {
        scenario["deterministic_seed"]
        for scenario in catalog.get("scenarios", [])
        if scenario.get("replay_tier") == "nightly"
    }
    return sorted(seeds)


def manifest_fixture_paths(directory: Path) -> tuple[list[Path], list[str]]:
    """The scenario-traceability manifests under `directory`, DERIVED.

    The registry gate's second input used to be `--extra-fixtures`, a CALLER'S
    ENUMERATION, and `scripts/test_tier0_hygiene.sh` hand-listed the two
    manifests this tree happens to have.  A third one is discovered by
    `list-manifests` and by Tier 2's `check-fragments` -- both derived from
    `discover_manifests` -- while its scenario ids reached `validate_registry`
    from nowhere, so they could be absent from `scenario_registry.yaml` with every
    gate green.  That is an enumeration standing in for a derivation, with the
    derivation already written and one function away.

    Measured before taking it: `discover_manifests` returns exactly the two paths
    Tier 0 hand-listed, so deriving costs the tree nothing and removes the hole.

    **Fails closed.**  A discovery error yields no paths and the errors, because a
    partial list that reads as a clean pass is the silence `v0.35.111` found in
    this same discovery.
    """
    manifests, errors = discover_manifests(directory)
    if errors:
        return [], errors
    return [m.path for m in manifests], []


def validate_registry(fixture_path: Path, registry_path: Path,
                      extra_fixture_paths: list[Path] | None = None) -> list[str]:
    """WS-I1/R-03: Validate that fixture scenario IDs and registry are consistent.

    This reconciles the ID column only.  The `expected_trace_fragment` column of
    a manifest is a claim about a SUITE'S OUTPUT, which Tier 0 cannot evaluate
    because it runs before any build; `check-fragments`, run from Tier 2, is
    that relation.

    `extra_fixture_paths` is DERIVED by the caller from `manifest_fixture_paths`;
    the parameter stays so a witness can drive the relation over a synthetic
    directory.
    """
    errors: list[str] = []

    if not registry_path.exists():
        errors.append(f"registry not found: {registry_path}")
        return errors
    if not fixture_path.exists():
        errors.append(f"fixture not found: {fixture_path}")
        return errors

    fixture_ids, id_errors = fixture_ids_and_errors(
        [fixture_path] + (extra_fixture_paths or []))
    if id_errors:
        # A file whose SHAPE cannot be decided contributes no ids, so continuing
        # would report every registry entry as missing from the fixture -- a
        # hundred errors naming the wrong cause.
        return id_errors

    # Parse scenario IDs from registry (YAML-like: "  ID:" lines)
    registry_ids: set[str] = set()
    registry_text = registry_path.read_text(encoding="utf-8")
    for line in registry_text.splitlines():
        m = re.match(r"^  ([A-Z]+-\d+):", line)
        if m:
            registry_ids.add(m.group(1))

    # Check fixture IDs not in registry
    missing_in_registry = fixture_ids - registry_ids
    for sid in sorted(missing_in_registry):
        errors.append(f"fixture scenario ID not in registry: {sid}")

    # Check registry IDs not in fixture
    missing_in_fixture = registry_ids - fixture_ids
    for sid in sorted(missing_in_fixture):
        errors.append(f"registry scenario ID not in fixture: {sid}")

    return errors


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Scenario catalog utilities")
    parser.add_argument("command", choices=[
        "validate", "nightly-seeds", "validate-registry", "generate-registry-stub",
        "list-manifests", "check-fragments",
    ])
    parser.add_argument(
        "--catalog",
        default="tests/scenarios/scenario_catalog.json",
        help="Path to scenario catalog JSON",
    )
    parser.add_argument(
        "--fixture",
        default="tests/fixtures/main_trace_smoke.expected",
        help="Trace fixture path for validation",
    )
    parser.add_argument(
        "--registry",
        default="tests/fixtures/scenario_registry.yaml",
        help="Scenario registry path for validate-registry",
    )
    parser.add_argument(
        "--fixture-dir",
        default="tests/fixtures",
        help="Directory swept by list-manifests",
    )
    parser.add_argument(
        "--manifest",
        default=None,
        help="Scenario-traceability manifest for check-fragments",
    )
    parser.add_argument(
        "--output",
        default=None,
        help="Captured suite stdout for check-fragments",
    )
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()

    catalog_path = Path(args.catalog)
    fixture_path = Path(args.fixture)

    # `list-manifests` and `check-fragments` ask about fixtures and suite output
    # only, so they are answered before the catalog is read: making them depend
    # on `tests/scenarios/scenario_catalog.json` would couple the fragment
    # relation to an artefact it says nothing about.
    if args.command == "list-manifests":
        directory = Path(args.fixture_dir)
        if not directory.is_dir():
            print(f"error: fixture directory not found: {directory}", file=sys.stderr)
            return 1
        manifests, errors = discover_manifests(directory)
        if errors:
            print("scenario-traceability manifest discovery failed:", file=sys.stderr)
            for error in errors:
                print(f"- {error}", file=sys.stderr)
            return 1
        for manifest in manifests:
            print(f"{manifest.path}\t{manifest.suite}")
        return 0

    if args.command == "check-fragments":
        if args.manifest is None or args.output is None:
            print("error: check-fragments requires --manifest and --output",
                  file=sys.stderr)
            return 1
        manifest_path = Path(args.manifest)
        output_path = Path(args.output)
        if not manifest_path.exists():
            print(f"error: manifest not found: {manifest_path}", file=sys.stderr)
            return 1
        if not output_path.exists():
            print(f"error: captured output not found: {output_path}", file=sys.stderr)
            return 1
        shape = classify_fixture(manifest_path)
        if shape.error is not None:
            print(f"error: {shape.error}", file=sys.stderr)
            return 1
        if shape.manifest is None:
            print(f"error: not a scenario-traceability manifest: {manifest_path}",
                  file=sys.stderr)
            return 1
        manifest = shape.manifest
        errors = check_fragments(manifest, output_path.read_text(encoding="utf-8"))
        if errors:
            print("scenario-traceability fragment check failed:", file=sys.stderr)
            for error in errors:
                print(f"- {error}", file=sys.stderr)
            print("  the manifest's expected_trace_fragment column names a line the",
                  file=sys.stderr)
            print("  suite emits; a renamed assertion label strands it.  Fix the",
                  file=sys.stderr)
            print("  label or the manifest row — never delete the row.", file=sys.stderr)
            return 1
        print(f"fragment check passed: {manifest_path} "
              f"({len(manifest.rows)} fragments emitted by `lake exe {manifest.suite}`)")
        return 0

    if not catalog_path.exists():
        print(f"error: catalog not found: {catalog_path}", file=sys.stderr)
        return 1

    try:
        catalog = load_catalog(catalog_path)
    except JSONDecodeError as exc:
        print(f"error: invalid JSON in {catalog_path}: {exc}", file=sys.stderr)
        return 1

    if args.command == "validate":
        if not fixture_path.exists():
            print(f"error: fixture not found: {fixture_path}", file=sys.stderr)
            return 1
        errors = validate_catalog(catalog, fixture_path)
        if errors:
            print("scenario catalog validation failed:", file=sys.stderr)
            for error in errors:
                print(f"- {error}", file=sys.stderr)
            return 1
        print(
            f"scenario catalog validation passed ({len(catalog['scenarios'])} scenarios; owner={catalog['owner']}; review={catalog['review_cadence']})"
        )
        return 0

    if args.command == "validate-registry":
        registry_path = Path(args.registry)
        # DERIVED, never a caller's list: see `manifest_fixture_paths`.
        extra_fixtures, discovery_errors = manifest_fixture_paths(
            Path(args.fixture_dir))
        if discovery_errors:
            print("scenario registry validation failed:", file=sys.stderr)
            for error in discovery_errors:
                print(f"- {error}", file=sys.stderr)
            return 1
        errors = validate_registry(fixture_path, registry_path, extra_fixtures)
        if errors:
            print("scenario registry validation failed:", file=sys.stderr)
            for error in errors:
                print(f"- {error}", file=sys.stderr)
            return 1
        print("scenario registry validation passed")
        return 0

    if args.command == "generate-registry-stub":
        # AN11-F (LOW) — generator rule for `tests/fixtures/scenario_registry.yaml`.
        # Scans the trace fixtures for scenario IDs that are NOT yet in the
        # registry and emits a YAML stub the maintainer can paste into the
        # canonical registry.  This is *not* a full regeneration (registry
        # entries carry hand-curated `source` / `function` / `subsystem`
        # / `description` fields the script cannot infer) — it surfaces
        # the missing-ID list with default placeholders so a fixture edit
        # cannot land without a registry update.
        registry_path = Path(args.registry)
        # The SAME derivation the validator reads, so the stub cannot propose a
        # different fixture set from the one the gate reconciles.
        extra_fixtures, discovery_errors = manifest_fixture_paths(
            Path(args.fixture_dir))
        if discovery_errors:
            print("scenario registry stub generation failed:", file=sys.stderr)
            for error in discovery_errors:
                print(f"- {error}", file=sys.stderr)
            return 1
        fixture_ids, id_errors = fixture_ids_and_errors(
            [fixture_path] + extra_fixtures)
        if id_errors:
            print("scenario registry stub generation failed:", file=sys.stderr)
            for error in id_errors:
                print(f"- {error}", file=sys.stderr)
            return 1
        registry_ids: set[str] = set()
        if registry_path.exists():
            for line in registry_path.read_text(encoding="utf-8").splitlines():
                m = re.match(r"^  ([A-Z]+-\d+):", line)
                if m:
                    registry_ids.add(m.group(1))
        missing = sorted(fixture_ids - registry_ids)
        if not missing:
            print(
                f"scenario registry up-to-date "
                f"({len(fixture_ids)} fixture IDs all present)"
            )
            return 0
        print("# AN11-F: missing scenario registry entries (paste into")
        print(f"# {registry_path} under the `scenarios:` block):")
        print()
        for sid in missing:
            print(f"  {sid}:")
            print("    source: TODO/path/to/source.lean")
            print("    function: TODO_function_name")
            print("    subsystem: TODO_subsystem")
            print(f'    description: "TODO: short description for {sid}"')
        return 1

    for seed in nightly_seeds(catalog):
        print(seed)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
