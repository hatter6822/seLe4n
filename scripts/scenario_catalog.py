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

`v0.35.111` corrected three presence-for-relation defects in that machinery,
every one of them the class it was written to close.  `check-fixture-index`
searched the README table's JOINED text, so an unlisted fixture passed whenever
any cell quoted a longer name containing it — its own `.sha256` companion, for
one — and ran only over the directory, so a row naming a deleted file was never
inspected; the membership question is now over PARSED CELLS of the `## Files`
section, in both directions.  `discover_manifests` skipped a file it could not
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

    The id must occur followed by an optional lowercase sub-case letter and then
    a character that cannot continue an id, so `RH-001` matches `RH-001a insert`
    and `[RH-001]` and does NOT match `RH-0010a ...`: a bare `in` test would
    accept a longer id that merely has this one as a prefix, which is the same
    defect one character down.
    """
    pattern = re.compile(re.escape(scenario_id) + r"[a-z]?(?![0-9A-Za-z-])")
    return pattern.search(fragment) is not None


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
    suite: str | None = None
    malformed: list[str] = []
    for lineno, line in enumerate(
            path.read_text(encoding="utf-8").splitlines(), start=1):
        stripped = line.strip()
        if not stripped:
            continue
        if stripped.startswith("#"):
            decl = SUITE_DECL.match(stripped)
            if decl:
                suite = decl.group(1)
            continue
        match = MANIFEST_ROW.match(stripped)
        if match is None:
            malformed.append(f"line {lineno} is not a row: {stripped!r}")
            continue
        scenario_id, subsystem, fragment = match.groups()
        if not fragment_names_scenario(scenario_id, fragment):
            malformed.append(
                f"line {lineno}: row {scenario_id}'s expected_trace_fragment "
                f"does not name {scenario_id}: {fragment!r}"
            )
            continue
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


def scenario_ids_in(path: Path) -> set[str]:
    """The scenario ids a fixture declares, in either of the two forms.

    Pipe-delimited manifest rows (`ID | SUBSYSTEM | fragment`) and the bracket
    form a trace fixture uses (`[ID] ...`).  One parser, because
    `validate-registry` and `generate-registry-stub` ask the same question and
    had grown two copies of the answer.
    """
    ids: set[str] = set()
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split("|")
        if len(parts) >= 3:
            ids.add(parts[0].strip())
        else:
            match = BRACKET_ID.match(line)
            if match:
                ids.add(match.group(1))
    return ids


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


# Files under `tests/fixtures/` that are deliberately NOT rows of the README's
# `## Files` table, each with the reason.  Reconciled in BOTH directions: a stale
# entry naming a file that no longer exists fails as loudly as an unclassified
# file, because an exemption nobody checks reads exactly like coverage.
FIXTURE_INDEX_EXEMPT = {
    "scenario_registry.yaml":
        "the scenario registry the manifests' ID columns are reconciled AGAINST, "
        "not a fixture compared against program output; described in the README's "
        "prose instead",
}

# The heading whose table `check_fixture_index` reads.  The read is SCOPED to that
# section, because a second table elsewhere in the README would otherwise widen
# the declared set: a filename backticked in a table of gates would satisfy a
# fixture's membership without the `## Files` table ever naming it.
FIXTURE_TABLE_HEADING = "## Files"
# A markdown heading, so the scoped read knows where the section ends.
MD_HEADING = re.compile(r"^#{1,6}\s")
# A backticked token naming a file: no path separator and at least one dot, so a
# bare word and a repository path are both excluded.  Applied to the `Fixture`
# and `Hash` CELLS only -- prose in the `Used by` column contributes nothing
# whatever it quotes, which is what keeps a mention from standing in for a row.
TABLE_FILENAME = re.compile(r"`([^`/\s]+\.[^`/\s]+)`")


def fixture_table_filenames(readme: Path) -> tuple[set[str], list[str]]:
    """The filenames the README's `## Files` table declares, plus errors.

    The table's first two columns name a fixture and its hash companion; the
    third describes the gate that compares it.  Reading CELLS rather than
    searching the joined table text is the whole point: a substring test over the
    table accepted a fixture whose own row is absent but whose `.sha256`
    companion is named in a neighbouring cell, so the file was reported as
    indexed while no row said which gate reads it.
    """
    lines = readme.read_text(encoding="utf-8").splitlines()
    start: int | None = None
    for index, line in enumerate(lines):
        if line.strip() == FIXTURE_TABLE_HEADING:
            start = index + 1
            break
    if start is None:
        return set(), [
            f"{readme}: no `{FIXTURE_TABLE_HEADING}` section — that table is "
            f"what check_fixture_index reconciles the directory against, and "
            f"the question cannot be answered without it"
        ]
    declared: set[str] = set()
    for line in lines[start:]:
        if MD_HEADING.match(line):
            break
        stripped = line.strip()
        if not stripped.startswith("|"):
            continue
        # `| a | b | c |`.split("|") == ['', ' a ', ' b ', ' c ', ''], so the
        # `Fixture` and `Hash` cells are [1:3].  The header and separator rows
        # carry no backticks and so declare nothing, with no special case.
        for cell in stripped.split("|")[1:3]:
            declared |= set(TABLE_FILENAME.findall(cell))
    return declared, []


def check_fixture_index(directory: Path, readme: Path,
                        exempt: dict[str, str] | None = None) -> list[str]:
    """Every file in `directory` is a row of its `README.md` table, or exempt.

    The README's `## Files` table claims to enumerate the fixture directory and
    to name each fixture's consumer, and it is the only place a reader learns
    which gate compares a given fixture.  It is hand-written, so it is an
    ENUMERATION standing in for a derivation, and at `v0.35.109` it was missing
    `syscall_return_shape.expected` (whose consumers are a Lean suite *and* the
    Rust ABI conformance test) and `qemu_boot_expected.txt` — while naming, for
    two fixtures, consumers that do not read them at all.  Deriving the set from
    the directory is what makes the next omission fail on the day it is made.

    Reconciled in BOTH directions, over PARSED CELLS.  Membership is a table row
    naming the file in its `Fixture` or `Hash` column, never a mention: the first
    cut joined the table's lines into one blob and asked whether the filename
    occurred anywhere in it, so an unlisted fixture passed whenever any cell
    quoted a longer name containing it -- its own `.sha256` companion, for one --
    and a row naming a DELETED file was never inspected at all, because the loop
    ran over the directory.  Both halves are the presence-for-relation defect
    this function was written to close, one level down.

    `exempt` defaults to `FIXTURE_INDEX_EXEMPT`, which is this tree's own
    classification; the CLI never passes anything else, and the parameter exists
    so a witness can exercise the reconciliation on a synthetic directory without
    inheriting the real tree's contents.
    """
    if exempt is None:
        exempt = FIXTURE_INDEX_EXEMPT
    if not readme.exists():
        return [f"{readme}: not found"]
    declared, errors = fixture_table_filenames(readme)
    if errors:
        return errors
    present = {p.name for p in directory.iterdir() if p.is_file()}
    accounted = declared | set(exempt) | {readme.name}
    for name in sorted(present - accounted):
        errors.append(
            f"{directory / name}: not a row of {readme}'s "
            f"`{FIXTURE_TABLE_HEADING}` table; add it with the gate that "
            f"compares it, or classify it in FIXTURE_INDEX_EXEMPT with a reason"
        )
    for name in sorted(declared - present):
        errors.append(
            f"{directory / name}: named by a row of {readme}'s "
            f"`{FIXTURE_TABLE_HEADING}` table but absent from the directory — "
            f"a row nothing backs describes a gate reading a file that is gone"
        )
    for name, reason in sorted(exempt.items()):
        if name not in present:
            errors.append(
                f"{directory / name}: stale FIXTURE_INDEX_EXEMPT entry "
                f"({reason}) — the file is gone"
            )
        elif name in declared:
            errors.append(
                f"{directory / name}: classified BOTH as a "
                f"FIXTURE_INDEX_EXEMPT entry ({reason}) and as a row of "
                f"{readme}'s `{FIXTURE_TABLE_HEADING}` table — one of the two "
                f"is wrong, and a file with two classifications has none"
            )
    return errors


def check_fragments(manifest: Manifest, output_text: str) -> list[str]:
    """Every row's fragment must occur in `output_text`.

    Containment rather than equality, because the two manifests quote their
    fragments at different widths: one carries the whole emitted line
    (`robin-hood check passed [RH-001a ...]`) and the other only the label
    (`TPH-001a ...`).

    That the fragment names its own row's scenario is `classify_fixture`'s
    question, not this one: a cross-wired row is a malformed manifest rather than
    a failed comparison, so it fails before any suite is run.
    """
    errors: list[str] = []
    if not manifest.rows:
        errors.append(f"{manifest.path}: no manifest rows — the check would pass vacuously")
        return errors
    for scenario_id, _subsystem, fragment in manifest.rows:
        if fragment not in output_text:
            errors.append(
                f"{manifest.path}: {scenario_id} expected_trace_fragment not emitted "
                f"by `lake exe {manifest.suite}`: {fragment!r}"
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


def validate_registry(fixture_path: Path, registry_path: Path,
                      extra_fixture_paths: list[Path] | None = None) -> list[str]:
    """WS-I1/R-03: Validate that fixture scenario IDs and registry are consistent.

    This reconciles the ID column only.  The `expected_trace_fragment` column of
    a manifest is a claim about a SUITE'S OUTPUT, which Tier 0 cannot evaluate
    because it runs before any build; `check-fragments`, run from Tier 2, is
    that relation.
    """
    errors: list[str] = []

    if not registry_path.exists():
        errors.append(f"registry not found: {registry_path}")
        return errors
    if not fixture_path.exists():
        errors.append(f"fixture not found: {fixture_path}")
        return errors

    fixture_ids: set[str] = set()
    for fp in [fixture_path] + (extra_fixture_paths or []):
        if fp.exists():
            fixture_ids |= scenario_ids_in(fp)

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
        "list-manifests", "check-fragments", "check-fixture-index",
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
        "--extra-fixtures",
        nargs="*",
        default=[],
        help="Additional fixture files for validate-registry (e.g., suite-specific fixtures)",
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

    if args.command == "check-fixture-index":
        directory = Path(args.fixture_dir)
        if not directory.is_dir():
            print(f"error: fixture directory not found: {directory}", file=sys.stderr)
            return 1
        errors = check_fixture_index(directory, directory / "README.md")
        if errors:
            print("fixture index check failed:", file=sys.stderr)
            for error in errors:
                print(f"- {error}", file=sys.stderr)
            return 1
        count = sum(1 for f in directory.iterdir()
                    if f.is_file() and f.name != "README.md")
        print(f"fixture index check passed ({count} files named in "
              f"{directory / 'README.md'})")
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
        extra_fixtures = [Path(p) for p in args.extra_fixtures]
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
        extra_fixtures = [Path(p) for p in args.extra_fixtures]
        fixture_ids: set[str] = set()
        for fp in [fixture_path] + extra_fixtures:
            if fp.exists():
                fixture_ids |= scenario_ids_in(fp)
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
