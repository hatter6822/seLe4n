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
against itself, not against the program.  `list-manifests` and `check-fragments`
are the relation, run from `scripts/test_tier2_trace.sh`, which is where this
tree answers "does a fixture agree with the program".
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


def parse_manifest(path: Path) -> Manifest | None:
    """Parse `path` as a scenario-traceability manifest, or return None.

    A file is a manifest when it has at least one row and EVERY non-empty,
    non-comment line is a row — so a trace fixture, whose lines are suite
    output, is never mistaken for one.  Classification is by content, not by
    filename: that is what makes the swept set derived.
    """
    rows: list[tuple[str, str, str]] = []
    suite: str | None = None
    for line in path.read_text(encoding="utf-8").splitlines():
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
            return None
        rows.append((match.group(1), match.group(2), match.group(3)))
    if not rows:
        return None
    return Manifest(path, suite, rows)


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

    A manifest carrying no `# Suite:` declaration is an ERROR, not a skip: the
    gate cannot ask whether its fragments are emitted without knowing what emits
    them, and silently dropping it would make the swept set smaller than the
    manifest set while the gate still reported PASS.
    """
    manifests: list[Manifest] = []
    errors: list[str] = []
    for path in sorted(directory.glob("*.expected")):
        manifest = parse_manifest(path)
        if manifest is None:
            continue
        if manifest.suite is None:
            errors.append(
                f"{path}: scenario-traceability manifest declares no producer; "
                f"add a `# Suite: <lake exe target>` header line so "
                f"scripts/test_tier2_trace.sh can check its "
                f"expected_trace_fragment column"
            )
            continue
        manifests.append(manifest)
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

    Membership is a TABLE ROW, not a mention: a fixture named in passing in the
    prose tells a reader nothing about which gate compares it, so accepting one
    would be a presence check standing in for the relation the table asserts.

    `exempt` defaults to `FIXTURE_INDEX_EXEMPT`, which is this tree's own
    classification; the CLI never passes anything else, and the parameter exists
    so a witness can exercise the reconciliation on a synthetic directory without
    inheriting the real tree's contents.
    """
    if exempt is None:
        exempt = FIXTURE_INDEX_EXEMPT
    errors: list[str] = []
    if not readme.exists():
        return [f"{readme}: not found"]
    rows = "\n".join(
        line for line in readme.read_text(encoding="utf-8").splitlines()
        if line.lstrip().startswith("|")
    )
    present = {p.name for p in directory.iterdir() if p.is_file()}
    for name in sorted(present):
        if name == readme.name or name in exempt:
            continue
        if name not in rows:
            errors.append(
                f"{directory / name}: not a row of {readme}'s `## Files` table; "
                f"add it with the gate that compares it, or classify it in "
                f"FIXTURE_INDEX_EXEMPT with a reason"
            )
    for name, reason in sorted(exempt.items()):
        if name not in present:
            errors.append(
                f"{directory / name}: stale FIXTURE_INDEX_EXEMPT entry "
                f"({reason}) — the file is gone"
            )
    return errors


def check_fragments(manifest: Manifest, output_text: str) -> list[str]:
    """Every row's fragment must occur in `output_text`.

    Containment rather than equality, because the two manifests quote their
    fragments at different widths: one carries the whole emitted line
    (`robin-hood check passed [RH-001a ...]`) and the other only the label
    (`TPH-001a ...`).
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
        manifest = parse_manifest(manifest_path)
        if manifest is None:
            print(f"error: not a scenario-traceability manifest: {manifest_path}",
                  file=sys.stderr)
            return 1
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
