#!/usr/bin/env python3
"""Validate and query WS-B11 scenario catalog metadata."""

from __future__ import annotations

import argparse
import json
from json import JSONDecodeError
from pathlib import Path
import sys

ALLOWED_TIERS = {"smoke", "nightly"}


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


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Scenario catalog utilities")
    parser.add_argument("command", choices=["validate", "nightly-seeds"])
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
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()

    catalog_path = Path(args.catalog)
    fixture_path = Path(args.fixture)

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

    for seed in nightly_seeds(catalog):
        print(seed)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
