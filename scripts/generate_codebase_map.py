#!/usr/bin/env python3
"""Generate a machine-readable seLe4n codebase map for website consumption.

Outputs JSON with:
- repository identity metadata
- source-derived sync metadata (stable across branches/merge commits)
- every Lean module under SeLe4n/ plus Main/tests
- declaration inventory (def/theorem/lemma/abbrev/instance/structure/inductive/class)

This lets consumers invalidate stale local caches whenever Lean declaration
surface changes, while avoiding branch/merge-only churn.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from dataclasses import asdict, dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DECL_RE = re.compile(
    r"^\s*(?:@[\w\[\]\.\s]+\s+)?(?:private\s+)?"
    r"(?P<kind>def|theorem|lemma|abbrev|instance|structure|inductive|class)\s+"
    r"(?P<name>[A-Za-z0-9_'.]+)"
)


@dataclass(frozen=True, slots=True)
class Decl:
    kind: str
    name: str
    line: int


@dataclass(frozen=True, slots=True)
class ModuleEntry:
    module: str
    path: str
    declarations: list[Decl]


def module_name(path: Path) -> str:
    rel = path.relative_to(ROOT).with_suffix("")
    return ".".join(rel.parts)


def parse_declarations(path: Path) -> list[Decl]:
    decls: list[Decl] = []
    with path.open(encoding="utf-8") as handle:
        for i, line in enumerate(handle, start=1):
            m = DECL_RE.match(line)
            if m:
                decls.append(Decl(kind=m.group("kind"), name=m.group("name"), line=i))
    return decls


def lean_files() -> list[Path]:
    prod = sorted((ROOT / "SeLe4n").rglob("*.lean"))
    test_files = sorted((ROOT / "tests").rglob("*.lean"))
    extras = [ROOT / "Main.lean"] if (ROOT / "Main.lean").exists() else []
    return prod + extras + test_files


def source_fingerprint(paths: list[Path]) -> str:
    """Compute a deterministic digest tied to Lean declaration sources only."""
    digest = hashlib.sha256()
    for path in paths:
        rel = path.relative_to(ROOT).as_posix()
        digest.update(rel.encode("utf-8"))
        digest.update(b"\0")
        digest.update(path.read_bytes())
        digest.update(b"\0")
    return digest.hexdigest()


def run_git(args: list[str]) -> str:
    out = subprocess.run(["git", *args], cwd=ROOT, text=True, capture_output=True, check=True)
    return out.stdout.strip()


def git_head_metadata() -> dict[str, str]:
    return {
        "branch": run_git(["rev-parse", "--abbrev-ref", "HEAD"]),
        "commit_sha": run_git(["rev-parse", "HEAD"]),
        "tree_sha": run_git(["rev-parse", "HEAD^{tree}"]),
        "committed_at_utc": run_git(["show", "-s", "--format=%cI", "HEAD"]),
    }


def normalized_for_check(payload: dict) -> dict:
    """Return the subset that must remain stable for docs-sync checks.

    `repository.head` is intentionally excluded because branch/commit metadata is
    expected to change across PR branch updates and merge commits.
    """
    repository = payload.get("repository", {})
    normalized_repository = {
        "name": repository.get("name"),
        "url": repository.get("url"),
    }
    return {
        "schema_version": payload.get("schema_version"),
        "repository": normalized_repository,
        "source_sync": payload.get("source_sync"),
        "summary": payload.get("summary"),
        "modules": payload.get("modules"),
    }


def build_map() -> dict:
    paths = lean_files()
    source_digest = source_fingerprint(paths)

    modules: list[ModuleEntry] = []
    for path in paths:
        modules.append(
            ModuleEntry(
                module=module_name(path),
                path=str(path.relative_to(ROOT)),
                declarations=parse_declarations(path),
            )
        )

    decl_total = sum(len(m.declarations) for m in modules)
    return {
        "schema_version": "1.0.0",
        "repository": {
            "name": "hatter6822/seLe4n",
            "url": "https://github.com/hatter6822/seLe4n",
            "head": git_head_metadata(),
        },
        "source_sync": {
            "scope": ["SeLe4n/**/*.lean", "Main.lean", "tests/**/*.lean"],
            "digest_algorithm": "sha256",
            "source_digest": source_digest,
        },
        "summary": {
            "module_count": len(modules),
            "declaration_count": decl_total,
        },
        "modules": [
            {
                "module": m.module,
                "path": m.path,
                "declaration_count": len(m.declarations),
                "declarations": [asdict(d) for d in m.declarations],
            }
            for m in modules
        ],
    }


def render_json(payload: dict, pretty: bool) -> str:
    return json.dumps(payload, indent=2 if pretty else None, ensure_ascii=False) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        default="docs/codebase_map.json",
        help="Output JSON path relative to repository root (default: docs/codebase_map.json)",
    )
    parser.add_argument("--pretty", action="store_true", help="Pretty-print JSON output")
    parser.add_argument(
        "--check",
        action="store_true",
        help="Fail if output file is out of date instead of writing it",
    )
    args = parser.parse_args()

    payload = build_map()
    output = ROOT / args.output
    rendered = render_json(payload, pretty=args.pretty)

    if args.check:
        if not output.exists():
            print(
                f"{output.relative_to(ROOT)} is stale. Regenerate with: "
                f"./scripts/generate_codebase_map.py {'--pretty ' if args.pretty else ''}--output {args.output}",
                file=sys.stderr,
            )
            return 1

        existing_payload = json.loads(output.read_text(encoding="utf-8"))
        if normalized_for_check(existing_payload) != normalized_for_check(payload):
            print(
                f"{output.relative_to(ROOT)} is stale. Regenerate with: "
                f"./scripts/generate_codebase_map.py {'--pretty ' if args.pretty else ''}--output {args.output}",
                file=sys.stderr,
            )
            return 1
        return 0

    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(rendered, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
