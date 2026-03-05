#!/usr/bin/env python3
"""Generate a machine-readable seLe4n codebase map for website consumption.

Outputs JSON with:
- repository sync metadata (commit SHA + cache key)
- every Lean module under SeLe4n/ plus Main/tests
- declaration inventory (def/theorem/lemma/abbrev/instance/structure/inductive/class)

This lets consumers invalidate stale local caches whenever commit SHA changes.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
from dataclasses import asdict, dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DECL_RE = re.compile(
    r"^\s*(?:@[\w\[\]\.\s]+\s+)?(?:private\s+)?"
    r"(?P<kind>def|theorem|lemma|abbrev|instance|structure|inductive|class)\s+"
    r"(?P<name>[A-Za-z0-9_'.]+)"
)


@dataclass
class Decl:
    kind: str
    name: str
    line: int


@dataclass
class ModuleEntry:
    module: str
    path: str
    declarations: list[Decl]


def run_git(args: list[str]) -> str:
    out = subprocess.run(["git", *args], cwd=ROOT, text=True, capture_output=True, check=True)
    return out.stdout.strip()


def module_name(path: Path) -> str:
    rel = path.relative_to(ROOT).with_suffix("")
    return ".".join(rel.parts)


def parse_declarations(path: Path) -> list[Decl]:
    decls: list[Decl] = []
    for i, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        m = DECL_RE.match(line)
        if m:
            decls.append(Decl(kind=m.group("kind"), name=m.group("name"), line=i))
    return decls


def lean_files() -> list[Path]:
    prod = sorted((ROOT / "SeLe4n").rglob("*.lean"))
    extras = [ROOT / "Main.lean"] + sorted((ROOT / "tests").rglob("*.lean"))
    return prod + extras


def build_map() -> dict:
    commit_sha = run_git(["rev-parse", "HEAD"])
    tree_sha = run_git(["rev-parse", "HEAD^{tree}"])
    branch = run_git(["rev-parse", "--abbrev-ref", "HEAD"])
    committed_at_utc = run_git(["show", "-s", "--format=%cI", "HEAD"])

    modules: list[ModuleEntry] = []
    for path in lean_files():
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
            "branch": branch,
            "commit_sha": commit_sha,
            "tree_sha": tree_sha,
            "cache_key": f"{commit_sha}:{tree_sha}",
        },
        "committed_at_utc": committed_at_utc,
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


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        default="docs/codebase_map.json",
        help="Output JSON path relative to repository root (default: docs/codebase_map.json)",
    )
    parser.add_argument("--pretty", action="store_true", help="Pretty-print JSON output")
    args = parser.parse_args()

    payload = build_map()
    output = ROOT / args.output
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(
        json.dumps(payload, indent=2 if args.pretty else None, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


if __name__ == "__main__":
    main()
