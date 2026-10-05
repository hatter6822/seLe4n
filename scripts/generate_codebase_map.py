#!/usr/bin/env python3
"""Generate a machine-readable seLe4n codebase map for website consumption.

Outputs JSON with:
- repository identity metadata
- source-derived sync metadata (stable across branches/merge commits)
- every Lean module under SeLe4n/ plus Main/tests
- declaration inventory (def/theorem/abbrev/instance/opaque/axiom/example/
  structure/inductive/class, and `where` helpers), each under the name it is
  declared with and its namespace-qualified `full_name`
- `called`: the declarations each one's text refers to, by full name, resolved
  the way Lean resolves names (see `scripts/lean_declarations.py`)

This lets consumers invalidate stale local caches whenever Lean declaration
surface changes, while avoiding branch/merge-only churn.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import multiprocessing
import os
import subprocess
import sys
from dataclasses import asdict, dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(__file__).resolve().parent))

from lean_declarations import Corpus, LexError, instance_name, parse_file, references  # noqa: E402,F401

SCHEMA_VERSION = "2.0.0"
PROJECT_ROOT = "SeLe4n"
# Constructors and structure fields resolve references; they are not entries.
_MEMBER_KINDS = {"ctor", "field"}


@dataclass(frozen=True, slots=True)
class Decl:
    kind: str
    name: str
    full_name: str | None
    line: int
    called: list[str]


@dataclass(frozen=True, slots=True)
class ModuleEntry:
    module: str
    path: str
    declarations: list[Decl]


def module_name(path: Path) -> str:
    rel = path.relative_to(ROOT).with_suffix("")
    return ".".join(rel.parts)


# Inherited by forked workers rather than pickled to them: the sources and,
# for the second pass, the finished corpus.
_SHARED: dict = {}


def _read_module(module: str) -> tuple[str, list, list[str]]:
    fp = parse_file(_SHARED["sources"][module], module)
    for d in fp.decls:
        if d.kind == "instance" and not d.full_name:
            # The header travels with the declaration: naming it needs the
            # whole corpus, which only the parent has.
            d.header_toks = fp.toks[d.header[0]:d.header[1]]
    return module, fp.decls, fp.imports


def _resolve_module(module: str) -> tuple[str, list[Decl]]:
    corpus = _SHARED["corpus"]
    toks = parse_file(_SHARED["sources"][module], module).toks
    corpus.enter(module)
    return module, [
        Decl(
            kind=d.kind,
            name=d.name,
            full_name=d.full_name or None,
            line=d.line,
            called=references(toks, d, corpus) if d.full_name else [],
        )
        for d in corpus.files[module]
        if d.kind not in _MEMBER_KINDS
    ]


def _map(fn, items: list[str], jobs: int) -> list:
    """`map`, across forked processes when there is more than one job.

    The result does not depend on `jobs`: every module is read and resolved
    independently, against the same corpus, and returned in input order.
    """
    if jobs > 1 and len(items) > 1 and "fork" in multiprocessing.get_all_start_methods():
        with multiprocessing.get_context("fork").Pool(jobs) as pool:
            return pool.map(fn, items, chunksize=max(1, len(items) // (jobs * 8)))
    return [fn(item) for item in items]


def build_declarations(sources: dict[str, str], jobs: int = 1) -> dict[str, list[Decl]]:
    """Declarations per module, with references resolved across the corpus.

    `sources` maps module name to source text.  Two passes: every file is read
    into the corpus first, so that a reference resolves against declarations
    later in the walk as well as earlier ones.
    """
    modules = list(sources)
    _SHARED["sources"] = sources
    corpus = Corpus()
    try:
        for module, decls, imports in _map(_read_module, modules, jobs):
            corpus.add_file(module, decls, imports)

        # Anonymous instances are named once the corpus is complete: the name
        # Lean generates depends on what the instance's type refers to.
        for module in modules:
            corpus.enter(module)
            for d in corpus.files[module]:
                if d.kind == "instance" and not d.full_name:
                    full = instance_name(d.header_toks, d, corpus, PROJECT_ROOT)
                    if full:
                        d.full_name = full
                        d.name = full[len(d.namespace) + 1:] if d.namespace else full
                        corpus.add(d)

        _SHARED["corpus"] = corpus
        return dict(_map(_resolve_module, modules, jobs))
    finally:
        _SHARED.clear()


def parse_declarations(path: Path) -> list[Decl]:
    """The declarations of one file, references resolved within that file."""
    return build_declarations({module_name(path) if path.is_relative_to(ROOT) else path.stem:
                               path.read_text(encoding="utf-8")}).popitem()[1]


def lean_files() -> list[Path]:
    prod = sorted((ROOT / "SeLe4n").rglob("*.lean"))
    test_files = sorted((ROOT / "tests").rglob("*.lean"))
    extras = [ROOT / "Main.lean"] if (ROOT / "Main.lean").exists() else []
    return prod + extras + test_files


def source_fingerprint(paths_or_cache, paths: list[Path] | None = None) -> str:
    """Compute a deterministic digest tied to Lean declaration sources only.

    Accepts either:
    - ``source_fingerprint(file_bytes_dict, paths)``  (internal fast path)
    - ``source_fingerprint(paths_list)``               (public backward-compat API)
    """
    if paths is None:
        # Backward-compatible: paths_or_cache is list[Path]
        path_list: list[Path] = paths_or_cache  # type: ignore[assignment]
        digest = hashlib.sha256()
        for path in path_list:
            rel = path.relative_to(ROOT).as_posix()
            digest.update(rel.encode("utf-8"))
            digest.update(b"\0")
            digest.update(path.read_bytes())
            digest.update(b"\0")
        return digest.hexdigest()

    # Fast path: file_bytes cache provided
    file_bytes: dict[Path, bytes] = paths_or_cache  # type: ignore[assignment]
    digest = hashlib.sha256()
    for path in paths:
        rel = path.relative_to(ROOT).as_posix()
        digest.update(rel.encode("utf-8"))
        digest.update(b"\0")
        digest.update(file_bytes[path])
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
    """Return the subset that must remain stable for `--check`.

    ``repository.head`` is intentionally excluded because branch/commit metadata
    is expected to change across PR branch updates and merge commits.
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
        "readme_sync": payload.get("readme_sync"),
        "modules": payload.get("modules"),
    }


def build_map() -> dict:
    paths = lean_files()

    # ---- Single-pass file I/O: read every file exactly once ----
    file_bytes: dict[Path, bytes] = {}
    file_lines: dict[Path, list[str]] = {}
    file_text: dict[Path, str] = {}
    for path in paths:
        raw = path.read_bytes()
        file_bytes[path] = raw
        file_text[path] = raw.decode("utf-8")
        file_lines[path] = file_text[path].splitlines()

    source_digest = source_fingerprint(file_bytes, paths)

    # ---- Declarations and the references between them ----
    names = {path: module_name(path) for path in paths}
    by_module = build_declarations({names[p]: file_text[p] for p in paths}, jobs=os.cpu_count() or 1)
    modules = [
        ModuleEntry(module=names[p], path=str(p.relative_to(ROOT)), declarations=by_module[names[p]])
        for p in paths
    ]

    # ---- Summary metrics (computed from cached data, no re-reads) ----
    prod_paths = [p for p in paths if not str(p.relative_to(ROOT)).startswith("tests/")]
    test_paths = [p for p in paths if str(p.relative_to(ROOT)).startswith("tests/")]

    prod_loc = sum(len(file_lines[p]) for p in prod_paths)
    test_loc = sum(len(file_lines[p]) for p in test_paths)

    # Counted off the declaration inventory, not a line pattern: the pattern it
    # replaces counted prose lines inside doc comments that begin with
    # "theorem" and missed every `protected`/`noncomputable`/`@[…]`-prefixed one.
    prod_modules = {names[p] for p in prod_paths}
    proved_count = sum(
        1
        for m in modules
        if m.module in prod_modules
        for d in m.declarations
        if d.kind in ("theorem", "lemma")
    )

    version = "unknown"
    lakefile = ROOT / "lakefile.toml"
    if lakefile.exists():
        for line in lakefile.read_text(encoding="utf-8").splitlines():
            if line.strip().startswith("version"):
                version = line.split("=", 1)[1].strip().strip('"')
                break

    lean_toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").splitlines()[0].strip().split(":")[-1]

    decl_total = sum(len(m.declarations) for m in modules)
    return {
        "schema_version": SCHEMA_VERSION,
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
        "readme_sync": {
            "version": version,
            "lean_toolchain": lean_toolchain,
            "production_files": len(prod_paths),
            "production_loc": prod_loc,
            "test_files": len(test_paths),
            "test_loc": test_loc,
            "proved_theorem_lemma_decls": proved_count,
            "hardware_target": "Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A)",
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
