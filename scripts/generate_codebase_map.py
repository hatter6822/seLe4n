#!/usr/bin/env python3
"""Generate a machine-readable seLe4n codebase map for website consumption.

Outputs JSON with:
- repository identity metadata
- source-derived sync metadata (stable across branches/merge commits)
- every Lean module under SeLe4n/ plus Main/tests
- declaration inventory (def/theorem/lemma/abbrev/instance/structure/inductive/class)
- cross-file "called" resolution for declaration dependencies

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
DECL_KINDS = [
    "inductive",
    "structure",
    "class",
    "def",
    "theorem",
    "lemma",
    "example",
    "instance",
    "opaque",
    "abbrev",
    "axiom",
    "constant",
    "constants",
    "declare_syntax_cat",
    "syntax_cat",
    "syntax",
    "macro",
    "macro_rules",
    "notation",
    "infix",
    "infixl",
    "infixr",
    "prefix",
    "postfix",
    "elab",
    "elab_rules",
    "term_elab",
    "command_elab",
    "tactic",
    "universe",
    "universes",
    "variable",
    "variables",
    "parameter",
    "parameters",
    "section",
    "namespace",
    "initialize",
]

DECL_MODIFIERS = [
    "private",
    "protected",
    "noncomputable",
    "unsafe",
    "partial",
    "scoped",
    "local",
]

DECL_HEAD_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:" + "|".join(DECL_MODIFIERS) + r")\s+)*"
    r"(?P<kind>" + "|".join(DECL_KINDS) + r")\b\s*(?P<rest>.*)$"
)

NAME_TOKEN_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")
FIRST_NAME_RE = re.compile(r"^\s*(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)")
QUOTED_TOKEN_RE = re.compile(r"\"[^\"\n]*\"")

NON_REFERENCABLE_DECL_KINDS = {
    "declare_syntax_cat",
    "syntax_cat",
    "syntax",
    "macro",
    "macro_rules",
    "notation",
    "infix",
    "infixl",
    "infixr",
    "prefix",
    "postfix",
    "elab",
    "elab_rules",
    "term_elab",
    "command_elab",
    "tactic",
    "universe",
    "universes",
    "variable",
    "variables",
    "parameter",
    "parameters",
    "section",
    "namespace",
}


def _declaration_ranges(decls: list[tuple[str, str, int]], line_count: int) -> list[tuple[int, int]]:
    ranges: list[tuple[int, int]] = []
    for i, (_, _, start_line) in enumerate(decls):
        next_start = decls[i + 1][2] if i + 1 < len(decls) else line_count + 1
        ranges.append((start_line - 1, next_start - 1))
    return ranges


def _strip_lean_comments(line: str, block_depth: int, *, strip_strings: bool = False) -> tuple[str, int]:
    """Strip line comments, nested block comments, and optionally string contents.

    When *strip_strings* is ``True``, plain string contents are removed so that
    tokens inside string literals are not falsely matched as declaration
    references.  Interpolated strings (``s!"..."``, ``m!"..."``, etc.) retain
    their content because ``{expr}`` sections contain real code with legitimate
    references.

    When *strip_strings* is ``False`` (the default), strings are left intact.
    This mode is used during declaration header parsing so that quoted names
    (e.g. ``syntax "visible"``) are preserved.

    Block comment depth is tracked across calls so that multi-line ``/- ... -/``
    blocks are handled correctly.
    """
    out: list[str] = []
    i = 0
    n = len(line)
    while i < n:
        if block_depth > 0:
            if i + 1 < n and line[i] == '/' and line[i + 1] == '-':
                block_depth += 1
                i += 2
            elif i + 1 < n and line[i] == '-' and line[i + 1] == '/':
                block_depth -= 1
                i += 2
            else:
                i += 1
            continue

        # Line comment — discard rest of line
        if i + 1 < n and line[i] == '-' and line[i + 1] == '-':
            break

        # Block comment start
        if i + 1 < n and line[i] == '/' and line[i + 1] == '-':
            block_depth += 1
            i += 2
            continue

        # String literal handling (only when strip_strings is enabled)
        if strip_strings and line[i] == '"':
            # Interpolated strings (s!"...", m!"...", f!"...") contain real
            # code inside {expr} — keep their content so references are found.
            is_interpolated = i >= 2 and line[i - 1] == '!' and line[i - 2].isalpha()
            i += 1
            if is_interpolated:
                # Keep all content — {expr} blocks have real references, and
                # the minor false positives from plain-text portions are
                # acceptable compared to losing real cross-file references.
                while i < n:
                    if line[i] == '\\' and i + 1 < n:
                        out.append(line[i])
                        out.append(line[i + 1])
                        i += 2
                    elif line[i] == '"':
                        i += 1
                        break
                    else:
                        out.append(line[i])
                        i += 1
            else:
                # Regular string — strip all content
                while i < n:
                    if line[i] == '\\' and i + 1 < n:
                        i += 2  # skip escaped character
                    elif line[i] == '"':
                        i += 1
                        break
                    else:
                        i += 1
            continue

        # Character literal — skip contents (only when stripping strings)
        if strip_strings and line[i] == '\'' and i + 2 < n and line[i + 1] != '\'' and line[i + 1] != ' ':
            # Only skip single-char literals like 'a' or '\n', not prime (')
            j = i + 1
            if j < n and line[j] == '\\':
                j += 2  # escape sequence
            else:
                j += 1
            if j < n and line[j] == '\'':
                i = j + 1
                continue

        out.append(line[i])
        i += 1

    return "".join(out), block_depth


def _compute_block_depth(lines: list[str], up_to: int, *, strip_strings: bool = False) -> int:
    """Compute the block comment nesting depth for lines[0:up_to]."""
    depth = 0
    for raw in lines[:up_to]:
        _, depth = _strip_lean_comments(raw, depth, strip_strings=strip_strings)
    return depth


def _tokenize_decl_ranges(
    lines: list[str],
    ranges: list[tuple[int, int]],
    reference_candidates: set[str],
) -> list[set[str]]:
    """Find references to known declarations within each declaration body.

    Improvements over the naive approach:
    - Block comment depth is correctly initialised from lines preceding the first
      declaration, so comments that opened in the import/preamble section do not
      cause false positives inside the first declaration.
    - String literal contents are stripped (by ``_strip_lean_comments``) to
      prevent tokens inside strings from being falsely counted.
    - Qualified name suffix matching: for a token like ``Foo.Bar.baz``, the
      suffixes ``Bar.baz`` and ``baz`` are also checked against the candidate
      set, catching qualified references to known declarations.
    """
    per_decl: list[set[str]] = []
    if not ranges:
        return per_decl

    # Correctly initialise block_depth from lines before the first declaration
    first_start = ranges[0][0]
    block_depth = _compute_block_depth(lines, first_start, strip_strings=True)

    for start_idx, end_idx in ranges:
        refs: set[str] = set()
        for raw in lines[start_idx:end_idx]:
            clean, block_depth = _strip_lean_comments(raw, block_depth, strip_strings=True)
            if not clean:
                continue
            for token in NAME_TOKEN_RE.findall(clean):
                # Direct match
                if token in reference_candidates:
                    refs.add(token)
                    continue
                # Qualified name suffix matching
                if '.' in token:
                    parts = token.split('.')
                    for j in range(1, len(parts)):
                        suffix = '.'.join(parts[j:])
                        if suffix in reference_candidates:
                            refs.add(suffix)
                            break
        per_decl.append(refs)
    return per_decl


def _split_head_segment(rest: str) -> str:
    for marker in (":=", " where", ":", "=>"):
        idx = rest.find(marker)
        if idx != -1:
            return rest[:idx]
    return rest


def _extract_names(kind: str, rest: str, line: int) -> list[str]:
    rest = rest.strip()
    if not rest:
        return [f"<anonymous:{kind}:{line}>"]

    if kind in {"constants", "universes", "variables", "parameters"}:
        names = NAME_TOKEN_RE.findall(_split_head_segment(rest))
        if names:
            return names
        return [f"<anonymous:{kind}:{line}>"]

    if kind in {
        "syntax",
        "notation",
        "infix",
        "infixl",
        "infixr",
        "prefix",
        "postfix",
        "elab",
        "macro",
        "macro_rules",
        "initialize",
    }:
        m = FIRST_NAME_RE.match(rest)
        if m:
            return [m.group("name")]
        quoted = QUOTED_TOKEN_RE.search(rest)
        if quoted:
            return [quoted.group(0)]
        if rest[0] in {'`', "'"}:
            return [rest.split()[0]]

    if kind in {
        "def",
        "theorem",
        "lemma",
        "example",
        "instance",
        "opaque",
        "abbrev",
        "axiom",
        "constant",
        "inductive",
        "structure",
        "class",
        "declare_syntax_cat",
        "syntax_cat",
        "elab_rules",
        "term_elab",
        "command_elab",
        "tactic",
        "universe",
        "variable",
        "parameter",
        "section",
        "namespace",
    }:
        m = FIRST_NAME_RE.match(rest)
        if m:
            return [m.group("name")]
        if kind in {"variable", "parameter"}:
            names = NAME_TOKEN_RE.findall(_split_head_segment(rest))
            if names:
                return [names[0]]

    return [f"<anonymous:{kind}:{line}>"]


@dataclass(frozen=True, slots=True)
class Decl:
    kind: str
    name: str
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


def _parse_declaration_headers(lines: list[str]) -> list[tuple[str, str, int]]:
    """Extract declaration headers (kind, name, line_number) from file lines.

    Correctly tracks nested block comment depth so that declarations appearing
    inside ``/- ... -/`` blocks are not enumerated.
    """
    decls: list[tuple[str, str, int]] = []
    block_depth = 0
    for i, line in enumerate(lines, start=1):
        clean, block_depth = _strip_lean_comments(line, block_depth)
        if block_depth > 0 and not clean.strip():
            continue
        m = DECL_HEAD_RE.match(clean)
        if m:
            kind = m.group("kind")
            for name in _extract_names(kind, m.group("rest"), i):
                decls.append((kind, name, i))
    return decls


def _resolve_calls(
    lines: list[str],
    decls: list[tuple[str, str, int]],
    global_names: set[str],
) -> list[Decl]:
    """Build Decl objects with cross-file 'called' resolution.

    Each declaration's body is scanned for tokens that match any known
    declaration name from the entire project (not just the current file).
    Self-references are excluded.
    """
    if not decls:
        return []

    ranges = _declaration_ranges(decls, len(lines))
    calls_per_decl = _tokenize_decl_ranges(lines, ranges, global_names)

    result: list[Decl] = []
    for (kind, name, line), called_names in zip(decls, calls_per_decl):
        # Build self-name set: exclude own name and all its dot-suffixes
        self_names: set[str] = {name}
        if '.' in name:
            parts = name.split('.')
            for j in range(1, len(parts)):
                self_names.add('.'.join(parts[j:]))

        result.append(
            Decl(
                kind=kind,
                name=name,
                line=line,
                called=sorted(n for n in called_names if n not in self_names),
            )
        )
    return result


def parse_declarations(path: Path) -> list[Decl]:
    """Public API: parse declarations from a single file with file-local 'called'.

    For backward compatibility with tests and external callers.  The internal
    ``build_map`` path uses the two-pass cross-file architecture instead.
    """
    lines = path.read_text(encoding="utf-8").splitlines()
    headers = _parse_declaration_headers(lines)
    local_names: set[str] = set()
    for kind, name, _ in headers:
        if kind not in NON_REFERENCABLE_DECL_KINDS and not name.startswith("<anonymous:"):
            local_names.add(name)
    return _resolve_calls(lines, headers, local_names)


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
    """Return the subset that must remain stable for docs-sync checks.

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
    for path in paths:
        raw = path.read_bytes()
        file_bytes[path] = raw
        file_lines[path] = raw.decode("utf-8").splitlines()

    source_digest = source_fingerprint(file_bytes, paths)

    # ---- Pass 1: extract declaration headers from every file ----
    all_headers: dict[Path, list[tuple[str, str, int]]] = {}
    for path in paths:
        all_headers[path] = _parse_declaration_headers(file_lines[path])

    # ---- Build global set of referencable declaration names ----
    global_names: set[str] = set()
    for headers in all_headers.values():
        for kind, name, _ in headers:
            if kind not in NON_REFERENCABLE_DECL_KINDS and not name.startswith("<anonymous:"):
                global_names.add(name)
                # For qualified names like "Foo.bar", also register the
                # unqualified leaf so that code using `open Foo` and then
                # referencing plain `bar` is correctly resolved.
                if '.' in name:
                    parts = name.split('.')
                    for j in range(1, len(parts)):
                        global_names.add('.'.join(parts[j:]))

    # ---- Pass 2: resolve cross-file "called" for each module ----
    modules: list[ModuleEntry] = []
    for path in paths:
        decls = _resolve_calls(file_lines[path], all_headers[path], global_names)
        modules.append(
            ModuleEntry(
                module=module_name(path),
                path=str(path.relative_to(ROOT)),
                declarations=decls,
            )
        )

    # ---- Summary metrics (computed from cached data, no re-reads) ----
    prod_paths = [p for p in paths if not str(p.relative_to(ROOT)).startswith("tests/")]
    test_paths = [p for p in paths if str(p.relative_to(ROOT)).startswith("tests/")]

    prod_loc = sum(len(file_lines[p]) for p in prod_paths)
    test_loc = sum(len(file_lines[p]) for p in test_paths)

    theorem_pattern = re.compile(r"^\s*(?:@[\w\[\]\.\s]+\s+)?(?:private\s+)?(?:theorem|lemma)\s+")
    proved_count = sum(
        1
        for p in prod_paths
        for line in file_lines[p]
        if theorem_pattern.match(line)
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
