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
    r"^\s*(?:@[\w\[\]\.\s]+\s+)?"
    r"(?:(?:" + "|".join(DECL_MODIFIERS) + r")\s+)*"
    r"(?P<kind>" + "|".join(DECL_KINDS) + r")\b\s*(?P<rest>.*)$"
)

NAME_TOKEN_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")
FIRST_NAME_RE = re.compile(r"^\s*(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)")
QUOTED_TOKEN_RE = re.compile(r"\"[^\"\n]*\"")

NON_REFERENCEABLE_KINDS = {"section", "namespace", "universe", "universes", "variable", "variables", "parameter", "parameters"}
LEAN_RESERVED_TOKENS = {
    "def", "theorem", "lemma", "example", "instance", "opaque", "abbrev", "axiom", "constant", "constants",
    "inductive", "structure", "class", "declare_syntax_cat", "syntax_cat", "syntax", "macro", "macro_rules",
    "notation", "infix", "infixl", "infixr", "prefix", "postfix", "elab", "elab_rules", "term_elab", "command_elab",
    "tactic", "universe", "universes", "variable", "variables", "parameter", "parameters", "section", "namespace",
    "private", "protected", "noncomputable", "unsafe", "partial", "scoped", "local", "where", "by", "match", "with",
    "let", "in", "if", "then", "else", "do", "for", "return", "have", "show", "from", "fun", "Type", "Prop",
}


def _strip_lean_comments(line: str, block_depth: int) -> tuple[str, int]:
    """Strip line + block comments while tracking nested block depth."""
    out: list[str] = []
    i = 0
    while i < len(line):
        if block_depth > 0:
            if line.startswith("/-", i):
                block_depth += 1
                i += 2
                continue
            if line.startswith("-/", i):
                block_depth -= 1
                i += 2
                continue
            i += 1
            continue

        if line.startswith("--", i):
            break
        if line.startswith("/-", i):
            block_depth += 1
            i += 2
            continue

        out.append(line[i])
        i += 1

    return "".join(out), block_depth


def _strip_quoted_literals(line: str) -> str:
    return QUOTED_TOKEN_RE.sub(" ", line)


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
    calls: list[str]


@dataclass(frozen=True, slots=True)
class DeclSpan:
    kind: str
    name: str
    line: int
    end_line: int


@dataclass(frozen=True, slots=True)
class ModuleEntry:
    module: str
    path: str
    declarations: list[Decl]


def module_name(path: Path) -> str:
    rel = path.relative_to(ROOT).with_suffix("")
    return ".".join(rel.parts)


def parse_declarations(path: Path) -> list[Decl]:
    return [Decl(kind=d.kind, name=d.name, line=d.line, calls=[]) for d in parse_declaration_spans(path)]


def parse_declaration_spans(path: Path) -> list[DeclSpan]:
    decls: list[DeclSpan] = []
    pending_heads: list[tuple[str, str, int]] = []
    block_depth = 0
    lines = path.read_text(encoding="utf-8").splitlines()
    for i, line in enumerate(lines, start=1):
        clean, block_depth = _strip_lean_comments(line, block_depth)
        if block_depth > 0 and not clean.strip():
            continue
        m = DECL_HEAD_RE.match(clean)
        if m:
            if pending_heads:
                for kind, name, start_line in pending_heads:
                    decls.append(DeclSpan(kind=kind, name=name, line=start_line, end_line=i - 1))
                pending_heads = []
            kind = m.group("kind")
            for name in _extract_names(kind, m.group("rest"), i):
                pending_heads.append((kind, name, i))

    end_line = len(lines) if lines else 1
    for kind, name, start_line in pending_heads:
        decls.append(DeclSpan(kind=kind, name=name, line=start_line, end_line=end_line))
    return decls


def _called_declarations_for_span(
    lines: list[str],
    span: DeclSpan,
    token_index: dict[str, set[str]],
    parent_qualified_name: str,
) -> list[str]:
    if span.kind in NON_REFERENCEABLE_KINDS:
        return []

    called: set[str] = set()
    block_depth = 0
    start = max(1, span.line)
    end = min(len(lines), max(span.end_line, span.line))
    for line_no in range(start, end + 1):
        clean, block_depth = _strip_lean_comments(lines[line_no - 1], block_depth)
        if line_no == span.line:
            head = DECL_HEAD_RE.match(clean)
            if head:
                clean = head.group("rest")

        clean = _strip_quoted_literals(clean)
        for token in NAME_TOKEN_RE.findall(clean):
            if token in LEAN_RESERVED_TOKENS:
                continue
            matched = token_index.get(token)
            if not matched:
                continue
            called.update(matched)

    called.discard(parent_qualified_name)
    return sorted(called)


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

    spans_by_path: dict[Path, list[DeclSpan]] = {path: parse_declaration_spans(path) for path in paths}

    qualified_by_token: dict[str, set[str]] = {}
    for path, spans in spans_by_path.items():
        mod = module_name(path)
        for span in spans:
            if span.name.startswith("<anonymous:") or span.kind in NON_REFERENCEABLE_KINDS:
                continue
            if not NAME_TOKEN_RE.fullmatch(span.name):
                continue
            qualified = f"{mod}.{span.name}"
            qualified_by_token.setdefault(span.name, set()).add(qualified)

    modules: list[ModuleEntry] = []
    for path in paths:
        spans = spans_by_path[path]
        lines = path.read_text(encoding="utf-8").splitlines()
        decls: list[Decl] = []
        mod = module_name(path)
        for span in spans:
            qualified_parent = f"{mod}.{span.name}"
            calls = _called_declarations_for_span(
                lines=lines,
                span=span,
                token_index=qualified_by_token,
                parent_qualified_name=qualified_parent,
            )
            decls.append(Decl(kind=span.kind, name=span.name, line=span.line, calls=calls))

        modules.append(
            ModuleEntry(
                module=mod,
                path=str(path.relative_to(ROOT)),
                declarations=decls,
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
