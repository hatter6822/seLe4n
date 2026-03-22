#!/usr/bin/env python3
"""Semantic L-08 proof-depth validation for preserves-theorems.

Scans Lean files for theorems with `preserves` in the declaration and flags:
- bodies containing `sorry`
- bodies that are trivially one-line proofs (`rfl`, `trivial`, `simp`, `simpa`)
- bodies that are a single tactic line with no structural proof steps
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

DECL_RE = re.compile(r"^\s*(?:private\s+)?theorem\s+([\w']+)\b")
SINGLE_TACTIC_RE = re.compile(r"^by\s+([A-Za-z_][\w']*)\s*$")
TRIVIAL_TACTICS = {"rfl", "trivial", "simp", "simpa"}

NEXT_DECL_PREFIXES = (
    "theorem ", "private theorem ", "lemma ", "private lemma ",
    "def ", "abbrev ", "structure ", "inductive ", "namespace ",
    "section ", "end", "@[",
)


def strip_comments(line: str) -> str:
    idx = line.find("--")
    return line if idx == -1 else line[:idx]


def extract_theorems(lines: list[str]) -> list[tuple[str, int, list[str], str]]:
    out: list[tuple[str, int, list[str], str]] = []
    i = 0
    while i < len(lines):
        m = DECL_RE.match(lines[i])
        if not m:
            i += 1
            continue
        name = m.group(1)
        decl_lines = [lines[i]]
        start = i + 1
        i += 1
        while i < len(lines) and ":=" not in decl_lines[-1]:
            decl_lines.append(lines[i])
            i += 1
        decl_text = "\n".join(decl_lines)
        if "preserves" not in decl_text:
            continue
        body: list[str] = []
        while i < len(lines):
            s = lines[i].lstrip()
            if any(s.startswith(p) for p in NEXT_DECL_PREFIXES):
                break
            body.append(lines[i])
            i += 1
        out.append((name, start, body, decl_text))
    return out


def is_trivial(body: list[str]) -> bool:
    cleaned = [strip_comments(x).strip() for x in body]
    cleaned = [x for x in cleaned if x]
    if not cleaned:
        return True
    if len(cleaned) == 1:
        t = cleaned[0]
        if t in TRIVIAL_TACTICS:
            return True
        m = SINGLE_TACTIC_RE.match(t)
        if m and m.group(1) in TRIVIAL_TACTICS:
            return True
        if m and m.group(1) not in {"cases", "induction", "constructor", "refine", "apply", "have", "exact", "rw", "simp_all"}:
            return True
    return False


def has_sorry(body: list[str]) -> bool:
    """Detect sorry in proof body, excluding tracked TPI-D* exceptions."""
    for line in body:
        stripped = strip_comments(line).strip()
        if re.search(r"\bsorry\b", stripped):
            # Allow sorry that has a TPI-D* annotation in the original line
            if re.search(r"TPI-D\d+", line):
                continue
            return True
    return False


def main(argv: list[str]) -> int:
    files = [Path(p) for p in argv[1:]]
    if not files:
        print("usage: check_proof_depth.py <lean-file> [...]")
        return 2

    any_fail = False
    for f in files:
        if not f.exists():
            print(f"L-08 SKIP: {f} (missing)")
            continue
        lines = f.read_text(encoding="utf-8").splitlines()
        thms = extract_theorems(lines)
        trivial = 0
        bad = []
        for name, line_no, body, _decl in thms:
            if has_sorry(body):
                bad.append((line_no, name, "contains sorry"))
            elif is_trivial(body):
                trivial += 1
                bad.append((line_no, name, "trivial/single-tactic proof"))

        if bad:
            any_fail = True
            print(f"L-08 FAIL: {f} ({len(thms)} preserves-theorems, {len(bad)} flagged)")
            for line_no, name, reason in bad[:20]:
                print(f"  - {name} @ L{line_no}: {reason}")
        else:
            print(f"L-08 PASS: {f} ({len(thms)} theorems, 0 trivial)")

    return 1 if any_fail else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
