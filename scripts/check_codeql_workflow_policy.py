#!/usr/bin/env python3
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
"""Enforce the three CodeQL workflow invariants that keep the merge gate honest.

The repository enforces a code-scanning merge requirement naming CodeQL, so a
CodeQL run that does not deliver results does not merely lose signal -- it
leaves every affected pull request permanently unmergeable, reporting
``Code scanning is waiting for results from CodeQL for the commits ...``.
Three distinct configuration mistakes produce that outcome, so three
invariants are checked here:

1. PRESENCE -- at least one ``codeql-action/init`` and one
   ``codeql-action/analyze`` reference must exist.  Deleting or renaming the
   analyze step silently removes analysis while leaving the merge requirement
   in place, and a gate that only inspects steps it can find would report
   "blocking" for a workflow that runs no CodeQL at all.

2. PARITY -- every ``github/codeql-action/*`` reference must pin the same
   commit.  ``init`` stamps the config file it writes with its own action
   version and ``analyze`` refuses to load a config stamped with a different
   one ("Loaded a configuration file for version 'X', but running version
   'Y'"), which ends the run as a CodeQL *configuration error* whose
   diagnostics-only "failed run" SARIF code scanning rejects.  Refs must also
   be full 40-character commit SHAs: parity over a mutable tag is meaningless,
   and the F-14 SHA-pinning scan in ``test_tier0_hygiene.sh`` cannot reach
   sub-path actions, whose owner/repo segment contains a ``/``.

3. UNMASKED -- the analyze step must not be masked by ``continue-on-error``,
   at the step level *or* at the level of the job containing it.  Masking is
   why the PR #858 / #859 breakage went unseen: CodeQL died in a configuration
   error, code scanning received nothing, and the job still reported success.

Gates read code, prose reads prose: YAML comments are stripped (quote-aware)
before matching, and ``continue-on-error`` is matched as a mapping *key*, so a
step named "Run CodeQL without continue-on-error masking" cannot trip the
gate and a sentence explaining the rule cannot satisfy or trip it either.

Usage:
    check_codeql_workflow_policy.py              # scan the repository
    check_codeql_workflow_policy.py --self-test  # prove the gate still bites

Exits 0 when clean, 1 on any violation or self-test failure.
"""

from __future__ import annotations

import os
import re
import sys
import tempfile

MARKER = "github/codeql-action/"
SHA_RE = re.compile(r"^[0-9a-f]{40}$")
USES_RE = re.compile(r"^-?\s*uses\s*:\s*(\S.*)$")
KEY_RE = re.compile(r"^-?\s*([A-Za-z0-9_.-]+)\s*:")
JOB_KEY_RE = re.compile(r"^([A-Za-z0-9_-]+)\s*:\s*$")
CONTINUE_ON_ERROR = "continue-on-error"


def split_comment(line: str) -> tuple[str, str]:
    """Split a YAML line into (code, comment), respecting quoted scalars.

    A ``#`` only opens a comment outside quotes and at line start or after
    whitespace -- matching YAML, and keeping a ``#`` inside a quoted value
    from truncating the code half.
    """
    quote = None
    for i, ch in enumerate(line):
        if quote is not None:
            if ch == quote:
                quote = None
        elif ch in ('"', "'"):
            quote = ch
        elif ch == "#" and (i == 0 or line[i - 1] in " \t"):
            return line[:i], line[i + 1:].strip()
    return line, ""


def unquote(value: str) -> str:
    value = value.strip()
    if len(value) >= 2 and value[0] == value[-1] and value[0] in ('"', "'"):
        return value[1:-1]
    return value


class Line:
    __slots__ = ("no", "indent", "code", "stripped", "comment")

    def __init__(self, no: int, raw: str):
        code, comment = split_comment(raw.rstrip("\n"))
        self.no = no
        self.code = code
        self.stripped = code.strip()
        self.indent = len(code) - len(code.lstrip(" ")) if self.stripped else 0
        self.comment = comment


def read_lines(path: str) -> list[Line]:
    with open(path, "r", encoding="utf-8", errors="replace") as handle:
        return [Line(n, raw) for n, raw in enumerate(handle, start=1)]


def codeql_ref(line: Line):
    """Return (sub_action, ref, version_comment) for a codeql `uses:` line."""
    if not line.stripped:
        return None
    match = USES_RE.match(line.stripped)
    if not match:
        return None
    value = unquote(match.group(1))
    if not value.startswith(MARKER):
        return None
    spec = value[len(MARKER):]
    sub_action, _, ref = spec.partition("@")
    return sub_action.strip(), ref.strip(), line.comment.strip()


def is_key(line: Line, name: str) -> bool:
    match = KEY_RE.match(line.stripped)
    return bool(match) and match.group(1) == name


def step_blocks(lines: list[Line]):
    """Yield each ``- ...`` list item as a block of lines.

    A block runs to the next item at the same indent or to the first line
    that dedents out of it, so a mask written above the ``uses:`` line is
    found exactly as one written below it -- YAML mapping order is free.
    """
    start = None
    indent = None
    for idx, line in enumerate(lines):
        if not line.stripped:
            continue
        if line.stripped.startswith("- ") and (indent is None or line.indent <= indent):
            if start is not None:
                yield lines[start:idx]
            start, indent = idx, line.indent
        elif indent is not None and line.indent < indent:
            yield lines[start:idx]
            start, indent = None, None
    if start is not None:
        yield lines[start:]


def job_blocks(lines: list[Line]):
    """Yield (job_name, block) for each job under a top-level ``jobs:`` key."""
    jobs_idx = next((i for i, ln in enumerate(lines) if is_key(ln, "jobs")), None)
    if jobs_idx is None:
        return
    body = lines[jobs_idx + 1:]
    job_indent = next((ln.indent for ln in body if ln.stripped), None)
    if job_indent is None:
        return
    start = None
    name = None
    for idx, line in enumerate(body):
        if not line.stripped:
            continue
        if line.indent < job_indent:
            break
        match = JOB_KEY_RE.match(line.stripped)
        if line.indent == job_indent and match:
            if start is not None:
                yield name, body[start:idx]
            start, name = idx, match.group(1)
    if start is not None:
        yield name, body[start:]


def block_has_analyze(block: list[Line]) -> bool:
    return any((ref or ("", "", ""))[0] == "analyze" for ref in map(codeql_ref, block))


def masked_at_step(block: list[Line]) -> bool:
    return any(is_key(ln, CONTINUE_ON_ERROR) for ln in block)


def scan(root: str) -> list[str]:
    workflows = os.path.join(root, ".github", "workflows")
    problems: list[str] = []
    refs: list[tuple[str, int, str, str, str]] = []

    paths = []
    if os.path.isdir(workflows):
        for name in sorted(os.listdir(workflows)):
            if name.endswith((".yml", ".yaml")):
                paths.append(os.path.join(workflows, name))

    for path in paths:
        rel = os.path.relpath(path, root)
        lines = read_lines(path)

        for line in lines:
            parsed = codeql_ref(line)
            if parsed:
                refs.append((rel, line.no, parsed[0], parsed[1], parsed[2]))

        # UNMASKED, step level.
        for block in step_blocks(lines):
            if block_has_analyze(block) and masked_at_step(block):
                problems.append(
                    f"{rel}:{block[0].no}: the codeql-action/analyze step is masked by "
                    f"`{CONTINUE_ON_ERROR}`"
                )

        # UNMASKED, job level: a failing job is tolerated by the run, so the
        # analyze failure is swallowed exactly as a step-level mask would.
        for name, block in job_blocks(lines):
            if not any(block_has_analyze(b) for b in step_blocks(block)):
                continue
            child_indent = next(
                (ln.indent for ln in block[1:] if ln.stripped), None
            )
            if child_indent is None:
                continue
            for line in block[1:]:
                if line.indent == child_indent and is_key(line, CONTINUE_ON_ERROR):
                    problems.append(
                        f"{rel}:{line.no}: job `{name}` contains a codeql-action/analyze "
                        f"step and is itself masked by `{CONTINUE_ON_ERROR}`"
                    )

    # PRESENCE.
    sub_actions = {ref[2] for ref in refs}
    for required in ("init", "analyze"):
        if required not in sub_actions:
            problems.append(
                f"no `github/codeql-action/{required}` step found in .github/workflows "
                f"-- CodeQL cannot deliver results, but the code-scanning merge "
                f"requirement still waits for them"
            )

    if not refs:
        return problems

    # PARITY.
    for rel, no, sub_action, ref, _ in refs:
        if not SHA_RE.match(ref):
            problems.append(
                f"{rel}:{no}: `{sub_action}@{ref}` is not a full 40-character commit SHA"
            )

    distinct_refs = {ref[3] for ref in refs}
    if len(distinct_refs) > 1:
        sites = ", ".join(f"{r}:{n} {s}@{ref[:12]}" for r, n, s, ref, _ in refs)
        problems.append(
            "github/codeql-action/* references disagree -- `init` stamps its config "
            "with its own version and `analyze` rejects a config from a different "
            f"one, so the run ends in a configuration error: {sites}"
        )
    elif len({ref[4] for ref in refs}) > 1:
        sites = ", ".join(f"{r}:{n} # {c}" for r, n, _, _, c in refs)
        problems.append(
            f"codeql-action refs share a commit but their version comments disagree: {sites}"
        )

    return problems


def report(problems: list[str]) -> int:
    if problems:
        print("CodeQL workflow policy FAIL:", file=sys.stderr)
        for problem in problems:
            print(f"  {problem}", file=sys.stderr)
        print("", file=sys.stderr)
        print("  See docs/CI_POLICY.md §8 (blocking gate) and §9.1 (pin parity).",
              file=sys.stderr)
        return 1
    print("CodeQL workflow policy: init+analyze present, pins agree, analyze unmasked.")
    return 0


# --------------------------------------------------------------------------
# Self-test.  A scanner that stops reaching the misconfiguration it exists to
# catch goes silent rather than loud, so every case below is machine-checked.
# --------------------------------------------------------------------------

SHA_A = "5595ccaf912efad79be6eef63a5619ff05969be3"
SHA_B = "f205ea1c3313d32999d8d6a48b4f6530d4437b38"


def _workflow(init_ref=SHA_A, analyze_ref=SHA_A, quoted=False,
              step_mask=False, job_mask=False, analyze=True,
              analyze_name="Run CodeQL analysis", init_comment="v4.37.6",
              analyze_comment="v4.37.6"):
    def render(sub, ref, comment):
        value = f"github/codeql-action/{sub}@{ref}"
        if quoted:
            value = f'"{value}"'
        return f"{value} # {comment}"

    out = [
        "name: Baseline",
        "on: [pull_request]",
        "jobs:",
        "  scan:",
        "    runs-on: ubuntu-latest",
    ]
    if job_mask:
        out.append("    continue-on-error: true")
    out += [
        "    steps:",
        "      # prose mentioning continue-on-error must not decide the gate",
        "      - name: Initialize CodeQL",
        f"        uses: {render('init', init_ref, init_comment)}",
    ]
    if analyze:
        out += [
            f"      - name: {analyze_name}",
            f"        uses: {render('analyze', analyze_ref, analyze_comment)}",
        ]
        if step_mask:
            out.append("        continue-on-error: true")
    return "\n".join(out) + "\n"


def _tree(tmp: str, name: str, content: str) -> str:
    root = os.path.join(tmp, name)
    os.makedirs(os.path.join(root, ".github", "workflows"))
    with open(os.path.join(root, ".github", "workflows", "w.yml"), "w",
              encoding="utf-8") as handle:
        handle.write(content)
    return root


def self_test() -> int:
    cases = [
        ("a healthy workflow", _workflow(), True),
        ("PR #858's mismatched pair", _workflow(analyze_ref=SHA_B), False),
        ("a QUOTED mismatched pair", _workflow(analyze_ref=SHA_B, quoted=True), False),
        ("quoted refs that agree", _workflow(quoted=True), True),
        ("a mutable tag ref", _workflow(init_ref="v4", analyze_ref="v4"), False),
        ("a step-level continue-on-error", _workflow(step_mask=True), False),
        ("a JOB-level continue-on-error", _workflow(job_mask=True), False),
        ("a deleted analyze step", _workflow(analyze=False), False),
        ("a step NAMED after the flag",
         _workflow(analyze_name="Run CodeQL without continue-on-error masking"), True),
        ("disagreeing version comments", _workflow(analyze_comment="v4.37.4"), False),
    ]

    failures = 0
    with tempfile.TemporaryDirectory() as tmp:
        for index, (label, content, want_clean) in enumerate(cases):
            root = _tree(tmp, f"case{index}", content)
            clean = not scan(root)
            if clean != want_clean:
                verb = "accepted" if clean else "rejected"
                print(f"SELF-TEST FAIL: {label} was {verb}.", file=sys.stderr)
                failures += 1

        # The scan must read code, not the tree it happens to sit in.
        empty = os.path.join(tmp, "empty")
        os.makedirs(empty)
        if not scan(empty):
            print("SELF-TEST FAIL: a tree with no workflows reported no problem, "
                  "but CodeQL is required.", file=sys.stderr)
            failures += 1

    if failures:
        return 1
    print(f"CodeQL workflow policy self-test: {len(cases) + 1} cases "
          f"(quoted refs, job- and step-level masks, missing analyze, prose) all correct.")
    return 0


def main() -> int:
    if len(sys.argv) > 1 and sys.argv[1] == "--self-test":
        return self_test()
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    return report(scan(root))


if __name__ == "__main__":
    sys.exit(main())
