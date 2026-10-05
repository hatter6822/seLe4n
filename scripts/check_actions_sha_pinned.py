#!/usr/bin/env python3
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
"""Every remote `uses:` reference must name a full 40-hex commit SHA (F-14).

The files are parsed as YAML, not scanned as text, so a key is what YAML
resolves it to: `"\\u0075ses"` is `uses`, an alias is its anchor's value, and
a flow mapping is a mapping.  Every mapping in every document is walked, and
every value whose key is `uses` is classified:

  ./path                          a local action: exempt
  docker://image@sha256:<64 hex>  a container: the digest is required
  owner/repo[/path]@<40 hex>      a remote action or reusable workflow

Anything else fails, as does a file that does not parse.  Parsing goes through
a loader that rejects duplicate keys, since YAML leaves the winner of a
duplicate to the reader.  A non-string or empty value, a missing PyYAML, a
missing workflows directory and a tree with no `uses:` at all also fail.

Files: `.github/workflows/*.yml` and `*.yaml` (the files GitHub runs) and every
composite action's `action.yml` / `action.yaml` in the repository.

Usage:
    check_actions_sha_pinned.py              # check the repository
    check_actions_sha_pinned.py --self-test  # prove the check still bites
"""

from __future__ import annotations

import os
import re
import sys
import tempfile

try:
    import yaml
except ImportError:  # pragma: no cover - exercised by running without PyYAML
    print("F-14: PyYAML is not installed, so workflow `uses:` references cannot "
          "be parsed or checked.  Install it with `python3 -m pip install "
          "pyyaml` (or the `python3-yaml` package); `scripts/setup_lean_env.sh` "
          "installs it with the test dependencies.", file=sys.stderr)
    sys.exit(2)

SHA_RE = re.compile(r"[0-9a-f]{40}")
REMOTE_RE = re.compile(r"([A-Za-z0-9_.-]+)/([A-Za-z0-9_.-]+)(/[^@\s]+)?@([^@\s]+)")
DOCKER_RE = re.compile(r"docker://[^@\s]+@sha256:[0-9a-f]{64}")
STR_TAG = "tag:yaml.org,2002:str"
MERGE_TAG = "tag:yaml.org,2002:merge"
#: Directories never searched for composite actions: VCS data, build output.
PRUNE = {".git", ".lake", "target", "node_modules", "__pycache__"}


class StrictLoader(yaml.SafeLoader):
    """`SafeLoader` that refuses a mapping with the same key twice."""

    def construct_mapping(self, node, deep=False):
        if isinstance(node, yaml.MappingNode):
            seen = set()
            for key_node, _ in node.value:
                if key_node.tag == MERGE_TAG:
                    continue
                key = self.construct_object(key_node, deep=True)
                try:
                    duplicate = key in seen
                except TypeError:
                    raise yaml.constructor.ConstructorError(
                        "while constructing a mapping", node.start_mark,
                        "found an unhashable key", key_node.start_mark)
                if duplicate:
                    raise yaml.constructor.ConstructorError(
                        "while constructing a mapping", node.start_mark,
                        f"found duplicate key {key!r}", key_node.start_mark)
                seen.add(key)
        return super().construct_mapping(node, deep)


def classify(value: str) -> str | None:
    """None when `value` is an acceptable reference, else the reason."""
    if not value or re.search(r"\s", value):
        return "cannot classify this `uses:` value"
    if value.startswith("./"):
        return None
    if value.startswith("docker://"):
        if DOCKER_RE.fullmatch(value):
            return None
        return "docker image is not pinned to an @sha256: digest"
    match = REMOTE_RE.fullmatch(value)
    if not match:
        return "cannot classify this `uses:` value as owner/repo[/path]@ref"
    if not SHA_RE.fullmatch(match.group(4)):
        return f"ref `{match.group(4)}` is not a full 40-hex commit SHA"
    return None


def uses_values(node, seen: set[int]):
    """Yield (value node) for every value whose key resolves to `uses`."""
    if id(node) in seen:  # an alias revisits its anchor; walk it once
        return
    seen.add(id(node))
    if isinstance(node, yaml.MappingNode):
        for key_node, value_node in node.value:
            if isinstance(key_node, yaml.ScalarNode) and key_node.value == "uses" \
                    and key_node.tag != MERGE_TAG:
                yield value_node
            yield from uses_values(key_node, seen)
            yield from uses_values(value_node, seen)
    elif isinstance(node, yaml.SequenceNode):
        for item in node.value:
            yield from uses_values(item, seen)


def check_file(root: str, rel: str, counts: dict[str, int]) -> list[str]:
    path = os.path.join(root, rel)
    try:
        with open(path, encoding="utf-8") as handle:
            text = handle.read()
    except (OSError, UnicodeDecodeError) as err:
        return [f"{rel}: cannot be read ({err}), so its `uses:` cannot be checked"]
    problems: list[str] = []
    loader = StrictLoader(text)
    try:
        while loader.check_node():
            document = loader.get_node()
            loader.construct_document(document)  # duplicates, unknown tags
            for value in uses_values(document, set()):
                line = value.start_mark.line + 1
                if not (isinstance(value, yaml.ScalarNode) and value.tag == STR_TAG):
                    problems.append(f"{rel}:{line}: `uses:` value is not a string "
                                    f"({value.tag})")
                    continue
                reason = classify(value.value)
                if reason:
                    problems.append(f"{rel}:{line}: {reason}: {value.value}")
                    continue
                kind = ("local" if value.value.startswith("./") else
                        "docker" if value.value.startswith("docker://") else "remote")
                counts[kind] += 1
    except yaml.YAMLError as err:
        mark = getattr(err, "problem_mark", None)
        where = f"{rel}:{mark.line + 1}" if mark else rel
        problem = getattr(err, "problem", None) or str(err).splitlines()[0]
        problems.append(f"{where}: does not parse as YAML ({problem}), so its "
                        f"`uses:` cannot be checked")
    finally:
        loader.dispose()
    return problems


def target_files(root: str) -> tuple[list[str], list[str]]:
    """(files to check, problems).  The workflows directory must exist."""
    problems: list[str] = []
    files: list[str] = []
    workflows = os.path.join(root, ".github", "workflows")
    if not os.path.isdir(workflows):
        problems.append(".github/workflows: missing, so no workflow was checked")
    else:
        for name in sorted(os.listdir(workflows)):
            if name.endswith((".yml", ".yaml")) and \
                    os.path.isfile(os.path.join(workflows, name)):
                files.append(f".github/workflows/{name}")
    for base, dirs, names in os.walk(root):
        dirs[:] = sorted(d for d in dirs if d not in PRUNE)
        for name in names:
            if name in ("action.yml", "action.yaml"):
                files.append(os.path.relpath(os.path.join(base, name), root))
    return files, problems


def check(root: str) -> tuple[list[str], dict[str, int]]:
    counts = {"remote": 0, "docker": 0, "local": 0}
    files, problems = target_files(root)
    for rel in files:
        problems.extend(check_file(root, rel, counts))
    if not problems and not sum(counts.values()):
        problems.append("no `uses:` reference found in .github/workflows or any "
                        "action.yml, so nothing was checked")
    return problems, counts


# --------------------------------------------------------------------------
# Self-test.  Each case's lines start at line 8 of a workflow whose line 7 is
# a pinned step, and a failing case must name the line it fails on, so a
# finding that loses its location fails the self-test too.
# --------------------------------------------------------------------------
SHA = "0123456789abcdef0123456789abcdef01234567"
DIGEST = "0123456789abcdef" * 4
HEAD = ["name: t", "on: push", "jobs:", "  j:", "    runs-on: ubuntu-latest",
        "    steps:", f"      - uses: actions/checkout@{SHA} # v4"]
STEP = "      "

CASES = [
    # (passes, label, lines from line 8, location a failure must name)
    (True, "a pinned sub-path action", [f"- uses: github/codeql-action/init@{SHA} # v4.38.0"], ""),
    (True, "a pinned owner and repo with digits", [f"- uses: actions2/check-out9@{SHA}"], ""),
    (True, "a quoted pinned reference", [f'- uses: "actions/checkout@{SHA}"'], ""),
    (True, "a local action", ["- uses: ./.github/actions/local"], ""),
    (True, "a docker image pinned to a digest", [f"- uses: docker://alpine@sha256:{DIGEST}"], ""),
    (True, "a reference inside a comment", ["# - uses: actions/checkout@v4"], ""),
    (True, "uses: inside a step name", ["- name: 'Check uses: actions/checkout@v4'"], ""),
    (True, "uses: inside a run block", ["- run: |", "    echo 'uses: actions/checkout@v4'"], ""),
    (True, "an alias to a pinned anchor",
     [f"- uses: &pin actions/setup-node@{SHA}", "- uses: *pin"], ""),
    (False, "an unpinned sub-path action", ["- uses: github/codeql-action/init@v3"], "w.yml:8"),
    (False, "an owner with digits on a tag", ["- uses: actions2/checkout@v4"], "w.yml:8"),
    (False, "a branch ref", ["- uses: actions/checkout@main"], "w.yml:8"),
    (False, "a short SHA", ["- uses: actions/checkout@a1b2c3d"], "w.yml:8"),
    (False, "a non-v tag", ["- uses: aquasecurity/trivy-action@0.36.0"], "w.yml:8"),
    (False, "a quoted tag", ['- uses: "actions/checkout@v4"'], "w.yml:8"),
    (False, "a space before the colon", ["- uses : actions/checkout@v4"], "w.yml:8"),
    (False, "a quoted key", ['- "uses": actions/checkout@v4'], "w.yml:8"),
    (False, "an escaped quoted key", ['- "\\u0075ses": actions/checkout@v4'], "w.yml:8"),
    (False, "a flow mapping", ["- {name: x, uses: actions/checkout@v4}"], "w.yml:8"),
    (False, "a key written across a line", ["- ? uses", "  : actions/checkout@v4"], "w.yml:9"),
    (False, "an alias to an unpinned anchor",
     ["- uses: &tag actions/setup-node@v4", "- uses: *tag"], "w.yml:8"),
    (False, "a duplicate key", [f"- uses: actions/checkout@{SHA}", "  uses: ./local"], "w.yml:9"),
    (False, "a duplicate key spelled with an escape",
     [f"- uses: actions/checkout@{SHA}", '  "\\u0075ses": ./local'], "w.yml:9"),
    (False, "a docker tag", ["- uses: docker://alpine:3.8"], "w.yml:8"),
    (False, "a reusable workflow on a tag",
     ["- uses: octo-org/repo/.github/workflows/ci.yml@v1"], "w.yml:8"),
    (False, "an empty value", ["- uses:"], "w.yml:8"),
    (False, "a non-string value", ["- uses: [actions/checkout@v4]"], "w.yml:8"),
    (False, "no ref at all", ["- uses: actions/checkout"], "w.yml:8"),
    (False, "an expression", ["- uses: actions/checkout@${{ github.sha }}"], "w.yml:8"),
    (False, "a file that does not parse", ["- uses: [unterminated"], "w.yml:"),
]


def _write(root: str, rel: str, text: str) -> None:
    full = os.path.join(root, rel)
    os.makedirs(os.path.dirname(full), exist_ok=True)
    with open(full, "w", encoding="utf-8") as handle:
        handle.write(text)


def _workflow(lines: list[str]) -> str:
    return "\n".join(HEAD + [STEP + line for line in lines]) + "\n"


def self_test() -> int:
    failures = 0
    checked = 0

    def expect(label: str, root: str, passes: bool, must_name: str) -> None:
        nonlocal failures, checked
        checked += 1
        problems, _ = check(root)
        if (not problems) != passes:
            verdict = "passed" if not problems else f"failed: {problems}"
            print(f"SELF-TEST FAIL: {label}: {verdict}", file=sys.stderr)
            failures += 1
        elif must_name and not any(p.startswith(must_name) for p in problems):
            print(f"SELF-TEST FAIL: {label}: no finding starts with {must_name}: "
                  f"{problems}", file=sys.stderr)
            failures += 1

    with tempfile.TemporaryDirectory() as tmp:
        for index, (passes, label, lines, must_name) in enumerate(CASES):
            root = os.path.join(tmp, f"case{index}")
            _write(root, ".github/workflows/w.yml", _workflow(lines))
            expect(label, root, passes, must_name and f".github/workflows/{must_name}")

        root = os.path.join(tmp, "composite")
        _write(root, ".github/workflows/w.yml", _workflow([]))
        _write(root, ".github/actions/setup/action.yml",
               "name: s\nruns:\n  using: composite\n  steps:\n"
               "    - uses: actions/cache@v4\n")
        expect("an unpinned step in a composite action", root, False,
               ".github/actions/setup/action.yml:5")

        root = os.path.join(tmp, "nodir")
        os.makedirs(root)
        expect("a tree with no workflows directory", root, False, ".github/workflows")

        root = os.path.join(tmp, "nouses")
        _write(root, ".github/workflows/w.yml", "name: t\non: push\njobs: {}\n")
        _write(root, ".github/workflows/notes.md", "- uses: actions/checkout@v4\n")
        expect("workflows with no `uses:` (a .md file is not a workflow)",
               root, False, "no `uses:`")

    if failures:
        print(f"SELF-TEST FAILED: {failures} of {checked} case(s).", file=sys.stderr)
        return 1
    print(f"Action pin self-test: {checked} cases correct.")
    return 0


def main() -> int:
    if sys.argv[1:] == ["--self-test"]:
        return self_test()
    if sys.argv[1:]:
        print(__doc__, file=sys.stderr)
        return 2
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    problems, counts = check(root)
    if problems:
        for problem in problems:
            print(problem, file=sys.stderr)
        print(f"F-14 regression: {len(problems)} problem(s); every remote `uses:` "
              f"must name a full commit SHA (see docs/CI_POLICY.md §9).",
              file=sys.stderr)
        return 1
    print(f"F-14: {counts['remote']} remote reference(s) pinned to a commit SHA, "
          f"{counts['docker']} docker digest(s), {counts['local']} local action(s).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
