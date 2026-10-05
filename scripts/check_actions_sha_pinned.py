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

  ./path                          a local action or reusable workflow: followed
  docker://image@sha256:<64 hex>  a container: the digest is required
  owner/repo[/path]@<40 hex>      a remote action or reusable workflow

Anything else fails, as does a file that does not parse.  Parsing goes through
a loader that rejects duplicate keys, since YAML leaves the winner of a
duplicate to the reader.  A non-string or empty value, a missing PyYAML, a
tree with no tracked workflow and a tree with no `uses:` at all also fail.

Files come from the git index (`git ls-files`, what CI checks out), and their
text is read from the index too, so the names and the bytes describe the same
snapshot.  Nothing is pruned.  The roots are `.github/workflows/*.yml` and
`*.yaml` (the files GitHub runs) and every tracked `action.yml` /
`action.yaml`.  A `./path` reference is resolved against the repository root,
as the runner resolves it, to a tracked workflow file or to the tracked
`action.yml` / `action.yaml` in that directory, and the target is checked in
turn, so a chain of local actions is followed to its end; a visited set stops
a cycle.  A local reference with no tracked target, one that leaves the
repository, and a workflow or action file tracked as a symlink or submodule
fail closed: the runner would read a file this check never saw.

Usage:
    check_actions_sha_pinned.py              # check the repository
    check_actions_sha_pinned.py --self-test  # prove the check still bites
"""

from __future__ import annotations

import os
import posixpath
import re
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from indexed_source import DerivationFailed, indexed_contents, run_git  # noqa: E402

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
#: A workflow GitHub runs: a YAML file directly in `.github/workflows`.
WORKFLOW_RE = re.compile(r"\.github/workflows/[^/]+\.ya?ml")
#: The metadata file a `./dir` action reference resolves to.
ACTION_NAMES = ("action.yml", "action.yaml")
#: Index modes whose blob is not the file the runner reads: symlink, submodule.
INDIRECT_MODES = {"120000": "a symlink", "160000": "a submodule"}


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


def check_text(rel: str, text: str, counts: dict[str, int]
               ) -> tuple[list[str], list[tuple[int, str]]]:
    """(problems, local references as (line, value)) for one file's text."""
    problems: list[str] = []
    local: list[tuple[int, str]] = []
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
                if value.value.startswith("./"):
                    local.append((line, value.value))
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
    return problems, local


def tracked_modes(root: str) -> dict[str, str]:
    """Every path in the index, with its mode (`git ls-files --stage`)."""
    out = run_git(root, ["ls-files", "--stage", "-z"])
    modes: dict[str, str] = {}
    for entry in out.decode("utf-8", "surrogateescape").split("\0"):
        if not entry:
            continue
        meta, sep, path = entry.partition("\t")
        if not sep or not meta.split():
            raise DerivationFailed(["git", "ls-files", "--stage", "-z"], 0, "",
                                   f"unreadable entry {entry!r}")
        modes[path] = meta.split()[0]
    return modes


def resolve_local(value: str, modes: dict[str, str]) -> tuple[list[str], str | None]:
    """The tracked file(s) a `./path` reference runs, else the reason none."""
    target = posixpath.normpath(value[2:] or ".")
    if target == ".." or target.startswith(("../", "/")):
        return [], "local reference leaves the repository"
    if target in modes:
        if WORKFLOW_RE.fullmatch(target):
            return [target], None
        return [], "local reference names a tracked file that is not a workflow"
    prefix = "" if target == "." else target + "/"
    found = [prefix + name for name in ACTION_NAMES if prefix + name in modes]
    if not found:
        return [], "local reference has no tracked action.yml or action.yaml"
    return found, None


def check(root: str) -> tuple[list[str], dict[str, int]]:
    """Check the roots, then every local target they reach, once each."""
    counts = {"remote": 0, "docker": 0, "local": 0}
    problems: list[str] = []
    try:
        modes = tracked_modes(root)
    except DerivationFailed as err:
        return [f"the git index cannot be listed ({err}), so nothing was checked"], counts
    roots = [p for p in sorted(modes) if WORKFLOW_RE.fullmatch(p)]
    if not roots:
        problems.append(".github/workflows: no tracked workflow, so no workflow "
                        "was checked")
    roots += [p for p in sorted(modes) if posixpath.basename(p) in ACTION_NAMES
              and p not in roots]
    visited: set[str] = set()
    pending = roots
    while pending:
        batch = [p for p in dict.fromkeys(pending) if p not in visited]
        pending = []
        visited.update(batch)
        try:
            texts = indexed_contents(root, batch)
        except DerivationFailed as err:
            return problems + [f"the index cannot be read ({err}), so "
                               f"{len(batch)} file(s) were not checked"], counts
        for rel in batch:
            if modes[rel] in INDIRECT_MODES:
                problems.append(f"{rel}: tracked as {INDIRECT_MODES[modes[rel]]}, "
                                f"so the file the runner reads is not checked")
                continue
            if rel not in texts:
                problems.append(f"{rel}: not UTF-8 text in the index, so its "
                                f"`uses:` cannot be checked")
                continue
            found, local = check_text(rel, texts[rel], counts)
            problems.extend(found)
            for line, value in local:
                targets, reason = resolve_local(value, modes)
                if reason:
                    problems.append(f"{rel}:{line}: {reason}: {value}")
                pending.extend(targets)
    if not problems and not sum(counts.values()):
        problems.append("no `uses:` reference found in .github/workflows or any "
                        "action.yml, so nothing was checked")
    return problems, counts


# --------------------------------------------------------------------------
# Self-test.  Each case's lines start at line 8 of a workflow whose line 7 is
# a pinned step; each tree is a scratch git repository.  Every finding of a
# failing case must name the location it fails on, so a finding that loses its
# location, or a spurious extra one, fails the self-test too.
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


W = ".github/workflows/w.yml"


def _workflow(lines: list[str]) -> str:
    return "\n".join(HEAD + [STEP + line for line in lines]) + "\n"


def _action(*steps: str) -> str:
    """A composite action whose first step is on line 5."""
    return ("name: a\nruns:\n  using: composite\n  steps:\n"
            + "".join(f"    - uses: {step}\n" for step in steps))


PINNED = _action(f"actions/cache@{SHA}")
UNPINNED = _action("actions/cache@v4")

TREES = [
    # (passes, label, tracked files, untracked files, tracked symlinks, must_name)
    (False, "an unpinned step in a composite action",
     {W: _workflow([]), ".github/actions/setup/action.yml": UNPINNED}, {}, {},
     ".github/actions/setup/action.yml:5"),
    (False, "an action under node_modules (a pruned walk skipped it)",
     {W: _workflow(["- uses: ./node_modules/evil"]),
      "node_modules/evil/action.yml": UNPINNED}, {}, {}, "node_modules/evil/action.yml:5"),
    (False, "a local reference with no target",
     {W: _workflow(["- uses: ./.github/actions/missing"])}, {}, {}, f"{W}:8"),
    (False, "a local reference whose target is not tracked",
     {W: _workflow(["- uses: ./tools/act"])}, {"tools/act/action.yml": PINNED}, {},
     f"{W}:8"),
    (False, "a local reference that leaves the repository",
     {W: _workflow(["- uses: ./a/../../other"])}, {}, {}, f"{W}:8"),
    (False, "a local reference to a file that is not a workflow",
     {W: _workflow(["- uses: ./run.sh"]), "run.sh": "true\n"}, {}, {}, f"{W}:8"),
    (True, "a cycle of local actions",
     {W: _workflow(["- uses: ./a"]), "a/action.yml": _action("./b", f"actions/cache@{SHA}"),
      "b/action.yml": _action("./a")}, {}, {}, ""),
    (False, "a chain of local actions ending in an unpinned step",
     {W: _workflow(["- uses: ./a"]), "a/action.yml": _action("./b"),
      "b/action.yaml": _action("./c/"), "c/action.yml": UNPINNED}, {}, {}, "c/action.yml:5"),
    (True, "a local reusable workflow",
     {W: "on: push\njobs:\n  call:\n    uses: ./.github/workflows/r.yml\n",
      ".github/workflows/r.yml": _workflow([])}, {}, {}, ""),
    (False, "an action file tracked as a symlink",
     {W: _workflow(["- uses: ./a"]), "real.yml": UNPINNED}, {}, {"a/action.yml": "../real.yml"},
     "a/action.yml:"),
    (False, "a workflow that is not tracked",
     {}, {W: _workflow(["- uses: actions/checkout@v4"])}, {}, ".github/workflows"),
    (False, "workflows with no `uses:` (a .md file is not a workflow)",
     {W: "name: t\non: push\njobs: {}\n",
      ".github/workflows/notes.md": "- uses: actions/checkout@v4\n"}, {}, {}, "no `uses:`"),
]


def _write(root: str, rel: str, text: str) -> None:
    full = os.path.join(root, rel)
    os.makedirs(os.path.dirname(full), exist_ok=True)
    with open(full, "w", encoding="utf-8") as handle:
        handle.write(text)


def _tree(root: str, tracked: dict[str, str], untracked: dict[str, str],
          links: dict[str, str]) -> None:
    """A git repository at `root`: `tracked` and `links` staged, `untracked` not."""
    os.makedirs(root)
    run_git(root, ["init", "-q"])
    for rel, text in tracked.items():
        _write(root, rel, text)
    for rel, target in links.items():
        os.makedirs(os.path.dirname(os.path.join(root, rel)), exist_ok=True)
        os.symlink(target, os.path.join(root, rel))
    run_git(root, ["add", "--all"])
    for rel, text in untracked.items():
        _write(root, rel, text)


def self_test() -> int:
    failures = 0
    checked = 0
    # A hook exports GIT_DIR / GIT_INDEX_FILE; the scratch repositories must not
    # inherit them, or `git add` would stage into the caller's index.
    for name in [name for name in os.environ if name.startswith("GIT_")]:
        del os.environ[name]

    def expect(label: str, root: str, passes: bool, must_name: str) -> None:
        nonlocal failures, checked
        checked += 1
        problems, _ = check(root)
        if (not problems) != passes:
            verdict = "passed" if not problems else f"failed: {problems}"
            print(f"SELF-TEST FAIL: {label}: {verdict}", file=sys.stderr)
            failures += 1
        elif must_name and not all(p.startswith(must_name) for p in problems):
            print(f"SELF-TEST FAIL: {label}: a finding does not start with "
                  f"{must_name}: {problems}", file=sys.stderr)
            failures += 1

    with tempfile.TemporaryDirectory() as tmp:
        for index, (passes, label, lines, must_name) in enumerate(CASES):
            root = os.path.join(tmp, f"case{index}")
            _tree(root, {W: _workflow(lines),
                         ".github/actions/local/action.yml": PINNED}, {}, {})
            expect(label, root, passes, must_name and f".github/workflows/{must_name}")
        for index, (passes, label, tracked, untracked, links, must_name) in \
                enumerate(TREES):
            root = os.path.join(tmp, f"tree{index}")
            _tree(root, tracked, untracked, links)
            expect(label, root, passes, must_name)

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
