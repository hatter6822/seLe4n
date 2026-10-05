#!/usr/bin/env python3
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
"""Every remote action is pinned to a commit SHA, every image to a digest (F-14).

The files are parsed as YAML, not scanned as text, so a key is what YAML
resolves it to: `"\\u0075ses"` is `uses`, an alias is its anchor's value, a
`<<` merge is the mapping it builds, and a flow mapping is a mapping.  The
walk follows the schema, visiting only the positions GitHub resolves --
`jobs.<id>.uses` and `jobs.<id>.steps[*].uses` in a workflow,
`runs.steps[*].uses` in an action -- so an action input, a `with:` argument
or an `env:` variable that happens to be named `uses` is data.  Each `uses`
value is classified:

  ./path                          a local action or reusable workflow: followed
  docker://image@sha256:<64 hex>  a container: the digest is required
  owner/repo[/path]@<40 hex>      a remote action or reusable workflow

The keys GitHub pulls an image from are read the same way:
`jobs.<id>.container` (a string, or its `image`) and
`jobs.<id>.services.<id>.image` in a workflow, and `runs.image` in an action.
Each must be `[docker://]image[:tag]@sha256:<64 hex>`; a `runs.image` that is
not `docker://` is a Dockerfile path, resolved against the action's directory
as the runner resolves it, and must name a tracked file, whose images are
checked in turn: each `FROM` (read as BuildKit reads it: parser directives,
continuations, comments, `--platform`, `AS <name>`) must name `scratch`, an
earlier stage or a digest-pinned image, and a `# syntax=` frontend must be
digest-pinned.  A document, `jobs`,
job, step, `services`, service or `runs` that is not a mapping, `steps` that
are not a sequence, a container or service with no image, and a value whose
shape is not one of these fail.

Anything else fails, as does a file that does not parse.  Parsing goes through
a loader that rejects duplicate keys, since YAML leaves the winner of a
duplicate to the reader.  A non-string or empty value, a missing PyYAML, a
tree with no tracked workflow and a tree with no `uses:` or image also fail.

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
#: One path component of an image name, as the Docker reference grammar has it.
IMAGE_COMPONENT = r"[a-z0-9]+(?:(?:[._]|__|-+)[a-z0-9]+)*"
#: `[docker://][registry[:port]/]name[/name...][:tag][@sha256:<64 hex>]`.
IMAGE_RE = re.compile(
    rf"(?:docker://)?(?:[A-Za-z0-9.-]+(?::[0-9]+)?/)?{IMAGE_COMPONENT}"
    rf"(?:/{IMAGE_COMPONENT})*(?::[A-Za-z0-9_][A-Za-z0-9_.-]{{0,127}})?"
    rf"(@sha256:[0-9a-f]{{64}})?")
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
        return classify_image(value)
    match = REMOTE_RE.fullmatch(value)
    if not match:
        return "cannot classify this `uses:` value as owner/repo[/path]@ref"
    if not SHA_RE.fullmatch(match.group(4)):
        return f"ref `{match.group(4)}` is not a full 40-hex commit SHA"
    return None


def classify_image(value: str) -> str | None:
    """None when `value` is an image pinned to a digest, else the reason."""
    match = IMAGE_RE.fullmatch(value)
    if not match:
        return "cannot classify this image reference"
    if not match.group(1):
        return "image is not pinned to an @sha256: digest"
    return None


def last_value(mapping, key: str):
    """The node `key` constructs to in `mapping`, or None.

    Construction has already flattened any `<<` merge into the node's pairs,
    merged pairs first, and the last pair for a key is the one it keeps.
    """
    found = None
    for key_node, value_node in mapping.value:
        if isinstance(key_node, yaml.ScalarNode) and key_node.tag == STR_TAG \
                and key_node.value == key:
            found = value_node
    return found


def schema_references(document, workflow: bool, action: bool):
    """(references as (field, kind, node), shape failures as (line, reason)).

    Only the positions GitHub resolves are visited, so a key that happens to be
    named `uses` or `image` anywhere else (an action input, a `with:` argument,
    an `env:` variable) is data and is ignored.  In a workflow:
    `jobs.<id>.uses`, `jobs.<id>.steps[*].uses`, `jobs.<id>.container` (a
    string, or its `image`) and `jobs.<id>.services.<id>.image`.  In an action:
    `runs.steps[*].uses` and `runs.image`.  A node on the way to one of them
    that has the wrong type cannot be followed, so it fails.
    """
    refs: list[tuple[str, str, object]] = []
    shape: list[tuple[int, str]] = []

    def typed(node, field: str, kind, noun: str):
        if node is None or isinstance(node, kind):
            return node
        shape.append((node.start_mark.line + 1,
                      f"`{field}` is not a {noun}, so it cannot be checked"))
        return None

    def mapping(node, field: str):
        return typed(node, field, yaml.MappingNode, "mapping")

    def add(owner, key: str, field: str, kind: str) -> None:
        value = last_value(owner, key)
        if value is not None:
            refs.append((field, kind, value))

    def required_image(node, field: str) -> None:
        if last_value(node, "image") is None:
            shape.append((node.start_mark.line + 1, f"`{field}` has no `image`"))
        add(node, "image", f"{field}.image", "image")

    def steps(owner, prefix: str) -> None:
        sequence = typed(last_value(owner, "steps"), f"{prefix}.steps",
                         yaml.SequenceNode, "sequence")
        for index, step in enumerate(sequence.value if sequence else []):
            field = f"{prefix}.steps[{index}]"
            if mapping(step, field) is not None:
                add(step, "uses", f"{field}.uses", "uses")

    root = mapping(document, "document")
    if root is None:
        return refs, shape
    if workflow:
        jobs = mapping(last_value(root, "jobs"), "jobs")
        for job_key, job in jobs.value if jobs else []:
            job_id = f"jobs.{getattr(job_key, 'value', '?')}"
            if mapping(job, job_id) is None:
                continue
            add(job, "uses", f"{job_id}.uses", "uses")
            steps(job, job_id)
            container = last_value(job, "container")
            if isinstance(container, yaml.MappingNode):
                required_image(container, f"{job_id}.container")
            elif container is not None:
                refs.append((f"{job_id}.container", "image", container))
            services = mapping(last_value(job, "services"), f"{job_id}.services")
            for service_key, service in services.value if services else []:
                service_id = f"{job_id}.services.{getattr(service_key, 'value', '?')}"
                if mapping(service, service_id) is not None:
                    required_image(service, service_id)
    if action:
        runs = mapping(last_value(root, "runs"), "runs")
        if runs is not None:
            steps(runs, "runs")
            add(runs, "image", "runs.image", "image")
    return refs, shape


def check_text(rel: str, text: str, counts: dict[str, int]
               ) -> tuple[list[str], list[tuple[int, str, str]]]:
    """(problems, local references) for one file's text.

    A local reference is (line, field, value): a `uses` value naming `./path`,
    or a `runs.image` naming a Dockerfile rather than a `docker://` image.
    """
    problems: list[str] = []
    local: list[tuple[int, str, str]] = []
    workflow = bool(WORKFLOW_RE.fullmatch(rel))
    action = posixpath.basename(rel) in ACTION_NAMES
    loader = StrictLoader(text)
    try:
        while loader.check_node():
            document = loader.get_node()
            loader.construct_document(document)  # duplicates, unknown tags, merges
            refs, shape = schema_references(document, workflow, action)
            problems.extend(f"{rel}:{line}: {reason}" for line, reason in shape)
            for field, kind, value in refs:
                line = value.start_mark.line + 1
                if not (isinstance(value, yaml.ScalarNode) and value.tag == STR_TAG):
                    problems.append(f"{rel}:{line}: `{field}` is not a string "
                                    f"({value.tag})")
                    continue
                text_value = value.value
                if kind == "uses":
                    reason = classify(text_value)
                    if reason:
                        problems.append(f"{rel}:{line}: `{field}`: {reason}: {text_value}")
                    elif text_value.startswith("./"):
                        local.append((line, field, text_value))
                        counts["local"] += 1
                    else:
                        counts["image" if text_value.startswith("docker://")
                               else "remote"] += 1
                elif field == "runs.image" and not text_value.startswith("docker://"):
                    local.append((line, field, text_value))
                    counts["local"] += 1
                elif reason := classify_image(text_value):
                    problems.append(f"{rel}:{line}: `{field}`: {reason}: {text_value}")
                else:
                    counts["image"] += 1
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


def resolve_dockerfile(rel: str, value: str, modes: dict[str, str]
                       ) -> tuple[str | None, str | None]:
    """(the tracked Dockerfile an action's `runs.image` path names, why not).

    The runner resolves the path against the action's own directory.
    """
    if not value or value.startswith("/") or re.search(r"\s|\$\{\{", value):
        return None, "cannot classify this `runs.image` (not docker:// and not a path)"
    target = posixpath.normpath(posixpath.join(posixpath.dirname(rel), value))
    if target == ".." or target.startswith("../"):
        return None, "`runs.image` leaves the repository"
    if target not in modes or modes[target] in INDIRECT_MODES:
        return None, f"`runs.image` names no tracked file (resolved to {target})"
    return target, None


#: A parser directive: `# key=value` in the lines before anything else.
DIRECTIVE_RE = re.compile(r"#[ \t]*([A-Za-z][A-Za-z0-9_-]*)[ \t]*=[ \t]*(\S*)[ \t]*")


def dockerfile_instructions(text: str) -> tuple[list[tuple[int, str]], list[tuple[int, str]]]:
    """(instructions as (first line, joined text), problems as (line, reason)).

    As BuildKit reads it: parser directives are the `# key=value` lines at the
    very top, and `escape` picks the continuation character (`\\` or a
    backtick); `syntax` names a frontend image, which is pulled, so it is
    returned as a `syntax` pseudo-instruction and checked like a `FROM`.
    A line ending in the escape character (trailing blanks allowed) continues
    on the next, which is appended without trimming; a comment line or a
    blank line inside a continuation is dropped.  A here-document body is not
    recognised, so a body line that starts with `FROM` is checked as one:
    that over-reads, which fails rather than passes.
    """
    lines = text.split("\n")
    problems: list[tuple[int, str]] = []
    instructions: list[tuple[int, str]] = []
    escape = "\\"
    seen: set[str] = set()
    start = 0
    for start, raw in enumerate(lines):
        match = DIRECTIVE_RE.fullmatch(raw.strip())
        if not match:
            break
        key, value = match.group(1).lower(), match.group(2)
        if key in seen:
            problems.append((start + 1, f"parser directive `{key}` is given twice"))
        seen.add(key)
        if key == "escape":
            if value not in ("\\", "`"):
                problems.append((start + 1, f"cannot classify escape character {value!r}"))
            escape = value or "\\"
        elif key == "syntax":
            instructions.append((start + 1, f"syntax {value}"))
    else:
        start = len(lines)
    continued = re.compile(re.escape(escape) + r"[ \t]*$")
    index = start
    while index < len(lines):
        raw = lines[index]
        index += 1
        if not raw.strip() or raw.lstrip().startswith("#"):
            continue
        first = index
        line, more = continued.subn("", raw.lstrip())
        while more and index < len(lines):
            raw = lines[index]
            index += 1
            if not raw.strip() or raw.lstrip().startswith("#"):
                continue
            part, more = continued.subn("", raw)
            line += part
        instructions.append((first, line))
    return instructions, problems


def check_dockerfile(rel: str, text: str, counts: dict[str, int]) -> list[str]:
    """Every image a Dockerfile pulls is digest-pinned.

    Each `FROM [--platform=…] <image> [AS <name>]` names `scratch`, a stage
    named by an earlier `FROM … AS`, or an image with an `@sha256:` digest,
    and a `syntax` directive names a digest-pinned frontend.  An image built
    from a build argument (`$`), a flag other than `--platform`, a malformed
    `FROM`, a bad `escape` directive and a file with no `FROM` fail.
    """
    instructions, shape = dockerfile_instructions(text)
    problems = [f"{rel}:{line}: {reason}" for line, reason in shape]
    stages: set[str] = set()
    froms = 0
    for line, instruction in instructions:
        words = instruction.split()
        keyword = words[0].lower()
        if keyword not in ("from", "syntax"):
            continue
        where = f"{rel}:{line}"
        if keyword == "syntax":
            image = words[1] if len(words) == 2 else ""
            reason = ("cannot classify an image built from a build argument"
                      if "$" in image else classify_image(image))
            if reason:
                problems.append(f"{where}: `# syntax` frontend: {reason}: {image}")
            else:
                counts["image"] += 1
            continue
        froms += 1
        args = words[1:]
        while args and args[0].startswith("--"):
            if not args[0].lower().startswith("--platform="):
                problems.append(f"{where}: cannot classify the FROM flag `{args[0]}`")
            args = args[1:]
        if len(args) == 3 and args[1].lower() == "as":
            image, stage = args[0], args[2].lower()
        elif len(args) == 1:
            image, stage = args[0], None
        else:
            problems.append(f"{where}: cannot classify this FROM: {instruction.strip()}")
            continue
        if "$" in image:
            problems.append(f"{where}: cannot classify an image built from a build "
                            f"argument: {image}")
        elif image.lower() == "scratch" or image.lower() in stages:
            counts["local"] += 1
        elif reason := classify_image(image):
            problems.append(f"{where}: FROM: {reason}: {image}")
        else:
            counts["image"] += 1
        if stage:
            stages.add(stage)
    if not froms:
        problems.append(f"{rel}: has no FROM instruction, so its base image cannot "
                        f"be checked")
    return problems


def check(root: str) -> tuple[list[str], dict[str, int]]:
    """Check the roots, then every local target they reach, once each."""
    counts = {"remote": 0, "image": 0, "local": 0}
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
    dockerfiles: dict[str, None] = {}
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
            for line, field, value in local:
                if field == "runs.image":
                    dockerfile, reason = resolve_dockerfile(rel, value, modes)
                    if dockerfile:
                        dockerfiles[dockerfile] = None
                    targets = []
                else:
                    targets, reason = resolve_local(value, modes)
                if reason:
                    problems.append(f"{rel}:{line}: {reason}: {value}")
                pending.extend(targets)
    # The Dockerfiles the visited actions build, read from the same index.
    try:
        texts = indexed_contents(root, list(dockerfiles))
    except DerivationFailed as err:
        return problems + [f"the index cannot be read ({err}), so "
                           f"{len(dockerfiles)} Dockerfile(s) were not checked"], counts
    for rel in dockerfiles:
        if rel not in texts:
            problems.append(f"{rel}: not UTF-8 text in the index, so its FROM "
                            f"images cannot be checked")
        else:
            problems.extend(check_dockerfile(rel, texts[rel], counts))
    if not problems and not sum(counts.values()):
        problems.append("no `uses:` or image reference found in .github/workflows "
                        "or any action.yml, so nothing was checked")
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
    (True, "a `uses` key under `with:` and `env:` (data, not a reference)",
     [f"- uses: actions/checkout@{SHA}", "  with:", "    uses: v4", "  env:",
      "    uses: actions/checkout@v4"], ""),
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
    (False, "a step that is not a mapping", ["- actions/checkout@v4"], "w.yml:8"),
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


def _job(lines: list[str]) -> str:
    """A workflow whose job-level lines start at line 6."""
    return "\n".join(["on: push", "jobs:", "  j:", "    runs-on: ubuntu-latest",
                      f"    steps: [{{uses: actions/checkout@{SHA}}}]"]
                     + ["    " + line for line in lines]) + "\n"


def _docker(image: str) -> str:
    """A Docker action whose `runs.image` is on line 4."""
    return f"name: d\nruns:\n  using: docker\n  image: {image}\n"


#: A workflow step that runs the Docker action at `d/`.
RUN_D = {W: _workflow(["- uses: ./d"])}

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
    # The walk follows the schema: a `uses` key elsewhere is data.
    (True, "an action input named `uses`",
     {W: _workflow(["- uses: ./a"]),
      "a/action.yml": "name: a\ninputs:\n  uses:\n    description: which action\n"
                      "    default: actions/checkout@v4\nruns:\n  using: composite\n"
                      f"  steps:\n    - uses: actions/cache@{SHA}\n"}, {}, {}, ""),
    (False, "a job-level reusable workflow on a tag",
     {W: "on: push\njobs:\n  call:\n    uses: octo-org/repo/.github/workflows/ci.yml@v1\n"},
     {}, {}, f"{W}:4"),
    (False, "job steps that are not a sequence",
     {W: "on: push\njobs:\n  j:\n    runs-on: x\n    steps: {uses: actions/checkout@v4}\n"},
     {}, {}, f"{W}:5"),
    (False, "composite steps that are not a sequence",
     {W: _workflow(["- uses: ./a"]),
      "a/action.yml": "name: a\nruns:\n  using: composite\n  steps: actions/cache@v4\n"},
     {}, {}, "a/action.yml:4"),
    # Images: a job's container, its services, and a Docker action's runs.image.
    (True, "a container pinned to a digest",
     {W: _job([f"container: node:18@sha256:{DIGEST}"])}, {}, {}, ""),
    (True, "a container mapping on a registry with a port",
     {W: _job(["container:", f"  image: localhost:5000/team/ci-img:1.2@sha256:{DIGEST}"])},
     {}, {}, ""),
    (True, "a service pinned to a digest",
     {W: _job(["services:", "  db:", f"    image: ghcr.io/o/postgres@sha256:{DIGEST}"])},
     {}, {}, ""),
    (True, "a Docker action on a pinned docker:// image",
     {**RUN_D, "d/action.yml": _docker(f"docker://alpine:3.8@sha256:{DIGEST}")}, {}, {}, ""),
    (True, "a Docker action on a tracked Dockerfile beside it",
     {**RUN_D, "d/action.yml": _docker("Dockerfile"), "d/Dockerfile": "FROM scratch\n"},
     {}, {}, ""),
    (False, "a container on a tag", {W: _job(["container: node:18"])}, {}, {}, f"{W}:6"),
    (False, "a container mapping on a tag",
     {W: _job(["container:", "  image: node:18"])}, {}, {}, f"{W}:7"),
    (False, "a container mapping with no image",
     {W: _job(["container:", "  options: --cpus 1"])}, {}, {}, f"{W}:7"),
    (False, "a container from an expression",
     {W: _job(["container: ${{ matrix.image }}"])}, {}, {}, f"{W}:6"),
    (False, "a container that is not a string", {W: _job(["container: [node]"])}, {}, {},
     f"{W}:6"),
    (False, "a container with a short digest",
     {W: _job(["container: node@sha256:abc123"])}, {}, {}, f"{W}:6"),
    (False, "a service on a tag",
     {W: _job(["services:", "  db:", "    image: postgres:16"])}, {}, {}, f"{W}:8"),
    (False, "a service with no image",
     {W: _job(["services:", "  db:", "    ports: [5432]"])}, {}, {}, f"{W}:8"),
    (False, "services that are not a mapping", {W: _job(["services: [db]"])}, {}, {},
     f"{W}:6"),
    (False, "a job that is not a mapping", {W: "on: push\njobs:\n  j: run\n"}, {}, {},
     f"{W}:3"),
    (False, "a container merged in with `<<`",
     {W: "on: push\nx-base: &base\n  container: node:18\njobs:\n  j:\n    <<: *base\n"
         f"    runs-on: ubuntu-latest\n    steps: [{{uses: actions/checkout@{SHA}}}]\n"},
     {}, {}, f"{W}:3"),
    (False, "a Docker action on a docker:// tag",
     {**RUN_D, "d/action.yml": _docker("docker://alpine:3.8")}, {}, {}, "d/action.yml:4"),
    (False, "a Docker action on a remote image without docker://",
     {**RUN_D, "d/action.yml": _docker("alpine:3.8")}, {}, {}, "d/action.yml:4"),
    (False, "a Docker action on an untracked Dockerfile",
     {**RUN_D, "d/action.yml": _docker("Dockerfile")}, {"d/Dockerfile": "FROM scratch\n"},
     {}, "d/action.yml:4"),
    (False, "a Docker action on a Dockerfile outside the repository",
     {**RUN_D, "d/action.yml": _docker("../../Dockerfile")}, {}, {}, "d/action.yml:4"),
    # A Dockerfile's FROM images, as BuildKit reads them.
    (True, "a Dockerfile FROM pinned to a digest",
     {**RUN_D, "d/action.yml": _docker("Dockerfile"),
      "d/Dockerfile": f"FROM alpine:3.19@sha256:{DIGEST}\nRUN true\n"}, {}, {}, ""),
    (True, "a multi-stage Dockerfile: flags, continuation, comments, stage names",
     {**RUN_D, "d/action.yml": _docker("Dockerfile"),
      "d/Dockerfile": "# FROM alpine:latest is a comment\n"
                      "from --platform=$BUILDPLATFORM \\  \n  # the base\n\n"
                      f"    ghcr.io/o/base@sha256:{DIGEST} as Build\n"
                      "RUN make\nFROM scratch\nFROM build AS final\n"}, {}, {}, ""),
    (True, "a pinned syntax frontend and a backtick escape",
     {**RUN_D, "d/action.yml": _docker("Dockerfile"),
      "d/Dockerfile": f"# syntax=docker/dockerfile:1@sha256:{DIGEST}\n# escape=`\n"
                      f"FROM `\n  alpine@sha256:{DIGEST}\n"}, {}, {}, ""),
    (False, "a Dockerfile FROM on a tag",
     {**RUN_D, "d/action.yml": _docker("Dockerfile"), "d/Dockerfile": "FROM alpine:latest\n"},
     {}, {}, "d/Dockerfile:1"),
    (False, "a Dockerfile FROM with no tag",
     {**RUN_D, "d/action.yml": _docker("Dockerfile"), "d/Dockerfile": "FROM alpine\n"},
     {}, {}, "d/Dockerfile:1"),
    (False, "an unpinned FROM after a pinned stage",
     {**RUN_D, "d/action.yml": _docker("Dockerfile"),
      "d/Dockerfile": f"FROM alpine@sha256:{DIGEST} AS a\nRUN x\nFROM debian:12\n"},
     {}, {}, "d/Dockerfile:3"),
    (False, "an unpinned image split across a continuation",
     {**RUN_D, "d/action.yml": _docker("Dockerfile"), "d/Dockerfile": "FROM alp\\\nine:3\n"},
     {}, {}, "d/Dockerfile:1"),
    (False, "a FROM built from a build argument",
     {**RUN_D, "d/action.yml": _docker("Dockerfile"),
      "d/Dockerfile": f"ARG BASE=alpine@sha256:{DIGEST}\nFROM ${{BASE}}\n"},
     {}, {}, "d/Dockerfile:2"),
    (False, "a stage named only later",
     {**RUN_D, "d/action.yml": _docker("Dockerfile"),
      "d/Dockerfile": f"FROM build\nFROM alpine@sha256:{DIGEST} AS build\n"},
     {}, {}, "d/Dockerfile:1"),
    (False, "a FROM flag other than --platform",
     {**RUN_D, "d/action.yml": _docker("Dockerfile"),
      "d/Dockerfile": f"FROM --pull=always alpine@sha256:{DIGEST}\n"}, {}, {}, "d/Dockerfile:1"),
    (False, "a malformed FROM",
     {**RUN_D, "d/action.yml": _docker("Dockerfile"),
      "d/Dockerfile": f"FROM alpine@sha256:{DIGEST} AS\n"}, {}, {}, "d/Dockerfile:1"),
    (False, "a Dockerfile with no FROM",
     {**RUN_D, "d/action.yml": _docker("Dockerfile"), "d/Dockerfile": "RUN true\n"},
     {}, {}, "d/Dockerfile"),
    (False, "an unpinned syntax frontend",
     {**RUN_D, "d/action.yml": _docker("Dockerfile"),
      "d/Dockerfile": f"# syntax=docker/dockerfile:1\nFROM alpine@sha256:{DIGEST}\n"},
     {}, {}, "d/Dockerfile:1"),
    (False, "an escape directive it cannot classify",
     {**RUN_D, "d/action.yml": _docker("Dockerfile"),
      "d/Dockerfile": f"# escape=x\nFROM alpine@sha256:{DIGEST}\n"}, {}, {}, "d/Dockerfile:1"),
    (False, "an action whose `runs` is not a mapping",
     {**RUN_D, "d/action.yml": "name: d\nruns: docker\n"}, {}, {}, "d/action.yml:2"),
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
              f"must name a full commit SHA and every image an @sha256: digest "
              f"(see docs/CI_POLICY.md §9).",
              file=sys.stderr)
        return 1
    print(f"F-14: {counts['remote']} remote reference(s) pinned to a commit SHA, "
          f"{counts['image']} image(s) pinned to a digest, {counts['local']} local "
          f"reference(s).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
