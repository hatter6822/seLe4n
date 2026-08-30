#!/usr/bin/env python3
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
"""WS-RR RR1.8 -- keep the aarch64 cross-compile coverage configured.

Before WS-RR RR1 no aarch64 target was compiled anywhere in the tree or in
CI, so 67 ``#[cfg(target_arch = "aarch64")]`` blocks, 57 ``asm!`` sites and
all three ``.S`` files had zero compile coverage.  RR1 built that coverage;
this gate keeps it, because every way of losing it again is silent:

1. **TOOLCHAIN** -- ``rust/rust-toolchain.toml`` must list
   ``aarch64-unknown-none`` under ``targets``.  Dropping it does not fail
   anything on a machine that already has the target installed; it fails on
   the next fresh clone, and on a CI runner it fails as a missing ``core``,
   which reads as a source defect.

2. **GATE** -- ``scripts/test_aarch64_cross_build.sh`` must exist, be
   executable, and keep what makes it mean anything: the target triple,
   ``--features hw_target``, and a ``cargo build --target`` in *both*
   profiles.  Each is load-bearing in a way that is invisible if lost.  The
   feature is empty by default and guards the hardware-only paths, so a run
   without it compiles none of the code the gate exists to cover.  ``cargo
   check`` stops before code generation, so it never hands an ``asm!``
   template to the assembler -- it reported the tree clean while four
   ``TLBI *OS`` sites could not be encoded for the target at all.  And
   inline-asm register allocation depends on the optimisation level, so a
   single profile is half the coverage.  A gate weakened in any of those
   directions stays green over nothing.

3. **CI** -- ``.github/workflows/lean_action_ci.yml`` must contain a job that
   runs that script and installs the target for it.  A gate script nothing
   invokes is not a gate.

4. **ASSEMBLY** -- ``rust/sele4n-hal/build.rs`` must still hand all three
   ``.S`` sources to the assembler.  Dropping a ``.file`` line removes that
   source's only compile coverage without failing any build.

5. **HOST LANE** -- ``scripts/test_rust.sh`` must run its tests with
   ``host_tools``.  The feature exists because the Tier-5 oracle is a
   ``std`` binary that cannot build for the bare-metal target, and gating it
   has a cost on the other side: a ``required-features`` target that is not
   selected is not merely skipped from the build, its ``#[cfg(test)]``
   module does not run either.  Dropping the flag silently removes 14 tests
   and the step still reports a clean pass over one fewer binary -- which is
   how this gate found the defect on the very cut that introduced it.

A presence check is not a relation check.  Each check below resolves the
text into the structure it stands for -- the script's variables are expanded
so flags are read ON the build command, the build script's `.file` calls are
located between the arch gate and the `.compile` that consumes them, the
toolchain's `targets` array is matched by element -- because searching for a
token anywhere in the file is satisfied by an unused assignment, a step name
or a dead helper.  Seven such holes shipped in this cut; see CLAUDE.md's
"A presence check is not a relation check".  Add a check here only with a
negative case that KEEPS its token and breaks its relation.

Gates read code, prose reads prose: the YAML, TOML and shell files scanned
here are stripped of ``#`` comments (quote-aware) first and ``build.rs`` of
its ``//`` comments, so the sentences in this docstring -- and the
explanatory comments in the workflow, the toolchain file, the gate script
and the build script -- can neither satisfy a check nor trip one.

Usage:
    check_aarch64_cross_target.py              # scan the repository
    check_aarch64_cross_target.py --self-test  # prove the gate still bites

Exits 0 when clean, 1 on any violation or self-test failure.
"""

from __future__ import annotations

import os
import re
import sys
import tempfile

CROSS_TARGET = "aarch64-unknown-none"
GATE_SCRIPT = "scripts/test_aarch64_cross_build.sh"
TOOLCHAIN_FILE = "rust/rust-toolchain.toml"
WORKFLOW_FILE = ".github/workflows/lean_action_ci.yml"
BUILD_SCRIPT = "rust/sele4n-hal/build.rs"
HOST_LANE = "scripts/test_rust.sh"
ASM_SOURCES = ("src/boot.S", "src/vectors.S", "src/trap.S")


def split_comment(line: str) -> str:
    """Return the code half of a ``#``-commented line, respecting quotes.

    A ``#`` opens a comment only outside quotes and only at line start or
    after whitespace.  That rule holds for YAML, TOML and POSIX shell alike,
    which is why one function serves all three file kinds scanned here.
    """
    quote = None
    for i, ch in enumerate(line):
        if quote is not None:
            if ch == quote:
                quote = None
        elif ch in ('"', "'"):
            quote = ch
        elif ch == "#" and (i == 0 or line[i - 1] in " \t"):
            return line[:i]
    return line


def code_view(text: str) -> str:
    """Strip ``#`` comments from every line, keeping line structure."""
    return "\n".join(split_comment(line) for line in text.splitlines())


def rust_code_view(text: str) -> str:
    """Strip ``//`` line comments from Rust source, keeping line structure.

    ``build.rs`` documents each scanner it runs in a ``///`` docstring that
    names the very ``.S`` files this gate looks for, so reading the raw text
    would let the prose satisfy the check.
    """
    out = []
    for line in text.splitlines():
        idx = line.find("//")
        out.append(line if idx < 0 else line[:idx])
    return "\n".join(out)


SHELL_ASSIGN = re.compile(
    r"""^\s*([A-Za-z_][A-Za-z0-9_]*)=(?:"([^"\n]*)"|'([^'\n]*)'|(\S*))\s*$""",
    re.MULTILINE,
)


def expand_shell_vars(code: str) -> str:
    """Substitute simple `NAME=value` assignments into `$NAME` / `${NAME}`.

    The gate script keeps its settings in variables and passes them to
    cargo, so a check that looks for the target triple or the feature name
    anywhere in the file is satisfied by the *assignment* and says nothing
    about the command.  Expanding first means the checks below read what
    cargo will actually receive.

    Deliberately simple: literal single-line assignments only, applied
    longest-name-first so `$CROSS_TARGET` is not partly eaten by a shorter
    `$CROSS`.  A value this cannot resolve is left as the bare `$NAME`,
    which fails the checks -- the safe direction for a gate.

    A name assigned more than once is NOT expanded, for the same reason.
    Taking the first assignment would read `CROSS_FEATURES="hw_target"`
    while the command that runs receives a later `CROSS_FEATURES=""`, and
    taking the last is equally wrong under a conditional.  Leaving it
    unresolved makes the checks fail rather than pass on a value the gate
    cannot actually determine -- which is the whole point of this cut.
    """
    values: dict[str, str] = {}
    reassigned: set[str] = set()
    for match in SHELL_ASSIGN.finditer(code):
        name = match.group(1)
        value = next(g for g in match.groups()[1:] if g is not None)
        if name in values and values[name] != value:
            reassigned.add(name)
        values.setdefault(name, value)
    for name in reassigned:
        del values[name]
    for name in sorted(values, key=len, reverse=True):
        code = code.replace(f"${{{name}}}", values[name]).replace(
            f"${name}", values[name]
        )
    return code


def read(root: str, rel: str) -> str | None:
    path = os.path.join(root, rel)
    try:
        with open(path, encoding="utf-8") as handle:
            return handle.read()
    except OSError:
        return None


def check_toolchain(root: str) -> list[str]:
    """`rust-toolchain.toml` still asks rustup for the cross target."""
    text = read(root, TOOLCHAIN_FILE)
    if text is None:
        return [f"{TOOLCHAIN_FILE}: missing"]
    code = code_view(text)
    # `targets = [...]` may wrap across lines; join the whole code view and
    # look for the key with the triple inside its array.
    match = re.search(r"targets\s*=\s*\[(.*?)\]", code, re.DOTALL)
    if match is None:
        return [
            f"{TOOLCHAIN_FILE}: no `targets = [...]` key. "
            f"The `{CROSS_TARGET}` target must be listed there so rustup "
            f"installs it on first use from rust/; without it a fresh clone "
            f"fails the aarch64 gate with a missing `core` crate."
        ]
    # Exact ELEMENTS, not a substring of the array text.
    # `targets = ["aarch64-unknown-none-softfloat"]` is a real and
    # different target that contains the triple as a prefix, so a
    # substring test passes while rustup installs something the gate
    # script never builds for.
    elements = re.findall(r'"([^"]*)"|\'([^\']*)\'', match.group(1))
    listed = {a or b for a, b in elements}
    if CROSS_TARGET not in listed:
        return [
            f"{TOOLCHAIN_FILE}: `targets` does not list `{CROSS_TARGET}` "
            f"as an element (found: {sorted(listed) or match.group(1).strip()})."
        ]
    return []


def check_gate_script(root: str) -> list[str]:
    """The gate script exists, is runnable, and keeps its load-bearing flags."""
    problems: list[str] = []
    text = read(root, GATE_SCRIPT)
    if text is None:
        return [
            f"{GATE_SCRIPT}: missing. It is the single place the aarch64 "
            f"build flags live; CI and developers both invoke it."
        ]
    path = os.path.join(root, GATE_SCRIPT)
    if not os.access(path, os.X_OK):
        problems.append(f"{GATE_SCRIPT}: not executable (chmod +x).")

    # Expand the script's own shell variables before matching.  Searching
    # for the target triple and the feature name as free-floating tokens
    # would be satisfied by their `CROSS_TARGET=`/`CROSS_FEATURES=`
    # assignments alone, so a script that kept those assignments unused and
    # built `--target x86_64-unknown-linux-gnu --features other` would pass
    # a gate whose entire purpose is that CI still compiles the AArch64
    # paths.  The settings are therefore checked ON the build commands.
    code = expand_shell_vars(code_view(text))

    cross_builds = [
        line
        for line in code.splitlines()
        if re.search(r"cargo\s+build\b", line)
    ]
    targeted = [
        line
        for line in cross_builds
        if re.search(rf"--target[=\s]+\S*{re.escape(CROSS_TARGET)}", line)
    ]
    if not targeted:
        problems.append(
            f"{GATE_SCRIPT}: no `cargo build` names `--target "
            f"{CROSS_TARGET}`. `cargo check` stops before code generation, "
            f"so it never reaches the backend and cannot surface an `asm!` "
            f"or codegen error -- which is the defect class this gate "
            f"exists for -- and a build for any other target compiles none "
            f"of the cross surface."
        )
    unfeatured = [
        line
        for line in targeted
        if not re.search(r"--features[=\s]+\S*\bhw_target\b", line)
        and "--all-features" not in line
    ]
    if targeted and unfeatured:
        problems.append(
            f"{GATE_SCRIPT}: a cross `cargo build` does not pass "
            f"`--features hw_target`: {unfeatured[0].strip()!r}. The "
            f"feature is empty by default and guards the hardware-only "
            f"paths (the Lean calls in timer.rs, trap.rs and smp.rs), so "
            f"without it the gate compiles none of the code it exists to "
            f"cover and stays green through a regression in exactly those "
            f"blocks."
        )
    if targeted:
        # Both profiles, because inline-asm register allocation and
        # constraint checking depend on the optimisation level: an `asm!`
        # block the allocator satisfies at `-O0` can fail to at `-O2`, and
        # the deployed kernel is a release build.  Losing one profile still
        # leaves a `cargo build --target` in the file, so the pair is
        # checked rather than the presence of a build.
        missing = [
            profile
            for profile, present in (
                ("debug", any("--release" not in b for b in cross_builds)),
                ("release", any("--release" in b for b in cross_builds)),
            )
            if not present
        ]
        if missing:
            problems.append(
                f"{GATE_SCRIPT}: no cross `cargo build` for the "
                f"{' and '.join(missing)} profile. Both are built because "
                f"inline-asm register allocation depends on the "
                f"optimisation level -- an `asm!` block that satisfies the "
                f"allocator at `-O0` can fail to at `-O2`, and the deployed "
                f"kernel is a release build."
            )
    return problems


def workflow_jobs(code: str) -> dict[str, list[str]]:
    """Split the workflow's code view into ``job name -> its lines``.

    A two-space-indented ``name:`` line under ``jobs:`` opens a job; the job
    body is every line indented further, up to the next such line.  That is
    enough structure for the questions this gate asks, and it avoids a
    dependency on a YAML parser the CI image is not guaranteed to have.
    """
    lines = code.splitlines()
    jobs: dict[str, list[str]] = {}
    in_jobs = False
    current: str | None = None
    for line in lines:
        if re.match(r"^jobs\s*:\s*$", line):
            in_jobs = True
            continue
        if not in_jobs:
            continue
        if line.strip() and not line.startswith(" "):
            # Back to a top-level key: `jobs:` has ended.
            in_jobs = False
            current = None
            continue
        header = re.match(r"^  ([A-Za-z0-9_-]+)\s*:\s*$", line)
        if header:
            current = header.group(1)
            jobs[current] = []
            continue
        if current is not None:
            jobs[current].append(line)
    return jobs


def check_workflow(root: str) -> list[str]:
    """Some CI job runs the gate script, and installs the target for it."""
    text = read(root, WORKFLOW_FILE)
    if text is None:
        return [f"{WORKFLOW_FILE}: missing"]
    code = code_view(text)
    jobs = workflow_jobs(code)

    # A job runs the gate only if a `run:` value invokes it.  Matching the
    # path anywhere in the job body is satisfied by a step *name* --
    # "Build sele4n-hal for aarch64-unknown-none" is one line away from
    # "replaced ./scripts/test_aarch64_cross_build.sh" -- so a job could
    # look like the runner while running nothing.
    run_invokes = re.compile(
        rf"^\s*(?:-\s*)?run\s*:.*{re.escape(GATE_SCRIPT)}", re.MULTILINE
    )
    runners = [
        name for name, body in jobs.items() if run_invokes.search("\n".join(body))
    ]
    if not runners:
        return [
            f"{WORKFLOW_FILE}: no job runs `{GATE_SCRIPT}`. A gate script "
            f"nothing invokes is not a gate -- the aarch64 surface would go "
            f"uncompiled on every PR with nothing reporting it."
        ]

    problems: list[str] = []
    # Matched as a `targets:` KEY carrying the triple, not as the triple
    # appearing anywhere in the job.  The step that runs the gate is named
    # "Build sele4n-hal for aarch64-unknown-none", so a substring search
    # over the job body is satisfied by a step *name* and would report the
    # target installed after the `targets:` input was deleted -- which is
    # exactly what a first version of this check did.
    targets_key = re.compile(
        rf"^\s*targets\s*:\s*.*\b{re.escape(CROSS_TARGET)}\b", re.MULTILINE
    )
    for name in runners:
        body = "\n".join(jobs[name])
        if not targets_key.search(body):
            problems.append(
                f"{WORKFLOW_FILE}: job `{name}` runs the aarch64 gate but "
                f"has no `targets:` input naming `{CROSS_TARGET}` on its "
                f"rust-toolchain step. The gate would then depend on "
                f"whatever the runner image happens to ship."
            )
    return problems


def check_build_script(root: str) -> list[str]:
    """`build.rs` still hands all three `.S` sources to the assembler."""
    text = read(root, BUILD_SCRIPT)
    if text is None:
        return [f"{BUILD_SCRIPT}: missing"]
    code = rust_code_view(text)

    # The `.file` calls must sit in the LIVE assembly chain: after the
    # `CARGO_CFG_TARGET_ARCH` gate that returns early on non-aarch64, and
    # before the `.compile(...)` that consumes them.  Presence anywhere in
    # the file is satisfied by a dead helper or a second, unused
    # `cc::Build`, which assembles nothing while the check reports the
    # source covered.
    gate_at = code.find("CARGO_CFG_TARGET_ARCH")
    compile_at = code.find('.compile("sele4n_hal_asm")')
    if gate_at < 0 or compile_at < 0 or gate_at > compile_at:
        return [
            f"{BUILD_SCRIPT}: cannot locate the assembly block "
            f"(`CARGO_CFG_TARGET_ARCH` gate at {gate_at}, "
            f'`.compile("sele4n_hal_asm")` at {compile_at}). If the build '
            f"script was restructured, update this gate so the three `.S` "
            f"sources stay pinned to the live chain."
        ]

    missing = [
        src
        for src in ASM_SOURCES
        if not any(
            gate_at < pos < compile_at
            for pos in _occurrences(code, f'.file("{src}")')
        )
    ]
    if missing:
        return [
            f"{BUILD_SCRIPT}: {', '.join(missing)} is not handed to the "
            f"assembler in the live chain (expected a `.file(\"<path>\")` "
            f"call between the `CARGO_CFG_TARGET_ARCH` gate and "
            f'`.compile("sele4n_hal_asm")`). Dropping a source -- or '
            f"leaving it only in an unreachable one -- removes its only "
            f"compile coverage without failing any build."
        ]
    return []


def _occurrences(haystack: str, needle: str) -> list[int]:
    """Every start offset of `needle` in `haystack`."""
    found, start = [], haystack.find(needle)
    while start >= 0:
        found.append(start)
        start = haystack.find(needle, start + 1)
    return found


def check_host_lane(root: str) -> list[str]:
    """The host lane still selects the `host_tools`-gated targets."""
    text = read(root, HOST_LANE)
    if text is None:
        return [
            f"{HOST_LANE}: missing. It is the host half of the Rust "
            f"coverage; the cross gate does not run any tests."
        ]
    # Expanded for the same reason as the gate script above: the flags are
    # read ON the command, so a settings variable must be resolved first.
    code = expand_shell_vars(code_view(text))
    test_lines = [
        line for line in code.splitlines() if re.search(r"cargo\s+test\b", line)
    ]
    if not test_lines:
        return [f"{HOST_LANE}: no `cargo test` invocation found."]
    # `--all-features` enables `host_tools` along with everything else, so
    # it satisfies the requirement; rejecting it would fail a
    # configuration that is in fact correct.
    if not any(
        "host_tools" in line or "--all-features" in line for line in test_lines
    ):
        return [
            f"{HOST_LANE}: no `cargo test` invocation selects `host_tools`. "
            f"`src/bin/rw_lock_oracle.rs` carries "
            f"`required-features = [\"host_tools\"]` so the bare-metal build "
            f"skips it -- and cargo does not run a skipped target's "
            f"`#[cfg(test)]` module either, so without the feature its tests "
            f"stop running and the step still reports a clean pass over one "
            f"fewer binary."
        ]
    return []


def run_checks(root: str) -> list[str]:
    problems: list[str] = []
    problems += check_toolchain(root)
    problems += check_gate_script(root)
    problems += check_workflow(root)
    problems += check_build_script(root)
    problems += check_host_lane(root)
    return problems


# ---------------------------------------------------------------------------
# Self-test.
#
# A scanner that under-reaches reports PASS, so each defect it exists to
# catch is reproduced here and asserted caught, and the clean baseline is
# asserted to pass.  Two of the fixtures put the expected token in a comment
# instead of in code: a gate satisfied by prose measures nothing.
# ---------------------------------------------------------------------------

GOOD_TOOLCHAIN = f"""# comment naming {CROSS_TARGET} must not satisfy the gate
[toolchain]
channel = "1.94.1"
components = ["clippy", "rustfmt"]
targets = ["{CROSS_TARGET}"]
profile = "minimal"
"""

# Two shapes here are deliberate, because the real files have them and a
# looser fixture let both checks pass over a real defect: the gate builds
# BOTH profiles (so mutating only the first line leaves a `cargo build`
# behind), and the workflow's step NAME carries the triple (so a substring
# search over the job body stays satisfied after `targets:` is deleted).
GOOD_GATE = f"""#!/usr/bin/env bash
set -euo pipefail
CROSS_TARGET="{CROSS_TARGET}"
cargo build --target "$CROSS_TARGET" -p sele4n-hal --features hw_target
cargo build --release --target "$CROSS_TARGET" -p sele4n-hal --features hw_target
"""

GOOD_WORKFLOW = f"""name: CI
on: [pull_request]
jobs:
  test-rust:
    runs-on: ubuntu-latest
    steps:
      - run: ./scripts/test_rust.sh
  test-aarch64-cross:
    runs-on: ubuntu-latest
    steps:
      - uses: dtolnay/rust-toolchain@0000000000000000000000000000000000000000
        with:
          toolchain: 1.94.1
          targets: {CROSS_TARGET}
      - name: Build sele4n-hal for {CROSS_TARGET}
        run: ./{GATE_SCRIPT}
"""

GOOD_HOST_LANE = """#!/usr/bin/env bash
set -euo pipefail
cargo build --all --features host_tools
cargo test --all --features std,host_tools
cargo clippy --all-targets --all-features -- -D warnings
"""

# Mirrors the real `build.rs` shape: an arch gate that returns early, then
# the live `cc::Build` chain.  A fixture without the gate is thinner than
# the file under test, and a check calibrated against it measures less than
# it appears to.
GOOD_BUILD_RS = """fn main() {
    let target_arch = std::env::var("CARGO_CFG_TARGET_ARCH").unwrap_or_default();
    if target_arch != "aarch64" {
        return;
    }

    let mut asm = cc::Build::new();
    asm.file("src/boot.S")
        .file("src/vectors.S")
        .file("src/trap.S")
        .compile("sele4n_hal_asm");
}
"""


def write_tree(root: str, files: dict[str, str]) -> None:
    for rel, content in files.items():
        path = os.path.join(root, rel)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w", encoding="utf-8") as handle:
            handle.write(content)
    gate = os.path.join(root, GATE_SCRIPT)
    if os.path.exists(gate):
        os.chmod(gate, 0o755)


def baseline() -> dict[str, str]:
    return {
        TOOLCHAIN_FILE: GOOD_TOOLCHAIN,
        GATE_SCRIPT: GOOD_GATE,
        WORKFLOW_FILE: GOOD_WORKFLOW,
        BUILD_SCRIPT: GOOD_BUILD_RS,
        HOST_LANE: GOOD_HOST_LANE,
    }


def self_test() -> int:
    cases: list[tuple[str, dict[str, str], bool]] = []

    cases.append(("clean baseline", baseline(), False))

    drop_target = baseline()
    drop_target[TOOLCHAIN_FILE] = GOOD_TOOLCHAIN.replace(
        f'targets = ["{CROSS_TARGET}"]\n', ""
    )
    cases.append(("toolchain drops the targets key", drop_target, True))

    comment_target = baseline()
    comment_target[TOOLCHAIN_FILE] = GOOD_TOOLCHAIN.replace(
        f'targets = ["{CROSS_TARGET}"]',
        f'targets = ["aarch64-unknown-linux-gnu"]',
    )
    cases.append(("toolchain lists the wrong target", comment_target, True))

    no_feature = baseline()
    no_feature[GATE_SCRIPT] = GOOD_GATE.replace(" --features hw_target", "")
    cases.append(("gate drops --features hw_target", no_feature, True))

    feature_in_prose = baseline()
    feature_in_prose[GATE_SCRIPT] = GOOD_GATE.replace(
        " --features hw_target", "  # was --features hw_target"
    )
    cases.append(("gate keeps hw_target only in a comment", feature_in_prose, True))

    feature_unpassed = baseline()
    feature_unpassed[GATE_SCRIPT] = GOOD_GATE.replace(
        "--features hw_target", "hw_target"
    )
    cases.append(
        ("gate keeps the feature name but drops --features", feature_unpassed, True)
    )

    check_not_build = baseline()
    check_not_build[GATE_SCRIPT] = GOOD_GATE.replace(
        "cargo build --target", "cargo check --target", 1
    )
    cases.append(
        (
            "gate downgrades only the debug build to check, leaving the "
            "release line saying `cargo build`",
            check_not_build,
            True,
        )
    )

    check_both_profiles = baseline()
    check_both_profiles[GATE_SCRIPT] = GOOD_GATE.replace("cargo build", "cargo check")
    cases.append(("gate downgrades every build to check", check_both_profiles, True))

    host_target_build = baseline()
    host_target_build[GATE_SCRIPT] = GOOD_GATE.replace('--target "$CROSS_TARGET" ', "")
    cases.append(
        (
            "gate builds the host target instead of the cross one",
            host_target_build,
            True,
        )
    )

    no_job = baseline()
    no_job[WORKFLOW_FILE] = GOOD_WORKFLOW.replace(
        f"        run: ./{GATE_SCRIPT}\n", ""
    )
    cases.append(("workflow stops running the gate", no_job, True))

    job_in_prose = baseline()
    job_in_prose[WORKFLOW_FILE] = GOOD_WORKFLOW.replace(
        f"        run: ./{GATE_SCRIPT}", f"        # run: ./{GATE_SCRIPT}"
    )
    cases.append(("workflow comments the gate out", job_in_prose, True))

    # The exact shape the PR #883 review reproduced: the settings stay in
    # the file as unused assignments while the builds target something
    # else, so a token search anywhere in the file still finds them.
    settings_unbound = baseline()
    settings_unbound[GATE_SCRIPT] = GOOD_GATE.replace(
        '--target "$CROSS_TARGET" -p sele4n-hal --features hw_target',
        "--target x86_64-unknown-linux-gnu -p sele4n-hal --features other",
    )
    cases.append(
        (
            "gate keeps the settings as unused variables while building "
            "another target",
            settings_unbound,
            True,
        )
    )

    feature_unbound = baseline()
    feature_unbound[GATE_SCRIPT] = GOOD_GATE.replace(
        "--features hw_target", "--features other"
    )
    cases.append(
        ("gate builds the cross target without hw_target", feature_unbound, True)
    )

    settings_reassigned = baseline()
    settings_reassigned[GATE_SCRIPT] = GOOD_GATE.replace(
        'CROSS_TARGET="', 'CROSS_FEATURES="hw_target"\nCROSS_FEATURES=""\nCROSS_TARGET="'
    ).replace("--features hw_target", '--features "$CROSS_FEATURES"')
    cases.append(
        (
            "gate re-assigns a settings variable, so its value is not "
            "determinable from the text",
            settings_reassigned,
            True,
        )
    )

    no_targets_input = baseline()
    no_targets_input[WORKFLOW_FILE] = GOOD_WORKFLOW.replace(
        f"          targets: {CROSS_TARGET}\n", ""
    )
    cases.append(("workflow job stops installing the target", no_targets_input, True))

    for dropped in ASM_SOURCES:
        broken = baseline()
        # Remove the call itself rather than a whole indented line: the
        # first source sits on `asm.file("…")` and the rest on continuation
        # lines, so a line-shaped mutation silently no-ops on one of them
        # and leaves a case that asserts nothing.
        broken[BUILD_SCRIPT] = GOOD_BUILD_RS.replace(f'.file("{dropped}")', "")
        cases.append((f"build.rs drops {dropped}", broken, True))

    # --- The mutation class that finds "presence checked, relation not" ---
    #
    # Each case below KEEPS the token a naive check looks for and breaks
    # the relation the check actually means.  Deleting the token is the
    # easy mutation and every presence check survives it; these are the
    # ones that do not.  A new check here needs at least one.

    asm_in_dead_code = baseline()
    asm_in_dead_code[BUILD_SCRIPT] = GOOD_BUILD_RS.replace(
        '    asm.file("src/boot.S")\n', "    asm\n"
    ) + '\nfn unused_helper() {\n    cc::Build::new().file("src/boot.S");\n}\n'
    cases.append(
        (
            "build.rs keeps `.file(\"src/boot.S\")` only in an unreachable helper",
            asm_in_dead_code,
            True,
        )
    )

    toolchain_prefix_target = baseline()
    toolchain_prefix_target[TOOLCHAIN_FILE] = GOOD_TOOLCHAIN.replace(
        f'"{CROSS_TARGET}"', f'"{CROSS_TARGET}-softfloat"'
    )
    cases.append(
        (
            "toolchain lists a different target that CONTAINS the triple",
            toolchain_prefix_target,
            True,
        )
    )

    workflow_name_only = baseline()
    workflow_name_only[WORKFLOW_FILE] = GOOD_WORKFLOW.replace(
        f"        run: ./{GATE_SCRIPT}",
        f"        run: true",
    ).replace(
        f"      - name: Build sele4n-hal for {CROSS_TARGET}",
        f"      - name: replaced ./{GATE_SCRIPT}",
    )
    cases.append(
        (
            "workflow names the gate in a step NAME while running nothing",
            workflow_name_only,
            True,
        )
    )

    asm_in_prose = baseline()
    asm_in_prose[BUILD_SCRIPT] = GOOD_BUILD_RS.replace(
        '        .file("src/trap.S")\n',
        '        // .file("src/trap.S")\n',
    )
    cases.append(("build.rs keeps trap.S only in a comment", asm_in_prose, True))

    host_lane_unfeatured = baseline()
    host_lane_unfeatured[HOST_LANE] = GOOD_HOST_LANE.replace(
        "cargo test --all --features std,host_tools",
        "cargo test --all --features std",
    )
    cases.append(
        (
            "host lane TESTS without host_tools though its build has it",
            host_lane_unfeatured,
            True,
        )
    )

    host_lane_prose = baseline()
    host_lane_prose[HOST_LANE] = GOOD_HOST_LANE.replace(
        "cargo test --all --features std,host_tools",
        "# was: cargo test --all --features std,host_tools\n"
        "cargo test --all --features std",
    )
    cases.append(
        ("host lane keeps host_tools only in a comment", host_lane_prose, True)
    )

    host_lane_all_features = baseline()
    host_lane_all_features[HOST_LANE] = GOOD_HOST_LANE.replace(
        "cargo test --all --features std,host_tools",
        "cargo test --all --all-features",
    )
    cases.append(
        ("host lane selects host_tools via --all-features", host_lane_all_features, False)
    )

    # A case expected to be CAUGHT must actually differ from the clean
    # baseline.  A mutation that silently no-ops -- because the string it
    # replaced is not in the fixture -- produces a case that asserts
    # nothing while reading as coverage.  That happened here once already,
    # so it is checked rather than trusted.
    clean = baseline()
    failures = 0
    for label, files, expect_problems in cases:
        if expect_problems and files == clean:
            failures += 1
            print(f"[SELF-TEST FAIL] inert mutation, fixture unchanged: {label}")
            continue
        with tempfile.TemporaryDirectory() as tmp:
            write_tree(tmp, files)
            problems = run_checks(tmp)
            detected = bool(problems)
            if detected != expect_problems:
                failures += 1
                verb = "missed" if expect_problems else "false-positived on"
                print(f"[SELF-TEST FAIL] gate {verb}: {label}")
                for problem in problems:
                    print(f"                 reported: {problem}")
            else:
                state = "caught" if expect_problems else "accepted"
                print(f"[SELF-TEST OK]   {state}: {label}")

    if failures:
        print(f"\n[FAIL] {failures} self-test case(s) failed")
        return 1
    print(f"\n[PASS] {len(cases)} self-test case(s)")
    return 0


def main(argv: list[str]) -> int:
    if "--self-test" in argv:
        return self_test()

    root = os.path.abspath(
        os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
    )
    problems = run_checks(root)
    if problems:
        print("[FAIL] aarch64 cross-target configuration (WS-RR RR1.8):")
        for problem in problems:
            print(f"  - {problem}")
        return 1
    print("[PASS] aarch64 cross-target configuration intact")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
