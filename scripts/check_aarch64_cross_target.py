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
    if CROSS_TARGET not in match.group(1):
        return [
            f"{TOOLCHAIN_FILE}: `targets` does not list `{CROSS_TARGET}` "
            f"(found: {match.group(1).strip()})."
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

    code = code_view(text)
    if CROSS_TARGET not in code:
        problems.append(f"{GATE_SCRIPT}: no longer names `{CROSS_TARGET}`.")
    if not re.search(r"\bhw_target\b", code) or "--features" not in code:
        problems.append(
            f"{GATE_SCRIPT}: no longer passes `--features hw_target`. "
            f"The feature is empty by default and guards the hardware-only "
            f"paths (the Lean calls in timer.rs, trap.rs and smp.rs), so "
            f"without it the gate compiles none of the code it exists to "
            f"cover and stays green through a regression in exactly those "
            f"blocks."
        )
    # `--target` on the same line: a `cargo build` for the HOST would
    # satisfy a bare `cargo\s+build` search while compiling none of the
    # cross surface.
    cross_builds = [
        line
        for line in code.splitlines()
        if re.search(r"cargo\s+build\b.*--target\b", line)
    ]
    if not cross_builds:
        problems.append(
            f"{GATE_SCRIPT}: no longer runs a `cargo build --target ...`. "
            f"`cargo check` stops before code generation, so it never "
            f"reaches the backend and cannot surface an `asm!` or codegen "
            f"error -- which is the defect class this gate exists for -- and "
            f"a host-target build compiles none of the cross surface."
        )
    else:
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

    runners = [
        name for name, body in jobs.items() if GATE_SCRIPT in "\n".join(body)
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
    missing = [
        src for src in ASM_SOURCES if f'.file("{src}")' not in code
    ]
    if missing:
        return [
            f"{BUILD_SCRIPT}: no longer assembles {', '.join(missing)} "
            f"(expected a `.file(\"<path>\")` call for each). Dropping a "
            f"source removes its only compile coverage without failing any "
            f"build."
        ]
    return []


def check_host_lane(root: str) -> list[str]:
    """The host lane still selects the `host_tools`-gated targets."""
    text = read(root, HOST_LANE)
    if text is None:
        return [
            f"{HOST_LANE}: missing. It is the host half of the Rust "
            f"coverage; the cross gate does not run any tests."
        ]
    code = code_view(text)
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

GOOD_BUILD_RS = """fn main() {
    cc::Build::new()
        .file("src/boot.S")
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

    no_targets_input = baseline()
    no_targets_input[WORKFLOW_FILE] = GOOD_WORKFLOW.replace(
        f"          targets: {CROSS_TARGET}\n", ""
    )
    cases.append(("workflow job stops installing the target", no_targets_input, True))

    for dropped in ASM_SOURCES:
        broken = baseline()
        broken[BUILD_SCRIPT] = GOOD_BUILD_RS.replace(
            f'        .file("{dropped}")\n', ""
        )
        cases.append((f"build.rs drops {dropped}", broken, True))

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

    failures = 0
    for label, files, expect_problems in cases:
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
