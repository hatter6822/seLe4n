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
import shlex
import sys
import tempfile

CROSS_TARGET = "aarch64-unknown-none"
GATE_SCRIPT = "scripts/test_aarch64_cross_build.sh"
TOOLCHAIN_FILE = "rust/rust-toolchain.toml"
WORKFLOW_FILE = ".github/workflows/lean_action_ci.yml"
BUILD_SCRIPT = "rust/sele4n-hal/build.rs"
HOST_LANE = "scripts/test_rust.sh"
# The three `.S` sources as of this cut.  Kept as a floor, NOT as the source
# of truth: `assembly_sources` enumerates what is actually on disk, so a
# fourth `.S` added later and never handed to the assembler is reported
# rather than silently uncovered -- the same hole a hand-written wrapper
# list had in the TLBI gate (PR #883 review round 4).
ASM_SOURCES = ("src/boot.S", "src/vectors.S", "src/trap.S")
HAL_CRATE = "rust/sele4n-hal"
ORACLE_PKG = "sele4n-hal"
ORACLE_BIN = "rw_lock_oracle"
# Cargo flags that RESTRICT which target kinds a `cargo test` runs. Any
# of them excludes a `[[bin]]` target unless the binary is re-selected
# explicitly, so the oracle's `#[cfg(test)]` module does not execute.
TARGET_KIND_FLAGS = (
    "--doc",
    "--lib",
    "--test",
    "--tests",
    "--example",
    "--examples",
    "--bench",
    "--benches",
)


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


# ---------------------------------------------------------------------------
# Shell structure.
#
# Every remaining hole in this gate had the same shape: the question is
# about a COMMAND ("does cargo receive this flag", "is this script the thing
# being run", "does this invocation select that target") and the answer was
# read off a LINE.  A line is not a command -- it may hold several, it may
# hold half of one, and a token on it may belong to `echo`.  Three bypasses
# followed from that single substitution (PR #883 review round 3):
#
#   * a host `cargo build --release` satisfied the requirement that the
#     CROSS build be done in both profiles;
#   * `cargo test --doc ... --features host_tools` satisfied "the host lane
#     tests with host_tools" while running no oracle test at all;
#   * `run: echo ./scripts/test_aarch64_cross_build.sh` satisfied "a job
#     runs the gate script".
#
# So the script is split into commands once, here, and every check below
# reads an argv.
# ---------------------------------------------------------------------------

def shell_commands(script: str) -> list[str]:
    """Split a comment-stripped, variable-expanded script into commands.

    Backslash-continuations are joined first, so a command wrapped across
    lines is read whole -- the cross gate's `cargo clippy` invocation is
    written that way, and a line-based reader sees only its head.

    QUOTE-AWARE, and that is not a nicety.  A regex split on `;`/`|`/`&&`
    cuts inside string literals too, and the fragment after the cut reads as
    a fresh command, so

        run: echo "building; ./scripts/test_aarch64_cross_build.sh next"

    yielded `./scripts/test_aarch64_cross_build.sh next"` with the path in
    command position and satisfied the check that a job RUNS the gate --
    the very hole this splitter was written to close, reintroduced one
    layer down.  Found by self-audit of this cut, not by review.  Splitting
    text without respecting the quoting it stands for is the same
    substitution as every other instance of the class.
    """
    joined = re.sub(r"\\\n\s*", " ", script)
    commands: list[str] = []
    current: list[str] = []
    quote: str | None = None
    index = 0
    while index < len(joined):
        char = joined[index]
        if quote is not None:
            current.append(char)
            if char == quote:
                quote = None
            elif char == "\\" and quote == '"' and index + 1 < len(joined):
                current.append(joined[index + 1])
                index += 1
            index += 1
            continue
        if char in ("'", '"'):
            quote = char
            current.append(char)
            index += 1
            continue
        if joined.startswith("&&", index) or joined.startswith("||", index):
            commands.append("".join(current))
            current = []
            index += 2
            continue
        if char in ";\n|":
            commands.append("".join(current))
            current = []
            index += 1
            continue
        current.append(char)
        index += 1
    commands.append("".join(current))
    return [command.strip() for command in commands if command.strip()]


def argv_of(command: str) -> list[str]:
    """Tokenise a command the way a shell would.

    `shlex`, not `split()` plus `strip("\"'")`.  Quotes must be resolved by
    the same rules that produced them: `--target "${CROSS_TARGET}"` expands
    to `--target "aarch64-unknown-none"`, so the quotes survive expansion
    and a naive comparison fails; and a quoted value CONTAINING A SPACE --
    `RUSTFLAGS="-D warnings" ./gate.sh` -- splits into two tokens under
    whitespace splitting, which pushed the real command word out of
    position and made the check miss a job that does run the gate.

    An unbalanced quote raises, and the fallback is the naive split: a
    script this cannot tokenise is one the checks should read
    pessimistically rather than not at all.
    """
    try:
        return shlex.split(command)
    except ValueError:
        return [token.strip("\"'") for token in command.split()]


def option_values(argv: list[str], *names: str) -> list[str]:
    """Every value passed to any of `names`, in `--n v`, `--n=v` and `-n v`.

    Comma-separated values are split, since cargo accepts `--features a,b`
    as two features.
    """
    flags = tuple((f"--{n}" if len(n) > 1 else f"-{n}") for n in names)
    values: list[str] = []
    for index, token in enumerate(argv):
        if token in flags and index + 1 < len(argv):
            values.append(argv[index + 1])
        else:
            for flag in flags:
                if token.startswith(f"{flag}="):
                    values.append(token[len(flag) + 1 :])
    return [piece for value in values for piece in value.split(",") if piece]


# A shell function whose body execs its own arguments -- `"$@"` -- passes
# execution through to whatever it is called with, so `cargo` behind one is
# genuinely run.  Derived from the script rather than named, so renaming the
# wrapper cannot silently blind the gate.
_SHELL_FUNCTION_RE = re.compile(
    r"^\s*(?:function\s+)?([A-Za-z_][A-Za-z0-9_]*)\s*\(\)\s*\{", re.MULTILINE
)


def body_execs_arguments(body: str) -> bool:
    """Does this shell-function body EXECUTE `"$@"`, rather than mention it?

    Command position, one level down.  Accepting any body that contains
    `"$@"` classified `log_step() { shift; echo "$@"; }` as a pass-through
    wrapper, so a host lane refactored to merely log its steps unwrapped as
    an executed cargo command and the oracle-coverage gate stayed green
    while nothing ran (PR #883 review round 6).  That is the third time the
    same substitution has appeared in this file, each time in the code
    written to fix the previous one -- so it is answered with the same
    resolver the callers use, applied to the body.
    """
    for command in shell_commands(body):
        argv = argv_of(command)
        # Peel `VAR=value` prefixes and the shell keywords that introduce a
        # command without being one.  The real wrapper writes
        # `if "$@" > "$log" 2>&1; then`, so requiring `"$@"` to be argv[0]
        # outright would reject the configuration this gate must accept.
        while argv and (
            re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*=.*", argv[0], re.DOTALL)
            or argv[0] in ("if", "elif", "while", "until", "then", "do", "else", "!", "{")
        ):
            argv = argv[1:]
        if argv and argv[0] in ('"$@"', "$@", "$*"):
            return True
        # `exec "$@"` and `eval "$@"` execute it too.
        if len(argv) > 1 and argv[0] in ("exec", "eval", "command") and argv[1] in (
            '"$@"',
            "$@",
        ):
            return True
    return False


def executing_wrappers(script: str) -> dict[str, int]:
    """Shell functions in `script` that exec `"$@"`, and how much they shift.

    Maps the wrapper's name to the number of leading arguments it consumes
    before exec'ing the rest, counted from the `shift` statements in its
    body.  The host lane's `run_cargo_step "label" cargo test ...` takes one
    label and shifts once, so the argv it execs starts at `cargo`.

    Both error directions are safe: consume too few and the command word is
    the label, consume too many and it is a flag; either way no `cargo`
    invocation is recognised and the check reports a problem rather than
    passing over one it could not resolve.
    """
    wrappers: dict[str, int] = {}
    for match in _SHELL_FUNCTION_RE.finditer(script):
        body_start = script.index("{", match.start())
        depth, index = 0, body_start
        while index < len(script):
            if script[index] == "{":
                depth += 1
            elif script[index] == "}":
                depth -= 1
                if depth == 0:
                    break
            index += 1
        body = script[body_start:index]
        if not body_execs_arguments(body):
            continue
        shifted = 0
        for shift in re.finditer(r"^\s*shift(?:\s+(\d+))?\s*$", body, re.MULTILINE):
            shifted += int(shift.group(1) or 1)
        wrappers[match.group(1)] = shifted
    return wrappers


def executed_argv(command: str, wrappers: dict[str, int]) -> list[str]:
    """The argv a command actually execs, with prefixes and wrappers peeled.

    Peels `VAR=value` prefixes and pass-through wrappers (`sudo`, `env`,
    `time`, `exec`, plus the script's own `"$@"` functions) until the
    command word is the thing that runs.  Shared by every check that asks
    "is X the thing being executed" -- `job_runs_gate` and
    `cargo_invocations` both, because they ask the same question and the
    first version answered it in only one of them.
    """
    argv = argv_of(command)
    while argv:
        head = argv[0]
        if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*=.*", head, re.DOTALL):
            argv = argv[1:]
            continue
        if head in ("sudo", "env", "time", "exec"):
            argv = argv[1:]
            continue
        if head in wrappers:
            # A `"$@"` wrapper execs whatever remains after its own
            # `shift`s. Drop the wrapper and exactly the arguments it
            # consumes; everything else, options included, is passed
            # through untouched.
            argv = argv[1 + wrappers[head] :]
            continue
        break
    return argv


def cargo_invocations(script: str, subcommand: str) -> list[list[str]]:
    """Every EXECUTED `cargo <subcommand>` in `script`, as argv from `cargo`.

    Command position, not "a `cargo` token somewhere in the command".  The
    first version scanned every token, so `echo cargo build --target
    aarch64-unknown-none --features hw_target` satisfied the check that the
    gate script builds the cross target in both profiles -- CI would have
    run `echo` while Tier 0 reported the AArch64 surface compiled (PR #883
    review round 4).  That is the same defect as the `run: echo ./gate.sh`
    one fixed the round before, in the neighbouring function: the resolver
    was written and then applied at only one of the two sites that ask the
    question.  `executed_argv` is now shared by both.

    The host lane invokes every step through `run_cargo_step "label" cargo
    test ...`, a shell function that execs `"$@"`; such wrappers are
    derived from the script, so `cargo` behind one still counts.
    """
    wrappers = executing_wrappers(script)
    found: list[list[str]] = []
    for command in shell_commands(script):
        argv = executed_argv(command, wrappers)
        if (
            argv
            and (argv[0] == "cargo" or argv[0].endswith("/cargo"))
            and len(argv) > 1
            and argv[1] == subcommand
        ):
            found.append(argv)
    return found


def selects_oracle(argv: list[str]) -> bool:
    """Would this `cargo test` argv run `src/bin/rw_lock_oracle.rs`'s tests?

    Enabling `host_tools` makes the target *buildable*; it does not make it
    *selected*.  Cargo runs a `[[bin]]`'s `#[cfg(test)]` module only when
    the invocation's target-kind selection includes binaries -- by default,
    or explicitly -- and only when its package selection includes the crate.
    Both halves are required, and neither is implied by the feature flag.
    """
    # Everything after `--` is passed to the test harness, not to cargo, so
    # it must not be read as a cargo selector: `cargo test --all -- --doc`
    # is an unrestricted run with a harness argument, and reading the
    # trailing `--doc` as a target-kind restriction would reject it.
    if "--" in argv:
        argv = argv[: argv.index("--")]
    # `--no-run` COMPILES the selected targets and runs none of them, so it
    # satisfies every selector below while executing zero oracle tests --
    # the `--doc` finding again, one flag over (PR #883 review round 5).
    # Checked before selection, because selection is irrelevant once
    # nothing runs.
    if "--no-run" in argv:
        return False
    if "--bins" in argv or "--all-targets" in argv:
        return True
    if ORACLE_BIN in option_values(argv, "bin"):
        return True
    if any(
        token in TARGET_KIND_FLAGS or token.split("=", 1)[0] in TARGET_KIND_FLAGS
        for token in argv
    ):
        return False
    if "--all" in argv or "--workspace" in argv:
        return True
    packages = option_values(argv, "p", "package")
    return not packages or ORACLE_PKG in packages


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

    builds = cargo_invocations(code, "build")
    targeted = [
        argv for argv in builds if CROSS_TARGET in option_values(argv, "target")
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
        argv
        for argv in targeted
        if "hw_target" not in option_values(argv, "features")
        and "--all-features" not in argv
    ]
    if targeted and unfeatured:
        problems.append(
            f"{GATE_SCRIPT}: a cross `cargo build` does not pass "
            f"`--features hw_target`: {' '.join(unfeatured[0])!r}. The "
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
        # Derived from `targeted`, NOT from every `cargo build` in the
        # file.  Asking "is there a release build anywhere" is a presence
        # check standing in for "is the CROSS build done in release": a
        # host `cargo build --release` on any other line satisfied it while
        # the aarch64 surface was compiled at `-O0` only, which is exactly
        # half the coverage this pair exists to give (PR #883 review
        # round 3).
        # THREE-way, not two.  `not release` is not `debug`: cargo takes an
        # arbitrary `--profile <name>`, and an optimised custom profile
        # answered "no" to `is_release` and was counted as the `-O0` build
        # the pair exists to guarantee (PR #883 review round 6).  An
        # unrecognised profile is classified `unknown` and satisfies
        # neither requirement, so it fails closed and asks to be re-pinned.
        def profile_of(argv: list[str]) -> str:
            named = option_values(argv, "profile")
            if "--release" in argv or "release" in named:
                return "release"
            if not named or named == ["dev"]:
                return "debug"
            return "unknown"

        seen = {profile_of(argv) for argv in targeted}
        missing = [
            profile for profile in ("debug", "release") if profile not in seen
        ]
        if missing:
            problems.append(
                f"{GATE_SCRIPT}: no cross `cargo build --target "
                f"{CROSS_TARGET}` for the {' and '.join(missing)} profile. "
                f"Both are built because "
                f"inline-asm register allocation depends on the "
                f"optimisation level -- an `asm!` block that satisfies the "
                f"allocator at `-O0` can fail to at `-O2`, and the deployed "
                f"kernel is a release build."
                + (
                    "\n      A cross build names a profile this gate does "
                    "not recognise as either; `--profile <name>` with an "
                    "arbitrary name is classified `unknown` and counts as "
                    "neither, since an optimised custom profile is not the "
                    "`-O0` half of the pair."
                    if any(profile_of(a) == "unknown" for a in targeted)
                    else ""
                )
            )
    # The cross CLIPPY lane. `cargo build` proves the target compiles;
    # only clippy with `-D warnings` proves it is clean, and this is the
    # ONLY lint lane that sees `#[cfg(target_arch = "aarch64")]` code --
    # the host lane has every such block removed before rustc or clippy
    # sees it, which is how three lints reached review invisible to it.
    # Deleting the command left this gate clean, because it checked builds
    # only and the fixture had no clippy command to notice was missing (PR
    # #883 review round 6).
    lints = [
        argv
        for argv in cargo_invocations(code, "clippy")
        if CROSS_TARGET in option_values(argv, "target")
    ]
    if not lints:
        problems.append(
            f"{GATE_SCRIPT}: no executed `cargo clippy --target "
            f"{CROSS_TARGET}`. It is the only lint lane that sees the "
            f'`#[cfg(target_arch = "aarch64")]` blocks at all -- the host '
            f"lane has them removed before rustc or clippy runs -- so "
            f"without it the cross surface is compiled but never linted."
        )
    for argv in lints:
        if (
            "hw_target" not in option_values(argv, "features")
            and "--all-features" not in argv
        ):
            problems.append(
                f"{GATE_SCRIPT}: the cross `cargo clippy` does not pass "
                f"`--features hw_target`, so it lints none of the "
                f"hardware-only paths: {' '.join(argv)!r}"
            )
        # `-D warnings` must reach CLIPPY, i.e. sit after the `--`
        # separator; before it, cargo takes it as its own flag.
        after = argv[argv.index("--") + 1 :] if "--" in argv else []
        denies = [
            after[i + 1]
            for i, token in enumerate(after)
            if token in ("-D", "--deny") and i + 1 < len(after)
        ] + [
            token.split("=", 1)[1] for token in after if token.startswith("--deny=")
        ]
        if "warnings" not in denies:
            problems.append(
                f"{GATE_SCRIPT}: the cross `cargo clippy` does not pass "
                f"`-- -D warnings`, so a lint on the aarch64 surface is "
                f"merely reported and the step still exits 0: "
                f"{' '.join(argv)!r}"
            )

    # Failure propagation. Every command above is load-bearing, and bash
    # continues past a failure by default: with `set -e` removed, a debug
    # build that hits a profile-specific `asm!` error is followed by a
    # successful release build, archive check and clippy, and the script
    # exits 0 on its final `echo` (PR #883 review round 6). The commands
    # being present says nothing about whether their failure is observed.
    directives: set[str] = set()
    for command in shell_commands(code):
        argv = argv_of(command)
        if argv and argv[0] == "set":
            directives.update(argv[1:])
    short_flags = "".join(
        d.lstrip("-") for d in directives if d.startswith("-") and not d.startswith("--")
    )
    if "e" not in short_flags and "errexit" not in directives:
        problems.append(
            f"{GATE_SCRIPT}: no `set -e` (or `set -o errexit`). Without it "
            f"bash runs past a failed command, so a broken cross build is "
            f"followed by the remaining steps and the script exits on its "
            f"final `echo` with status 0 -- CI green over a build that "
            f"failed."
        )
    if "pipefail" not in directives:
        problems.append(
            f"{GATE_SCRIPT}: no `set -o pipefail`. A build step piped into "
            f"a filter takes the pipeline's status from the last command, "
            f"so a failed `cargo build` piped into a successful `tee` or "
            f"`grep` reports success."
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


# Commands that execute their script argument.  Anything else in command
# position (`echo`, `cat`, `ls`) names the script without running it, so the
# list is an allowlist and an unrecognised command fails the check closed.
SCRIPT_INTERPRETERS = ("bash", "sh", "dash", "zsh", "ksh", "source", ".")


def run_scripts(body: str) -> list[str]:
    """Every `run:` value in a job body, block scalars included.

    `run: <command>` yields its inline value; `run: |` (or `>`), with an
    optional chomping/indent indicator, yields the indented block that
    follows.  Reading only the inline form would make a job that moved its
    command into a block scalar look like it runs nothing -- fail-closed,
    but wrongly, and the fix would then be to weaken the check.
    """
    lines = body.splitlines()
    scripts: list[str] = []
    index = 0
    while index < len(lines):
        line = lines[index]
        match = re.match(r"^(\s*)(?:-\s*)?run\s*:\s*(.*)$", line)
        index += 1
        if not match:
            continue
        indent, inline = match.group(1), match.group(2).strip()
        # `|`, `>`, with an optional explicit indent and an optional
        # chomping indicator IN EITHER ORDER (`|2-` and `|-2` are both
        # valid YAML).  Taking only one order made a correctly-configured
        # workflow read as running nothing -- fail-closed, but wrongly, and
        # the natural repair would be to weaken the check back toward a
        # substring search.
        if not re.fullmatch(r"[|>](?:[+-]?\d*|\d*[+-]?)", inline):
            if inline:
                scripts.append(inline)
            continue
        block: list[str] = []
        while index < len(lines):
            nxt = lines[index]
            if nxt.strip() and len(nxt) - len(nxt.lstrip()) <= len(indent):
                break
            block.append(nxt)
            index += 1
        scripts.append("\n".join(block))
    return scripts


def _names_gate(token: str) -> bool:
    """Is `token` a path referring to the gate script?"""
    basename = os.path.basename(GATE_SCRIPT)
    return (
        token.lstrip("./") == GATE_SCRIPT.lstrip("./")
        or token.endswith("/" + basename)
        or token == basename
    )


# Shell options that make the interpreter NOT execute what it reads.
# `bash -n` is documented as "Read commands but do not execute them", so a
# step spelled `bash -n ./gate.sh` type-checks the script and runs no build.
# Skipping every `-`-prefixed token before looking for the path accepted it
# (PR #883 review round 5): the options are not noise, they decide whether
# execution happens at all.
NON_EXECUTING_SHELL_OPTIONS = frozenset("n")


def interpreter_executes(argv: list[str]) -> bool:
    """Does this interpreter invocation actually run the gate script?

    Options are read as options -- short clusters expanded, `--` ending
    them -- rather than skipped.  A non-executing mode anywhere in the
    cluster (`-n`, `-en`, `--noexec`) disqualifies the invocation; an
    unrecognised long option does too, since this scanner cannot know
    whether it suppresses execution, and that is the fail-closed side.
    """
    index = 1
    while index < len(argv):
        token = argv[index]
        if token == "--":
            index += 1
            break
        if token.startswith("--"):
            if token in ("--noexec",):
                return False
            if token not in ("--norc", "--noprofile", "--posix", "--login"):
                return False
            index += 1
            continue
        if token.startswith("-") and len(token) > 1:
            if set(token[1:]) & NON_EXECUTING_SHELL_OPTIONS:
                return False
            if "c" in token[1:]:
                # `-c` takes the script as a STRING, so the next argument
                # is a command, not a path this scanner can resolve.
                return False
            index += 1
            continue
        break
    return any(_names_gate(token) for token in argv[index:])


def job_runs_gate(body: str) -> bool:
    """Does some `run:` step of this job actually execute the gate script?"""
    for script in run_scripts(body):
        wrappers = executing_wrappers(script)
        for command in shell_commands(script):
            argv = executed_argv(command, wrappers)
            if not argv:
                continue
            if _names_gate(argv[0]):
                return True
            if argv[0] in SCRIPT_INTERPRETERS and interpreter_executes(argv):
                return True
    return False


def check_workflow(root: str) -> list[str]:
    """Some CI job runs the gate script, and installs the target for it."""
    text = read(root, WORKFLOW_FILE)
    if text is None:
        return [f"{WORKFLOW_FILE}: missing"]
    code = code_view(text)
    jobs = workflow_jobs(code)

    # A job runs the gate only if the script sits in an EXECUTABLE COMMAND
    # POSITION of a `run:` script.  Two weaker forms both passed before:
    # matching the path anywhere in the job body is satisfied by a step
    # *name* ("Build sele4n-hal for aarch64-unknown-none" is one line from
    # "replaced ./scripts/test_aarch64_cross_build.sh"), and matching it
    # anywhere in a `run:` value is satisfied by `run: echo
    # ./scripts/test_aarch64_cross_build.sh`, which executes nothing (PR
    # #883 review round 3).  So the run script is split into commands and
    # the path must be the command word -- or the argument of an
    # interpreter that would exec it.
    runners = [
        name for name, body in jobs.items() if job_runs_gate("\n".join(body))
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

    # Membership in the COMPILED builder's chain, not merely a byte offset
    # inside an interval.  An interval test accepts a `.file()` on any
    # receiver that happens to sit between the two landmarks, so
    #
    #     let mut unused = cc::Build::new();
    #     unused.file("src/trap.S");
    #
    #     asm.file("src/boot.S").file("src/vectors.S")
    #        .compile("sele4n_hal_asm");
    #
    # reports `trap.S` covered while nothing assembles it (PR #883 review
    # round 5).  So the receiver that `.compile("sele4n_hal_asm")` is
    # called on is resolved first, and only `.file()` calls in ITS chain
    # count.
    receiver = compiled_builder_name(code, compile_at)
    if receiver is None:
        return [
            f"{BUILD_SCRIPT}: cannot resolve the receiver of "
            f'`.compile("sele4n_hal_asm")`. If the assembly chain was '
            f"restructured, update this gate so the `.S` sources stay "
            f"pinned to the builder that is actually compiled."
        ]
    sources = sorted(set(ASM_SOURCES) | assembly_sources(root))
    missing = [
        src
        for src in sources
        if not any(
            gate_at < pos < compile_at and chain_root(code, pos) == receiver
            for pos in _occurrences(code, f'.file("{src}")')
        )
    ]
    if missing:
        return [
            f"{BUILD_SCRIPT}: {', '.join(missing)} is not handed to the "
            f"assembler in the live chain (expected a `.file(\"<path>\")` "
            f"call on `{receiver}`, the builder that "
            f'`.compile("sele4n_hal_asm")` is called on). Dropping a '
            f"source -- or leaving it on a builder that is never compiled "
            f"-- removes its only compile coverage without failing any "
            f"build."
        ]
    return []


def assembly_sources(root: str) -> set[str]:
    """Every `.S` source in the HAL crate, as a `src/`-relative path."""
    base = os.path.join(root, HAL_CRATE)
    found: set[str] = set()
    for dirpath, _dirnames, filenames in os.walk(os.path.join(base, "src")):
        for name in filenames:
            if name.endswith(".S"):
                rel = os.path.relpath(os.path.join(dirpath, name), base)
                found.add(rel.replace(os.sep, "/"))
    return found


def chain_root(code: str, dot_at: int) -> str | None:
    """The identifier a method chain ending at `dot_at` is rooted in.

    `asm.file("a").file("b").compile("c")` roots at `asm` from any link.
    Returns `None` when the root is not a plain identifier -- a temporary
    (`cc::Build::new().file(...)`) or an expression this scanner cannot
    attribute -- which fails its callers closed rather than guessing.
    """
    head = code[:dot_at]
    while True:
        stripped = head.rstrip()
        if not stripped.endswith(")"):
            break
        depth, index = 0, len(stripped) - 1
        while index >= 0:
            if stripped[index] == ")":
                depth += 1
            elif stripped[index] == "(":
                depth -= 1
                if depth == 0:
                    break
            index -= 1
        if index < 0:
            return None
        before = stripped[:index].rstrip()
        dot = before.rfind(".")
        if dot < 0:
            return None
        head = before[:dot]
    match = re.search(r"([A-Za-z_][A-Za-z0-9_]*)\s*$", head.rstrip())
    return match.group(1) if match else None


def compiled_builder_name(code: str, compile_at: int) -> str | None:
    """The receiver `.compile("sele4n_hal_asm")` is called on."""
    return chain_root(code, compile_at)


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
    invocations = cargo_invocations(code, "test")
    if not invocations:
        return [f"{HOST_LANE}: no `cargo test` invocation found."]
    # `--all-features` enables `host_tools` along with everything else, so
    # it satisfies the requirement; rejecting it would fail a
    # configuration that is in fact correct.
    featured = [
        argv
        for argv in invocations
        if "host_tools" in option_values(argv, "features")
        or "--all-features" in argv
    ]
    if not featured:
        return [
            f"{HOST_LANE}: no `cargo test` invocation selects `host_tools`. "
            f"`src/bin/{ORACLE_BIN}.rs` carries "
            f"`required-features = [\"host_tools\"]` so the bare-metal build "
            f"skips it -- and cargo does not run a skipped target's "
            f"`#[cfg(test)]` module either, so without the feature its tests "
            f"stop running and the step still reports a clean pass over one "
            f"fewer binary."
        ]
    # The feature must reach an invocation that WOULD RUN the oracle.
    # Checking only that `host_tools` appears on some `cargo test` line is
    # a presence check standing in for that: `cargo test --doc -p
    # sele4n-hal --features host_tools` carries the feature and runs
    # doctests only, so the 14 oracle tests still never execute and the
    # step still reports a clean pass (PR #883 review round 3).
    if not any(selects_oracle(argv) for argv in featured):
        return [
            f"{HOST_LANE}: `host_tools` is passed only to `cargo test` "
            f"invocations that cannot run `src/bin/{ORACLE_BIN}.rs`: "
            f"{[' '.join(a) for a in featured]}. Enabling the feature is "
            f"not the same as selecting the target it gates -- a `--doc`, "
            f"`--lib` or `--test <name>` run carries the flag and executes "
            f"none of the oracle's tests, and the step still passes. The "
            f"invocation must select the binary (`--bins`, `--all-targets` "
            f"or `--bin {ORACLE_BIN}`) or leave the target kinds "
            f"unrestricted over a package set including `{ORACLE_PKG}`."
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
# The fixture must be NO THINNER than the file it stands for.  This one
# had no `cargo clippy` command, so the check that the cross lint lane
# still exists could not have been self-tested even once it was written --
# the clean baseline would have failed instead of the mutation (PR #883
# review round 6, and the third time a too-thin fixture has hidden a
# defect here).  It now mirrors every load-bearing element of the real
# `test_aarch64_cross_build.sh`: failure propagation, both build profiles,
# and the lint lane with its `-D warnings` past the `--` separator.
GOOD_GATE = f"""#!/usr/bin/env bash
set -euo pipefail
CROSS_TARGET="{CROSS_TARGET}"
cargo build --target "$CROSS_TARGET" -p sele4n-hal --features hw_target
cargo build --release --target "$CROSS_TARGET" -p sele4n-hal --features hw_target
cargo clippy --target "$CROSS_TARGET" -p sele4n-hal --features hw_target -- -D warnings
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


# The checks `run_checks` performs, by id.  Each must be exercised by at
# least one PRESERVING negative case below; the harness enforces it.
CHECKS = ("toolchain", "gate_script", "workflow", "build_script", "host_lane")


class Case:
    """One self-test fixture, tagged with what it proves.

    `mutation` records HOW the fixture differs from the clean baseline:
    ``"deleting"`` removes the token a check searches for -- necessary, and
    passed by every presence check ever written -- while ``"preserving"``
    KEEPS that token and breaks only the relation it stands in.  Only the
    second kind can find the defect this gate keeps shipping: a host
    `--release` standing in for a cross one, a `--doc` run carrying the
    feature that gates a binary it never runs, `echo` in front of the
    script path.  Enforced below rather than asserted in a comment, because
    asserting it in a comment did not stop three review rounds.
    """

    def __init__(
        self,
        label: str,
        files: dict[str, str],
        expect: bool,
        check: str | None = None,
        mutation: str = "deleting",
    ) -> None:
        assert check is None or check in CHECKS, check
        assert mutation in ("none", "deleting", "preserving"), mutation
        self.label = label
        self.files = files
        self.expect = expect
        self.check = check
        self.mutation = mutation


def self_test() -> int:
    cases: list[Case] = []

    cases.append(Case("clean baseline", baseline(), False, mutation="none"))

    drop_target = baseline()
    drop_target[TOOLCHAIN_FILE] = GOOD_TOOLCHAIN.replace(
        f'targets = ["{CROSS_TARGET}"]\n', ""
    )
    cases.append(Case("toolchain drops the targets key", drop_target, True, check="toolchain"))

    comment_target = baseline()
    comment_target[TOOLCHAIN_FILE] = GOOD_TOOLCHAIN.replace(
        f'targets = ["{CROSS_TARGET}"]',
        f'targets = ["aarch64-unknown-linux-gnu"]',
    )
    cases.append(Case("toolchain lists the wrong target", comment_target, True, check="toolchain", mutation="preserving"))

    no_feature = baseline()
    no_feature[GATE_SCRIPT] = GOOD_GATE.replace(" --features hw_target", "")
    cases.append(Case("gate drops --features hw_target", no_feature, True, check="gate_script"))

    feature_in_prose = baseline()
    feature_in_prose[GATE_SCRIPT] = GOOD_GATE.replace(
        " --features hw_target", "  # was --features hw_target"
    )
    cases.append(Case("gate keeps hw_target only in a comment", feature_in_prose, True, check="gate_script", mutation="preserving"))

    feature_unpassed = baseline()
    feature_unpassed[GATE_SCRIPT] = GOOD_GATE.replace(
        "--features hw_target", "hw_target"
    )
    cases.append(Case("gate keeps the feature name but drops --features", feature_unpassed, True, check="gate_script", mutation="preserving"))

    check_not_build = baseline()
    check_not_build[GATE_SCRIPT] = GOOD_GATE.replace(
        "cargo build --target", "cargo check --target", 1
    )
    cases.append(Case("gate downgrades only the debug build to check, leaving the "
            "release line saying `cargo build`",
            check_not_build,
            True, check="gate_script", mutation="preserving"))

    check_both_profiles = baseline()
    check_both_profiles[GATE_SCRIPT] = GOOD_GATE.replace("cargo build", "cargo check")
    cases.append(Case("gate downgrades every build to check", check_both_profiles, True, check="gate_script"))

    host_target_build = baseline()
    host_target_build[GATE_SCRIPT] = GOOD_GATE.replace('--target "$CROSS_TARGET" ', "")
    cases.append(Case("gate builds the host target instead of the cross one",
            host_target_build,
            True, check="gate_script", mutation="preserving"))

    no_job = baseline()
    no_job[WORKFLOW_FILE] = GOOD_WORKFLOW.replace(
        f"        run: ./{GATE_SCRIPT}\n", ""
    )
    cases.append(Case("workflow stops running the gate", no_job, True, check="workflow"))

    job_in_prose = baseline()
    job_in_prose[WORKFLOW_FILE] = GOOD_WORKFLOW.replace(
        f"        run: ./{GATE_SCRIPT}", f"        # run: ./{GATE_SCRIPT}"
    )
    cases.append(Case("workflow comments the gate out", job_in_prose, True, check="workflow", mutation="preserving"))

    # The exact shape the PR #883 review reproduced: the settings stay in
    # the file as unused assignments while the builds target something
    # else, so a token search anywhere in the file still finds them.
    settings_unbound = baseline()
    settings_unbound[GATE_SCRIPT] = GOOD_GATE.replace(
        '--target "$CROSS_TARGET" -p sele4n-hal --features hw_target',
        "--target x86_64-unknown-linux-gnu -p sele4n-hal --features other",
    )
    cases.append(Case("gate keeps the settings as unused variables while building "
            "another target",
            settings_unbound,
            True, check="gate_script", mutation="preserving"))

    feature_unbound = baseline()
    feature_unbound[GATE_SCRIPT] = GOOD_GATE.replace(
        "--features hw_target", "--features other"
    )
    cases.append(Case("gate builds the cross target without hw_target", feature_unbound, True, check="gate_script"))

    settings_reassigned = baseline()
    settings_reassigned[GATE_SCRIPT] = GOOD_GATE.replace(
        'CROSS_TARGET="', 'CROSS_FEATURES="hw_target"\nCROSS_FEATURES=""\nCROSS_TARGET="'
    ).replace("--features hw_target", '--features "$CROSS_FEATURES"')
    cases.append(Case("gate re-assigns a settings variable, so its value is not "
            "determinable from the text",
            settings_reassigned,
            True, check="gate_script", mutation="preserving"))

    no_targets_input = baseline()
    no_targets_input[WORKFLOW_FILE] = GOOD_WORKFLOW.replace(
        f"          targets: {CROSS_TARGET}\n", ""
    )
    cases.append(Case("workflow job stops installing the target", no_targets_input, True, check="workflow"))

    for dropped in ASM_SOURCES:
        broken = baseline()
        # Remove the call itself rather than a whole indented line: the
        # first source sits on `asm.file("…")` and the rest on continuation
        # lines, so a line-shaped mutation silently no-ops on one of them
        # and leaves a case that asserts nothing.
        broken[BUILD_SCRIPT] = GOOD_BUILD_RS.replace(f'.file("{dropped}")', "")
        cases.append(Case(f"build.rs drops {dropped}", broken, True, check="build_script"))

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
    cases.append(Case("build.rs keeps `.file(\"src/boot.S\")` only in an unreachable helper",
            asm_in_dead_code,
            True, check="build_script", mutation="preserving"))

    toolchain_prefix_target = baseline()
    toolchain_prefix_target[TOOLCHAIN_FILE] = GOOD_TOOLCHAIN.replace(
        f'"{CROSS_TARGET}"', f'"{CROSS_TARGET}-softfloat"'
    )
    cases.append(Case("toolchain lists a different target that CONTAINS the triple",
            toolchain_prefix_target,
            True, check="toolchain", mutation="preserving"))

    workflow_name_only = baseline()
    workflow_name_only[WORKFLOW_FILE] = GOOD_WORKFLOW.replace(
        f"        run: ./{GATE_SCRIPT}",
        f"        run: true",
    ).replace(
        f"      - name: Build sele4n-hal for {CROSS_TARGET}",
        f"      - name: replaced ./{GATE_SCRIPT}",
    )
    cases.append(Case("workflow names the gate in a step NAME while running nothing",
            workflow_name_only,
            True, check="workflow", mutation="preserving"))

    asm_in_prose = baseline()
    asm_in_prose[BUILD_SCRIPT] = GOOD_BUILD_RS.replace(
        '        .file("src/trap.S")\n',
        '        // .file("src/trap.S")\n',
    )
    cases.append(Case("build.rs keeps trap.S only in a comment", asm_in_prose, True, check="build_script", mutation="preserving"))

    host_lane_unfeatured = baseline()
    host_lane_unfeatured[HOST_LANE] = GOOD_HOST_LANE.replace(
        "cargo test --all --features std,host_tools",
        "cargo test --all --features std",
    )
    cases.append(Case("host lane TESTS without host_tools though its build has it",
            host_lane_unfeatured,
            True, check="host_lane"))

    host_lane_prose = baseline()
    host_lane_prose[HOST_LANE] = GOOD_HOST_LANE.replace(
        "cargo test --all --features std,host_tools",
        "# was: cargo test --all --features std,host_tools\n"
        "cargo test --all --features std",
    )
    cases.append(Case("host lane keeps host_tools only in a comment", host_lane_prose, True, check="host_lane", mutation="preserving"))

    host_lane_all_features = baseline()
    host_lane_all_features[HOST_LANE] = GOOD_HOST_LANE.replace(
        "cargo test --all --features std,host_tools",
        "cargo test --all --all-features",
    )
    cases.append(Case("host lane selects host_tools via --all-features", host_lane_all_features, False, check="host_lane", mutation="none"))

    # A HOST release build standing in for the cross one.  Every token is
    # present -- `cargo build`, `--release`, the triple, both profiles
    # somewhere in the file -- and only the relation is false: the release
    # build is not the cross build, so the aarch64 surface is compiled at
    # `-O0` only.
    host_release_stand_in = baseline()
    host_release_stand_in[GATE_SCRIPT] = GOOD_GATE.replace(
        'cargo build --release --target "$CROSS_TARGET" '
        "-p sele4n-hal --features hw_target",
        "cargo build --release -p sele4n-abi",
    )
    cases.append(
        Case(
            "gate replaces the cross release build with a host one",
            host_release_stand_in,
            True,
            check="gate_script",
            mutation="preserving",
        )
    )

    # The feature reaches a `cargo test`, and that invocation runs
    # doctests only -- so the oracle's `#[cfg(test)]` module, the thing
    # `host_tools` exists to make runnable, never executes.
    doc_only_feature = baseline()
    doc_only_feature[HOST_LANE] = (
        "#!/usr/bin/env bash\n"
        "cargo build --all --features host_tools\n"
        "cargo test --doc -p sele4n-hal --features host_tools\n"
        "cargo test --all\n"
    )
    cases.append(
        Case(
            "host lane passes host_tools only to a --doc run",
            doc_only_feature,
            True,
            check="host_lane",
            mutation="preserving",
        )
    )

    # The script path is in the `run:` value, and the step executes -- it
    # just executes `echo`.
    echoed_gate = baseline()
    echoed_gate[WORKFLOW_FILE] = GOOD_WORKFLOW.replace(
        f"run: ./{GATE_SCRIPT}", f"run: echo ./{GATE_SCRIPT}"
    )
    cases.append(
        Case(
            "workflow echoes the gate script instead of running it",
            echoed_gate,
            True,
            check="workflow",
            mutation="preserving",
        )
    )

    # The path is in a `run:` value AND the step executes -- inside a
    # quoted argument to `echo`, where a quote-unaware splitter cuts on the
    # `;` and reads the tail as a fresh command.  This is the same hole as
    # the `echo` case above, one layer down, in the splitter written to
    # close it; found by self-audit of this cut.
    quoted_echo = baseline()
    quoted_echo[WORKFLOW_FILE] = GOOD_WORKFLOW.replace(
        f"run: ./{GATE_SCRIPT}",
        f'run: echo "building; ./{GATE_SCRIPT} next"',
    )
    cases.append(
        Case(
            "workflow hides the gate path inside a quoted echo argument",
            quoted_echo,
            True,
            check="workflow",
            mutation="preserving",
        )
    )

    # ... and the other direction, which must NOT be reported: a real
    # invocation whose quoted environment prefix contains a space.  A
    # whitespace splitter pushes the command word out of position and
    # reports a job that does run the gate as running nothing -- fail-
    # closed, but wrongly, and the natural repair is to weaken the check.
    env_prefixed = baseline()
    env_prefixed[WORKFLOW_FILE] = GOOD_WORKFLOW.replace(
        f"run: ./{GATE_SCRIPT}",
        f'run: RUSTFLAGS="-D warnings" ./{GATE_SCRIPT}',
    )
    cases.append(
        Case(
            "a quoted env prefix containing a space still counts as running it",
            env_prefixed,
            False,
            check="workflow",
            mutation="none",
        )
    )

    # A block scalar with the indent before the chomping indicator (`|2-`)
    # is valid YAML and must be read as a script, not as a command.
    block_scalar = baseline()
    block_scalar[WORKFLOW_FILE] = GOOD_WORKFLOW.replace(
        f"        run: ./{GATE_SCRIPT}\n",
        f"        run: |2-\n          set -e\n          ./{GATE_SCRIPT}\n",
    )
    cases.append(
        Case(
            "a `|2-` block scalar running the gate is still a runner",
            block_scalar,
            False,
            check="workflow",
            mutation="none",
        )
    )

    # `echo cargo build ...` -- the token `cargo`, the subcommand, the
    # triple, the feature and both profiles are all present; only the
    # command word changed, so CI would run `echo` while Tier 0 reports the
    # AArch64 profiles built.  The same defect as the `run: echo` case
    # above, in the neighbouring function that was not swept when that one
    # was fixed.
    echoed_builds = baseline()
    echoed_builds[GATE_SCRIPT] = GOOD_GATE.replace(
        "cargo build", "echo cargo build"
    )
    cases.append(
        Case(
            "gate echoes its cargo builds instead of running them",
            echoed_builds,
            True,
            check="gate_script",
            mutation="preserving",
        )
    )

    # ... and the accepting direction: `cargo` behind a shell function that
    # execs `"$@"` after one `shift` is genuinely run, which is how the
    # host lane invokes every step.  A resolver that only accepted a bare
    # command word would reject the real configuration.
    wrapped_host_lane = baseline()
    wrapped_host_lane[HOST_LANE] = (
        "#!/usr/bin/env bash\n"
        "run_cargo_step() {\n"
        '    local step_label="$1"\n'
        "    shift\n"
        '    "$@"\n'
        "}\n"
        'run_cargo_step "Build succeeded" cargo build --all --features host_tools\n'
        'run_cargo_step "Unit tests passed" cargo test --all --features std,host_tools\n'
    )
    cases.append(
        Case(
            "cargo behind a `\"$@\"` wrapper still counts as executed",
            wrapped_host_lane,
            False,
            check="host_lane",
            mutation="none",
        )
    )

    # A FOURTH `.S` source that no `.file()` mentions.  Every token the
    # check searches for is present -- all three known sources are still
    # handed to the assembler -- and the new one assembles nowhere.
    unlisted_source = baseline()
    unlisted_source[f"{HAL_CRATE}/src/psci.S"] = (
        ".global psci_call\npsci_call:\n    ret\n"
    )
    cases.append(
        Case(
            "a new .S source no `.file()` mentions is uncovered",
            unlisted_source,
            True,
            check="build_script",
            mutation="preserving",
        )
    )

    # `trap.S` moved onto a builder that is never compiled.  Every token
    # is present and every byte offset is in the right interval -- only
    # the receiver changed, so nothing assembles the source.
    unused_builder = baseline()
    unused_builder[BUILD_SCRIPT] = GOOD_BUILD_RS.replace(
        '        .file("src/trap.S")\n',
        "",
    ).replace(
        "    let mut asm = cc::Build::new();",
        "    let mut unused = cc::Build::new();\n"
        '    unused.file("src/trap.S");\n'
        "    let mut asm = cc::Build::new();",
    )
    cases.append(
        Case(
            "a .S source on a builder that is never compiled is uncovered",
            unused_builder,
            True,
            check="build_script",
            mutation="preserving",
        )
    )

    # `bash -n` reads the script and executes nothing.  The interpreter,
    # the path and the command position are all intact.
    noexec_shell = baseline()
    noexec_shell[WORKFLOW_FILE] = GOOD_WORKFLOW.replace(
        f"run: ./{GATE_SCRIPT}", f"run: bash -n ./{GATE_SCRIPT}"
    )
    cases.append(
        Case(
            "workflow runs the gate under `bash -n`, which executes nothing",
            noexec_shell,
            True,
            check="workflow",
            mutation="preserving",
        )
    )

    # ... and an option that does NOT suppress execution must still pass.
    errexit_shell = baseline()
    errexit_shell[WORKFLOW_FILE] = GOOD_WORKFLOW.replace(
        f"run: ./{GATE_SCRIPT}", f"run: bash -ex ./{GATE_SCRIPT}"
    )
    cases.append(
        Case(
            "`bash -ex` still counts as running the gate",
            errexit_shell,
            False,
            check="workflow",
            mutation="none",
        )
    )

    # `--no-run` compiles the oracle and runs none of its tests.
    no_run_lane = baseline()
    no_run_lane[HOST_LANE] = GOOD_HOST_LANE.replace(
        "cargo test --all --features std,host_tools",
        "cargo test --all --features std,host_tools --no-run",
    )
    cases.append(
        Case(
            "host lane compiles the oracle with --no-run and runs nothing",
            no_run_lane,
            True,
            check="host_lane",
            mutation="preserving",
        )
    )

    # ... and a harness argument after `--` is not a cargo selector.
    harness_args = baseline()
    harness_args[HOST_LANE] = GOOD_HOST_LANE.replace(
        "cargo test --all --features std,host_tools",
        "cargo test --all --features std,host_tools -- --test-threads=1",
    )
    cases.append(
        Case(
            "a harness argument after `--` is not read as a cargo selector",
            harness_args,
            False,
            check="host_lane",
            mutation="none",
        )
    )

    # The cross lint lane deleted.  Both builds, the target, the feature
    # and every other token remain.
    no_clippy = baseline()
    no_clippy[GATE_SCRIPT] = "\n".join(
        line for line in GOOD_GATE.splitlines() if "cargo clippy" not in line
    ) + "\n"
    cases.append(
        Case(
            "gate drops the cross clippy lane",
            no_clippy,
            True,
            check="gate_script",
            mutation="preserving",
        )
    )

    # `-D warnings` moved BEFORE the `--`, where cargo takes it rather than
    # clippy, so a lint on the aarch64 surface no longer fails the step.
    deny_before_separator = baseline()
    deny_before_separator[GATE_SCRIPT] = GOOD_GATE.replace(
        "--features hw_target -- -D warnings", "-D warnings --features hw_target"
    )
    cases.append(
        Case(
            "gate passes -D warnings to cargo instead of clippy",
            deny_before_separator,
            True,
            check="gate_script",
            mutation="preserving",
        )
    )

    # An optimised CUSTOM profile standing in for the debug build: not
    # `release`, so a two-way classification counted it as `-O0`.
    custom_profile = baseline()
    custom_profile[GATE_SCRIPT] = GOOD_GATE.replace(
        'cargo build --target "$CROSS_TARGET"',
        'cargo build --profile production --target "$CROSS_TARGET"',
        1,
    )
    cases.append(
        Case(
            "an optimised custom profile does not count as the debug build",
            custom_profile,
            True,
            check="gate_script",
            mutation="preserving",
        )
    )

    # ... and `--profile dev` IS the debug build, so it must be accepted.
    explicit_dev = baseline()
    explicit_dev[GATE_SCRIPT] = GOOD_GATE.replace(
        'cargo build --target "$CROSS_TARGET"',
        'cargo build --profile dev --target "$CROSS_TARGET"',
        1,
    )
    cases.append(
        Case(
            "`--profile dev` is accepted as the debug build",
            explicit_dev,
            False,
            check="gate_script",
            mutation="none",
        )
    )

    # Failure propagation removed: every command remains, and none of their
    # failures is observed.
    no_errexit = baseline()
    no_errexit[GATE_SCRIPT] = GOOD_GATE.replace("set -euo pipefail", "set -u")
    cases.append(
        Case(
            "gate stops propagating failures",
            no_errexit,
            True,
            check="gate_script",
            mutation="preserving",
        )
    )

    # A wrapper that keeps `shift` and `"$@"` but only LOGS them.
    logging_wrapper = baseline()
    logging_wrapper[HOST_LANE] = (
        "#!/usr/bin/env bash\n"
        "run_cargo_step() {\n"
        '    local step_label="$1"\n'
        "    shift\n"
        '    echo "$@"\n'
        "}\n"
        'run_cargo_step "Unit tests passed" cargo test --all --features std,host_tools\n'
    )
    cases.append(
        Case(
            "a wrapper that only echoes its arguments is not a runner",
            logging_wrapper,
            True,
            check="host_lane",
            mutation="preserving",
        )
    )

    # A case expected to be CAUGHT must actually differ from the clean
    # baseline.  A mutation that silently no-ops -- because the string it
    # replaced is not in the fixture -- produces a case that asserts
    # nothing while reading as coverage.  That happened here once already,
    # so it is checked rather than trusted.
    clean = baseline()
    failures = 0
    for case in cases:
        if case.expect and case.files == clean:
            failures += 1
            print(
                f"[SELF-TEST FAIL] inert mutation, fixture unchanged: "
                f"{case.label}"
            )
            continue
        with tempfile.TemporaryDirectory() as tmp:
            write_tree(tmp, case.files)
            problems = run_checks(tmp)
            if bool(problems) != case.expect:
                failures += 1
                verb = "missed" if case.expect else "false-positived on"
                print(f"[SELF-TEST FAIL] gate {verb}: {case.label}")
                for problem in problems:
                    print(f"                 reported: {problem}")
            else:
                state = "caught" if case.expect else "accepted"
                mark = " [preserving]" if case.mutation == "preserving" else ""
                print(f"[SELF-TEST OK]   {state}: {case.label}{mark}")

    # Every check must be exercised by a mutation that KEEPS its token and
    # breaks only the relation.  Deleting the token is passed by any
    # presence check, so a suite made only of deletions certifies nothing
    # about the property the check is named for -- which is how nine holes
    # in this file reached review across three rounds while the suite
    # reported PASS on every one of them.  Enforced, not asserted.
    covered = {
        case.check
        for case in cases
        if case.expect and case.mutation == "preserving" and case.check
    }
    for check in CHECKS:
        if check not in covered:
            failures += 1
            print(
                f"[SELF-TEST FAIL] check `{check}` has no token-preserving "
                f"negative case. Add one that keeps the token the check "
                f"searches for and breaks only its relation (CLAUDE.md, "
                f"\"Test a gate by breaking the relation, not by deleting "
                f"the token\")."
            )

    if failures:
        print(f"\n[FAIL] {failures} self-test case(s) failed")
        return 1
    print(
        f"\n[PASS] {len(cases)} self-test case(s); "
        f"{len(CHECKS)}/{len(CHECKS)} checks have a token-preserving case"
    )
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
