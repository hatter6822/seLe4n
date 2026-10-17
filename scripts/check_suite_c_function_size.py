#!/usr/bin/env python3
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
"""No test-suite C function is large enough to stall clang.

The kernel's syscall entries are `@[inline]`, so a suite that calls one
directly receives the whole kernel inlined into the calling helper.  Lean emits
that helper as one C function of 70k-190k lines, and clang -O3 is superlinear
in function size: four suites built that way took 30-100 minutes each to
compile.  The suites call the out-of-line copies in
`SeLe4n/Testing/DispatchEntryCalls.lean` instead, which are compiled once.

This gate reads the C Lean generated for each named executable's root module
and fails if any function in it exceeds the budget.  The executable-to-module
map is read from `lakefile.toml` with `tomllib`.  A function's extent is
over-approximated as the run of lines from one definition header (a line
opening with `LEAN_EXPORT ` or `static ` and ending in `{`, the shape Lean's C
emitter gives every function it defines) to the next.  Whatever sits between
two headers is counted into the earlier run, so a header the pattern misses
only makes a run longer and the gate fails closed.  A missing C file is
a failure, never an empty pass.
"""
import pathlib
import re
import sys
import tomllib

BUDGET_LINES = 40_000
HEADER = re.compile(r"^(LEAN_EXPORT|static) .*\{$")


def main(argv: list[str]) -> int:
    root = pathlib.Path(__file__).resolve().parent.parent
    if not argv:
        print("usage: check_suite_c_function_size.py <lean_exe>...", file=sys.stderr)
        return 2
    lake = tomllib.loads((root / "lakefile.toml").read_text())
    roots = {exe["name"]: exe["root"] for exe in lake.get("lean_exe", [])}
    failures = []
    for exe in argv:
        if exe not in roots:
            failures.append(f"{exe}: no [[lean_exe]] with this name in lakefile.toml")
            continue
        c_file = root / ".lake/build/ir" / (roots[exe].replace(".", "/") + ".c")
        if not c_file.is_file():
            failures.append(f"{exe}: generated C not found at {c_file.relative_to(root)}")
            continue
        start, longest, longest_start = 1, 0, 1
        lines = c_file.read_text().splitlines()
        for lineno, line in enumerate(lines, start=1):
            if HEADER.match(line):
                if lineno - start > longest:
                    longest, longest_start = lineno - start, start
                start = lineno
        if len(lines) + 1 - start > longest:
            longest, longest_start = len(lines) + 1 - start, start
        if longest > BUDGET_LINES:
            failures.append(
                f"{exe}: a function of {longest} lines starts at "
                f"{c_file.relative_to(root)}:{longest_start} (budget {BUDGET_LINES}); "
                "call the kernel entry through SeLe4n.Testing.DispatchEntryCalls")
    for f in failures:
        print(f"FAIL: {f}", file=sys.stderr)
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
