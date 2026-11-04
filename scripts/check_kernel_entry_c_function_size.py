#!/usr/bin/env python3
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
"""Every exported kernel entry compiles to a dispatch, not to the kernel.

The syscall entry routes each syscall to its arm through
`syscallEntryCheckedK`, whose compiled form (`syscallEntryCheckedK_eq_routed`)
calls one out-of-line function per route (`SeLe4n/Kernel/RoutedArms/`).  Before
that, every `@[inline]` layer between the `@[export]` and the arms inlined the
whole kernel: the exported syscall entry was one C function of 278k lines, and
the chain held a dozen such copies that clang compiled for most of an hour and,
four at a time, ran out of memory on.

This gate holds the C function of every `@[export]` in the package to a budget.
The exports are read from the Lean **code view** with the shared attribute
parser (`lean_code_view.attribute_arguments`), so the set is derived from the
code: an entry added with `@[export]` is held to the budget without a list to
update.  Each exporting module's C is generated with Lake's `:c` facet (which
elaborates and compiles nothing), and the export's definition is located by its
symbol.  An export whose definition is not found is a failure, never an empty
pass.  A function's extent is over-approximated as the run from its header to
the next header (`check_suite_c_function_size.py`'s measure), so a header the
pattern misses only lengthens a run and the gate fails closed.
"""
from __future__ import annotations

import pathlib
import re
import subprocess
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import lean_code_view  # noqa: E402

BUDGET_LINES = 20_000
HEADER = re.compile(r"^(LEAN_EXPORT|static) .*\{$")


def export_extent(lines: list[str], symbol: str) -> tuple[int, int] | None:
    """The (first line, length) of `symbol`'s C definition, or `None`."""
    define = re.compile(r"^LEAN_EXPORT .*[ *]" + re.escape(symbol) + r"\(.*\{$")
    for index, line in enumerate(lines):
        if define.match(line):
            end = index + 1
            while end < len(lines) and not HEADER.match(lines[end]):
                end += 1
            return index + 1, end - index
    return None


def main() -> int:
    root = pathlib.Path(__file__).resolve().parent.parent
    exports: dict[str, list[str]] = {}
    for path in sorted((root / "SeLe4n").rglob("*.lean")):
        view = lean_code_view.code_no_strings(path.read_text())
        names = lean_code_view.attribute_arguments(view, "export")
        if names:
            module = ".".join(path.relative_to(root).with_suffix("").parts)
            exports[module] = names
    if not exports:
        print("FAIL: no @[export] found under SeLe4n/; the inventory is empty",
              file=sys.stderr)
        return 1
    generate = subprocess.run(
        ["lake", "build", *(module + ":c" for module in exports)], cwd=root)
    if generate.returncode != 0:
        print(f"FAIL: lake could not generate the entries' C (exit {generate.returncode})",
              file=sys.stderr)
        return 1
    failures: list[str] = []
    checked = 0
    for module, names in exports.items():
        c_file = root / ".lake/build/ir" / (module.replace(".", "/") + ".c")
        if not c_file.is_file():
            failures.append(f"{module}: generated C not found at {c_file.relative_to(root)}")
            continue
        lines = c_file.read_text().splitlines()
        for symbol in names:
            extent = export_extent(lines, symbol)
            if extent is None:
                failures.append(f"{module}: no C definition of the export {symbol} "
                                f"in {c_file.relative_to(root)}")
                continue
            checked += 1
            start, length = extent
            if length > BUDGET_LINES:
                failures.append(
                    f"{symbol}: {length} lines at {c_file.relative_to(root)}:{start} "
                    f"(budget {BUDGET_LINES}); an @[inline] layer above the routed arms "
                    "is compiling the kernel into the entry")
    for failure in failures:
        print(f"FAIL: {failure}", file=sys.stderr)
    if not failures:
        print(f"kernel entry C size: {checked} exports within {BUDGET_LINES} lines")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
