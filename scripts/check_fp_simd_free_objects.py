#!/usr/bin/env python3
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
"""The kernel's AArch64 object code uses no FP/SIMD register.

`boot.S` traps every FP/SIMD access at EL0 and EL1 (`CPACR_EL1 := 0`), and
the trap frame saves general-purpose registers only.  Both are sound only if
the kernel itself never touches an FP/SIMD register: a vector instruction in
kernel code would trap and halt the core, and if the trap were ever lifted it
would silently overwrite the interrupted thread's `q0`-`q31`.  Rust's
`aarch64-unknown-none` target enables `neon` and `fp-armv8`, and the HAL
built for it carried 129 such instructions (vector zeroing, `d8`-`d15`
spills); the HAL is built for `aarch64-unknown-none-softfloat` instead.

This gate is the evidence rather than the flag: it disassembles each object
or archive named on the command line and refuses any instruction with an
FP/SIMD/SVE register operand (`v`, `q`, `d`, `s`, `h`, `b`, `z` registers)
or an `FPCR`/`FPSR` access.  It reads operands only -- symbol names in
`<...>` and `//` comments are dropped -- so a function called `copy_d8`
cannot trip it and an FP register cannot hide in one.

It fails closed on what it cannot read: an input that does not disassemble
as AArch64 ELF, or that yields no instructions at all, is refused, since a
file that could not be read and a clean file must not produce the same PASS.

Scope.  It decides the files it is handed.  The linked image additionally
contains whatever members of the target's `compiler_builtins` the link pulls
in, and that library is **not** FP-free even for the softfloat target (its
complex-arithmetic helpers and `__negsf2` / `__negdf2` use `d` registers), so
the image-level run is WS-BP BP5.2's, where it decides what was actually
linked.

    check_fp_simd_free_objects.py [--objdump PATH] FILE...
    check_fp_simd_free_objects.py --self-test
"""

from __future__ import annotations

import argparse
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

# An FP/SIMD/SVE register operand, or an FP control/status register.  The
# lookbehind refuses a register-like fragment inside a longer token (`#0x1d0`,
# `x1d`), and the lookahead refuses one that continues (`at s1e1r` names an
# address-translation operation, not the register `s1`).
FP_OPERAND = re.compile(r"(?<![\w.#])(?:[vqdshbz]\d{1,2}(?:\.\w+)?|fpcr|fpsr)(?!\w)")

# `  1c:\tmnemonic\toperands` -- llvm-objdump's instruction line with
# `--no-show-raw-insn`.  The optional `<...>:` form is a function header.
INSTRUCTION = re.compile(r"^\s*[0-9a-f]+:\s+(\S+)(?:\s+(.*))?$")
FUNCTION = re.compile(r"^[0-9a-f]+ <(.+)>:$")
FILE_FORMAT = re.compile(r"file format (\S+)")
AARCH64_FORMAT = "elf64-littleaarch64"


class Unreadable(Exception):
    """A file the gate cannot decide."""


def operands_of(text: str) -> str:
    """The operand field with symbol annotations and comments removed."""
    return re.sub(r"<[^>]*>", "", text).split("//", 1)[0]


def fp_findings(disassembly: str) -> tuple[int, list[str]]:
    """(instructions read, FP/SIMD findings) for one `llvm-objdump -d` output.

    Raises `Unreadable` when a member's format is not AArch64 ELF or when no
    instruction was read at all."""
    formats = FILE_FORMAT.findall(disassembly)
    if not formats:
        raise Unreadable("no `file format` line: the input did not disassemble")
    foreign = sorted({f for f in formats if f != AARCH64_FORMAT})
    if foreign:
        raise Unreadable(f"not AArch64 ELF: {', '.join(foreign)}")
    count = 0
    findings: list[str] = []
    function = "?"
    for line in disassembly.splitlines():
        header = FUNCTION.match(line)
        if header:
            function = header.group(1)
            continue
        insn = INSTRUCTION.match(line)
        if not insn:
            continue
        count += 1
        operands = operands_of(insn.group(2) or "")
        if FP_OPERAND.search(operands):
            findings.append(f"{function}: {insn.group(1)} {operands.strip()}")
    if count == 0:
        raise Unreadable("no instructions disassembled")
    return count, findings


def rust_llvm_tool(name: str) -> str:
    """A tool from the toolchain-pinned `llvm-tools` component (rustup), else PATH.

    One owner for "which LLVM binutil does a gate read object code with", so
    the FP gate and the Lean cross-archive driver cannot disagree about it."""
    rustc = shutil.which("rustc")
    if rustc:
        try:
            sysroot = subprocess.run(
                [rustc, "--print", "sysroot"], cwd=REPO / "rust",
                capture_output=True, text=True, check=True,
            ).stdout.strip()
            host = subprocess.run(
                [rustc, "-vV"], cwd=REPO / "rust",
                capture_output=True, text=True, check=True,
            ).stdout
            triple = re.search(r"^host: (\S+)$", host, re.MULTILINE)
            if triple:
                pinned = Path(sysroot) / "lib/rustlib" / triple.group(1) / "bin" / name
                if pinned.is_file():
                    return str(pinned)
        except (OSError, subprocess.CalledProcessError):
            pass
    found = shutil.which(name)
    if found:
        return found
    raise Unreadable(
        f"no {name}: install the `llvm-tools` component "
        f"(listed in rust/rust-toolchain.toml) or put {name} on PATH"
    )


def default_objdump() -> str:
    """The toolchain-pinned `llvm-objdump` (rustup's `llvm-tools`), else PATH."""
    return rust_llvm_tool("llvm-objdump")


def disassemble(objdump: str, path: Path) -> str:
    if not path.is_file():
        raise Unreadable(f"{path}: no such file")
    result = subprocess.run(
        [objdump, "-d", "--no-show-raw-insn", str(path)],
        capture_output=True, text=True,
    )
    if result.returncode != 0:
        raise Unreadable(f"{path}: llvm-objdump exited {result.returncode}: "
                         f"{result.stderr.strip()[:300]}")
    return result.stdout


def check(paths: list[Path], objdump: str) -> int:
    failed = False
    for path in paths:
        try:
            count, findings = fp_findings(disassemble(objdump, path))
        except Unreadable as exc:
            print(f"FAIL {path}: cannot decide -- {exc}")
            failed = True
            continue
        if findings:
            failed = True
            print(f"FAIL {path}: {len(findings)} FP/SIMD instruction(s) in {count}:")
            for finding in findings[:40]:
                print(f"    {finding}")
            if len(findings) > 40:
                print(f"    ... and {len(findings) - 40} more")
        else:
            print(f"PASS {path}: {count} instructions, no FP/SIMD register operand")
    return 1 if failed else 0


# ---------------------------------------------------------------------------
# Self-test.  Every refused case keeps an FP register in the instruction and
# every accepted case keeps a register-like TOKEN outside the operands, so a
# scanner that matched text rather than operands fails one or the other.
# ---------------------------------------------------------------------------

HEADER = "\nlib.o:\tfile format elf64-littleaarch64\n\nDisassembly of section .text:\n\n"


def _disasm(*lines: str, header: str = HEADER) -> str:
    body = "\n".join(f"      {i * 4:x}:      \t{line}" for i, line in enumerate(lines))
    return f"{header}0000000000000000 <f>:\n{body}\n"


_REFUSED = [
    ("vector zeroing", "movi\tv0.2d, #0000000000000000"),
    ("q-register pair store", "stp\tq0, q1, [sp, #0x60]"),
    ("d-register spill", "stp\td9, d8, [sp, #0x80]"),
    ("single-precision move", "fmov\ts0, w1"),
    ("half-precision", "fcvt\th1, s0"),
    ("byte lane", "mov\tb2, v3.b[1]"),
    ("SIMD lane load", "ld1\t{ v0.b }[0], [x0]"),
    ("SVE register", "add\tz0.d, z1.d, z2.d"),
    ("FPCR read", "mrs\tx0, fpcr"),
    ("FPSR write", "msr\tfpsr, x1"),
    ("register after a symbol", "adr\tx0, <sym>\n      9:      \tfmov\td0, x0"),
]

_ACCEPTED = [
    ("symbol named exactly like a register", "bl\t0x40 <d8>"),
    ("symbol containing a register name", "bl\t0x40 <copy_d8>"),
    ("address-translation operation", "at\ts1e1r, x0"),
    ("register only in a comment", "mov\tx0, #-0x8000000000000000 // =d0"),
    ("hex immediate", "add\tx1, x1, #0x1d0"),
    ("encoded system register", "msr\tS3_0_C1_C0_2, xzr"),
    ("condition code", "b.hs\t0x20 <.L_loop>"),
    ("general registers", "stp\tx29, x30, [sp, #-0x10]!"),
    ("system register name", "msr\tcpacr_el1, xzr"),
]


def self_test() -> int:
    failures: list[str] = []
    for label, insn in _REFUSED:
        _, findings = fp_findings(_disasm("mov\tx0, x1", insn))
        if not findings:
            failures.append(f"refused case accepted: {label}")
    for label, insn in _ACCEPTED:
        _, findings = fp_findings(_disasm(insn))
        if findings:
            failures.append(f"accepted case refused: {label}: {findings}")
    for label, text in [
        ("no format line", "0000000000000000 <f>:\n      0:      \tret\n"),
        ("foreign format", _disasm("ret", header=HEADER.replace(AARCH64_FORMAT, "elf64-x86-64"))),
        ("mixed formats", _disasm("ret") + HEADER.replace(AARCH64_FORMAT, "elf64-x86-64")),
        ("no instructions", HEADER),
    ]:
        try:
            fp_findings(text)
        except Unreadable:
            continue
        failures.append(f"unreadable input decided: {label}")
    count, findings = fp_findings(_disasm("ret", "stp\tq0, q1, [sp]", "stp\td8, d9, [sp]"))
    if count != 3 or len(findings) != 2:
        failures.append(f"counts wrong: {count} instructions, {len(findings)} findings")
    for failure in failures:
        print(f"FAIL self-test: {failure}")
    total = len(_REFUSED) + len(_ACCEPTED) + 5
    if failures:
        return 1
    print(f"check_fp_simd_free_objects self-test: {total} cases passed")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--objdump", help="llvm-objdump to use")
    parser.add_argument("files", nargs="*", type=Path)
    args = parser.parse_args()
    if args.self_test:
        return self_test()
    if not args.files:
        parser.error("no files to check (a gate over nothing decides nothing)")
    try:
        objdump = args.objdump or default_objdump()
    except Unreadable as exc:
        print(f"FAIL: {exc}")
        return 1
    return check(args.files, objdump)


if __name__ == "__main__":
    sys.exit(main())
