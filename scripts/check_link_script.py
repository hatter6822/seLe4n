#!/usr/bin/env python3
"""The kernel's linker script links, and the Lean heap arena it places is where
the allocator and the boot map assume (WS-BP BP2.1).

`rust/sele4n-hal/link.ld` is linked by nothing in the tree until BP5.2 builds
the kernel image, so without this gate its sections, its symbols and its
`ASSERT`s would be text no tool had read.  This gate links the HAL's own
assembled objects — the real `.text.boot` and `.text.vectors` — under the
script with `rust-lld`, reads the symbol table the link produced, and asks the
relations the Rust side depends on:

  1. `__lean_heap_end - __lean_heap_start` is `LEAN_HEAP_SIZE`, the script's own
     constant, and the start is 4 KiB aligned (`lean_heap::ArenaLayout::of`
     refuses anything else, so a misplaced arena would halt the first Lean
     allocation on the board);
  2. the arena lies above the image and both stack regions, so it overlaps
     nothing the boot writes;
  3. the arena ends inside the smallest Raspberry Pi 5's RAM, `[0, 1 GiB)`.

Undefined symbols are ignored in the probe link: it is a layout check, and the
objects' references into the Rust and Lean code are BP5.2's link to resolve.

Each of the script's three `ASSERT`s is then proved *live* rather than present:
the script is mutated so exactly that assertion's relation breaks — a size that
is not a whole page, an arena that is not page-aligned, an arena too big for the
smallest board — and the link must fail naming that assertion's message.  An
`ASSERT` that a mutation cannot trip reads exactly like one that protects
something.

    check_link_script.py <libsele4n_hal_asm.a>
    check_link_script.py --self-test
"""

from __future__ import annotations

import re
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO / "scripts"))

from check_fp_simd_free_objects import Unreadable, rust_llvm_tool  # noqa: E402

LINK_SCRIPT = REPO / "rust" / "sele4n-hal" / "link.ld"
PAGE = 4096
# The smallest Raspberry Pi 5 is the 1 GiB board, whose RAM is [0, 1 GiB):
# `rpi5Variants` in SeLe4n/Platform/RPi5/Board.lean.
SMALLEST_BOARD_RAM_TOP = 0x4000_0000

# The three assertions, each with the one-edit mutation that must trip it and a
# fragment of the message it must fail with.  Every edit is applied to the real
# script and must match exactly once, so a script that stops matching the
# mutation fails the gate rather than making the witness inert.
ASSERTION_WITNESSES = (
    (
        "a size that is not a whole page",
        (("LEAN_HEAP_SIZE = 64M;", "LEAN_HEAP_SIZE = 64M + 8;"),),
        "whole number of 4 KiB pages",
    ),
    (
        "an arena that is not page-aligned",
        (
            ("    .lean_heap (NOLOAD) : ALIGN(4096) {", "    .lean_heap (NOLOAD) : ALIGN(16) {"),
            ("        . += (3 * 64K);", "        . += (3 * 64K) + 16;"),
        ),
        "must be 4 KiB aligned",
    ),
    (
        "an arena too big for the smallest board",
        (("LEAN_HEAP_SIZE = 64M;", "LEAN_HEAP_SIZE = 1024M;"),),
        "smallest RPi5's 1 GiB",
    ),
)


class GateFailure(Exception):
    """A relation this gate checks does not hold."""


def extract_members(archive: Path, into: Path) -> list[Path]:
    """The archive's object members, extracted.  An archive with no `boot.o`
    is refused: without it the probe has no `.text.boot` and proves nothing."""
    subprocess.run([rust_llvm_tool("llvm-ar"), "x", str(archive)], cwd=into, check=True)
    objects = sorted(into.glob("*.o"))
    if not any(o.name.endswith("boot.o") for o in objects):
        raise GateFailure(f"{archive} holds no boot.o (members: {[o.name for o in objects]})")
    return objects


def link(script: Path, objects: list[Path], out: Path) -> subprocess.CompletedProcess:
    return subprocess.run(
        [rust_llvm_tool("rust-lld"), "-flavor", "gnu", "-T", str(script),
         "--unresolved-symbols=ignore-all", *map(str, objects), "-o", str(out)],
        capture_output=True, text=True,
    )


def symbols(elf: Path) -> dict[str, int]:
    out = subprocess.run([rust_llvm_tool("llvm-nm"), str(elf)],
                         capture_output=True, text=True, check=True).stdout
    table: dict[str, int] = {}
    for line in out.splitlines():
        parts = line.split()
        if len(parts) == 3 and re.fullmatch(r"[0-9a-fA-F]+", parts[0]):
            table[parts[2]] = int(parts[0], 16)
    return table


def check_layout(table: dict[str, int]) -> list[str]:
    """The three relations, over one link's symbol table."""
    need = ("_start", "__bss_end", "__stack_top", "__smp_secondary_stack_top",
            "__lean_heap_start", "__lean_heap_end", "LEAN_HEAP_SIZE")
    missing = [n for n in need if n not in table]
    if missing:
        return [f"the link defines no {', '.join(missing)}"]
    problems = []
    start, end = table["__lean_heap_start"], table["__lean_heap_end"]
    if end - start != table["LEAN_HEAP_SIZE"]:
        problems.append(f"the arena spans {end - start:#x} bytes, not LEAN_HEAP_SIZE "
                        f"({table['LEAN_HEAP_SIZE']:#x})")
    if start % PAGE or end % PAGE:
        problems.append(f"the arena [{start:#x}, {end:#x}) is not 4 KiB aligned")
    below = max(table["__bss_end"], table["__stack_top"], table["__smp_secondary_stack_top"])
    if start < below or start < table["_start"]:
        problems.append(f"the arena starts at {start:#x}, inside the image or its stacks "
                        f"(which end at {below:#x})")
    if end > SMALLEST_BOARD_RAM_TOP:
        problems.append(f"the arena ends at {end:#x}, past the smallest board's RAM "
                        f"({SMALLEST_BOARD_RAM_TOP:#x})")
    return problems


def mutate(text: str, edits) -> str:
    for old, new in edits:
        if text.count(old) != 1:
            raise GateFailure(f"the witness edit {old!r} does not match link.ld exactly once; "
                              "update the witness with the script")
        text = text.replace(old, new)
    return text


_GOOD = {
    "_start": 0x80000, "__bss_end": 0x81000, "__stack_top": 0x91000,
    "__smp_secondary_stack_top": 0xC1000, "__lean_heap_start": 0xC2000,
    "__lean_heap_end": 0xC2000 + 0x400_0000, "LEAN_HEAP_SIZE": 0x400_0000,
}


def self_test() -> int:
    """`check_layout` over synthetic tables: each case keeps every symbol and
    breaks exactly one relation, so a check reduced to "the symbols exist"
    fails the case that relation owns."""
    cases = [
        ("the real shape", {}, None),
        ("an arena shorter than its constant", {"__lean_heap_end": _GOOD["__lean_heap_end"] - PAGE},
         "not LEAN_HEAP_SIZE"),
        ("an unaligned arena", {"__lean_heap_start": 0xC2010,
                                "__lean_heap_end": 0xC2010 + 0x400_0000}, "not 4 KiB aligned"),
        ("an arena inside the secondary stacks", {"__lean_heap_start": 0xC0000,
                                                  "__lean_heap_end": 0xC0000 + 0x400_0000},
         "inside the image or its stacks"),
        ("an arena past the smallest board", {"__lean_heap_start": 0x3FF0_0000,
                                               "__lean_heap_end": 0x43F0_0000}, "past the smallest"),
        ("a missing symbol", {"__lean_heap_end": None}, "defines no __lean_heap_end"),
    ]
    failures = 0
    for name, edits, expect in cases:
        table = {k: v for k, v in {**_GOOD, **edits}.items() if v is not None}
        problems = check_layout(table)
        if expect is None:
            ok = not problems
        else:
            ok = len(problems) == 1 and expect in problems[0]
        if not ok:
            failures += 1
            print(f"  FAIL {name}: {problems}", file=sys.stderr)
    for name, edits, _ in ASSERTION_WITNESSES:
        try:
            mutate(LINK_SCRIPT.read_text(), edits)
        except GateFailure as e:
            failures += 1
            print(f"  FAIL witness {name}: {e}", file=sys.stderr)
    total = len(cases) + len(ASSERTION_WITNESSES)
    print(f"check_link_script self-test: {total - failures}/{total} passed")
    return 1 if failures else 0


def main(argv: list[str]) -> int:
    if argv[1:] == ["--self-test"]:
        return self_test()
    if len(argv) != 2:
        print(__doc__.rsplit("\n\n", 1)[-1].strip(), file=sys.stderr)
        return 2
    archive = Path(argv[1]).resolve()
    try:
        with tempfile.TemporaryDirectory() as tmp:
            work = Path(tmp)
            objects = extract_members(archive, work)
            linked = link(LINK_SCRIPT, objects, work / "probe.elf")
            if linked.returncode != 0:
                raise GateFailure(f"link.ld does not link:\n{linked.stderr}")
            table = symbols(work / "probe.elf")
            problems = check_layout(table)
            if problems:
                raise GateFailure("; ".join(problems))
            print(f"  link.ld: arena [{table['__lean_heap_start']:#x}, "
                  f"{table['__lean_heap_end']:#x}) above the image and stacks, inside 1 GiB")
            text = LINK_SCRIPT.read_text()
            for name, edits, message in ASSERTION_WITNESSES:
                mutated = work / "mutated.ld"
                mutated.write_text(mutate(text, edits))
                result = link(mutated, objects, work / "mutated.elf")
                if result.returncode == 0:
                    raise GateFailure(f"link.ld accepts {name}: its ASSERT does not fire")
                if message not in result.stderr:
                    raise GateFailure(f"link.ld refuses {name}, but not with its ASSERT "
                                      f"({message!r}):\n{result.stderr}")
                print(f"  ASSERT live: {name} is refused")
    except (GateFailure, Unreadable, subprocess.CalledProcessError, OSError) as e:
        print(f"check_link_script: FAIL — {e}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
