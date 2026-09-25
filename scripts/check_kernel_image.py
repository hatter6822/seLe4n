#!/usr/bin/env python3
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
"""The kernel image is the program `link.ld` describes (WS-BP BP5.1).

`scripts/check_link_script.py` proves `link.ld`'s relations on a *probe*: the
HAL's assembly linked alone, undefined symbols ignored.  This gate asks the
same questions, and the ones only a real link can answer, of the image itself
(`sele4n-kernel`, the one final bare-metal binary in the tree):

  1. it is an AArch64 ELF executable;
  2. it is entered at `_start`, at `link.ld`'s load address (`MEMORY`'s
     `ORIGIN`), which is the first byte of `.text.boot` — the address the
     firmware jumps to, and the one `boot.S`'s FP-trap prologue must occupy;
  3. **nothing is left undefined**: no unresolved reference, and no weak
     undefined symbol, which a static link resolves to address `0` rather
     than refusing (the probe link ignores both; the image may not);
  4. every allocated section is one `link.ld` names, in the order it names
     them — an orphan the linker placed on its own is outside every boundary
     the boot map's permissions are built from — and each has the kind the
     script declares: a `NOLOAD` section occupies no file bytes and lies at or
     after `__bss_start`, every other one is loaded and lies inside
     `[_start, __image_load_end)`, the extent the boot cleans to the Point of
     Unification (BP4.5) and the flat image is cut from (BP5.3);
  5. `__exception_vectors` is `.text.vectors`' first byte, 2048-byte aligned
     (ARM ARM D1.10.2), and the entry points `boot.S` and the vectors branch
     to (`rust_boot_main`, `secondary_entry`, `rust_secondary_main`) are
     text;
  6. `check_link_script.check_layout`'s relations hold of the image's own
     symbol table — the arena, the permission boundaries, the loaded extent
     and the kernel's reserved extent the Lean side states;
  7. with `--lean-kernel ROOTS` (BP5.2), the image carries the Lean kernel:
     `ROOTS` is the linker script `build_lean_aarch64_archive.py` writes and
     the image link reads, it names the library initializer first and the
     boot entry `lean_kernel_main` among the production `@[export]`s, and
     every root it names is defined in the image's text.  A root the image
     does not define is a kernel the link did not carry, whatever the HAL
     half looks like.

It reads the ELF header and section headers itself (a few `struct` fields,
so there is no second tool to disagree with) and the symbol table with the
toolchain-pinned `llvm-nm`.  An input it cannot read is refused.

    check_kernel_image.py [--lean-kernel <libsele4n.roots.ld>] <sele4n-kernel ELF>
    check_kernel_image.py --self-test
"""

from __future__ import annotations

import re
import struct
import subprocess
import sys
from dataclasses import dataclass, replace
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO / "scripts"))

from check_fp_simd_free_objects import Unreadable, rust_llvm_tool  # noqa: E402
from check_link_script import (  # noqa: E402
    BOOT_MAP_FIXTURE, LINK_SCRIPT, _GOOD, check_layout, lean_reserved_extent, symbols,
)
from build_lean_aarch64_archive import Refused, parse_roots_script  # noqa: E402

ELF_MAGIC = b"\x7fELF"
ET_EXEC = 2
EM_AARCH64 = 183
SHF_ALLOC = 0x2
SHF_EXECINSTR = 0x4
SHT_NOBITS = 8
VECTOR_ALIGNMENT = 2048
# The three sections every image has, whatever the link pulled in.
REQUIRED_SECTIONS = (".text.boot", ".text.vectors", ".text")
# What `boot.S` and `vectors.S` branch to by name.
TEXT_SYMBOLS = ("rust_boot_main", "secondary_entry", "rust_secondary_main")
# What the Lean kernel's roots must include: the HAL enters the kernel here.
LEAN_BOOT_ENTRY = "lean_kernel_main"
LEAN_INITIALIZER_PREFIX = "initialize_"


class GateFailure(Exception):
    """A relation this gate checks does not hold."""


@dataclass(frozen=True)
class Section:
    name: str
    addr: int
    size: int
    nobits: bool
    executable: bool


@dataclass(frozen=True)
class Image:
    elf_type: int
    machine: int
    entry: int
    sections: tuple[Section, ...]


@dataclass(frozen=True)
class Script:
    """What `link.ld` declares: the load address and the output sections, in
    order, each with whether it is `NOLOAD`."""
    origin: int
    sections: tuple[tuple[str, bool], ...]


def parse_script(text: str) -> Script:
    origin = re.search(r"\bORIGIN\s*=\s*(0x[0-9A-Fa-f]+)", text)
    if origin is None:
        raise GateFailure(f"{LINK_SCRIPT} declares no MEMORY ORIGIN")
    body = re.search(r"^SECTIONS\s*\{(.*)^\}", text, re.MULTILINE | re.DOTALL)
    if body is None:
        raise GateFailure(f"{LINK_SCRIPT} has no SECTIONS block")
    code = re.sub(r"/\*.*?\*/", lambda m: " " * len(m.group(0)), body.group(1), flags=re.DOTALL)
    declared = tuple(
        (m.group(1), m.group(2) is not None)
        for m in re.finditer(r"^ {4}(\.[\w.]+)\s*(\(NOLOAD\))?\s*:", code, re.MULTILINE)
    )
    if not declared:
        raise GateFailure(f"{LINK_SCRIPT} declares no output section")
    return Script(int(origin.group(1), 16), declared)


def read_image(path: Path) -> Image:
    data = path.read_bytes()
    if data[:4] != ELF_MAGIC or data[4] != 2 or data[5] != 1:
        raise Unreadable(f"{path} is not a little-endian ELF64 file")
    (elf_type, machine, _version, entry, _phoff, shoff, _flags, _ehsize, _phentsize,
     _phnum, shentsize, shnum, shstrndx) = struct.unpack_from("<HHIQQQIHHHHHH", data, 16)
    if shentsize != 64 or shnum == 0 or shstrndx >= shnum:
        raise Unreadable(f"{path} has no readable section header table")
    headers = [struct.unpack_from("<IIQQQQIIQQ", data, shoff + i * 64) for i in range(shnum)]
    strtab_offset, strtab_size = headers[shstrndx][4], headers[shstrndx][5]
    names = data[strtab_offset:strtab_offset + strtab_size]
    sections = []
    for name_off, kind, flags, addr, _offset, size, *_ in headers:
        if not flags & SHF_ALLOC:
            continue
        end = names.find(b"\0", name_off)
        sections.append(Section(names[name_off:end].decode(), addr, size,
                                kind == SHT_NOBITS, bool(flags & SHF_EXECINSTR)))
    return Image(elf_type, machine, entry, tuple(sorted(sections, key=lambda s: s.addr)))


def undefined_symbols(path: Path) -> list[str]:
    out = subprocess.run([rust_llvm_tool("llvm-nm"), "--undefined-only", str(path)],
                         capture_output=True, text=True, check=True).stdout
    return [line.split()[-1] for line in out.splitlines() if line.split()]


def check_image(image: Image, script: Script, table: dict[str, int], undefined: list[str],
                reserved: tuple[int, int], lean_roots: list[str] | None = None) -> list[str]:
    problems: list[str] = []
    if image.elf_type != ET_EXEC or image.machine != EM_AARCH64:
        problems.append(f"the image is ELF type {image.elf_type}, machine {image.machine}; "
                        f"an AArch64 executable is type {ET_EXEC}, machine {EM_AARCH64}")
    if undefined:
        problems.append(f"the link leaves {len(undefined)} symbol(s) undefined: "
                        f"{', '.join(sorted(undefined)[:8])}")
    by_name = {s.name: s for s in image.sections}
    missing = [n for n in REQUIRED_SECTIONS if n not in by_name]
    if missing:
        problems.append(f"the image has no {', '.join(missing)} section")
        return problems
    start = table.get("_start")
    boot = by_name[".text.boot"]
    if not (image.entry == start == script.origin == boot.addr):
        problems.append(f"the entry is {image.entry:#x}, `_start` {start}, link.ld's ORIGIN "
                        f"{script.origin:#x} and `.text.boot` {boot.addr:#x}; all four are "
                        f"the one address the firmware jumps to")
    declared = dict(script.sections)
    order = [name for name, _ in script.sections]
    orphans = [s.name for s in image.sections if s.name not in declared]
    if orphans:
        problems.append(f"the image has section(s) link.ld does not name: {', '.join(orphans)}")
    placed = [s.name for s in image.sections if s.name in declared]
    if placed != sorted(placed, key=order.index):
        problems.append(f"the image's sections are in the order {placed}, not link.ld's")
    load_end, bss_start = table.get("__image_load_end"), table.get("__bss_start")
    if load_end is not None and bss_start is not None and start is not None:
        for s in image.sections:
            if s.name not in declared:
                continue
            if declared[s.name]:
                if not s.nobits or s.addr < bss_start:
                    problems.append(f"{s.name} is NOLOAD in link.ld but is "
                                    f"{'loaded' if not s.nobits else 'placed'} at {s.addr:#x}, "
                                    f"not at or after `__bss_start` ({bss_start:#x}) with no "
                                    f"file bytes")
            elif s.nobits or not start <= s.addr <= s.addr + s.size <= load_end:
                problems.append(f"{s.name} is loaded by link.ld but occupies "
                                f"[{s.addr:#x}, {s.addr + s.size:#x}), not inside "
                                f"[{start:#x}, {load_end:#x}) as file bytes")
    vectors = by_name[".text.vectors"]
    if table.get("__exception_vectors") != vectors.addr or vectors.addr % VECTOR_ALIGNMENT:
        problems.append(f"`__exception_vectors` is at {table.get('__exception_vectors')}, "
                        f"`.text.vectors` at {vectors.addr:#x}; the table is that section's "
                        f"first byte, {VECTOR_ALIGNMENT}-byte aligned")
    text_end = table.get("__text_end")
    text_symbols = list(TEXT_SYMBOLS)
    if lean_roots is not None:
        if not lean_roots or not lean_roots[0].startswith(LEAN_INITIALIZER_PREFIX):
            problems.append(f"the Lean kernel's roots do not begin with the library "
                            f"initializer: {lean_roots[:3]}")
        if LEAN_BOOT_ENTRY not in lean_roots:
            problems.append(f"the Lean kernel's roots do not name the boot entry "
                            f"`{LEAN_BOOT_ENTRY}`: {lean_roots}")
        text_symbols += [r for r in lean_roots if r not in text_symbols]
    for name in text_symbols:
        addr = table.get(name)
        if addr is None or start is None or text_end is None or not start <= addr < text_end:
            problems.append(f"`{name}` is at {addr}, not in the text [{start}, {text_end})")
    non_text = [s.name for s in image.sections
                if s.executable and s.name not in REQUIRED_SECTIONS]
    if non_text:
        problems.append(f"executable section(s) outside the text: {', '.join(non_text)}")
    problems.extend(check_layout(table, reserved))
    return problems


# A well-formed image, for the self-test: the shape a real link produces.
_SCRIPT = Script(0x80000, ((".text.boot", False), (".text.vectors", False), (".text", False),
                          (".rodata", False), (".data", False), (".bss", True),
                          (".stack", True), (".smp_stacks", True), (".lean_heap", True)))
_TABLE = {**_GOOD, "__exception_vectors": 0x80800, "rust_boot_main": 0x80900,
          "secondary_entry": 0x80100, "rust_secondary_main": 0x80a00}
_IMAGE = Image(ET_EXEC, EM_AARCH64, 0x80000, (
    Section(".text.boot", 0x80000, 0x100, False, True),
    Section(".text.vectors", 0x80800, 0x780, False, True),
    Section(".text", 0x81000, 0x0, False, True),
    Section(".rodata", 0x81000, 0x1000, False, False),
    Section(".data", 0x82000, 0x800, False, False),
    Section(".bss", 0x83000, 0x0, True, False),
    Section(".stack", 0x83000, 0xE000, True, False),
    Section(".smp_stacks", 0x91000, 0x30000, True, False),
    Section(".lean_heap", 0xC2000, 0x400_0000, True, False),
))


def _with_section(name: str, **fields) -> Image:
    return replace(_IMAGE, sections=tuple(replace(s, **fields) if s.name == name else s
                                          for s in _IMAGE.sections))


def self_test() -> int:
    """Each case keeps every section and symbol present and breaks one
    relation, so a check reduced to "the names exist" fails the case it owns."""
    reserved = (0, _TABLE["KERNEL_RESERVED_END"])
    cases = [
        ("the real shape", _IMAGE, _SCRIPT, _TABLE, [], None),
        ("a relocatable object rather than an executable", replace(_IMAGE, elf_type=1),
         _SCRIPT, _TABLE, [], "AArch64 executable"),
        ("an entry past `_start`", replace(_IMAGE, entry=0x80004), _SCRIPT, _TABLE, [],
         "the one address the firmware jumps to"),
        ("a load address the script does not declare", _IMAGE,
         replace(_SCRIPT, origin=0x200000), _TABLE, [], "the one address the firmware"),
        ("an unresolved reference", _IMAGE, _SCRIPT, _TABLE, ["lean_kernel_main"],
         "undefined"),
        ("an orphan section", replace(_IMAGE, sections=_IMAGE.sections + (
            Section(".got", 0x8200_0000, 8, False, False),)), _SCRIPT, _TABLE, [],
         "does not name"),
        ("the sections out of the script's order", _IMAGE,
         replace(_SCRIPT, sections=(_SCRIPT.sections[1], _SCRIPT.sections[0])
                 + _SCRIPT.sections[2:]), _TABLE, [], "not link.ld's"),
        ("a NOLOAD section carrying file bytes", _with_section(".stack", nobits=False),
         _SCRIPT, _TABLE, [], "NOLOAD in link.ld"),
        ("a loaded section past the loaded extent",
         _with_section(".data", size=0x1000), _SCRIPT, _TABLE, [], "as file bytes"),
        ("the vector table off its section's first byte", _IMAGE, _SCRIPT,
         {**_TABLE, "__exception_vectors": 0x80880}, [], "__exception_vectors"),
        ("the vector section off 2 KiB", _with_section(".text.vectors", addr=0x80400),
         _SCRIPT, {**_TABLE, "__exception_vectors": 0x80400}, [], "2048-byte aligned"),
        ("a branch target outside the text", _IMAGE, _SCRIPT,
         {**_TABLE, "rust_secondary_main": 0x81800}, [], "rust_secondary_main"),
        ("executable read-only data", _with_section(".rodata", executable=True),
         _SCRIPT, _TABLE, [], "outside the text"),
        ("an arena shorter than its constant", _IMAGE, _SCRIPT,
         {**_TABLE, "__lean_heap_end": _TABLE["__lean_heap_end"] - 4096}, [],
         "not LEAN_HEAP_SIZE"),
    ]
    roots = ["initialize_seLe4n_SeLe4n", "lean_kernel_main", "lean_per_core_timer_tick"]
    kernel = {**_TABLE, "initialize_seLe4n_SeLe4n": 0x80b00, "lean_kernel_main": 0x80c00,
              "lean_per_core_timer_tick": 0x80d00}
    lean_cases = [
        ("the Lean kernel's roots, all text", kernel, roots, None),
        ("a root the image does not define", {k: v for k, v in kernel.items()
                                              if k != "lean_per_core_timer_tick"}, roots,
         "lean_per_core_timer_tick"),
        ("the boot entry placed in read-only data", {**kernel, "lean_kernel_main": 0x81800},
         roots, "lean_kernel_main"),
        ("roots that lost the boot entry", kernel, [roots[0], roots[2]], "boot entry"),
        ("roots whose first is not the initializer", kernel, roots[1:] + roots[:1],
         "library initializer"),
    ]
    failures = 0
    for name, table, lean_roots, expect in lean_cases:
        problems = check_image(_IMAGE, _SCRIPT, table, [], reserved, lean_roots)
        ok = (not problems) if expect is None else (len(problems) == 1 and expect in problems[0])
        if not ok:
            failures += 1
            print(f"  FAIL {name}: {problems}", file=sys.stderr)
    for name, image, script, table, undefined, expect in cases:
        problems = check_image(image, script, table, undefined, reserved)
        ok = (not problems) if expect is None else (len(problems) == 1 and expect in problems[0])
        if not ok:
            failures += 1
            print(f"  FAIL {name}: {problems}", file=sys.stderr)
    # The real script parses into the sections the synthetic one names.
    try:
        real = parse_script(LINK_SCRIPT.read_text())
        if real.sections != _SCRIPT.sections or real.origin != _SCRIPT.origin:
            failures += 1
            print(f"  FAIL link.ld parses as {real}, not the shape the self-test assumes",
                  file=sys.stderr)
    except GateFailure as e:
        failures += 1
        print(f"  FAIL link.ld: {e}", file=sys.stderr)
    total = len(cases) + len(lean_cases) + 1
    print(f"check_kernel_image self-test: {total - failures}/{total} passed")
    return 1 if failures else 0


def main(argv: list[str]) -> int:
    if argv[1:] == ["--self-test"]:
        return self_test()
    args = argv[1:]
    roots_path = None
    if len(args) == 3 and args[0] == "--lean-kernel":
        roots_path, args = Path(args[1]), args[2:]
    if len(args) != 1 or args[0].startswith("-"):
        print(__doc__.rsplit("\n\n", 1)[-1].strip(), file=sys.stderr)
        return 2
    path = Path(args[0])
    try:
        roots = parse_roots_script(roots_path.read_text()) if roots_path else None
        image = read_image(path)
        table = symbols(path)
        problems = check_image(image, parse_script(LINK_SCRIPT.read_text()), table,
                               undefined_symbols(path),
                               lean_reserved_extent(BOOT_MAP_FIXTURE.read_text()), roots)
        if problems:
            raise GateFailure("; ".join(problems))
    except (GateFailure, Refused, Unreadable, subprocess.CalledProcessError, OSError,
            struct.error) as e:
        print(f"check_kernel_image: FAIL — {e}", file=sys.stderr)
        return 1
    loaded = sum(s.size for s in image.sections if not s.nobits)
    kernel = (f"; the Lean kernel's {len(roots)} roots are text" if roots
              else "; no Lean kernel checked")
    print(f"  {path.name}: entered at _start {image.entry:#x}, {len(image.sections)} sections "
          f"in link.ld's order, {loaded:#x} loaded bytes, nothing undefined{kernel}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
