#!/usr/bin/env python3
"""The kernel's linker script links, and the Lean heap arena it places is where
the allocator and the boot map assume (WS-BP BP2.1).

`rust/sele4n-hal/link.ld` lays out the kernel image, which
`scripts/check_kernel_image.py` checks once it links; this gate proves the
script's own relations first, on a probe no other part of the build can make
fail, so its `ASSERT`s are live rather than text no tool had read.  This gate links the HAL's own
assembled objects — the real `.text.boot` and `.text.vectors` — under the
script with `rust-lld`, reads the symbol table the link produced, and asks the
relations the Rust side depends on:

  1. `__lean_heap_end - __lean_heap_start` is `LEAN_HEAP_SIZE`, the script's own
     constant, and the start is 4 KiB aligned (`lean_heap::ArenaLayout::of`
     refuses anything else, so a misplaced arena would halt the first Lean
     allocation on the board);
  2. the arena lies above the image and both stack regions, so it overlaps
     nothing the boot writes;
  3. (WS-BP BP7.10) the kernel's reserved extent is whole 2 MiB blocks inside
     the gigabyte at the base of RAM, the level-2 table the boot map describes
     it with, and (WS-BP BP8.1) the image loads 512 KiB above that base, the
     offset its arm64 Image header declares;
  4. (WS-BP BP2.6) the boot map's permission boundaries `_start`, `__text_end`
     and `__rodata_end` are page aligned and ordered, and the read-only data
     begins where the text ends (`__rodata_start`) — which
     `mmu::ImageLayout::is_well_formed` requires of the layout it builds tables
     from;
  5. (WS-BP BP3.2) the arena ends inside the kernel's reserved extent
     `[0, KERNEL_RESERVED_END)`, and `KERNEL_RESERVED_END` is the number the
     Lean side states
     — read from the line `tests/Ak9PlatformSuite.lean` writes into
     `tests/fixtures/boot_map.expected`, so the extent the boot refuses
     untypeds over is the extent this link actually reserved;
  6. (WS-BP BP4.5) `__image_load_end`, the end of the extent the boot cleans to
     the Point of Unification, lies between the read-only data's end and
     `__bss_start` — every loaded byte, and nothing the firmware does not load;
  7. (WS-BP BP5.3) the device tree's window `[__dtb_window_start,
     __dtb_window_end)` is `DTB_WINDOW_SIZE` bytes on a 4 KiB page, lies after
     the Lean heap and ends inside the reserved extent — the window the image
     build's `config.txt` pins the firmware to, and the one `init_mmu` accepts.

Undefined symbols are ignored in the probe link: it is a layout check, and the
objects' references into the Rust and Lean code are the image link's to
resolve (WS-BP BP5.1, BP5.2).

Each of the script's `ASSERT`s is then proved *live* rather than present: the
script is mutated so exactly that assertion's relation breaks — a size that is
not a whole page, an arena that is not page-aligned, (BP7.10) a reserved extent
off a 2 MiB block, one past the first gigabyte and a RAM region that does not
end at it, and (BP2.6) each permission boundary moved off its page, or a
section placed between the text and the read-only data, and (BP4.5) a loaded
extent that runs into the NOLOAD sections, and (BP5.3) a device-tree window of
the wrong size, one moved into the heap, and one past the reserved extent — and
the link must fail naming that assertion's **whole** message.  An `ASSERT` that
a mutation cannot trip reads exactly like one that protects something, and so
does one whose witness is decided by a neighbour: two asserts here end in
"must end inside the kernel's reserved extent" and one mutation trips both, so
a fragment shared by the two would have let either be deleted with the gate
still reporting it live (the `v0.36.2` audit).  A conjoined `ASSERT` gets one
witness per conjunct — the reserved extent off a page, the window off its page,
the read-only data ending before the text, the loaded extent ending before the
read-only data — since a conjunct no mutation reaches is a conjunct nothing
checks.

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
# WS-BP BP7.10: the kernel's reserved extent is described by the boot map's
# level-2 table for the first gigabyte, in 2 MiB blocks (`mmu::KERNEL_RESERVED_END`'s
# compile-time assertion).  `SMALLEST_BOARD_RAM_TOP` is retired: no board's
# firmware reports its first gigabyte whole, so it bounded nothing real.
FIRST_GIGABYTE_TOP = 0x4000_0000
L2_BLOCK = 0x20_0000
BOOT_MAP_FIXTURE = REPO / "tests" / "fixtures" / "boot_map.expected"


def lean_reserved_extent(text: str) -> tuple[int, int]:
    """The `kernelReserved <base> <end>` line the Lean suite writes.  Exactly
    one, or the gate cannot say what the Lean side reserves."""
    rows = [line.split() for line in text.splitlines()
            if line.split()[:1] == ["kernelReserved"]]
    if len(rows) != 1 or len(rows[0]) != 3:
        raise GateFailure(f"{BOOT_MAP_FIXTURE} states the kernel's reserved extent "
                          f"{len(rows)} times; exactly one `kernelReserved base end` line")
    return int(rows[0][1], 16), int(rows[0][2], 16)

def lean_table_pool(text: str) -> tuple[int, int]:
    """The `tablePool <base> <pages>` line the Lean suite writes: the boot's
    table-page pool (WS-BP BP7.1).  Exactly one."""
    rows = [line.split() for line in text.splitlines()
            if line.split()[:1] == ["tablePool"]]
    if len(rows) != 1 or len(rows[0]) != 3:
        raise GateFailure(f"{BOOT_MAP_FIXTURE} states the boot table-page pool "
                          f"{len(rows)} times; exactly one `tablePool base pages` line")
    return int(rows[0][1], 16), int(rows[0][2], 16)


# The assertions, each with the one-edit mutation that must trip it and a
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
            ("        __fault_stacks_top = .;", "        __fault_stacks_top = .;\n        . += 16;"),
        ),
        "must be 4 KiB aligned",
    ),
    # PR #904 (`v0.36.41`): the kernel stacks' guard pages and the per-PE
    # fault stacks the EL1 fault vectors switch to.
    (
        "a boot stack not directly above its guard page",
        (("        . += STACK_GUARD_SIZE;", "        . += STACK_GUARD_SIZE - 16;"),),
        "the boot stack must sit directly above one 4 KiB guard page",
    ),
    (
        "secondary stack slots of the wrong size",
        (("        . += (3 * SECONDARY_STACK_STRIDE);", "        . += (3 * SECONDARY_STACK_STRIDE) - 4096;"),),
        "the secondary stack slots must be three page-aligned 128 KiB slots",
    ),
    (
        "fault stacks for fewer PEs than the image has",
        (("        . += (4 * FAULT_STACK_SIZE);", "        . += (3 * FAULT_STACK_SIZE);"),),
        "the fault stacks must be four 16 KiB stacks, one per PE",
    ),
    (
        "kernel text that starts off a page",
        (("ORIGIN = 0x80000, LENGTH = 0xFF80000", "ORIGIN = 0x80010, LENGTH = 0xFF7FFF0"),),
        "must start on a 4 KiB page",
    ),
    (
        "kernel text that ends off a page",
        (("        . = ALIGN(4096);\n        __text_end = .;",
          "        . = ALIGN(4096) + 8;\n        __text_end = .;"),),
        "must end on a 4 KiB page after it starts",
    ),
    (
        "a section between the kernel text and the read-only data",
        (("    /* Read-only data */\n",
          "    .gap : ALIGN(4096) { . += 4096; } > RAM\n\n    /* Read-only data */\n"),),
        "must begin where the kernel text ends",
    ),
    (
        "read-only data that ends off a page",
        (("        . = ALIGN(4096);\n        __rodata_end = .;",
          "        . = ALIGN(4096) + 8;\n        __rodata_end = .;"),),
        "read-only data must end on a 4 KiB page",
    ),
    (
        "a loaded extent that runs into the NOLOAD sections",
        (("        __image_load_end = .;", "        __image_load_end = . + 0x100000;"),),
        "end before the NOLOAD sections",
    ),
    (
        "an image that outgrows the kernel's reserved extent",
        (("KERNEL_RESERVED_END = 0x10000000;", "KERNEL_RESERVED_END = 0x1000000;"),),
        # The whole message: this mutation trips the device-tree window's
        # ASSERT too, and the fragment "must end inside the kernel's reserved
        # extent" is common to both, so a fragment left ASSERT 4 deletable.
        "the image, Lean heap included, must end inside the kernel's reserved extent",
    ),
    (
        "a reserved extent off a 2 MiB block",
        (("KERNEL_RESERVED_END = 0x10000000;", "KERNEL_RESERVED_END = 0x10001000;"),),
        "the kernel's reserved extent must be whole 2 MiB blocks",
    ),
    (
        "a device-tree window of the wrong size",
        (("        . += DTB_WINDOW_SIZE;", "        . += DTB_WINDOW_SIZE - 4096;"),),
        "must be DTB_WINDOW_SIZE bytes on a 4 KiB page",
    ),
    (
        "a device-tree window off its page",
        (("    .dtb_window (NOLOAD) : ALIGN(4096) {", "    .dtb_window (NOLOAD) : ALIGN(16) {"),
         ("        . += LEAN_HEAP_SIZE;", "        . += LEAN_HEAP_SIZE + 16;")),
        "the device tree's window must be DTB_WINDOW_SIZE bytes on a 4 KiB page",
    ),
    (
        "a device-tree window moved into the Lean heap",
        (("        __dtb_window_start = .;", "        __dtb_window_start = . - 4096;"),
         ("        . += DTB_WINDOW_SIZE;", "        . += DTB_WINDOW_SIZE - 4096;")),
        "must lie after the Lean heap",
    ),
    (
        "a device-tree window past the reserved extent",
        (("LEAN_HEAP_SIZE = 64M;", "LEAN_HEAP_SIZE = 254M;"),),
        "the device tree's window must end inside the kernel's reserved extent",
    ),
    (
        "read-only data that ends before the text",
        (("        __rodata_end = .;", "        __rodata_end = _start;"),),
        "the read-only data must end on a 4 KiB page",
    ),
    (
        "a loaded extent that ends before the read-only data",
        (("        __image_load_end = .;", "        __image_load_end = _start;"),),
        "the loaded image must run from the text through the initialised data",
    ),
    (
        "a reserved extent past the gigabyte at the base of RAM",
        (("KERNEL_RESERVED_END = 0x10000000;", "KERNEL_RESERVED_END = 0x50000000;"),),
        "the kernel's reserved extent must lie inside the gigabyte at the base of RAM",
    ),
    # WS-BP BP8.1: the RAM base is a board line, and the extent sits at the base
    # of a gigabyte-aligned RAM, with the image 512 KiB above it (the offset
    # the arm64 Image header declares).
    (
        "a RAM base off a gigabyte",
        (("RAM_BASE = 0x0;", "RAM_BASE = 0x200000;"),),
        "the kernel's reserved extent must lie inside the gigabyte at the base of RAM",
    ),
    (
        "an image loaded at another offset above the RAM base",
        (("ORIGIN = 0x80000, LENGTH = 0xFF80000", "ORIGIN = 0x100000, LENGTH = 0xFF00000"),),
        "the image must load 512 KiB above the base of RAM, the offset its arm64 Image header declares",
    ),
    (
        "a table-page pool that stops short of the reserved extent's end",
        (("    .boot_table_pool (KERNEL_RESERVED_END - BOOT_TABLE_POOL_PAGES * 4096) (NOLOAD) : {",
          "    .boot_table_pool (KERNEL_RESERVED_END - BOOT_TABLE_POOL_PAGES * 4096 - 4096) (NOLOAD) : {"),),
        "the boot table-page pool must end exactly at the kernel's reserved extent",
    ),
    (
        "a table-page pool off its page",
        (("    .boot_table_pool (KERNEL_RESERVED_END - BOOT_TABLE_POOL_PAGES * 4096) (NOLOAD) : {",
          "    .boot_table_pool (KERNEL_RESERVED_END - BOOT_TABLE_POOL_PAGES * 4096 + 8) (NOLOAD) : {"),
         ("        . += BOOT_TABLE_POOL_PAGES * 4096;", "        . += BOOT_TABLE_POOL_PAGES * 4096 - 8;")),
        "the boot table-page pool must be whole 4 KiB pages",
    ),
    (
        "a table-page pool reaching into the device tree's window",
        (("BOOT_TABLE_POOL_PAGES = 0x10;", "BOOT_TABLE_POOL_PAGES = 0xEF00;"),),
        "the boot table-page pool must lie after the device tree's window",
    ),
    (
        "a RAM region that ends short of the reserved extent",
        (("ORIGIN = 0x80000, LENGTH = 0xFF80000", "ORIGIN = 0x80000, LENGTH = 0xFF7F000"),),
        "link.ld's RAM region must end exactly at the kernel's reserved extent",
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


def check_layout(table: dict[str, int], reserved: tuple[int, int],
                 pool: tuple[int, int] | None = None) -> list[str]:
    """The relations, over one link's symbol table, the reserved extent the Lean
    side states and (WS-BP BP7.1) the table-page pool it states — `None` means
    the link's own pool, for the self-test's cases whose subject is elsewhere."""
    need = ("_start", "__text_end", "__rodata_start", "__rodata_end", "__image_load_end",
            "__bss_start", "__bss_end",
            "__stack_top", "__smp_secondary_stack_top", "__lean_heap_start",
            "__lean_heap_end", "LEAN_HEAP_SIZE", "KERNEL_RESERVED_END",
            "__dtb_window_start", "__dtb_window_end", "DTB_WINDOW_SIZE",
            "__boot_table_pool_start", "__boot_table_pool_end", "BOOT_TABLE_POOL_PAGES")
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
    text_start, text_end, rodata_end = (table["_start"], table["__text_end"],
                                        table["__rodata_end"])
    if text_start % PAGE or text_end % PAGE or rodata_end % PAGE:
        problems.append(f"the permission boundaries {text_start:#x}, {text_end:#x}, "
                        f"{rodata_end:#x} are not all 4 KiB aligned")
    if table["__rodata_start"] != text_end:
        problems.append(f"the read-only data begins at {table['__rodata_start']:#x}, not "
                        f"where the text ends ({text_end:#x})")
    if not text_start < text_end <= rodata_end <= table["__bss_end"]:
        problems.append(f"the permission boundaries {text_start:#x} < {text_end:#x} <= "
                        f"{rodata_end:#x} are not ordered inside the image")
    # WS-BP BP4.5: the extent the boot cleans to the Point of Unification is
    # every loaded byte and nothing the firmware does not load.
    load_end = table["__image_load_end"]
    if not rodata_end <= load_end <= table["__bss_start"]:
        problems.append(f"the loaded image ends at {load_end:#x}, outside "
                        f"[{rodata_end:#x}, {table['__bss_start']:#x}] (the read-only data's "
                        f"end to the NOLOAD sections' start)")
    reserved_end = table["KERNEL_RESERVED_END"]
    if reserved_end % L2_BLOCK or reserved_end > FIRST_GIGABYTE_TOP:
        problems.append(f"the kernel's reserved extent ends at {reserved_end:#x}, not on a "
                        f"2 MiB block inside the first gigabyte ({FIRST_GIGABYTE_TOP:#x})")
    if reserved != (0, reserved_end):
        problems.append(f"link.ld reserves [0, {reserved_end:#x}), the Lean side "
                        f"[{reserved[0]:#x}, {reserved[1]:#x})")
    if end > reserved_end:
        problems.append(f"the arena ends at {end:#x}, past the kernel's reserved extent "
                        f"({reserved_end:#x})")
    # WS-BP BP5.3: the window the firmware is pinned to write the device tree
    # in is one `init_mmu` accepts: outside the memory the image owns and
    # inside the extent no boot untyped reaches.
    dtb_start, dtb_end = table["__dtb_window_start"], table["__dtb_window_end"]
    if dtb_end - dtb_start != table["DTB_WINDOW_SIZE"] or dtb_start % PAGE:
        problems.append(f"the device tree's window [{dtb_start:#x}, {dtb_end:#x}) is not "
                        f"DTB_WINDOW_SIZE ({table['DTB_WINDOW_SIZE']:#x}) bytes on a page")
    if not end <= dtb_start <= dtb_end <= reserved_end:
        problems.append(f"the device tree's window [{dtb_start:#x}, {dtb_end:#x}) is not "
                        f"between the Lean heap's end ({end:#x}) and the reserved "
                        f"extent's ({reserved_end:#x})")
    # WS-BP BP7.1: the table-page pool is the last whole pages of the reserved
    # extent, after the device tree's window, and the pool the Lean side boots
    # configured address spaces from.
    pool_start, pool_end = table["__boot_table_pool_start"], table["__boot_table_pool_end"]
    pages = table["BOOT_TABLE_POOL_PAGES"]
    if pool_end != reserved_end or pool_start % PAGE or pool_end - pool_start != pages * PAGE:
        problems.append(f"the table-page pool [{pool_start:#x}, {pool_end:#x}) is not "
                        f"BOOT_TABLE_POOL_PAGES ({pages:#x}) pages ending at the reserved "
                        f"extent's end ({reserved_end:#x})")
    if pool_start < dtb_end:
        problems.append(f"the table-page pool starts at {pool_start:#x}, inside the device "
                        f"tree's window (which ends at {dtb_end:#x})")
    if pool is not None and pool != (pool_start, pages):
        problems.append(f"link.ld's table-page pool is ({pool_start:#x}, {pages:#x} pages), "
                        f"the Lean side's ({pool[0]:#x}, {pool[1]:#x} pages)")
    return problems


def mutate(text: str, edits) -> str:
    for old, new in edits:
        if text.count(old) != 1:
            raise GateFailure(f"the witness edit {old!r} does not match link.ld exactly once; "
                              "update the witness with the script")
        text = text.replace(old, new)
    return text


_GOOD = {
    "_start": 0x80000, "__text_end": 0x81000, "__rodata_start": 0x81000,
    "__rodata_end": 0x82000, "__image_load_end": 0x82800, "__bss_start": 0x83000,
    "__bss_end": 0x83000, "__stack_top": 0x91000,
    "__smp_secondary_stack_top": 0xC1000, "__lean_heap_start": 0xC2000,
    "__lean_heap_end": 0xC2000 + 0x400_0000, "LEAN_HEAP_SIZE": 0x400_0000,
    "KERNEL_RESERVED_END": 0x1000_0000,
    "__dtb_window_start": 0xC2000 + 0x400_0000, "__dtb_window_end": 0xC2000 + 0x420_0000,
    "DTB_WINDOW_SIZE": 0x20_0000,
    "__boot_table_pool_start": 0x0FFF_0000, "__boot_table_pool_end": 0x1000_0000,
    "BOOT_TABLE_POOL_PAGES": 0x10,
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
                                "__lean_heap_end": 0xC2010 + 0x400_0000,
                                "__dtb_window_start": 0xC3000 + 0x400_0000,
                                "__dtb_window_end": 0xC3000 + 0x420_0000}, "not 4 KiB aligned"),
        ("an arena inside the secondary stacks", {"__lean_heap_start": 0xC0000,
                                                  "__lean_heap_end": 0xC0000 + 0x400_0000},
         "inside the image or its stacks"),
        ("a reserved extent past the first gigabyte", {"KERNEL_RESERVED_END": 0x5000_0000},
         ("not on a 2 MiB block inside the first gigabyte", "pages ending at the reserved extent's end")),
        ("a reserved extent off a 2 MiB block", {"KERNEL_RESERVED_END": 0x1000_1000},
         ("not on a 2 MiB block inside the first gigabyte", "pages ending at the reserved extent's end")),
        ("a missing symbol", {"__lean_heap_end": None}, "defines no __lean_heap_end"),
        ("a text end off its page", {"__text_end": 0x81008, "__rodata_start": 0x81008},
         "not all 4 KiB aligned"),
        ("read-only data ending before the text", {"__rodata_end": 0x80000},
         "not ordered inside the image"),
        ("a gap between the text and the read-only data", {"__rodata_start": 0x82000},
         "not where the text ends"),
        ("an arena past the reserved extent", {"KERNEL_RESERVED_END": 0x200_0000},
         ("past the kernel's reserved extent", "between the Lean heap's end", "pages ending at the reserved extent's end")),
        ("a loaded extent that stops inside the read-only data",
         {"__image_load_end": 0x81800}, "the loaded image ends"),
        ("a loaded extent that runs into .bss", {"__image_load_end": 0x83800},
         "the loaded image ends"),
        ("a Lean extent that differs", {}, "the Lean side"),
        ("a device-tree window shorter than its constant",
         {"__dtb_window_end": _GOOD["__dtb_window_end"] - PAGE}, "not DTB_WINDOW_SIZE"),
        ("a device-tree window off its page",
         {"__dtb_window_start": _GOOD["__dtb_window_start"] + 8,
          "__dtb_window_end": _GOOD["__dtb_window_end"] + 8}, "not DTB_WINDOW_SIZE"),
        ("a device-tree window inside the Lean heap",
         {"__dtb_window_start": _GOOD["__lean_heap_end"] - PAGE,
          "__dtb_window_end": _GOOD["__lean_heap_end"] - PAGE + 0x20_0000},
         "between the Lean heap's end"),
        ("a device-tree window past the reserved extent",
         {"__dtb_window_start": 0x1000_0000, "__dtb_window_end": 0x1020_0000},
         ("between the Lean heap's end", "inside the device tree's window")),
        ("a table-page pool that stops short of the extent",
         {"__boot_table_pool_start": 0x0FFE_F000, "__boot_table_pool_end": 0x0FFF_F000},
         "pages ending at the reserved extent's end"),
        ("a table-page pool shorter than its constant",
         {"__boot_table_pool_start": 0x0FFF_1000}, "pages ending at the reserved extent's end"),
        ("a table-page pool inside the device tree's window",
         {"__boot_table_pool_start": _GOOD["__dtb_window_end"] - PAGE,
          "BOOT_TABLE_POOL_PAGES": (0x1000_0000 - _GOOD["__dtb_window_end"] + PAGE) // PAGE},
         "inside the device tree's window"),
        ("a Lean pool that differs", {}, "the Lean side's"),
    ]
    failures = 0
    for name, edits, expect in cases:
        table = {k: v for k, v in {**_GOOD, **edits}.items() if v is not None}
        # The Lean side states the link's own extent, except in the case whose
        # subject is that they differ.
        reserved = ((0, 0x2000_0000) if name == "a Lean extent that differs"
                    else (0, table.get("KERNEL_RESERVED_END", 0)))
        pool = ((0x0FFF_0000, 0x20) if name == "a Lean pool that differs"
                else (table.get("__boot_table_pool_start", 0),
                      table.get("BOOT_TABLE_POOL_PAGES", 0)))
        problems = check_layout(table, reserved, pool)
        # A case names the one relation it breaks, or -- where breaking it
        # necessarily breaks a second (an arena past the reserved extent puts
        # the window after it past the extent too) -- each, in order.
        expected = () if expect is None else (expect,) if isinstance(expect, str) else expect
        ok = len(problems) == len(expected) and all(
            fragment in problem for fragment, problem in zip(expected, problems))
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
            fixture = BOOT_MAP_FIXTURE.read_text()
            problems = check_layout(table, lean_reserved_extent(fixture), lean_table_pool(fixture))
            if problems:
                raise GateFailure("; ".join(problems))
            print(f"  link.ld: arena [{table['__lean_heap_start']:#x}, "
                  f"{table['__lean_heap_end']:#x}) above the image and stacks, inside the "
                  f"reserved extent [0, {table['KERNEL_RESERVED_END']:#x})")
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
