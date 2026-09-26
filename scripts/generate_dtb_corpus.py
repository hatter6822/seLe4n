#!/usr/bin/env python3
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
"""WS-BP BP0.1: the shared device-tree fixture corpus, rendered.

Two implementations read a device tree's structure block: the Rust walk in
`rust/sele4n-hal/src/cmdline.rs` (`fdt_structure_check`, which the bootargs
reader runs before it reads anything) and the Lean parser in
`SeLe4n/Platform/DeviceTree.lean` (`parseFdtNodes` and `fdtRoot?`, the boot
seam's bridge).  Each used to be tested only against blobs its own suite built,
so a refusal added to one side alone passed silently.  This corpus is the one
set of blobs **both** suites consume, against one manifest.

## What is hand-written and what is generated

The **expectations** are written by hand, in `CASES` below, beside the case that
produces them.  The generator only renders bytes and copies those expectations
into the manifest.  It deliberately does **not** compute them: a third
implementation of the walk here would make the manifest agree with whatever this
script believes, which is the drift the corpus exists to catch.

## The questions

`structure` — asked of **both** sides: `readable` when the header validates and
the structure block is one well-formed tree under a single unnamed root, or
`refused`.

`regions` — asked of the **Lean** side: the `(base, size)` extents of every
operational, `device_type` compatible, top-level `/memory` node, in blob order —
or `refused` when the blob is not read at all (every structural refusal, plus a
malformed `reg` or cell width, an extent ending past 2^64, or more than 16
extents), or `-` for none.  **WS-BP BP2.6** retired the Rust `/memory` walk
(the boot map no longer needs a RAM size), so this column is the Lean parser's
regression corpus; it had a Rust `ram_top` companion column until then.

## Files

* `tests/fixtures/dtb/<name>.dtb.hex` — each blob as annotated hex: `#` starts
  a comment, every other hex digit pair is a byte.
* `tests/fixtures/dtb/MANIFEST` — `name | structure | regions`, one per line.

`--check` regenerates in memory and fails on any difference, including a stale
or orphaned `.dtb.hex` file (Tier 0, `scripts/check_dtb_corpus_consumers.py`
runs it).
"""

from __future__ import annotations

import argparse
import struct
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CORPUS_DIR = ROOT / "tests" / "fixtures" / "dtb"
MANIFEST = CORPUS_DIR / "MANIFEST"
HEX_SUFFIX = ".dtb.hex"

FDT_MAGIC = 0xD00DFEED
BEGIN_NODE, END_NODE, PROP, NOP, END = 1, 2, 3, 4, 9
HEADER_SIZE = 40
RSV_BLOCK_SIZE = 16  # one terminating (0, 0) pair
TOKEN_NAMES = {BEGIN_NODE: "BEGIN_NODE", END_NODE: "END_NODE", PROP: "PROP",
               NOP: "NOP", END: "END"}


def be32(v: int) -> bytes:
    return struct.pack(">I", v & 0xFFFFFFFF)


def cells(*values: tuple[int, int]) -> bytes:
    """Big-endian cells: each `(value, width)` is `width` 32-bit cells."""
    out = bytearray()
    for value, width in values:
        for i in reversed(range(width)):
            out += be32(value >> (32 * i))
    return bytes(out)


def cstr(s: str) -> bytes:
    return s.encode("latin-1") + b"\0"


def pad4(b: bytes) -> bytes:
    return b + b"\0" * ((-len(b)) % 4)


class Fdt:
    """A structure block built token by token, each chunk annotated."""

    def __init__(self) -> None:
        self.chunks: list[tuple[bytes, str]] = []
        self.strings = bytearray()
        self.header_overrides: dict[str, int] = {}
        self.struct_trim = 0  # bytes cut off the declared structure block

    def nameoff(self, name: str) -> int:
        needle = cstr(name)
        pos = bytes(self.strings).find(needle)
        # Only reuse a string that starts on a string boundary.
        while pos > 0 and self.strings[pos - 1] != 0:
            pos = bytes(self.strings).find(needle, pos + 1)
        if pos >= 0:
            return pos
        off = len(self.strings)
        self.strings += needle
        return off

    def begin(self, name: str) -> "Fdt":
        self.chunks.append((be32(BEGIN_NODE) + pad4(cstr(name)),
                            f'BEGIN_NODE "{name}"'))
        return self

    def end(self) -> "Fdt":
        self.chunks.append((be32(END_NODE), "END_NODE"))
        return self

    def nop(self, n: int = 1) -> "Fdt":
        for _ in range(n):
            self.chunks.append((be32(NOP), "NOP"))
        return self

    def terminator(self) -> "Fdt":
        self.chunks.append((be32(END), "END"))
        return self

    def raw(self, data: bytes, note: str) -> "Fdt":
        self.chunks.append((data, note))
        return self

    def prop(self, name: str, value: bytes, note: str | None = None) -> "Fdt":
        off = self.nameoff(name)
        body = be32(PROP) + be32(len(value)) + be32(off) + pad4(value)
        self.chunks.append((body, note or f'PROP "{name}" ({len(value)} bytes)'))
        return self

    def u32prop(self, name: str, v: int) -> "Fdt":
        return self.prop(name, be32(v), f'PROP "{name}" = {v}')

    def strprop(self, name: str, v: str) -> "Fdt":
        return self.prop(name, cstr(v), f'PROP "{name}" = "{v}"')

    def reg(self, *pairs: tuple[int, int], ac: int = 2, sc: int = 2) -> "Fdt":
        value = cells(*[x for b, s in pairs for x in ((b, ac), (s, sc))])
        text = ", ".join(f"[{b:#x} +{s:#x}]" for b, s in pairs)
        return self.prop("reg", value, f'PROP "reg" {text}')

    def render(self) -> list[tuple[bytes, str]]:
        struct_block = b"".join(c for c, _ in self.chunks)
        declared_struct = len(struct_block) - self.struct_trim
        off_rsv = HEADER_SIZE
        off_struct = off_rsv + RSV_BLOCK_SIZE
        off_strings = off_struct + len(struct_block)
        strings = pad4(bytes(self.strings))
        total = off_strings + len(strings)
        fields = {
            "magic": FDT_MAGIC, "totalsize": total, "off_dt_struct": off_struct,
            "off_dt_strings": off_strings, "off_mem_rsvmap": off_rsv,
            "version": 17, "last_comp_version": 16, "boot_cpuid_phys": 0,
            "size_dt_strings": len(self.strings), "size_dt_struct": declared_struct,
        }
        fields.update(self.header_overrides)
        header = b"".join(be32(fields[k]) for k in (
            "magic", "totalsize", "off_dt_struct", "off_dt_strings",
            "off_mem_rsvmap", "version", "last_comp_version", "boot_cpuid_phys",
            "size_dt_strings", "size_dt_struct"))
        out = [(header, "header: " + ", ".join(
            f"{k}={v:#x}" for k, v in fields.items()))]
        out.append((b"\0" * RSV_BLOCK_SIZE, "memory reservation block: terminator only"))
        out.extend(self.chunks)
        out.append((strings, "strings block: " + ", ".join(
            repr(s.decode("latin-1")) for s in bytes(self.strings).split(b"\0")[:-1])))
        return out


def root(ac: int | None = 2, sc: int | None = 2) -> Fdt:
    f = Fdt().begin("")
    if ac is not None:
        f.u32prop("#address-cells", ac)
    if sc is not None:
        f.u32prop("#size-cells", sc)
    return f


def memory(f: Fdt, name: str, *pairs: tuple[int, int], device_type: str | None = "memory",
           status: str | None = None, ac: int = 2, sc: int = 2) -> Fdt:
    f.begin(name)
    if device_type is not None:
        f.strprop("device_type", device_type)
    if status is not None:
        f.strprop("status", status)
    f.reg(*pairs, ac=ac, sc=sc)
    return f.end()


def close(f: Fdt) -> Fdt:
    return f.end().terminator()


LOW = 0xFC00_0000
GIB = 0x4000_0000


def c_four_gib() -> Fdt:
    return close(memory(root(), "memory@0", (0, LOW)))


def c_eight_gib() -> Fdt:
    return close(memory(root(), "memory@0", (0, LOW), (0x1_0000_0000, 0x1_0000_0000)))


def c_eight_gib_bcm2711_relocated_bank() -> Fdt:
    # The BCM2711 (Raspberry Pi 4) shape: a low aperture ending at 0xFC00_0000
    # and the 64 MiB the peripheral window displaces relocated above 4 GiB.
    # Kept as a parser case; it is not what a Raspberry Pi 5 reports (below).
    return close(memory(root(), "memory@0", (0, LOW), (0x1_0000_0000, 0x1_0400_0000)))


# What a Raspberry Pi 5's firmware actually writes into /memory@0 on an 8 GiB
# board (Pi 5 Model B Rev 1.1 account, read 2026-09-25): the first 512 KiB, the
# rest of the first gigabyte up to 0x3FC0_0000 -- the firmware keeps the top
# 4 MiB for itself -- and everything above 1 GiB.  DRAM is contiguous across
# the 4 GiB boundary on the BCM2712, so there is no relocated bank.  The RPi5
# binding's variants declared `[0, ramSize)` whole, so until plan row BP7.10 no
# variant was covered by this account and the bridge refused it; BP7.10 reads
# the first gigabyte's RAM off the account, and the Lean witness
# `realFirmwareAccountBindsTheReportedRam` boots it bound to the 8 GiB member
# cut at `0x3FC00000`.
def c_eight_gib_rpi5_firmware() -> Fdt:
    return close(memory(root(), "memory@0", (0, 0x8_0000), (0x8_0000, 0x3FB8_0000),
                        (0x4000_0000, 0x1_C000_0000)))


def c_two_nodes_low_short() -> Fdt:
    f = memory(root(), "memory@0", (0, GIB))
    return close(memory(f, "memory@100000000", (0x1_0000_0000, 2 * GIB)))


def c_discontiguous_high() -> Fdt:
    return close(memory(root(), "memory@0", (0, LOW), (0x1_0000_0000, GIB),
                        (0x2_0000_0000, GIB)))


def c_split_low() -> Fdt:
    return close(memory(root(), "memory@0", (0, 0x8000_0000), (0x8000_0000, 0x7C00_0000)))


def c_out_of_order() -> Fdt:
    return close(memory(root(), "memory@0", (0x1_0000_0000, 0x1_0000_0000), (0, LOW)))


def c_foreign_base() -> Fdt:
    return close(memory(root(), "memory@40000000", (GIB, GIB)))


def c_single_cells() -> Fdt:
    return close(memory(root(1, 1), "memory@0", (0, 0x3C00_0000), ac=1, sc=1))


def c_default_cells() -> Fdt:
    # Neither width declared: §2.3.5's defaults, 2 address cells and 1 size cell.
    return close(memory(root(None, None), "memory@0", (0, GIB), ac=2, sc=1))


def c_address_cells_only() -> Fdt:
    return close(memory(root(2, None), "memory@0", (0, 0x2000_0000), ac=2, sc=1))


def c_no_unit_address() -> Fdt:
    return close(memory(root(), "memory", (0, 0x2000_0000), device_type=None))


def c_other_device_type() -> Fdt:
    return close(memory(root(), "memory@0", (0, LOW), device_type="cpu"))


def c_status_disabled() -> Fdt:
    return close(memory(root(), "memory@0", (0, LOW), status="disabled"))


def c_status_ok_spelling() -> Fdt:
    return close(memory(root(), "memory@0", (0, LOW), status="ok"))


def c_second_node_disabled() -> Fdt:
    f = memory(root(), "memory@0", (0, LOW), status="okay")
    return close(memory(f, "memory@100000000", (0x1_0000_0000, GIB), status="disabled"))


def c_reserved_memory_child() -> Fdt:
    f = memory(root(), "memory@0", (0, GIB))
    f.begin("reserved-memory").u32prop("#address-cells", 2).u32prop("#size-cells", 2)
    memory(f, "memory@1000000", (0x0100_0000, 0x0100_0000))
    return close(f.end())


def c_memory_controller() -> Fdt:
    return close(memory(root(), "memory-controller@0", (0, LOW)))


def c_nested_memory() -> Fdt:
    f = root().begin("soc")
    memory(f, "memory@0", (0, LOW))
    return close(f.end())


def c_no_memory() -> Fdt:
    return close(root().begin("chosen").strprop("bootargs", "smp_max_cores=2").end())


def c_memory_without_reg() -> Fdt:
    return close(root().begin("memory@0").strprop("device_type", "memory").end())


def c_empty_reg() -> Fdt:
    return close(root().begin("memory@0").prop("reg", b"").end())


def c_nop_interleaved() -> Fdt:
    f = root().nop(2)
    f.begin("memory@0").nop().strprop("device_type", "memory").nop().reg((0, LOW)).nop()
    return close(f.end().nop())


def c_many_nops() -> Fdt:
    # More tokens than any fixed walk fuel of 4096: a parser whose fuel is
    # derived from the structure block's own size reads this whole.
    f = memory(root(), "memory@0", (0, LOW))
    f.nop(5000)
    return close(f)


def c_sixteen_extents() -> Fdt:
    pairs = [(i * 0x0100_0000, 0x0100_0000) for i in range(16)]
    return close(memory(root(), "memory@0", *pairs))


def c_seventeen_extents() -> Fdt:
    pairs = [(i * 0x0100_0000, 0x0100_0000) for i in range(17)]
    return close(memory(root(), "memory@0", *pairs))


def c_extent_overflows() -> Fdt:
    return close(memory(root(), "memory@0", (0xFFFF_FFFF_FFFF_0000, 0x10_0000)))


def c_extent_ends_at_2_64() -> Fdt:
    return close(memory(root(), "memory@0", (0xFFFF_FFFF_FFFF_0000, 0x1_0000)))


def c_reg_partial_pair() -> Fdt:
    f = root().begin("memory@0").strprop("device_type", "memory")
    f.prop("reg", cells((0, 2), (LOW, 2), (0, 2)), 'PROP "reg" one pair and a stray address')
    return close(f.end())


def c_three_address_cells() -> Fdt:
    return close(memory(root(3, 2), "memory@0", (0, LOW), ac=3, sc=2))


def c_zero_size_cells() -> Fdt:
    return close(memory(root(2, 0), "memory@0", (0, 0), ac=2, sc=0))


def c_short_cells_property() -> Fdt:
    f = Fdt().begin("").prop("#address-cells", b"\0\0", 'PROP "#address-cells" 2 bytes')
    f.u32prop("#size-cells", 2)
    return close(memory(f, "memory@0", (0, LOW)))


def c_long_cells_property() -> Fdt:
    f = Fdt().begin("").prop("#address-cells", be32(2) + be32(7),
                             'PROP "#address-cells" 8 bytes')
    f.u32prop("#size-cells", 2)
    return close(memory(f, "memory@0", (0, LOW)))


def c_duplicate_reg() -> Fdt:
    f = root().begin("memory@0").strprop("device_type", "memory")
    f.reg((0, GIB)).reg((0, LOW))
    return close(f.end())


def c_duplicate_status() -> Fdt:
    f = root().begin("memory@0").strprop("status", "okay").strprop("status", "disabled")
    f.reg((0, LOW))
    return close(f.end())


def c_property_after_child() -> Fdt:
    f = memory(root(2, None), "memory@0", (0, LOW), ac=2, sc=2)
    f.u32prop("#size-cells", 2)
    return close(f)


def c_duplicate_sibling() -> Fdt:
    f = memory(root(), "memory@0", (0, GIB))
    return close(memory(f, "memory@0", (GIB, GIB)))


def c_duplicate_nested_sibling() -> Fdt:
    f = memory(root(), "memory@0", (0, LOW))
    f.begin("soc").begin("serial@0").end().nop().begin("serial@0").end().end()
    return close(f)


def c_named_root() -> Fdt:
    f = Fdt().begin("board").u32prop("#address-cells", 2).u32prop("#size-cells", 2)
    return close(memory(f, "memory@0", (0, LOW)))


def c_two_roots() -> Fdt:
    f = close(memory(root(), "memory@0", (0, LOW)))
    f.chunks.pop()  # drop the terminator; a second top-level node follows
    f.begin("").end().terminator()
    return f


def c_property_before_root() -> Fdt:
    f = Fdt().u32prop("#address-cells", 2)
    f.begin("").u32prop("#size-cells", 2)
    return close(memory(f, "memory@0", (0, LOW)))


def c_deep_nesting_ok() -> Fdt:
    f = memory(root(), "memory@0", (0, LOW))
    for i in range(31):  # root plus 31 levels: depth 32
        f.begin(f"n{i}")
    for _ in range(31):
        f.end()
    return close(f)


def c_deep_nesting_refused() -> Fdt:
    f = memory(root(), "memory@0", (0, LOW))
    for i in range(32):  # root plus 32 levels: depth 33
        f.begin(f"n{i}")
    for _ in range(32):
        f.end()
    return close(f)


def c_long_name_ok() -> Fdt:
    f = memory(root(), "memory@0", (0, LOW))
    return close(f.begin("n" * 255).end())


def c_long_name_refused() -> Fdt:
    f = memory(root(), "memory@0", (0, LOW))
    return close(f.begin("n" * 256).end())


def c_long_property_name_refused() -> Fdt:
    f = memory(root(), "memory@0", (0, LOW))
    return close(f.begin("chosen").strprop("p" * 256, "x").end())


def c_duplicate_chosen() -> Fdt:
    # Two `/chosen` siblings, each carrying bootargs: both walks refuse the blob,
    # so neither the RAM top nor the command line is taken from it.
    f = memory(root(), "memory@0", (0, LOW))
    f.begin("chosen").strprop("bootargs", "smp_enabled=false").end()
    f.begin("chosen").strprop("bootargs", "smp_max_cores=1").end()
    return close(f)


def c_chosen_under_named_root() -> Fdt:
    f = Fdt().begin("board").u32prop("#address-cells", 2).u32prop("#size-cells", 2)
    memory(f, "memory@0", (0, LOW))
    return close(f.begin("chosen").strprop("bootargs", "smp_enabled=false").end())


def c_strings_block_at_totalsize() -> Fdt:
    # No property anywhere, so the strings block is empty and — placed at the
    # blob's end — starts AT `totalsize`.  The Lean header validator requires
    # both block offsets strictly below `totalsize`; the Rust one required only
    # that each block END within it.
    f = Fdt().begin("").begin("chosen").end()
    return close(f)


def c_truncated_structure() -> Fdt:
    f = c_four_gib()
    f.struct_trim = 8  # the root's END_NODE and the END fall outside the block
    return f


def c_unbalanced_terminator() -> Fdt:
    f = memory(root(), "memory@0", (0, LOW))
    return f.nop().terminator()


def c_unknown_token() -> Fdt:
    f = memory(root(), "memory@0", (0, LOW))
    return close(f.raw(be32(0x7), "unknown token 0x7"))


def c_end_node_at_top_level() -> Fdt:
    f = close(memory(root(), "memory@0", (0, LOW)))
    f.chunks.insert(len(f.chunks) - 1, (be32(END_NODE), "END_NODE with no node open"))
    return f


def c_no_terminator() -> Fdt:
    return memory(root(), "memory@0", (0, LOW)).end()


def c_bad_magic() -> Fdt:
    f = c_four_gib()
    f.header_overrides["magic"] = 0xD00DFEEE
    return f


def c_version_sixteen() -> Fdt:
    f = c_four_gib()
    f.header_overrides["version"] = 16
    return f


def c_last_comp_too_new() -> Fdt:
    f = c_four_gib()
    f.header_overrides["last_comp_version"] = 18
    return f


def c_rsvmap_past_totalsize() -> Fdt:
    f = c_four_gib()
    f.header_overrides["off_mem_rsvmap"] = 0x10000
    return f


# (name, builder, structure, regions) — structure: True = readable;
# regions: None = refused, [] = none.
CASES: list[tuple[str, object, bool, list[tuple[int, int]] | None]] = [
    ("four_gib_low_aperture", c_four_gib, True, [(0, LOW)]),
    ("eight_gib_two_pairs", c_eight_gib, True, [(0, LOW), (0x1_0000_0000, 0x1_0000_0000)]),
    ("eight_gib_bcm2711_relocated_bank", c_eight_gib_bcm2711_relocated_bank, True, [(0, LOW), (0x1_0000_0000, 0x1_0400_0000)]),
    ("eight_gib_rpi5_firmware", c_eight_gib_rpi5_firmware, True, [(0, 0x8_0000), (0x8_0000, 0x3FB8_0000), (0x4000_0000, 0x1_C000_0000)]),
    ("low_aperture_short_forfeits_high", c_two_nodes_low_short, True, [(0, GIB), (0x1_0000_0000, 2 * GIB)]),
    ("discontiguous_high_stops_at_hole", c_discontiguous_high, True, [(0, LOW), (0x1_0000_0000, GIB), (0x2_0000_0000, GIB)]),
    ("split_low_aperture", c_split_low, True, [(0, 0x8000_0000), (0x8000_0000, 0x7C00_0000)]),
    ("extents_out_of_order", c_out_of_order, True, [(0x1_0000_0000, 0x1_0000_0000), (0, LOW)]),
    ("ram_only_at_foreign_base", c_foreign_base, True, [(GIB, GIB)]),
    ("single_cell_widths", c_single_cells, True, [(0, 0x3C00_0000)]),
    ("default_cell_widths", c_default_cells, True, [(0, GIB)]),
    ("address_cells_only_size_default", c_address_cells_only, True, [(0, 0x2000_0000)]),
    ("memory_without_unit_address", c_no_unit_address, True, [(0, 0x2000_0000)]),
    ("memory_named_other_device_type", c_other_device_type, True, []),
    ("memory_status_disabled", c_status_disabled, True, []),
    ("memory_status_ok_spelling", c_status_ok_spelling, True, [(0, LOW)]),
    ("second_node_disabled", c_second_node_disabled, True, [(0, LOW)]),
    ("reserved_memory_child_not_ram", c_reserved_memory_child, True, [(0, GIB)]),
    ("memory_controller_not_memory", c_memory_controller, True, []),
    ("nested_memory_not_top_level", c_nested_memory, True, []),
    ("no_memory_node", c_no_memory, True, []),
    ("memory_node_without_reg", c_memory_without_reg, True, []),
    ("memory_node_empty_reg", c_empty_reg, True, []),
    ("nops_interleaved", c_nop_interleaved, True, [(0, LOW)]),
    ("more_tokens_than_fixed_fuel", c_many_nops, True, [(0, LOW)]),
    ("sixteen_extents_fit", c_sixteen_extents, True, [(i * 0x0100_0000, 0x0100_0000) for i in range(16)]),
    ("seventeen_extents_refused", c_seventeen_extents, True, None),
    ("extent_overflows_64_bits", c_extent_overflows, True, None),
    ("extent_ends_at_2_pow_64", c_extent_ends_at_2_64, True, None),
    ("reg_partial_pair", c_reg_partial_pair, True, None),
    ("three_address_cells", c_three_address_cells, True, None),
    ("zero_size_cells", c_zero_size_cells, True, None),
    ("short_cells_property", c_short_cells_property, True, None),
    ("long_cells_property", c_long_cells_property, True, None),
    ("duplicate_reg_property", c_duplicate_reg, False, None),
    ("duplicate_status_property", c_duplicate_status, False, None),
    ("property_after_child", c_property_after_child, False, None),
    ("duplicate_sibling_memory", c_duplicate_sibling, False, None),
    ("duplicate_nested_sibling", c_duplicate_nested_sibling, False, None),
    ("named_root", c_named_root, False, None),
    ("two_top_level_nodes", c_two_roots, False, None),
    ("property_before_root", c_property_before_root, False, None),
    ("nesting_depth_thirty_two", c_deep_nesting_ok, True, [(0, LOW)]),
    ("nesting_depth_thirty_three", c_deep_nesting_refused, False, None),
    ("node_name_255_bytes", c_long_name_ok, True, [(0, LOW)]),
    ("node_name_256_bytes", c_long_name_refused, False, None),
    ("property_name_256_bytes", c_long_property_name_refused, False, None),
    ("duplicate_chosen_with_bootargs", c_duplicate_chosen, False, None),
    ("chosen_under_named_root", c_chosen_under_named_root, False, None),
    ("empty_strings_block_at_totalsize", c_strings_block_at_totalsize, False, None),
    ("truncated_structure_block", c_truncated_structure, False, None),
    ("terminator_inside_open_node", c_unbalanced_terminator, False, None),
    ("unknown_token", c_unknown_token, False, None),
    ("end_node_at_top_level", c_end_node_at_top_level, False, None),
    ("no_terminator", c_no_terminator, False, None),
    ("bad_magic", c_bad_magic, False, None),
    ("version_sixteen", c_version_sixteen, False, None),
    ("last_comp_version_too_new", c_last_comp_too_new, False, None),
    ("reservation_block_past_totalsize", c_rsvmap_past_totalsize, False, None),
]


def render_hex(chunks: list[tuple[bytes, str]]) -> str:
    lines = ["# Generated by scripts/generate_dtb_corpus.py -- do not edit by hand.",
             "# '#' starts a comment; every other hex digit pair is one byte."]
    # A run of NOPs is one annotated chunk, so a long run stays reviewable.
    merged: list[tuple[bytes, str]] = []
    for data, note in chunks:
        if note.startswith("NOP") and merged and merged[-1][1].startswith("NOP"):
            prev, _ = merged.pop()
            data = prev + data
            note = f"NOP x{len(data) // 4}"
        merged.append((data, note))
    offset = 0
    for data, note in merged:
        lines.append(f"# {offset:#06x}: {note}")
        for i in range(0, len(data), 16):
            row = data[i:i + 16]
            words = [row[j:j + 4].hex() for j in range(0, len(row), 4)]
            lines.append(" ".join(words))
        offset += len(data)
    return "\n".join(lines) + "\n"


def fmt_regions(regions: list[tuple[int, int]] | None) -> str:
    if regions is None:
        return "refused"
    if not regions:
        return "-"
    return ",".join(f"{b:#x}+{s:#x}" for b, s in regions)


def fmt_structure(readable: bool) -> str:
    return "readable" if readable else "refused"


def render_all() -> dict[str, str]:
    files: dict[str, str] = {}
    names = [c[0] for c in CASES]
    if len(set(names)) != len(names):
        raise SystemExit("duplicate case name in CASES")
    manifest = [
        "# WS-BP BP0.1 shared device-tree corpus -- generated by",
        "# scripts/generate_dtb_corpus.py from hand-written expectations.",
        "# name | structure | regions",
        "#   structure: readable | refused (both the Rust and the Lean walk)",
        "#   regions: base+size,... | - (none) | refused (the Lean parser)",
    ]
    for name, build, readable, regions in CASES:
        if not readable and regions is not None:
            raise SystemExit(f"{name}: a structurally refused blob declares no regions")
        files[name + HEX_SUFFIX] = render_hex(build().render())
        manifest.append(f"{name} | {fmt_structure(readable)} | {fmt_regions(regions)}")
    files["MANIFEST"] = "\n".join(manifest) + "\n"
    return files


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true",
                    help="fail if the checked-in corpus differs from a fresh render")
    args = ap.parse_args()
    files = render_all()
    existing = {p.name for p in CORPUS_DIR.glob("*" + HEX_SUFFIX)} if CORPUS_DIR.exists() else set()
    if args.check:
        problems = []
        for name, text in files.items():
            path = CORPUS_DIR / name
            if not path.exists():
                problems.append(f"missing: {path.relative_to(ROOT)}")
            elif path.read_text() != text:
                problems.append(f"stale: {path.relative_to(ROOT)}")
        for orphan in sorted(existing - set(files)):
            problems.append(f"orphaned (no case renders it): tests/fixtures/dtb/{orphan}")
        if problems:
            print("DTB corpus drift -- regenerate with ./scripts/generate_dtb_corpus.py:")
            for p in problems:
                print("  " + p)
            return 1
        print(f"DTB corpus fresh: {len(CASES)} fixtures")
        return 0
    CORPUS_DIR.mkdir(parents=True, exist_ok=True)
    for orphan in existing - set(files):
        (CORPUS_DIR / orphan).unlink()
    for name, text in files.items():
        (CORPUS_DIR / name).write_text(text)
    print(f"wrote {len(CASES)} fixtures to {CORPUS_DIR.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
