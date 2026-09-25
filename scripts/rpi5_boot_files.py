#!/usr/bin/env python3
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
"""The Raspberry Pi 5 boot files: `kernel8.img` and `config.txt` (WS-BP BP5.3).

The firmware loads a flat binary, not an ELF, and it loads it where
`config.txt` says; it writes the device tree where `config.txt` says too.
Both are relations to the linked image, so both files are *cut from* the image
and then *checked against* it:

  1. `kernel8.img` is the image's loaded extent `[_start, __image_load_end)`,
     byte for byte: every loaded section's file bytes at `addr - _start`,
     zero between them, and nothing past `__image_load_end` -- the `NOLOAD`
     sections are the firmware's to leave alone.  It is cut with the
     toolchain's `llvm-objcopy -O binary` and checked against a
     reconstruction from the ELF's own section headers, so the two readings
     of "which bytes are the image" come from two implementations;
  2. `kernel_address` is the image's entry, `_start` and `link.ld`'s
     `MEMORY` `ORIGIN` -- the address `check_kernel_image.py` already holds
     the three equal at -- so the firmware's default load address is never
     what the kernel is entered at;
  3. `device_tree_address` / `device_tree_end` are the linker's
     `.dtb_window` (`__dtb_window_start`, `__dtb_window_end`), which is
     `DTB_WINDOW_SIZE` bytes, 8-byte aligned (Devicetree Specification v0.4
     §5.1), and admissible to `mmu::dtb_window_admissible`: inside the
     kernel's reserved extent the Lean side states (so no boot untyped can
     describe the blob, BP3.2) and disjoint from `[_start, __lean_heap_end)`,
     the memory the image owns.  `device_tree_end` bounds what the firmware
     may write to the window every reader bounds what it reads by;
  4. `config.txt` sets exactly those keys and `arm_64bit` / `kernel`, each
     once, with no conditional `[...]` section: a firmware option the check
     does not name is one that could load the kernel, or write the blob,
     somewhere this check did not look, so an unknown key is refused.

    rpi5_boot_files.py package <sele4n-kernel ELF> <out dir>   # write, then check
    rpi5_boot_files.py check <sele4n-kernel ELF> <out dir>     # check only
    rpi5_boot_files.py --self-test
"""

from __future__ import annotations

import struct
import subprocess
import sys
from dataclasses import replace
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO / "scripts"))

from check_fp_simd_free_objects import Unreadable, rust_llvm_tool  # noqa: E402
from check_kernel_image import (  # noqa: E402
    _IMAGE, _TABLE, Image, parse_script, read_image,
)
from check_link_script import (  # noqa: E402
    BOOT_MAP_FIXTURE, LINK_SCRIPT, lean_reserved_extent, symbols,
)

KERNEL_NAME = "kernel8.img"
CONFIG_NAME = "config.txt"
# Devicetree Specification v0.4 §5.1: the blob is 8-byte aligned in memory.
FDT_ALIGNMENT = 8
# Every key `config.txt` may set, and nothing else.
CONFIG_KEYS = ("arm_64bit", "kernel", "kernel_address", "device_tree_address",
               "device_tree_end")


class GateFailure(Exception):
    """A relation between the boot files and the image does not hold."""


def render_config(entry: int, dtb_start: int, dtb_end: int) -> str:
    return (
        "# seLe4n Raspberry Pi 5 boot configuration.  Generated from the linked\n"
        "# kernel image by scripts/build_rpi5_image.sh; do not edit.  Each value is\n"
        "# the image's own: its entry (link.ld's load address) and the window\n"
        "# link.ld places the device tree in (.dtb_window).\n"
        "arm_64bit=1\n"
        f"kernel={KERNEL_NAME}\n"
        f"kernel_address={entry:#x}\n"
        f"device_tree_address={dtb_start:#x}\n"
        f"device_tree_end={dtb_end:#x}\n"
    )


def parse_config(text: str) -> dict[str, str]:
    values: dict[str, str] = {}
    for number, raw in enumerate(text.splitlines(), 1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("["):
            raise GateFailure(f"{CONFIG_NAME}:{number}: a conditional section `{line}` "
                              f"would let the firmware apply settings this check does "
                              f"not read")
        key, sep, value = line.partition("=")
        if not sep or key.strip() != key or not key:
            raise GateFailure(f"{CONFIG_NAME}:{number}: `{line}` is not `key=value`")
        if key not in CONFIG_KEYS:
            raise GateFailure(f"{CONFIG_NAME}:{number}: `{key}` is not a key the image "
                              f"build sets ({', '.join(CONFIG_KEYS)})")
        if key in values:
            raise GateFailure(f"{CONFIG_NAME}:{number}: `{key}` is set twice")
        values[key] = value.strip()
    missing = [k for k in CONFIG_KEYS if k not in values]
    if missing:
        raise GateFailure(f"{CONFIG_NAME} does not set {', '.join(missing)}")
    return values


def expected_flat(image: Image, data: bytes, start: int, load_end: int) -> bytes:
    """The loaded extent, rebuilt from the section headers alone."""
    flat = bytearray(load_end - start)
    for s in image.sections:
        if s.nobits or s.size == 0:
            continue
        if not start <= s.addr <= s.addr + s.size <= load_end:
            raise GateFailure(f"{s.name} [{s.addr:#x}, {s.addr + s.size:#x}) is loaded "
                              f"outside [{start:#x}, {load_end:#x})")
        flat[s.addr - start:s.addr - start + s.size] = data[s.offset:s.offset + s.size]
    return bytes(flat)


def _hex(value: int | None) -> str:
    return "undefined" if value is None else f"{value:#x}"


def _address(values: dict[str, str], key: str) -> int:
    try:
        return int(values[key], 0)
    except ValueError:
        raise GateFailure(f"{CONFIG_NAME}: `{key}={values[key]}` is not an address") from None


def check_boot_files(image: Image, table: dict[str, int], origin: int,
                     reserved: tuple[int, int], config_text: str, flat: bytes,
                     expected: bytes) -> list[str]:
    problems: list[str] = []
    if flat != expected:
        first = next((i for i, (a, b) in enumerate(zip(flat, expected)) if a != b),
                     min(len(flat), len(expected)))
        problems.append(f"{KERNEL_NAME} is {len(flat):#x} bytes and the image's loaded "
                        f"extent {len(expected):#x}; they first differ at offset {first:#x}")
    try:
        values = parse_config(config_text)
    except GateFailure as e:
        return problems + [str(e)]
    if values["arm_64bit"] != "1":
        problems.append(f"{CONFIG_NAME}: `arm_64bit={values['arm_64bit']}`; the kernel is "
                        f"an AArch64 image and is entered in AArch64")
    if values["kernel"] != KERNEL_NAME:
        problems.append(f"{CONFIG_NAME}: `kernel={values['kernel']}` names a file the image "
                        f"build does not write ({KERNEL_NAME})")
    kernel_address = _address(values, "kernel_address")
    if not kernel_address == image.entry == table.get("_start") == origin:
        problems.append(f"{CONFIG_NAME}: `kernel_address` is {kernel_address:#x}; the "
                        f"image's entry is {image.entry:#x}, `_start` {_hex(table.get('_start'))} "
                        f"and link.ld's ORIGIN {origin:#x}, all one address")
    dtb_start = _address(values, "device_tree_address")
    dtb_end = _address(values, "device_tree_end")
    window = (table.get("__dtb_window_start"), table.get("__dtb_window_end"))
    if (dtb_start, dtb_end) != window:
        problems.append(f"{CONFIG_NAME}: the device tree is pinned to [{dtb_start:#x}, "
                        f"{dtb_end:#x}); link.ld's window is [{_hex(window[0])}, {_hex(window[1])})")
    if dtb_end - dtb_start != table.get("DTB_WINDOW_SIZE") or dtb_start % FDT_ALIGNMENT:
        problems.append(f"{CONFIG_NAME}: the device tree's window [{dtb_start:#x}, "
                        f"{dtb_end:#x}) is not DTB_WINDOW_SIZE bytes, {FDT_ALIGNMENT}-byte "
                        f"aligned")
    start, heap_end = table.get("_start", 0), table.get("__lean_heap_end", 0)
    inside = reserved[0] <= dtb_start <= dtb_end <= reserved[1]
    disjoint = dtb_end <= start or heap_end <= dtb_start
    if not (inside and disjoint):
        problems.append(f"{CONFIG_NAME}: the device tree's window [{dtb_start:#x}, "
                        f"{dtb_end:#x}) is not inside the reserved extent [{reserved[0]:#x}, "
                        f"{reserved[1]:#x}) outside the image [{start:#x}, {heap_end:#x}); "
                        f"init_mmu refuses a device tree anywhere else")
    return problems


def _inputs(elf: Path):
    image = read_image(elf)
    table = symbols(elf)
    origin = parse_script(LINK_SCRIPT.read_text()).origin
    reserved = lean_reserved_extent(BOOT_MAP_FIXTURE.read_text())
    for name in ("_start", "__image_load_end"):
        if name not in table:
            raise GateFailure(f"{elf} defines no `{name}`")
    expected = expected_flat(image, elf.read_bytes(), table["_start"],
                             table["__image_load_end"])
    return image, table, origin, reserved, expected


def check(elf: Path, out: Path) -> str:
    image, table, origin, reserved, expected = _inputs(elf)
    problems = check_boot_files(image, table, origin, reserved,
                                (out / CONFIG_NAME).read_text(),
                                (out / KERNEL_NAME).read_bytes(), expected)
    if problems:
        raise GateFailure("; ".join(problems))
    return (f"{KERNEL_NAME} is the image's {len(expected):#x} loaded bytes, entered at "
            f"{image.entry:#x}; the device tree is pinned to "
            f"[{table['__dtb_window_start']:#x}, {table['__dtb_window_end']:#x})")


def package(elf: Path, out: Path) -> str:
    image, table, _origin, _reserved, _expected = _inputs(elf)
    for name in ("__dtb_window_start", "__dtb_window_end"):
        if name not in table:
            raise GateFailure(f"{elf} defines no `{name}`: link.ld places no device-tree "
                              f"window")
    out.mkdir(parents=True, exist_ok=True)
    (out / KERNEL_NAME).unlink(missing_ok=True)
    subprocess.run([rust_llvm_tool("llvm-objcopy"), "-O", "binary", str(elf),
                    str(out / KERNEL_NAME)], check=True)
    (out / CONFIG_NAME).write_text(render_config(
        image.entry, table["__dtb_window_start"], table["__dtb_window_end"]))
    return check(elf, out)


def self_test() -> int:
    """Each case keeps both files present and well-formed and breaks one
    relation, so a check reduced to "the files exist" fails the case it owns."""
    base = 0x1_0000
    image = replace(_IMAGE, sections=tuple(
        replace(s, offset=base + s.addr - _IMAGE.entry) for s in _IMAGE.sections))
    data = bytes((i * 7 + 3) & 0xFF for i in range(base + 0x4000))
    table = _TABLE
    reserved = (0, table["KERNEL_RESERVED_END"])
    start, load_end = table["_start"], table["__image_load_end"]
    good_flat = expected_flat(image, data, start, load_end)
    good_config = render_config(image.entry, table["__dtb_window_start"],
                                table["__dtb_window_end"])
    flipped = bytearray(good_flat)
    flipped[0x900] ^= 0xFF
    shifted_image = replace(image, sections=tuple(
        replace(s, offset=s.offset + 4) if s.name == ".rodata" else s for s in image.sections))

    def config(**changes: str) -> str:
        lines = good_config.splitlines(keepends=True)
        for key, value in changes.items():
            lines = [f"{key}={value}\n" if line.startswith(f"{key}=") else line
                     for line in lines]
        return "".join(lines)

    heap_end = table["__lean_heap_end"]
    cases = [
        ("the real shape", image, table, good_config, good_flat, None),
        ("a flat image missing its initialised data", image, table, good_config,
         good_flat[:-0x800], "first differ"),
        ("a flat image carrying one NOLOAD page", image, table, good_config,
         good_flat + bytes(0x1000), "first differ"),
        ("a flat image with one byte changed", image, table, good_config,
         bytes(flipped), "first differ at offset 0x900"),
        ("a section read from the wrong file offset", shifted_image, table, good_config,
         good_flat, "first differ"),
        ("the firmware's default load address", image, table,
         config(kernel_address="0x200000"), good_flat, "all one address"),
        ("a 32-bit entry", image, table, config(arm_64bit="0"), good_flat, "AArch64"),
        ("another kernel file", image, table, config(kernel="kernel_2712.img"), good_flat,
         "does not write"),
        ("a device tree inside the Lean heap", image, table,
         config(device_tree_address=hex(heap_end - 0x1000),
                device_tree_end=hex(heap_end - 0x1000 + 0x20_0000)), good_flat,
         ("link.ld's window", "outside the image")),
        ("a device tree past the reserved extent", image, table,
         config(device_tree_address="0x10000000", device_tree_end="0x10200000"), good_flat,
         ("link.ld's window", "outside the image")),
        ("a device-tree end the firmware may write past", image, table,
         config(device_tree_end=hex(table["__dtb_window_end"] + 0x1000)), good_flat,
         ("link.ld's window", "not DTB_WINDOW_SIZE")),
        ("a linker window off the FDT alignment", image,
         {**table, "__dtb_window_start": table["__dtb_window_start"] + 4,
          "__dtb_window_end": table["__dtb_window_end"] + 4},
         config(device_tree_address=hex(table["__dtb_window_start"] + 4),
                device_tree_end=hex(table["__dtb_window_end"] + 4)), good_flat,
         "8-byte aligned"),
        ("an option the check does not read", image, table,
         good_config + "kernel_old=1\n", good_flat, "not a key the image build sets"),
        ("a key set twice", image, table,
         good_config + f"kernel_address={image.entry:#x}\n", good_flat, "set twice"),
        ("a conditional section", image, table, good_config + "[pi5]\n", good_flat,
         "conditional section"),
        ("a key left out", image, table,
         "".join(line for line in good_config.splitlines(keepends=True)
                 if not line.startswith("device_tree_end=")), good_flat,
         "does not set device_tree_end"),
    ]
    failures = 0
    for name, img, tbl, cfg, flat, expect in cases:
        expected = expected_flat(img, data, start, load_end)
        problems = check_boot_files(img, tbl, _IMAGE.entry, reserved, cfg, flat, expected)
        fragments = () if expect is None else (expect,) if isinstance(expect, str) else expect
        ok = len(problems) == len(fragments) and all(
            f in p for f, p in zip(fragments, problems))
        if not ok:
            failures += 1
            print(f"  FAIL {name}: {problems}", file=sys.stderr)
    # A loaded section outside the loaded extent cannot be laid out at all.
    try:
        expected_flat(image, data, start, load_end - 0x1000)
        failures += 1
        print("  FAIL a section past the loaded extent was laid out", file=sys.stderr)
    except GateFailure:
        pass
    total = len(cases) + 1
    print(f"rpi5_boot_files self-test: {total - failures}/{total} passed")
    return 1 if failures else 0


def main(argv: list[str]) -> int:
    if argv[1:] == ["--self-test"]:
        return self_test()
    if len(argv) != 4 or argv[1] not in ("package", "check"):
        print(__doc__.rsplit("\n\n", 1)[-1].strip(), file=sys.stderr)
        return 2
    elf, out = Path(argv[2]), Path(argv[3])
    try:
        summary = (package if argv[1] == "package" else check)(elf, out)
    except (GateFailure, Unreadable, subprocess.CalledProcessError, OSError,
            struct.error) as e:
        print(f"rpi5_boot_files: FAIL — {e}", file=sys.stderr)
        return 1
    print(f"  {out}: {summary}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
