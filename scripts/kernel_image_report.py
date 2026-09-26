#!/usr/bin/env python3
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
"""The kernel image's size and section map, published with the run (WS-BP BP5.4).

`check_kernel_image.py` decides whether the image is the program `link.ld`
describes and `rpi5_boot_files.py` whether the boot files are cut from it.
Neither says how big anything is, so a change that doubles `.text` or pushes
the image towards the kernel's reserved extent passes both and is found on the
board.  This report makes those numbers part of every run:

  * the size of `kernel8.img` -- the file the firmware loads -- read from the
    **file**, and required to equal the image's loaded extent
    `[_start, __image_load_end)`, so the figure published is the figure of what
    ships rather than a sum that could disagree with it;
  * the loaded section bytes and the alignment padding between them, which is
    the flat image less the sections;
  * the `NOLOAD` bytes (`.bss`, both stack regions, the Lean heap, the
    device-tree window), which the firmware never writes but the kernel owns;
  * how much of the kernel's reserved extent `[0, KERNEL_RESERVED_END)` the
    image uses, up to `__dtb_window_end`, the last thing `link.ld` places;
  * the section map: every allocated section, in address order, with its
    extent, its size and whether it is text, loaded data or `NOLOAD`.

It writes Markdown to stdout and, when `GITHUB_STEP_SUMMARY` names a file (a
GitHub Actions run), **appends** the same Markdown there, and it writes the
numbers as JSON beside the boot files (`kernel-image-report.json`) so the run's
artifact carries them.  An input it cannot read, a missing symbol, or a
`kernel8.img` that is not the loaded extent is refused: a report built on a
number it could not establish would be a guess published as a measurement.

    kernel_image_report.py <sele4n-kernel ELF> <boot-files dir>
    kernel_image_report.py --self-test
"""

from __future__ import annotations

import json
import os
import struct
import subprocess
import sys
import tempfile
from dataclasses import replace
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO / "scripts"))

from check_fp_simd_free_objects import Unreadable  # noqa: E402
from check_kernel_image import _IMAGE, _TABLE, Image, read_image  # noqa: E402
from check_link_script import symbols  # noqa: E402

KERNEL_NAME = "kernel8.img"
REPORT_NAME = "kernel-image-report.json"
NEEDED = ("_start", "__image_load_end", "__dtb_window_end", "KERNEL_RESERVED_END")


class ReportRefused(Exception):
    """A number the report publishes could not be established."""


def _mib(n: int) -> str:
    return f"{n / (1 << 20):.2f} MiB"


def _kind(section) -> str:
    if section.nobits:
        return "NOLOAD"
    return "text" if section.executable else "loaded data"


def measure(image: Image, table: dict[str, int], flat_size: int) -> dict:
    """The report's numbers, or `ReportRefused` naming the one it could not
    establish."""
    missing = [n for n in NEEDED if n not in table]
    if missing:
        raise ReportRefused(f"the image defines no {', '.join(missing)}")
    start, load_end = table["_start"], table["__image_load_end"]
    if flat_size != load_end - start:
        raise ReportRefused(f"{KERNEL_NAME} is {flat_size:#x} bytes, but the image's loaded "
                            f"extent [_start, __image_load_end) is {load_end - start:#x}: the "
                            f"file is not the image, so its size is not the image's")
    if not image.sections:
        raise ReportRefused("the image has no allocated section")
    loaded = sum(s.size for s in image.sections if not s.nobits)
    noload = sum(s.size for s in image.sections if s.nobits)
    text = sum(s.size for s in image.sections if s.executable and not s.nobits)
    if loaded > flat_size:
        raise ReportRefused(f"the loaded sections carry {loaded:#x} bytes, more than the "
                            f"{flat_size:#x} of {KERNEL_NAME}")
    reserved_end, placed_end = table["KERNEL_RESERVED_END"], table["__dtb_window_end"]
    return {
        "entry": image.entry,
        "flat_bytes": flat_size,
        "loaded_section_bytes": loaded,
        "padding_bytes": flat_size - loaded,
        "text_bytes": text,
        "noload_bytes": noload,
        "reserved_extent_end": reserved_end,
        "placed_end": placed_end,
        "sections": [{"name": s.name, "start": s.addr, "end": s.addr + s.size,
                      "size": s.size, "kind": _kind(s)} for s in image.sections],
    }


def render(m: dict) -> str:
    used = m["placed_end"]
    total = m["reserved_extent_end"]
    rows = [
        "### Kernel image (`sele4n-kernel`)",
        "",
        "| | bytes | |",
        "|---|---:|---|",
        f"| `{KERNEL_NAME}` (the loaded extent `[_start, __image_load_end)`) | "
        f"{m['flat_bytes']:#x} | {_mib(m['flat_bytes'])} |",
        f"| loaded section bytes | {m['loaded_section_bytes']:#x} | "
        f"{_mib(m['loaded_section_bytes'])} |",
        f"| of which text | {m['text_bytes']:#x} | {_mib(m['text_bytes'])} |",
        f"| alignment padding in `{KERNEL_NAME}` | {m['padding_bytes']:#x} | |",
        f"| `NOLOAD` (`.bss`, stacks, Lean heap, device-tree window) | "
        f"{m['noload_bytes']:#x} | {_mib(m['noload_bytes'])} |",
        f"| reserved extent used, to `__dtb_window_end` | {used:#x} of {total:#x} | "
        f"{100 * used / total:.1f}% |",
        "",
        f"Entered at `{m['entry']:#x}`.",
        "",
        "| section | start | end | size | kind |",
        "|---|---:|---:|---:|---|",
    ]
    rows += [f"| `{s['name']}` | {s['start']:#x} | {s['end']:#x} | {s['size']:#x} | {s['kind']} |"
             for s in m["sections"]]
    return "\n".join(rows) + "\n"


def publish(m: dict, out: Path, summary: str | None) -> str:
    text = render(m)
    (out / REPORT_NAME).write_text(json.dumps(m, indent=2) + "\n")
    if summary:
        with open(summary, "a", encoding="utf-8") as f:
            f.write(text + "\n")
    return text


def self_test() -> int:
    """Each refusal case keeps every input present and breaks one relation."""
    table = dict(_TABLE)
    flat = table["__image_load_end"] - table["_start"]
    failures = 0

    def expect(label: str, ok: bool) -> None:
        nonlocal failures
        print(f"  {'ok  ' if ok else 'FAIL'} {label}")
        failures += 0 if ok else 1

    good = measure(_IMAGE, table, flat)
    expect("the loaded bytes are the loaded sections' sum",
           good["loaded_section_bytes"] == sum(s.size for s in _IMAGE.sections if not s.nobits))
    expect("the padding is the flat image less the sections",
           good["padding_bytes"] == flat - good["loaded_section_bytes"])
    expect("text is the executable loaded sections",
           good["text_bytes"] == sum(s.size for s in _IMAGE.sections
                                     if s.executable and not s.nobits))
    expect("every allocated section is in the map, in address order",
           [s["name"] for s in good["sections"]] == [s.name for s in _IMAGE.sections])
    text = render(good)
    expect("the Markdown names every section and the flat size",
           all(f"`{s.name}`" in text for s in _IMAGE.sections) and f"{flat:#x}" in text)

    refusals = [
        ("a kernel8.img one page short of the loaded extent",
         lambda: measure(_IMAGE, table, flat - 0x1000), "is not the image"),
        ("a kernel8.img carrying one NOLOAD page",
         lambda: measure(_IMAGE, table, flat + 0x1000), "is not the image"),
        ("an image with no device-tree window",
         lambda: measure(_IMAGE, {k: v for k, v in table.items() if k != "__dtb_window_end"},
                         flat), "__dtb_window_end"),
        ("an image with no allocated section",
         lambda: measure(replace(_IMAGE, sections=()), table, flat), "no allocated section"),
    ]
    for label, run, fragment in refusals:
        try:
            run()
            expect(f"refuses {label}", False)
        except ReportRefused as e:
            expect(f"refuses {label}", fragment in str(e))

    with tempfile.TemporaryDirectory() as tmp:
        out = Path(tmp)
        summary = out / "summary.md"
        summary.write_text("earlier step\n")
        publish(good, out, str(summary))
        publish(good, out, str(summary))
        written = summary.read_text()
        expect("the step summary is appended to, never overwritten",
               written.startswith("earlier step\n") and written.count("### Kernel image") == 2)
        expect("the JSON carries the published numbers",
               json.loads((out / REPORT_NAME).read_text())["flat_bytes"] == flat)
    print(f"kernel_image_report self-test: {'PASS' if failures == 0 else 'FAIL'}")
    return 0 if failures == 0 else 1


def main(argv: list[str]) -> int:
    if argv[1:] == ["--self-test"]:
        return self_test()
    if len(argv) != 3 or argv[1].startswith("-"):
        print(__doc__.rsplit("\n\n", 1)[-1].strip(), file=sys.stderr)
        return 2
    elf, out = Path(argv[1]), Path(argv[2])
    try:
        m = measure(read_image(elf), symbols(elf), (out / KERNEL_NAME).stat().st_size)
        text = publish(m, out, os.environ.get("GITHUB_STEP_SUMMARY") or None)
    except (ReportRefused, Unreadable, subprocess.CalledProcessError, OSError,
            struct.error) as e:
        print(f"kernel_image_report: FAIL — {e}", file=sys.stderr)
        return 1
    print(text, end="")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
