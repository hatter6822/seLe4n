#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Render QEMU `virt`'s own device tree as the annotated-hex fixture
`tests/fixtures/qemu_virt_dtb.hex` (WS-BP BP8.1).

The fixture is QEMU's blob, not a hand-written one: the `virt` board check
(`SeLe4n.Platform.QemuVirt.qemuVirtPlatformConfigFromDtb`) is tested against
exactly what QEMU hands the kernel in `x0`, so a QEMU release that moves a
device or the RAM is caught by regenerating this file and running
`lake exe ak9_platform_suite`, not by the first boot.

QEMU pads the blob it dumps to 1 MiB of zeros, and the header's `totalsize`
says so.  The render keeps every byte the header's blocks name — the header,
the memory reservation block, the structure block and the strings block — and
rewrites `totalsize` to the strings block's end, which is where the padding
begins.  Nothing else changes, and the self-test holds both halves: every byte
the four blocks name survives, and the result ends exactly at the strings
block.

QEMU also writes two fresh random values into `/chosen` on every run —
`kaslr-seed` and `rng-seed` — so two dumps of one machine never agree byte for
byte.  The render zeroes those two values, keeping their lengths, which is the
only other change; the kernel reads neither (the verified parser reads
`/chosen` for nothing, and the HAL's reader for `bootargs` alone), and without
it the fixture could not be checked against a fresh dump at all.  For the same
reason the alignment padding after each node name and property value is
zeroed: the format gives it no meaning, and QEMU leaves at least one such byte
uninitialised (after `/chosen`'s `stdout-path`), so it too differs run to run.

    ./scripts/qemu_virt_dtb_fixture.py                # regenerate from QEMU
    ./scripts/qemu_virt_dtb_fixture.py --check        # the fixture is QEMU's (skips without QEMU)
    ./scripts/qemu_virt_dtb_fixture.py --from-dtb F   # render a blob already dumped
    ./scripts/qemu_virt_dtb_fixture.py --self-test
"""

from __future__ import annotations

import os
import shutil
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
FIXTURE = REPO / "tests" / "fixtures" / "qemu_virt_dtb.hex"
#: The machine `scripts/test_qemu.sh` boots — the same arguments, so the
#: fixture is the blob the lane's kernel is handed.
QEMU_ARGS = ["-M", "virt,gic-version=2", "-cpu", "cortex-a76", "-smp", "4", "-m", "1G",
             "-nic", "none"]
FDT_MAGIC = 0xD00DFEED
HEADER = struct.Struct(">10I")
#: The `/chosen` properties QEMU fills with fresh randomness on every run.
RANDOM_PROPERTIES = (b"kaslr-seed", b"rng-seed")


class DtbError(Exception):
    """The blob is not one this renderer can compact faithfully."""


def compact(blob: bytes) -> bytes:
    """Cut QEMU's zero padding: `totalsize` becomes the strings block's end."""
    if len(blob) < HEADER.size:
        raise DtbError("shorter than an FDT header")
    (magic, totalsize, off_struct, off_strings, off_rsv, version, last_comp,
     boot_cpu, size_strings, size_struct) = HEADER.unpack_from(blob)
    if magic != FDT_MAGIC:
        raise DtbError(f"bad magic {magic:#x}")
    if totalsize > len(blob):
        raise DtbError("totalsize is past the dumped bytes")
    end = off_strings + size_strings
    blocks_end = max(end, off_struct + size_struct, off_rsv + 16)
    if blocks_end != end:
        raise DtbError("the strings block is not the last block — nothing to cut")
    if end > totalsize:
        raise DtbError("the strings block ends past totalsize")
    if any(blob[end:totalsize]):
        raise DtbError("the bytes past the strings block are not padding")
    out = bytearray(blob[:end])
    struct.pack_into(">I", out, 4, end)
    _zero_random_properties(out, off_struct, size_struct, off_strings, size_strings)
    return bytes(out)


def _zero_random_properties(blob: bytearray, off_struct: int, size_struct: int,
                            off_strings: int, size_strings: int) -> None:
    """Zero the values of `RANDOM_PROPERTIES`, walking the structure block."""
    at, end = off_struct, off_struct + size_struct
    while at + 4 <= end:
        (token,) = struct.unpack_from(">I", blob, at)
        at += 4
        if token == 1:  # BEGIN_NODE: a NUL-terminated name, padded to 4
            nul = blob.index(0, at)
            padded = (nul + 4) & ~3
            blob[nul:padded] = bytes(padded - nul)
            at = padded
        elif token == 3:  # PROP: len, nameoff, value padded to 4
            length, nameoff = struct.unpack_from(">II", blob, at)
            at += 8
            if nameoff >= size_strings:
                raise DtbError("a property name is outside the strings block")
            name_at = off_strings + nameoff
            name = bytes(blob[name_at:blob.index(0, name_at)])
            if name in RANDOM_PROPERTIES:
                blob[at:at + length] = bytes(length)
            padded = (at + length + 3) & ~3
            blob[at + length:padded] = bytes(padded - at - length)
            at = padded
        elif token in (2, 4):  # END_NODE, NOP
            continue
        elif token == 9:  # END
            return
        else:
            raise DtbError(f"unknown structure token {token:#x}")
    raise DtbError("the structure block has no FDT_END")


def render(blob: bytes, provenance: str) -> str:
    """The annotated-hex form the Lean suite reads (`#` comments, pairs of hex)."""
    lines = [
        "# QEMU `virt`'s device tree, as QEMU hands it to the kernel in x0 (WS-BP BP8.1).",
        f"# Generated by scripts/qemu_virt_dtb_fixture.py from {provenance} -- do not edit by hand.",
        "# Changes from QEMU's dump: totalsize cut to the strings block's end, and the",
        "# values of /chosen's per-run random kaslr-seed and rng-seed zeroed, with",
        "# the alignment padding after names and values (which QEMU leaves uninitialised).",
        "# '#' starts a comment; every other hex digit pair is one byte.",
    ]
    for at in range(0, len(blob), 16):
        chunk = blob[at:at + 16]
        words = [chunk[i:i + 4].hex() for i in range(0, len(chunk), 4)]
        lines.append(" ".join(words))
    return "\n".join(lines) + "\n"


def parse(text: str) -> bytes:
    digits = "".join("".join(line.split("#", 1)[0].split()) for line in text.splitlines())
    return bytes.fromhex(digits)


def dump_from_qemu(qemu: str) -> bytes:
    with tempfile.TemporaryDirectory() as tmp:
        target = Path(tmp) / "virt.dtb"
        args = list(QEMU_ARGS)
        args[1] = f"{args[1]},dumpdtb={target}"
        # QEMU's refusal to start is the one diagnostic worth keeping: without it
        # a missing option ROM read as "the fixture is stale".
        done = subprocess.run([qemu, *args, "-nographic"], stdin=subprocess.DEVNULL,
                              capture_output=True, text=True)
        if done.returncode != 0 or not target.is_file():
            raise DtbError(f"{qemu} did not dump its `virt` device tree "
                           f"(exit {done.returncode}): {done.stderr.strip()}")
        return target.read_bytes()


def qemu_version(qemu: str) -> str:
    out = subprocess.run([qemu, "--version"], check=True, capture_output=True, text=True)
    return out.stdout.splitlines()[0].strip()


def self_test() -> int:
    strings = b"rng-seed\0model\0"
    structure = (
        struct.pack(">I", 1) + b"\0\xaa\xbb\xcc"                        # BEGIN_NODE "", dirty pad
        + struct.pack(">III", 3, 5, 0) + b"\x11\x22\x33\x44\x55\xee\xee\xee"  # rng-seed
        + struct.pack(">III", 3, 2, 9) + b"q\0\xdd\xdd"                    # model = "q"
        + struct.pack(">II", 2, 9)                                       # END_NODE, END
    )
    off_rsv = HEADER.size
    off_struct = off_rsv + 16
    off_strings = off_struct + len(structure)
    total = off_strings + len(strings) + 64
    body = bytearray(total)
    HEADER.pack_into(body, 0, FDT_MAGIC, total, off_struct, off_strings, off_rsv, 17, 16, 0,
                     len(strings), len(structure))
    body[off_struct:off_strings] = structure
    body[off_strings:off_strings + len(strings)] = strings
    padded = bytes(body)
    out = compact(padded)
    failures = []
    if len(out) != off_strings + len(strings):
        failures.append("the compacted blob does not end at the strings block")
    if struct.unpack_from(">I", out, 4)[0] != len(out):
        failures.append("totalsize was not rewritten to the new end")
    seed_at = off_struct + 8 + 12
    if out[seed_at:seed_at + 8] != bytes(8):
        failures.append("rng-seed's value or its padding was not zeroed")
    model_at = seed_at + 8 + 12
    if out[model_at:model_at + 4] != b"q\0\0\0":
        failures.append("an ordinary property's value changed, or its padding was not zeroed")
    if out[off_struct + 4:off_struct + 8] != bytes(4):
        failures.append("a node name's padding was not zeroed")
    if out[:4] != padded[:4] or out[8:off_struct] != padded[8:off_struct]:
        failures.append("the header or the reservation block changed beyond totalsize")
    if parse(render(out, "self-test")) != out:
        failures.append("render/parse is not the identity")
    for name, bad in [
        ("non-zero padding", padded[:-1] + b"\x01"),
        ("bad magic", b"\0\0\0\0" + padded[4:]),
    ]:
        try:
            compact(bad)
            failures.append(f"{name} was compacted")
        except DtbError:
            pass
    for f in failures:
        print(f"[FAIL] qemu_virt_dtb_fixture self-test: {f}")
    if not failures:
        print("[PASS] qemu_virt_dtb_fixture self-test: 9 checks")
    return 1 if failures else 0


def main(argv: list[str]) -> int:
    if argv[:1] == ["--self-test"]:
        return self_test()
    if argv[:1] == ["--from-dtb"] and len(argv) == 2:
        blob = Path(argv[1]).read_bytes()
        FIXTURE.write_text(render(compact(blob), f"`{Path(argv[1]).name}`"))
        print(f"wrote {FIXTURE.relative_to(REPO)}")
        return 0
    qemu = os.environ.get("QEMU_BIN", "qemu-system-aarch64")
    if shutil.which(qemu) is None:
        if argv[:1] == ["--check"]:
            print(f"[SKIP] qemu_virt_dtb_fixture: `{qemu}` not installed")
            return 0
        print(f"error: `{qemu}` not installed", file=sys.stderr)
        return 1
    try:
        blob = compact(dump_from_qemu(qemu))
    except DtbError as err:
        print(f"[FAIL] qemu_virt_dtb_fixture: {err}")
        return 1
    rendered = render(blob, qemu_version(qemu) + " " + " ".join(QEMU_ARGS))
    if argv[:1] == ["--check"]:
        current = parse(FIXTURE.read_text())
        if current != blob:
            print(f"[FAIL] {FIXTURE.relative_to(REPO)} is not the device tree "
                  f"{qemu_version(qemu)} dumps for {' '.join(QEMU_ARGS)}; regenerate it")
            return 1
        print(f"[PASS] {FIXTURE.relative_to(REPO)} is {qemu_version(qemu)}'s `virt` device tree")
        return 0
    FIXTURE.write_text(rendered)
    print(f"wrote {FIXTURE.relative_to(REPO)} ({len(blob)} bytes)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
