#!/usr/bin/env python3
"""Generate canonical current-state metrics for README/docs sync."""
from __future__ import annotations

from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def line_count(path: Path) -> int:
    with path.open("r", encoding="utf-8") as f:
        return sum(1 for _ in f)


def count_theorem_like(files: list[Path]) -> int:
    pattern = re.compile(r"^\s*(?:@[\w\[\]\.\s]+\s+)?(?:private\s+)?(?:theorem|lemma)\s+")
    total = 0
    for path in files:
        for line in path.read_text(encoding="utf-8").splitlines():
            if pattern.match(line):
                total += 1
    return total


def read_first(path: Path) -> str:
    return path.read_text(encoding="utf-8").splitlines()[0].strip()


prod_files = sorted((ROOT / "SeLe4n").rglob("*.lean")) + [ROOT / "Main.lean"]
test_files = sorted((ROOT / "tests").rglob("*.lean"))

prod_loc = sum(line_count(p) for p in prod_files)
test_loc = sum(line_count(p) for p in test_files)
proved = count_theorem_like(prod_files)

version = "unknown"
for line in (ROOT / "lakefile.toml").read_text(encoding="utf-8").splitlines():
    if line.strip().startswith("version"):
        version = line.split("=", 1)[1].strip().strip('"')
        break

lean_toolchain = read_first(ROOT / "lean-toolchain").split(":")[-1]

build_jobs = "unknown"
try:
    out = subprocess.run(
        ["bash", "-lc", "source ~/.elan/env && lake build 2>/dev/null | tail -1"],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=False,
    ).stdout.strip()
    m = re.search(r"\((\d+) jobs\)", out)
    if m:
        build_jobs = m.group(1)
except Exception:
    pass

print(f"version={version}")
print(f"lean_toolchain={lean_toolchain}")
print(f"production_files={len(prod_files)}")
print(f"production_loc={prod_loc}")
print(f"test_files={len(test_files)}")
print(f"test_loc={test_loc}")
print(f"proved_theorem_lemma_decls={proved}")
print(f"build_jobs={build_jobs}")
