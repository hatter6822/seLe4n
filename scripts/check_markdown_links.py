#!/usr/bin/env python3
from __future__ import annotations

import re
import subprocess
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
LINK_RE = re.compile(r"\[[^\]]+\]\(([^)]+)\)")
SKIP_PREFIXES = ("http://", "https://", "mailto:", "tel:")


SKIP_DIRS = ("docs/dev_history/",)


def tracked_markdown_files() -> list[Path]:
    result = subprocess.run(
        ["git", "ls-files", "*.md"],
        cwd=REPO_ROOT,
        check=True,
        text=True,
        capture_output=True,
    )
    return [
        REPO_ROOT / line
        for line in result.stdout.splitlines()
        if line.strip() and not line.startswith(SKIP_DIRS)
    ]


def normalize_target(raw: str) -> str:
    target = raw.strip()
    if target.startswith("<") and target.endswith(">"):
        target = target[1:-1].strip()
    return target


def validate_links(markdown_file: Path) -> list[str]:
    errors: list[str] = []
    text = markdown_file.read_text(encoding="utf-8")
    for lineno, line in enumerate(text.splitlines(), start=1):
        for match in LINK_RE.finditer(line):
            target = normalize_target(match.group(1))
            if not target or target.startswith(SKIP_PREFIXES):
                continue
            if target.startswith("#"):
                continue
            target_path = target.split("#", maxsplit=1)[0].split("?", maxsplit=1)[0]
            if not target_path:
                continue
            resolved = (markdown_file.parent / target_path).resolve()
            try:
                resolved.relative_to(REPO_ROOT)
            except ValueError:
                errors.append(f"{markdown_file.relative_to(REPO_ROOT)}:{lineno}: outside-repo link target '{target}'")
                continue
            if not resolved.exists():
                errors.append(f"{markdown_file.relative_to(REPO_ROOT)}:{lineno}: missing link target '{target}'")
    return errors


def main() -> int:
    errors: list[str] = []
    for markdown_file in tracked_markdown_files():
        errors.extend(validate_links(markdown_file))

    if errors:
        for error in errors:
            print(error)
        print(f"markdown link check failed ({len(errors)} error(s))")
        return 1

    print("markdown link check passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
