#!/usr/bin/env python3
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
"""A Markdown document with its fenced code blanked: the one fence reader.

Three scripts read Markdown structure -- headings and table rows -- and each
must not read an example inside a fence as the real thing:
`check_workstream_plan.py` (sub-task rows and prose counts),
`check_workstream_id_resolution.py` (what a plan defines) and
`generate_agents_md.py` (`CLAUDE.md`'s sections).  Each used to carry its own
fence handling, and each got a different part of it wrong: a column-0 backtick
toggle, a regex that took a line opening with inline code for an opener, and
neither knew tilde fences, indented fences or a longer closer.  They now ask
this module, so the question has one answer.

    python3 scripts/markdown_prose_view.py --self-test
"""
from __future__ import annotations

import re
import sys


# Fenced code as CommonMark reads it (spec 4.5).  An opener is a run of three
# or more backticks or tildes, indented at most three columns past its
# container; a backtick opener's info string may not hold a backtick, so a prose
# line that merely opens with inline code (``` `toList = []` ```) opens nothing.
# (Read as an opener, that line paired every later fence one off and blanked
# 14,055 lines of `CHANGELOG.md`.)  A closer is a run of the opener's character
# at least as long, indented at most three columns past the container, with
# nothing after it but spaces or tabs; any other run inside the block is
# content.  A fence nobody closes runs to the end of its container: the
# document, or the list item it opened in, which ends at the first non-blank
# line indented less than the item's content (fenced code takes no lazy
# continuation).  A lazy paragraph line is read as ending its item too early,
# which only reads a later fence at the document's column and so blanks more,
# never less.  Block quotes are not tracked: their lines open with `>`, so
# nothing in one reads as a heading or a row either way.
FENCE_RUN = re.compile(r"^( *)(`{3,}|~{3,})(.*)$")
LIST_MARKER = re.compile(r"^( *)([-+*]|\d{1,9}[.)])( *)(.?)")
THEMATIC_BREAK = re.compile(r"^ {0,3}([-*_])(?:[ \t]*\1){2,}[ \t]*$")


def _opens_fence(line: str, column: int) -> tuple[str, int] | None:
    """`(char, length)` when `line` opens a fence in a container at `column`."""
    run = FENCE_RUN.match(line)
    if not run or len(run.group(1)) - column > 3:
        return None
    char = run.group(2)[0]
    if char == "`" and "`" in run.group(3):
        return None
    return char, len(run.group(2))


def _item_content_column(line: str) -> int | None:
    """Where a list item's content starts, when `line` opens one."""
    marker = LIST_MARKER.match(line)
    if not marker or THEMATIC_BREAK.match(line):
        return None
    indent, mark, gap, first = (len(marker.group(1)), marker.group(2),
                                len(marker.group(3)), marker.group(4))
    if first and not gap:
        return None                      # `-x`, `1.5`: not a marker
    if not first or gap > 4:
        gap = 1                          # an empty item, or indented code after it
    return indent + len(mark) + gap


def prose_view(text: str) -> str:
    """The document with fenced blocks blanked out, line count preserved.

    A plan illustrating a row shape or citing an example ID inside a fence is
    showing the reader what one looks like, not declaring one.  Parsing those
    as data made the gate fail legitimate documents — a phantom phase from a
    fenced table, a dangling citation from an example ID — which is the mirror
    of a bypass: it pushes authors to contort prose to satisfy the scanner,
    which this project forbids in as many words.  Lines are replaced rather
    than removed so any position the caller reports still lines up.
    """
    lines = text.split("\n")
    out = list(lines)
    items: list[int] = []            # content columns of the open list items
    fence: tuple[str, int, int] | None = None   # (char, length, container column)
    for i, raw in enumerate(lines):
        line = raw.rstrip("\r").expandtabs(4)
        indent = len(line) - len(line.lstrip(" "))
        blank = not line.strip()
        if fence is not None:
            char, length, column = fence
            if blank or indent >= column:
                out[i] = ""
                run = FENCE_RUN.match(line)
                if (run and indent - column <= 3 and run.group(2)[0] == char
                        and len(run.group(2)) >= length and not run.group(3).strip()):
                    fence = None
                continue
            fence = None                 # its list item ended, and the fence with it
        if blank:
            continue
        while items and indent < items[-1]:
            items.pop()
        column = items[-1] if items else 0
        opened = _opens_fence(line, column)
        if opened:
            fence, out[i] = (*opened, column), ""
            continue
        content = _item_content_column(line)
        if content is not None and indent - column <= 3:
            items.append(content)
            opened = _opens_fence(" " * content + line[content:], content)
            if opened:
                fence, out[i] = (*opened, content), ""
    return "\n".join(out)


def _self_test() -> int:
    """Each CommonMark fence rule, read straight off the view."""
    cases = [
        ("an opener indented three columns hides column-0 lines to its closer",
         "   ```\n## XX9\n| XX9.1 | a |\n   ```\nafter\n", ["after"]),
        ("a tilde run opens a fence", "~~~\n## XX9\n| XX9.1 | a |\n~~~\nafter\n", ["after"]),
        ("a backtick run does not close a tilde fence",
         "~~~\n```\n## XX9\n| XX9.1 | a |\n~~~\nafter\n", ["after"]),
        ("a shorter run does not close a fence and a longer one does",
         "````\n```\n## XX9\n| XX9.1 | a |\n`````\nafter\n", ["after"]),
        ("a run carrying an info string does not close a fence",
         "```\n```lean\n## XX9\n```\nafter\n", ["after"]),
        ("a closer indented three columns closes", "```\n## XX9\n   ```\n## XX8\n", ["## XX8"]),
        ("a run indented four columns opens nothing", "    ```\n## XX9\n", ["    ```", "## XX9"]),
        ("an unclosed fence runs to the end of the document",
         "```\n## XX9\n| XX9.1 | a |\n", []),
        ("a fence opened in a list item ends with the item",
         "1. step\n\n   ```\n   code\n## XX9\n", ["1. step", "## XX9"]),
        ("a line opening with inline code opens nothing",
         "``` `x` ``` opens this sentence.\n## XX9\n```\nfenced\n```\n",
         ["``` `x` ``` opens this sentence.", "## XX9"]),
        ("a tilde opener may carry a backtick in its info string",
         "~~~ `x`\n## XX9\n~~~\nafter\n", ["after"]),
        ("a fence opened on a list item's own line ends with the item",
         "- ```\n  code\n## XX9\n", ["## XX9"]),
    ]
    failed = 0
    for name, doc, standing in cases:
        view = prose_view(doc)
        got = [line for line in view.split("\n") if line.strip()]
        ok = got == standing and view.count("\n") == doc.count("\n")
        failed += not ok
        print(f"  {'PASS' if ok else 'FAIL'}: {name}" + ("" if ok else f" -- got {got}"))
    if failed:
        print(f"SELF-TEST FAILED: {failed} case(s)")
        return 1
    print(f"markdown_prose_view self-test: {len(cases)} cases, all correct.")
    return 0


if __name__ == "__main__":
    if sys.argv[1:] != ["--self-test"]:
        print(f"usage: {sys.argv[0]} --self-test", file=sys.stderr)
        sys.exit(2)
    sys.exit(_self_test())
