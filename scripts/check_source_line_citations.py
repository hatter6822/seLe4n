#!/usr/bin/env python3
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# check_source_line_citations.py — forbid `File.ext:NNN` citations in prose.
#
# WHY THIS GATE EXISTS
#
# A citation of the form `SeLe4n/Platform/Boot.lean:551` is stale the moment
# anything above line 551 changes, which in this tree is roughly every PR.
# An audit of the active documentation found 511 such citations; of the ones
# that could be checked mechanically, 178 pointed at a line that no longer
# had anything to do with the surrounding prose (`Endpoint.lean:723` resolved
# to a bare `| ok p3 =>`), 3 pointed past end-of-file, and 66 named a file so
# ambiguously (`Policy.lean:484`) that the path did not even resolve. The 107
# that were still accurate were one edit away from joining them.
#
# The durable fix is not to renumber them — that just restarts the clock —
# but to stop citing line numbers at all. A file path plus a symbol name is
# stable under edits and is what a reader actually needs.
#
# SCOPE
#
#   * Active documentation only: docs/ (excluding docs/dev_history/, which is
#     archival by policy), plus CLAUDE.md / AGENTS.md / README.md.
#   * CHANGELOG.md is exempt: it is an append-only historical record whose
#     entries quote verbatim compiler diagnostics (`foo.lean:1:0: error ...`)
#     and, since v0.32.108, discuss this very pattern by quoting it.
#   * Fenced code blocks are exempt: they hold verbatim tool output and
#     command transcripts, where a line number is data, not a citation.
#
# Exit codes:
#   0  no prose line-number citations found
#   1  at least one found (message names file, line, and the offending text)

import re
import subprocess
import sys

CITATION = re.compile(
    r'(?:[A-Za-z0-9_][A-Za-z0-9_./-]*)\.(?:rs|lean|sh|py|toml|S):\d+'
)


def target_files() -> list[str]:
    listing = subprocess.run(
        ['bash', '-c',
         "find docs -name '*.md' -not -path 'docs/dev_history/*'; "
         "ls CLAUDE.md AGENTS.md README.md"],
        capture_output=True, text=True, check=True).stdout.split()
    return sorted(set(listing))


def main() -> int:
    files = target_files()
    if not files:
        print('FAIL: no documentation files matched; the check would be vacuous.',
              file=sys.stderr)
        return 1

    findings = []
    for path in files:
        in_fence = False
        with open(path, encoding='utf-8', errors='replace') as handle:
            for lineno, line in enumerate(handle, 1):
                if line.lstrip().startswith('```'):
                    in_fence = not in_fence
                    continue
                if in_fence:
                    continue
                match = CITATION.search(line)
                if match:
                    findings.append((path, lineno, match.group(0), line.strip()))

    if findings:
        print('FAIL: source citations with line numbers found in prose.',
              file=sys.stderr)
        print('      Line numbers go stale on the next edit above them; cite the'
              ' file and a symbol instead.', file=sys.stderr)
        for path, lineno, cite, text in findings[:25]:
            print(f'  {path}:{lineno}: {cite}', file=sys.stderr)
            print(f'      {text[:100]}', file=sys.stderr)
        if len(findings) > 25:
            print(f'  ... and {len(findings) - 25} more', file=sys.stderr)
        return 1

    print(f'PASS: no prose line-number citations across {len(files)} '
          'documentation files.')
    return 0


if __name__ == '__main__':
    sys.exit(main())
