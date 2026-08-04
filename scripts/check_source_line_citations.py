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

# Extensions a citation may carry are DERIVED from the tree, not hard-coded.
# The original list (`rs|lean|sh|py|toml|S`) silently omitted formats the
# repository actually contains — `.yml`, `.yaml`, `.ld`, `.json` — so a
# citation like `.github/workflows/lean_action_ci.yml:213` sailed past the gate
# and went stale exactly like the ones it was written to catch. A hard-coded
# list has to be remembered every time a format is introduced; derivation
# cannot fall behind.
#
# The filter keeps extensions that start with a letter and are at most eight
# characters, which excludes numeric suffixes (a `foo.1` man page would put
# `1` in the set, and `v0.32.1:5` would then read as a citation).
EXTENSION_RE = re.compile(r'\.([A-Za-z][A-Za-z0-9]{0,7})$')

# A Markdown fenced-code delimiter: three or more backticks or tildes, with
# whatever info string follows. Leading whitespace is accepted at any depth
# rather than CommonMark's 0-3 columns, because fences nested in list items are
# indented past that in this repo's docs and treating them as prose would be a
# regression; the delimiter *character* and *run length* are matched strictly,
# which is what the exemption actually turns on.
FENCE_RE = re.compile(r'^\s*(?P<delim>`{3,}|~{3,})(?P<info>.*?)\s*$')

# Extensions that must always be covered regardless of what the tree happens to
# hold today. If derivation breaks or a format disappears, the gate fails loudly
# instead of quietly narrowing its own scope — the failure mode this check
# exists to prevent, applied to the check itself.
REQUIRED_EXTENSIONS = frozenset(
    {'rs', 'lean', 'sh', 'py', 'toml', 'S', 'yml', 'yaml', 'ld', 'json'}
)


def cited_extensions() -> set[str]:
    tracked = subprocess.run(
        ['git', 'ls-files'], capture_output=True, text=True, check=True
    ).stdout.split()
    found = set()
    for path in tracked:
        match = EXTENSION_RE.search(path)
        if match:
            found.add(match.group(1))
    return found


def build_citation_re(extensions: set[str]) -> re.Pattern[str]:
    # Longest-first so the alternation cannot match a proper prefix of a longer
    # extension (`.sh` inside `.sha256`).
    alternation = '|'.join(
        re.escape(e) for e in sorted(extensions, key=lambda e: (-len(e), e))
    )
    return re.compile(
        r'(?:[A-Za-z0-9_][A-Za-z0-9_./-]*)\.(?:' + alternation + r'):\d+'
    )


# The same citation spelled as prose. `File.ext:NNN` is only the compact
# form; `at line 471`, `at lines 3711-3712` and `on line 92` go stale for
# exactly the same reason and were invisible to a gate whose PASS line
# claims there are no prose line-number citations at all. The verb set is
# the one that actually introduces a location in this repo's docs; a bare
# "line 12" is left alone because it also means a line of output, a line
# of a table, or a line in a quoted block.
# Two spellings, both stale-able and both previously invisible:
#   `at line 471`, `from lines 113-125`   — verb-introduced
#   `(line 530 ...)`, `lines 603/607`     — bare, usually parenthetical
# A two-digit floor keeps "line 5 of the table" and similar out; a
# citation into a real source file is essentially never single-digit
# here, and the fenced-block exemption already covers code samples such
# as CLAUDE.md's `# lines 501-1000` pagination example.
TEXTUAL_CITATION_RE = re.compile(
    r'\b(?:at|on|around|near|from)\s+lines?\s+\d+'
    r'|~?\blines?\s+\d{2,}',
    re.IGNORECASE
)

# The ORPHANED half of a citation pair, e.g. `` (`API.lean`, `:303`) `` or
# `` (`Defs.lean` / :237) ``.
#
# These exist because the v0.32.109 sweep that removed 511 citations
# rewrote `File.ext:NNN` and stopped there: where a sentence cited two
# lines of one file, the second was written as a bare `:NNN` that the
# filename pattern never matched. So the sweep stripped the anchor and
# left the number -- a citation strictly worse than the one it replaced,
# since it is both stale AND no longer says what file it indexes. The
# gate reported PASS over its own wreckage for twelve versions.
#
# A cleanup that can leave the tree in a state its own gate cannot see
# is the actual defect here; matching the residue is what makes the
# sweep's completion checkable rather than assumed.
#
# Deliberately narrow, since a colon before digits is common: the colon
# must open a token (preceded by a backtick, space, `(`, `,`, `/` or
# `~`) and be followed immediately by two or more digits. That excludes
# `12:30`, `3:2`, `host:8080` and `**Note**: 42` (space after the
# colon), while catching every orphan spelling the sweep produced.
ORPHAN_CITATION_RE = re.compile(r'(?:(?<=[\s`(,/~])|^):\d{2,}\b')


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

    extensions = cited_extensions()
    missing = REQUIRED_EXTENSIONS - extensions
    if missing:
        print('FAIL: extension derivation lost formats this gate must cover: '
              + ', '.join(sorted(missing)), file=sys.stderr)
        print('      Either the repository no longer contains them (drop them '
              'from REQUIRED_EXTENSIONS) or the derivation is broken.',
              file=sys.stderr)
        return 1
    citation_re = build_citation_re(extensions)

    findings = []
    for path in files:
        # The open fence as (delimiter char, run length), or None outside a
        # fenced block.  Tracking both is what makes the exemption match
        # CommonMark rather than approximate it: a `~~~` block is a valid
        # fence, and a closing fence must use the *same* character and be at
        # least as long as the opener — so a ``` run inside a ```` block is
        # content, not a close.  A bare toggle on '```' got both wrong,
        # silently subjecting real transcripts to the prose rule.
        fence = None
        with open(path, encoding='utf-8', errors='replace') as handle:
            for lineno, line in enumerate(handle, 1):
                marker = FENCE_RE.match(line)
                if marker:
                    delim = marker.group('delim')
                    char, length, info = delim[0], len(delim), marker.group('info')
                    if fence is None:
                        # A backtick opener may not carry a backtick in its
                        # info string (CommonMark 4.5); a tilde opener may.
                        if not (char == '`' and '`' in info):
                            fence = (char, length)
                            continue
                    elif char == fence[0] and length >= fence[1] and not info.strip():
                        fence = None
                        continue
                    # Not a valid open or close: fall through and treat the
                    # line as ordinary content.
                if fence is not None:
                    continue
                match = (citation_re.search(line)
                         or TEXTUAL_CITATION_RE.search(line)
                         or ORPHAN_CITATION_RE.search(line))
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
