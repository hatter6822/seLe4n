#!/usr/bin/env python3
"""Self-test for the internal-first naming gate.

`check_identifier_naming.py` has shipped under-enforced five times, and
every cause was the same shape: some part of its *scope* was written out
by hand and was narrower than the rule it enforces.  A gate whose failure
mode is silence needs its own regression witnesses, so each mechanism
below is pinned by a check that provably fails against the version that
lacked it.

Each check is load-bearing: run against the pre-fix checker, every one
of them reports the wrong answer.  A test that passes against both the
broken and the fixed code documents nothing.

Run directly (`python3 scripts/test_identifier_naming_gate.py`) or as
part of Tier 0 hygiene.
"""
from __future__ import annotations

import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import check_identifier_naming as gate  # noqa: E402

# Built by concatenation throughout: these are plain (non-f) literals, so
# the gate blanks them when it scans this file, exactly as it blanks any
# other prose.  A test for a naming rule must not trip the naming rule.
CODED = "phase5" + "_helper"

failures: list[str] = []
performed = 0


def check(label: str, got: object, want: object) -> None:
    global performed
    performed += 1
    if got != want:
        failures.append(f"{label}: got {got!r}, want {want!r}")


# --- Documentation is exempt by LOCATION, never by suffix -------------
# Scoping the exemption by suffix let `scripts/<coded>.json` and
# `tests/<coded>.expected` skip even *path* scanning, because a suffix
# says nothing about whether a file is prose.
check("json under scripts is in scope",
      gate.is_doc("scripts/" + CODED + ".json"), False)
check("expected fixture is in scope",
      gate.is_doc("tests/" + CODED + ".expected"), False)
check("checksum file is in scope", gate.is_doc("tests/f.sha256"), False)
check("txt outside docs is in scope", gate.is_doc("scripts/manifest.txt"), False)
# ...but the documents that exist to carry prose stay exempt.  Audit
# reports are *named after* the workstream they record.
check("docs/ tree is exempt",
      gate.is_doc("docs/audits/WS_RC_R4_CLOSEOUT_PLAN.md"), True)
check("root README is exempt", gate.is_doc("README.md"), True)
check("root CHANGELOG is exempt", gate.is_doc("CHANGELOG.md"), True)
check("stray root doc is in scope", gate.is_doc("NOTES_WS_SM.md"), False)


# --- The baseline counts occurrences per (identifier, file) -----------
# A net total passes a patch that retires one grandfathered name and adds
# a different one.  A *set* of pairs additionally cannot see a second use
# of a name the file already contains.  Counts close both.
def risen(base: Counter, cur: Counter) -> list:
    return sorted(k for k in cur if cur[k] > base.get(k, 0))


one = Counter({("ak9ce", "a.lean"): 1})
check("a second use in the same file is caught",
      risen(one, Counter({("ak9ce", "a.lean"): 2})), [("ak9ce", "a.lean")])
check("an unchanged count passes",
      risen(one, Counter({("ak9ce", "a.lean"): 1})), [])
check("a falling count passes",
      risen(one, Counter({("ak9ce", "a.lean"): 0})), [])
check("the same name in a new file is caught",
      risen(one, one + Counter({("ak9ce", "b.lean"): 1})), [("ak9ce", "b.lean")])


# --- Interpolation is code, in every language that has it -------------
q, dq = chr(39), chr(34)
check("Lean interpolation is kept",
      CODED in gate.strip_lean("s!" + dq + "{" + CODED + "}" + dq), True)
check("a plain Lean literal is blanked",
      CODED in gate.strip_lean(dq + CODED + dq), False)
check("Rust inline format args are kept",
      CODED in gate.strip_rust("println!(" + dq + "{" + CODED + "}" + dq + ")"), True)
check("a brace escape is not interpolation",
      CODED in gate.strip_rust(dq + "{{" + CODED + "}}" + dq), False)

# Python needs the `f` prefix checked first.  Without it, `'{x}'` is a
# literal brace; preserving those would start scanning docstring prose
# and break the exemption this file itself depends on.
check("a Python f-string is kept",
      CODED in gate.strip_hash("x = f" + q + "{" + CODED + "}" + q), True)
check("a plain Python literal is blanked",
      CODED in gate.strip_hash("x = " + q + "{" + CODED + "}" + q), False)
check("a triple-quoted f-string is kept",
      CODED in gate.strip_hash("x = f" + q * 3 + "{" + CODED + "}" + q * 3), True)
check("a docstring is blanked",
      CODED in gate.strip_hash(q * 3 + "{" + CODED + "}" + q * 3), False)
check("rb is not an f-string prefix",
      CODED in gate.strip_hash("x = rb" + q + "{" + CODED + "}" + q), False)
check("a comment is blanked", CODED in gate.strip_hash("# " + CODED), False)


# --- Shell is not Python, and its two quote kinds differ --------------
# Sharing the Python stripper blanked quoted shell as prose, so an
# identifier used only inside double quotes was invisible.
dollar = chr(36)
check("a shell ${} expansion is kept",
      CODED in gate.strip_shell("echo " + dq + dollar + "{" + CODED + "}" + dq), True)
check("a shell $name expansion is kept",
      CODED in gate.strip_shell("echo " + dq + dollar + CODED + dq), True)
check("double-quoted message text is prose",
      CODED in gate.strip_shell("echo " + dq + "AN7-A: " + CODED + dq), False)
# Single quotes carry executable payloads (`bash -lc '...'`), so their
# contents stay in scope; blanking them hid 280 occurrences.
check("a single-quoted payload is code",
      CODED in gate.strip_shell("bash -lc " + q + "def " + CODED + q), True)
check("a shell comment is blanked",
      CODED in gate.strip_shell("# " + CODED), False)
check("a word-internal hash is not a comment",
      CODED in gate.strip_shell("echo abc#" + CODED), True)
check("a length expansion is not a comment",
      CODED in gate.strip_shell("echo " + dollar + "{#" + CODED + "}"), True)


# --- Discovery is NUL-delimited ---------------------------------------
# Splitting `git ls-files` on whitespace turns a path containing a space
# into fragments naming no file, and the failed read is swallowed.
check("tracked paths are enumerated", len(gate.tracked_all()) > 100, True)
check("no path fragment survives splitting",
      all(" " not in p or (gate.REPO_ROOT / p).exists() for p in gate.tracked_all()), True)


# --- The baseline is not scanned as code ------------------------------
# It necessarily spells out every grandfathered name, so scanning it
# reports its own contents and each regeneration re-adds them.
check("the baseline exempts itself",
      gate.is_doc("scripts/identifier_naming_baseline.json"), True)


# --- Every maintained format has a stripper ---------------------------
# A format absent from the table still has its path scanned, so adding
# one is a strengthening; but its *contents* go unread until it is here.
for suffix in (".rs", ".lean", ".py", ".sh", ".bash", ".S", ".ld",
               ".toml", ".yml", ".yaml", ".json", ".expected"):
    check(f"{suffix} contents are scanned", suffix in gate.CONTENT_STRIPPERS, True)
# Shell must not share Python's stripper -- that is the exact mistake.
check("shell has its own stripper",
      gate.CONTENT_STRIPPERS[".sh"] is not gate.CONTENT_STRIPPERS[".py"], True)

# Comment syntax differs by format, and guessing wrong blanks real code.
check("a linker script has no // comment",
      CODED in gate.strip_block_only("KEEP // " + CODED), True)
check("assembly does have // comments",
      CODED in gate.strip_asm("nop // " + CODED), False)
check("a cpp directive is code, not a comment",
      CODED in gate.strip_asm("#define " + CODED + " 1"), True)


# --- The code grammar -------------------------------------------------
check("a lone ws is left alone", gate.is_coded("ws"), False)
# Recognising only sm/an/ak let eleven further real families through.
# The list is checked against docs/WORKSTREAM_HISTORY.md, so a family
# retired from the registry must be retired here too.
for family in ("aa", "ac", "ad", "ae", "af", "ag", "ah",
               "ai", "aj", "ak", "al", "am", "an", "sm"):
    check(f"{family} family recognised", gate.is_coded(family + "2_helper"), True)
# `r<n>` phase codes are deliberately absent: as an identifier rule they
# match ARM registers and Lean proof hypotheses far more often than
# workstream codes.  Pinned so a future round does not "fix" it.
check("r-phase deliberately not a family", gate.is_coded("r8_hardening"), False)
check("an ARM register survives", gate.is_coded("r0"), False)
check("a proof hypothesis survives", gate.is_coded("hR1"), False)
# Generalising the families is what these guard against.
check("RPi5 is not a code", gate.is_coded("RPi5"), False)
check("ARMv8VSpace is not a code", gate.is_coded("ARMv8VSpace"), False)
check("the project name is not a code", gate.is_coded("SeLe4n"), False)
check("a compound ws is flagged", gate.is_coded("ws" + "_sm_helper"), True)
check("camelCase is normalised", gate.is_coded("ws" + "SmHelper"), True)
check("SHOUTING_CASE is normalised", gate.is_coded("SM5I" + "_ANCHORS"), True)
check("a phase code is flagged", gate.is_coded("phase5"), True)
check("an ordinary name passes", gate.is_coded("shootdownRoundLock"), False)
check("a digit-bearing ordinary name passes", gate.is_coded("armv8Sequence"), False)


def main() -> int:
    if failures:
        print("FAIL: the naming gate lost a mechanism it is supposed to have:",
              file=sys.stderr)
        for f in failures:
            print("  " + f, file=sys.stderr)
        return 1
    print(f"PASS: naming gate self-test ({performed} checks).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
