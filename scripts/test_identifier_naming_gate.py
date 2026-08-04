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
# ...and a DOUBLE-quoted payload handed to an interpreter is code for
# the same reason the single-quoted one is.  The tree writes it both
# ways -- single-quoted in `test_tier0_hygiene.sh`, double-quoted in
# the Tier-2/3/4 scripts -- and which quote the author reached for
# follows what the payload contains, not whether it is code.
check("a double-quoted bash -lc payload is code",
      CODED in gate.strip_shell("bash -lc " + dq + "def " + CODED + dq), True)
check("a double-quoted sh -c payload is code",
      CODED in gate.strip_shell("sh -c " + dq + CODED + dq), True)
check("an eval payload is code",
      CODED in gate.strip_shell("eval " + dq + CODED + dq), True)
# The exemption that keeps the gate usable: only the payload changes
# treatment, not every double-quoted span on the line.
check("a label beside a payload stays prose",
      CODED in gate.strip_shell(
          "run_check " + dq + CODED + dq + " bash -lc " + dq + "true" + dq),
      False)
check("an echoed diagnostic stays prose",
      CODED in gate.strip_shell("echo " + dq + CODED + " done" + dq), False)


# --- Config and data formats are not Python prose ---------------------
# A YAML `run:` is a command and a TOML value is often a package or
# target name; the Python stripper blanked both as quoted prose.
check("a YAML quoted scalar is code",
      CODED in gate.strip_config("  run: " + dq + CODED + dq), True)
check("a TOML value is code",
      CODED in gate.strip_config("name = " + dq + CODED + dq), True)
check("a config comment is blanked",
      CODED in gate.strip_config("# " + CODED), False)
check("a hash inside a value is not a comment",
      CODED in gate.strip_config("url = " + dq + "a#" + CODED + dq), True)
check("config does not share Python's stripper",
      gate.CONTENT_STRIPPERS[".yml"] is not gate.CONTENT_STRIPPERS[".py"], True)
# Both formats start a `#` comment only OUTSIDE a quoted scalar.  The
# preceding check covers `a#b` (no space); with a space in front, the
# `#` was read as a comment and the rest of the command blanked -- and
# the tree already holds the shape (`description: "... #1 sender: 1"`).
check("a spaced hash inside a quoted scalar is not a comment",
      CODED in gate.strip_config("run: " + dq + "echo # " + CODED + dq), True)
check("a spaced hash inside a TOML string is not a comment",
      CODED in gate.strip_config("name = " + dq + "foo # " + CODED + dq), True)
check("a single-quoted scalar is covered too",
      CODED in gate.strip_config("cmd: " + q + "run # " + CODED + q), True)
# The three exemptions that keep quote-tracking from over-keeping.  All
# three over-KEEP when wrong, which turns prose into false positives.
check("a real trailing comment is still blanked",
      CODED in gate.strip_config("key: value   # " + CODED), False)
# Both inputs below carry a SECOND quote after the `#` on purpose.
# Without it a naive scan finds no pair, falls through, and blanks the
# comment anyway -- so the weaker spelling of these checks passes
# against the very implementation it exists to reject.  Same failure as
# the round-24 check that started passing for the wrong reason.
check("an apostrophe does not pair across the comment after it",
      CODED in gate.strip_config(
          "note: don" + q + "t  # it" + q + "s " + CODED), False)
check("a quote closing on a later line does not swallow the comment",
      CODED in gate.strip_config(
          "a: " + dq + "open\nb: ok  # " + CODED + "\nc: " + dq + "end" + dq),
      False)
# The quote tracking above must honour each format's ESCAPES.  Taking
# the first matching character ends the scalar early, and the `#` then
# reverts to opening a comment inside a value that has not closed --
# the narrower under-reach that v0.32.137's fix for the wider one
# opened.  The two kinds escape differently and both are exercised.
check("a backslash-escaped quote does not end the scalar",
      CODED in gate.strip_config(
          "run: " + dq + "echo \\" + dq + "label # " + CODED + "\\" + dq + dq),
      True)
check("a TOML basic string escapes the same way",
      CODED in gate.strip_config(
          "name = " + dq + "a \\" + dq + "b # " + CODED + "\\" + dq + dq),
      True)
check("a YAML doubled quote is a literal, not a terminator",
      CODED in gate.strip_config("cmd: " + q + "it" + q + q + "s # " + CODED + q),
      True)


# --- A hyphen separates words in a FILE NAME --------------------------
# `WS-SM_helpers.py` splits into `WS` + `SM_helpers`, and the lone `WS`
# is ignored by the bare-token rule -- so the carve-out that keeps `ws`
# usable as a word opened a hole in the canonical `WS-*` spelling.
# Calls the gate's own tokenizer, not a copy of it: a duplicate here
# passed against the version that lacked the fix, which is exactly the
# kind of vacuous check this file exists to avoid.
def path_is_coded(rel: str) -> bool:
    return any(gate.is_coded(t) for t in gate.path_tokens(rel))


check("a hyphenated workstream path is caught",
      path_is_coded("scripts/WS" + "-SM_helpers.py"), True)
check("an ordinary hyphenated path passes",
      path_is_coded("rust/rust-toolchain.toml"), False)
check("a hyphen is not normalised in CONTENTS",   # there it is subtraction
      CODED in gate.strip_lean("a - b"), False)


# --- Discovery is NUL-delimited ---------------------------------------
# Splitting `git ls-files` on whitespace turns a path containing a space
# into fragments naming no file, and the failed read is swallowed.
check("tracked paths are enumerated", len(gate.tracked_all()) > 100, True)
check("no path fragment survives splitting",
      all(" " not in p or (gate.REPO_ROOT / p).exists() for p in gate.tracked_all()), True)


# --- Contents come from the INDEX, not the working tree ---------------
# `git ls-files` enumerates the index, so reading the working tree
# checks a state that is not the one being committed: a coded identifier
# could be staged and then deleted from the unstaged copy.
check("staged contents are readable",
      len(gate.index_contents(["scripts/check_identifier_naming.py"])), 1)
check("the index read returns real content",
      "COMPONENT_CODES" in gate.index_contents(
          ["scripts/check_identifier_naming.py"])
      .get("scripts/check_identifier_naming.py", ""), True)
check("a missing index entry is skipped, not fatal",
      gate.index_contents(["no/such/file.py"]), {})


# --- The baseline is not scanned as code ------------------------------
# It necessarily spells out every grandfathered name, so scanning it
# reports its own contents and each regeneration re-adds them.
check("the baseline exempts itself",
      gate.is_doc("scripts/identifier_naming_baseline.json"), True)


# --- Every maintained format has a stripper ---------------------------
# A format absent from the table still has its path scanned, so adding
# one is a strengthening; but its *contents* go unread until it is here.
for suffix in (".rs", ".lean", ".py", ".sh", ".bash", ".S", ".ld",
               ".toml", ".yml", ".yaml", ".json", ".expected", ".sha256"):
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

# Audit IDs.  The rule names them alongside workstream IDs, and no
# single component of `AUDIT_v0.30.11` is coded -- the shape is the
# adjacency, so these pin the pair rule and its non-firing neighbours.
check("an audit id is flagged", gate.is_coded("audit_v0" + "_30_11_helper"), True)
check("a bare version stamp is flagged", gate.is_coded("v0" + "_30_11"), True)
check("an audit log is not a code", gate.is_coded("auditLog"), False)
check("a versioned name without a number passes",
      gate.is_coded("sha256_v2_digest"), False)
check("an architecture version passes", gate.is_coded("armv8_1_features"), False)

# The canonical audit filename is DOTTED, and `IDENTIFIER` needs a
# leading letter, so without stem normalisation `30` and `11` never
# become tokens and the shape above is unreachable from a path.
check("a dotted audit path is tokenised whole",
      "audit_v0" + "_30_11_probe" in gate.path_tokens(
          "scripts/audit_v0" + ".30.11_probe.sh"), True)
check("a dotted audit path is flagged",
      any(gate.is_coded(t)
          for t in gate.path_tokens("scripts/audit_v0" + ".30.11_probe.sh")), True)
check("an ordinary suffix stays its own token",
      gate.path_tokens("SeLe4n/Model/State.lean"),
      ["SeLe4n", "Model", "State", "lean"])

# Backticks are executable in the same places `$(...)` is, including
# inside double quotes, where the span is otherwise blanked as message
# text.  The bare form already survived; these pin that both do.
_bt = gate.strip_shell('a="`' + 'phase5_helper' + '`"\nb=`' + 'ak9ce_01_run' + '`\n')
check("a quoted backtick command survives", "phase5_helper" in _bt, True)
check("a bare backtick command survives", "ak9ce_01_run" in _bt, True)

# The baseline is compared against the INDEX, like the sources it
# excuses; a working-tree read would let a regenerated baseline pardon
# a violation the index still carries.
# Single-letter families.  `z` is real and enforced; `x` and `d` are
# real in the registry but rejected as identifier rules because they
# collide with AArch64 register names and the DTB magic.  Pinning the
# rejections keeps a later round from adding them without re-measuring.
check("the z family is recognised", gate.is_coded("z10_helper"), True)
check("a z phase code is recognised", gate.is_coded("z3_gate"), True)
check("x is not a family", gate.is_coded("x5_helper"), False)
check("d is not a family", gate.is_coded("d6_helper"), False)
# The witnesses: these are why. An AArch64 register accessor in Rust
# (held at a hard zero, so no grandfathering is available) and the
# device-tree magic number must not be violations.
check("an AArch64 register accessor passes", gate.is_coded("set_x0"), False)
check("a register-range test name passes",
      gate.is_coded("syscall_args_from_trap_frame_extracts_x0_to_x5"), False)
check("the device-tree magic passes", gate.is_coded("xD00DFEED"), False)
check("a Lean D-hypothesis passes", gate.is_coded("hD1"), False)

# A phase code may carry a letter suffix.
check("a lettered phase code is flagged", gate.is_coded("phase2a_helper"), True)
check("a two-digit lettered phase is flagged",
      gate.is_coded("phase12bRunner"), True)
check("an ordinary phase word passes", gate.is_coded("phased"), False)

# A hyphen joins a name in config/data and separates operands in code,
# so content normalisation is per-format.  Getting this backwards either
# way is a defect: normalising Lean would merge `a-b` into one token,
# and not normalising YAML hides the canonical `WS-*` spelling.
check("config formats join hyphenated names",
      ".yaml" in gate.HYPHEN_JOINS_NAMES and ".toml" in gate.HYPHEN_JOINS_NAMES
      and ".json" in gate.HYPHEN_JOINS_NAMES, True)
check("code formats do NOT join hyphens",
      not (gate.HYPHEN_JOINS_NAMES & {".lean", ".rs", ".py", ".sh", ".S"}), True)
check("a hyphenated id is coded once joined",
      gate.is_coded("WS" + "-SM-helper".replace("-", "_")), True)
check("the same id is invisible unjoined",
      any(gate.is_coded(t) for t in gate.IDENTIFIER.findall("WS" + "-SM-helper")),
      False)

# ---------------------------------------------------------------------
# The two ratchets.  Every other check in this file pins a mechanism I
# already knew to look for; these two exist to catch the ones I do not,
# by failing when the repository grows a family or a file type that has
# never been classified.  Five review rounds found missing families and
# four found missing formats — both lists were hand-maintained.
# ---------------------------------------------------------------------

# Families come from the registry, not from a literal in the source.
check("families are derived, not hand-listed",
      "REGISTRY_FAMILY_RE.findall" in Path(gate.__file__).read_text(), True)
# The registry spells a workstream `WS-Q` for the family and `WS-Q1`
# for a phase of it, and a word boundary after the letters saw only the
# first -- so nine families appearing ONLY in the fused form never
# reached the grammar.  Deriving from a source is only as good as the
# parse of that source.
check("the fused spelling yields its family",
      gate.REGISTRY_FAMILY_RE.findall("see WS" + "-J1 for this"), ["J"])
check("the bare spelling still yields its family",
      gate.REGISTRY_FAMILY_RE.findall("see WS" + "-SM for this"), ["SM"])
check("a fused two-letter family is parsed",
      gate.REGISTRY_FAMILY_RE.findall("WS" + "-RC12"), ["RC"])
# Load-bearing against the REAL registry: `j` appears there only fused,
# so it is present exactly when the parse is right.
check("a fused-only family reaches the grammar",
      "j" in gate.registry_families(), True)
check("and it carries a recorded decision",
      "j" in gate.SINGLE_LETTER_ENFORCED or "j" in gate.SINGLE_LETTER_DECLINED,
      True)
check("the registry's two-letter families are all covered",
      {f for f in gate.registry_families() if len(f) > 1}
      <= set(gate.WORKSTREAM_FAMILIES), True)
check("every registry single-letter family has a decision",
      {f for f in gate.registry_families() if len(f) == 1}
      <= gate.SINGLE_LETTER_ENFORCED | set(gate.SINGLE_LETTER_DECLINED), True)


def _families_for(fams):
    real = gate.registry_families
    gate.registry_families = lambda: fams
    try:
        return gate.enforced_families()
    except SystemExit:
        return None
    finally:
        gate.registry_families = real


# `p` is a letter the registry does not name, so it has no decision.
# This check previously used `j` — which the registry DOES name, in the
# fused `WS-J1` spelling the parse could not see.  Fixing the parse gave
# `j` a decision and this check started passing for the wrong reason,
# which is its own small lesson: a negative check pinned to a specific
# input can be invalidated by an unrelated fix, silently.
check("an unclassified single-letter family FAILS the gate",
      _families_for({"sm", "p"}), None)
check("a new two-letter family is covered without a decision",
      "bq" in (_families_for({"sm", "bq"}) or ()), True)
check("a declined single-letter family stays out",
      "x" not in (_families_for({"sm", "x"}) or ()), True)

# Every tracked file type must carry an explicit scan decision.
check("no tracked file type is unclassified",
      gate.format_coverage_gap(), (set(), set()))
check("the two format tables do not overlap",
      set(gate.CONTENT_STRIPPERS) & set(gate.NO_CONTENT_SCAN), set())
check("skipped formats each record a reason",
      all(v.strip() for v in gate.NO_CONTENT_SCAN.values()), True)

# ...and an extensionless file is classified by NAME, not by the one
# `""` decision that used to stand for all of them.  That entry read
# "LICENSE, git hooks, CI helper stubs" while also silently covering
# both `.gitignore` files, whose patterns are maintained names -- and
# the coverage ratchet saw `""` as classified, so it reported full
# coverage over a decision that had stopped describing its members.
check("a gitignore's contents are scanned",
      gate.content_rule(".gitignore") is not None, True)
check("a nested gitignore rides the same decision",
      gate.content_rule("rust/.gitignore") is not None, True)
check("licence prose stays exempt", gate.content_rule("LICENSE"), None)
check("an extensionless name joins hyphens",       # a bare name IS a name
      gate.content_rule(".gitignore")[1], True)
check("extensionless tables do not overlap",
      set(gate.EXTENSIONLESS_STRIPPERS) & set(gate.EXTENSIONLESS_NO_SCAN),
      set())
check("skipped extensionless files each record a reason",
      all(v.strip() for v in gate.EXTENSIONLESS_NO_SCAN.values()), True)
# The ratchet must fire on a NEW extensionless file, which is the part
# the `""` entry disabled: `""` was already classified, so nothing
# unclassified could ever appear.
check("an unclassified extensionless file is a gap",
      "Makefile" in (set(gate.EXTENSIONLESS_STRIPPERS)
                     | set(gate.EXTENSIONLESS_NO_SCAN)), False)
check("one lookup serves scanning and classification",
      "content_rule(p)" in Path(gate.__file__).read_text(), True)

# Every input — sources, baseline, registry — must come from the index,
# because paths are enumerated from the index and any working-tree read
# lets a contributor stage one state and present another. Two rounds hit
# this in two different inputs; the third (the registry) arrived with the
# derivation itself. Pinning the *property* rather than a call site: no
# bare `read_text` on a tracked file may return.
_src = Path(gate.__file__).read_text()
check("no input is read from the working tree",
      [ln.strip() for ln in _src.splitlines()
       if ".read_text(" in ln and not ln.lstrip().startswith("#")
       and "REPO_ROOT /" not in ln],
      [])
check("there is one reader for tracked files",
      _src.count("def read_tracked(") == 1
      and _src.count("def index_contents(") == 1, True)
check("the registry is read through it",
      "read_tracked" in gate.registry_families.__code__.co_names, True)
check("the baseline is read through it", "read_tracked(BASELINE_REL)" in _src,
      True)

# A string literal that supplies a linker-visible symbol is code. The
# Rust scan is a hard zero with no baseline, so `#[export_name = "..."]`
# was the one spelling that could put a coded name in the kernel's symbol
# table with every surrounding identifier reading clean.
check("Rust export_name literals are scanned",
      "phase5_helper" in gate.strip_rust(
          '#[export_name = "phase5_helper"] pub fn semantic() {}'), True)
check("Rust link_name literals are scanned",
      "ws_sm_thing" in gate.strip_rust('#[link_name = "ws_sm_thing"] fn f();'),
      True)
check("Rust link_section literals are scanned",
      "an3_boot" in gate.strip_rust(
          '#[link_section = ".text.an3_boot"] static X: u8 = 0;'), True)
check("assembly section names are scanned",
      "ak9ce_01" in gate.strip_asm('.section "ak9ce_01", "ax"'), True)
# ...and the exemption that makes the whole gate usable still holds: an
# ordinary literal is prose, or every docstring in the tree becomes a
# violation.
check("ordinary Rust literals stay exempt",
      "ws_sm" in gate.strip_rust('let m = "the ws_sm workstream is prose";'),
      False)
check("format-string prose stays exempt",
      "phase5" in gate.strip_rust('println!("phase5 of the plan");'), False)

# The same reasoning one level in. An inline-assembly template is
# assembly SOURCE, and a symbol it declares is linker-visible exactly as
# `#[export_name]`'s is. The preceding-text test above cannot reach it:
# a template is routinely one literal per assembly line and only the
# first has the macro name in front of it, so the macro's argument SPAN
# is what gets tracked.
check("an asm template's symbols are scanned",
      "phase5_helper" in gate.strip_rust('global_asm!(".global phase5_helper");'),
      True)
check("every literal of a multi-line template is scanned",
      "phase5_helper" in gate.strip_rust(
          'asm!(\n  "nop",\n  ".global phase5_helper",\n  options(nostack),\n);'),
      True)
check("a raw-string template is scanned",
      "ak9ce_01" in gate.strip_rust('global_asm!(r#".global ak9ce_01"#);'), True)
# The walk back over the macro name is exact, so a name merely ENDING in
# `asm` opens nothing, and the span closes with the macro's own paren.
check("a name ending in asm does not open a template",
      "phase5_helper" in gate.strip_rust('notasm!("phase5_helper");'), False)
check("a literal after the template closes is prose",
      "phase5_helper" in gate.strip_rust('asm!("nop"); let m = "phase5_helper";'),
      False)

# A checksum manifest is `<digest>  <name>`, and the NAME is what
# `sha256sum -c` opens. Scanning the companion fixture's path instead
# checks a different string -- nothing forces the two to agree -- so the
# manifest was covered only by proxy.
_digest = "d645916c8523466719ce59c8640a835c7bc822a6dfad0512a2044d8073d1de77"
check("a manifest's filename is scanned",
      "phase5_helper" in gate.strip_checksum_manifest(
          _digest + "  phase5_helper.expected\n"), True)
check("a binary-mode manifest record is handled",
      "phase5_helper" in gate.strip_checksum_manifest(
          _digest + " *phase5_helper.expected\n"), True)
# The digest is data, and a hex run beginning with a letter tokenises as
# an identifier, so it must not survive into the scan.
check("a manifest's digest is not scanned",
      _digest in gate.strip_checksum_manifest(_digest + "  x.expected\n"), False)


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
