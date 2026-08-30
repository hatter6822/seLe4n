#!/usr/bin/env python3
"""SMP completion-phase theorem manifest — generator and drift gate.

`SMP_RELEASE_CLOSURE_PLAN.md` carried its theorem total as a hand-summed
literal: "16 SM0 + 1 SM1 + 22 SM2 + 28 SM3 + ~50 SM4 + 30 SM5 + 25 SM6 +
14 SM7 + 18 SM8 + 5 SM10 = 209 ~= 210".  That sum runs SM8 -> SM10 with **no
SM9 term**, though SM9 is a landed phase, so `wsm_theorem_count` and
SM10.B.13 would both have certified a number computed as if SM9 never
happened.  A hand-sum cannot detect its own staleness: nothing breaks when a
phase is added, renamed, or grows.

This script replaces the sum with a measurement.  It discovers every theorem
inventory in the tree, reads the count each one's Lean size witness **proves**,
and attributes it to the WS-SM phase that owns it.  The result is written to
`docs/smp_theorem_manifest.json` and cross-checked against the Lean-side
manifest in `SeLe4n/Kernel/Concurrency/PhaseTheoremManifest.lean`, whose
`wsmTheoremCount` is a `List.sum` over per-phase entries rather than a
literal.

Two independent mechanisms, closing two different failure modes:

* **Lean** proves each entry's `theoremCount` equals the real inventory
  lengths, so a resized inventory fails the build.  It cannot, on its own,
  notice an inventory the manifest never mentions.
* **This gate** discovers inventories from the tree and fails when one is
  claimed by no phase, or claimed twice, or claimed with the wrong number.
  That is the SM9 shape: a whole phase's worth of theorems missing from a
  total that still looked plausible.

## What counts as an inventory

A theorem inventory is a list of theorem identifiers carrying a duplicate-free
witness `<name>_identifiers_nodup` and a size witness
`<name>_count : <name>.length = N`.  Discovery keys on the `_identifiers_nodup`
witness because it is what distinguishes an inventory of *theorem names* from
the many `X.all.length = N` enumerations of operations, rules and kinds that
are not theorem counts.  Both witnesses must be present: an inventory with a
nodup witness and no size witness is a hard failure, not a skip, since "the
gate could not read it" and "the gate checked it" must never produce the same
PASS line.

Assumption ledgers (`smpLatentInventory`, `smpRetiredInventory`) carry the same
two witnesses but enumerate *assumptions*, not proved theorems.  They are
claimed by the manifest like everything else -- so they cannot go unregistered
-- under `kind = assumptionLedger`, and contribute nothing to the theorem
total.

Every read goes through `lean_code_view.strip`, the comment-free code view, so
a witness that survives only in a docstring cannot satisfy this gate and a code
sample inside a block comment cannot invent one.

Exit status: 0 when the manifest agrees with the tree, 1 on any drift.
"""

from __future__ import annotations

import argparse
import json
import os
import pathlib
import re
import sys

REPO_ROOT = pathlib.Path(__file__).resolve().parent.parent
MANIFEST_JSON = REPO_ROOT / "docs" / "smp_theorem_manifest.json"
LEAN_MANIFEST = (
    REPO_ROOT / "SeLe4n" / "Kernel" / "Concurrency" / "PhaseTheoremManifest.lean"
)
LEAN_ROOTS = ("SeLe4n",)

sys.path.insert(0, str(REPO_ROOT / "scripts"))
import lean_code_view  # noqa: E402  (needs the path insert above)

# The eleven WS-SM phases, each constructor bound to the code its label must
# carry.  Stated here rather than derived from the manifest: a phase absent
# from the manifest is the defect this whole mechanism exists to catch, so
# deriving the expected set from the thing under test would make the check
# vacuous.
#
# The BINDING is the point, not the two sets.  Checking "every constructor
# appears" and "every code appears" independently leaves both satisfied when
# two entries swap labels — the sets are still complete while every inventory
# is attributed to the wrong phase, and the generated JSON says so.  A renamed
# constructor fails here as an unknown key rather than passing quietly.
EXPECTED_PHASE_CODES = {
    "foundations": "SM0",
    "rustHal": "SM1",
    "verifiedLockPrimitives": "SM2",
    "perObjectLocks": "SM3",
    "perCoreState": "SM4",
    "perCoreScheduler": "SM5",
    "crossCoreIpc": "SM6",
    "tlbShootdown": "SM7",
    "informationFlow": "SM8",
    "declassification": "SM9",
    "releaseClosure": "SM10",
}
PHASE_CODES = list(EXPECTED_PHASE_CODES.values())

# A declaration's leading modifiers.  Matching them is not cosmetic: keying
# discovery on a bare `^theorem` would let `private theorem
# fooTheorems_identifiers_nodup` hide a whole inventory from this gate while
# Lean elaborated it happily — a fail-open in the one direction that matters,
# since an inventory the gate cannot see is an inventory no phase has to claim.
# Lean accepts a top-level declaration at any indentation — `theorem foo …`
# nested two spaces inside a `namespace` block elaborates exactly like an
# unindented one.  Anchoring discovery at a bare `^` therefore made the
# completeness guarantee depend on FORMATTING: indent an inventory's witnesses
# and it vanishes from the gate while Tier 0 still reports PASS.  Verified
# against the elaborator, not assumed.
_LEAD = r"[ \t]*"
_MODIFIERS = r"(?:@\[[^\]]*\]\s*|private\s+|protected\s+|nonrec\s+)*"

# Lean accepts `lemma` wherever it accepts `theorem`, and this repository uses
# both.  Keying discovery on `theorem` alone made a `lemma`-declared witness
# invisible to the gate, so its inventory could stay unclaimed while the gate
# reported PASS — the same fail-open shape as the modifier gap above, and
# contrary to the completeness this gate exists to provide.
_THEOREM = r"(?:theorem|lemma)"

# A Lean identifier, and a possibly-qualified one.  A declaration may be
# written under an explicit namespace prefix — `theorem Foo.xTheorems_count`
# elaborates exactly like `theorem xTheorems_count` inside `namespace Foo` —
# and a capture that stopped at the dot matched neither form, so the whole
# inventory vanished from discovery while Tier 0 reported PASS.
#
# This is the third distinct declaration form to have slipped past this
# pattern (`lemma`, then indentation, now qualification), so the fix is the
# general one: match Lean's identifier grammar rather than enumerate the
# spellings that happen to appear in the tree today.
_IDENT = r"[A-Za-z_][A-Za-z0-9_'!?]*"
_QUALIFIED = _IDENT + r"(?:\." + _IDENT + r")*"


def _name_alternatives(inv: str) -> str:
    """`Foo.xTheorems` -> `(?:Foo\.xTheorems|xTheorems)`.

    A qualified witness may refer to its own inventory either way: written as
    `theorem Foo.xTheorems_count : Foo.xTheorems.length = N` at the top level,
    or as `xTheorems.length` from inside `namespace Foo`.  Both name the same
    list, so both are accepted.
    """
    bare = inv.rsplit(".", 1)[-1]
    if bare == inv:
        return re.escape(inv)
    return r"(?:" + re.escape(inv) + r"|" + re.escape(bare) + r")"


# `<inventory>_identifiers_nodup` — the discovery key.
NODUP_RE = re.compile(
    r"^" + _LEAD + _MODIFIERS + _THEOREM + r"\s+(" + _QUALIFIED + r")_identifiers_nodup\b",
    re.M,
)


def _count_re(inv: str) -> re.Pattern[str]:
    """`theorem <inv>_count : <inv>.length = N` — statement may wrap a line."""
    alt = _name_alternatives(inv)
    return re.compile(
        r"^" + _LEAD + _MODIFIERS + _THEOREM + r"\s+" + alt + r"_count\b\s*:\s*"
        r"(?:\r?\n\s*)?" + alt + r"\.length\s*=\s*(\d+)",
        re.M,
    )


def read_code(path: pathlib.Path) -> str:
    """Read a Lean source through the comment-free code view."""
    return lean_code_view.strip(path.read_text(encoding="utf-8"))


def lean_files() -> list[pathlib.Path]:
    out: list[pathlib.Path] = []
    for root in LEAN_ROOTS:
        out.extend(sorted((REPO_ROOT / root).rglob("*.lean")))
    return out


def discover_in(sources: dict[str, str]) -> tuple[dict[str, dict[str, object]], list[str]]:
    """Find every theorem inventory in `sources` and the count it proves.

    `sources` maps a display path to **already-stripped** Lean text.  Split out
    from the tree walk so the self-test can drive the same parser over
    fixtures: a scanner that under-reaches fails silently, so the parser has to
    be exercisable without a repository around it.

    Returns `(inventories, errors)`.  An inventory whose nodup witness is
    present but whose size witness is missing or unreadable is an error, not
    an omission.
    """
    found: dict[str, dict[str, object]] = {}
    errors: list[str] = []
    for rel, src in sources.items():
        for m in NODUP_RE.finditer(src):
            written = m.group(1)
            # The manifest claims an inventory by its bare name, so that is the
            # key.  Two inventories whose qualified names share a final
            # component therefore collide here — and that collision is an
            # error rather than something to disambiguate, because the
            # manifest's `inventories : List String` could not tell them apart
            # either.  It is reported by the duplicate branch below.
            inv = written.rsplit(".", 1)[-1]
            if inv in found:
                errors.append(
                    f"inventory {inv!r} declared in two modules: "
                    f"{found[inv]['module']} and {rel}"
                )
                continue
            cm = _count_re(written).search(src)
            if cm is None:
                errors.append(
                    f"inventory {inv!r} ({rel}) has {written}_identifiers_nodup but no "
                    f"readable size witness `theorem {written}_count : {written}.length = N`"
                )
                continue
            found[inv] = {"module": rel, "count": int(cm.group(1))}
    return found, errors


def discover() -> tuple[dict[str, dict[str, object]], list[str]]:
    """`discover_in` over the tree, read through the comment-free code view."""
    return discover_in(
        {str(p.relative_to(REPO_ROOT)): read_code(p) for p in lean_files()}
    )


# ---------------------------------------------------------------------------
# Lean-side manifest parsing
# ---------------------------------------------------------------------------

ENTRY_RE = re.compile(
    r"\{\s*phase\s*:=\s*\.(?P<phase>[A-Za-z][A-Za-z0-9]*)\s*,"
    r"\s*label\s*:=\s*\"(?P<label>[^\"]*)\"\s*,"
    r"\s*kind\s*:=\s*\.(?P<kind>theoremInventory|assumptionLedger|unregistered)\s*,"
    r"\s*inventories\s*:=\s*\[(?P<invs>[^\]]*)\]\s*,"
    r"\s*entryCount\s*:=\s*(?P<entries>\d+)\s*,"
    r"\s*theoremCount\s*:=\s*(?P<count>\d+)\s*\}",
    re.S,
)
INV_NAME_RE = re.compile(r"\"([A-Za-z_][A-Za-z0-9_'!?]*)\"")
# `SmpCompletionPhase.all` — the Lean phase enumeration, read so the gate
# checks the manifest against the inductive rather than against its own idea
# of what the constructors are called.
PHASE_ALL_RE = re.compile(
    r"^def\s+SmpCompletionPhase\.all\s*:\s*List\s+SmpCompletionPhase\s*:=\s*"
    r"\[(?P<body>[^\]]*)\]",
    re.M | re.S,
)
PHASE_CTOR_RE = re.compile(r"\.([A-Za-z][A-Za-z0-9]*)")

# The gate measures ENTRIES.  Propositionality is a fact about the Lean
# environment, so `smpInventoriedTheoremCount` is verified by the census inside
# `PhaseTheoremManifest.lean`, not here — this gate reads it only to confirm it
# is not larger than the entry total, which would be incoherent on its face.
TOTAL_RE = re.compile(
    r"^" + _LEAD + _MODIFIERS + _THEOREM + r"\s+smp_inventoried_entry_count\s*:\s*"
    r"smpInventoriedEntryCount\s*=\s*(\d+)",
    re.M,
)
THEOREM_TOTAL_RE = re.compile(
    r"^" + _LEAD + _MODIFIERS + _THEOREM + r"\s+smp_inventoried_theorem_count\s*:\s*"
    r"smpInventoriedTheoremCount\s*=\s*(\d+)",
    re.M,
)

# The two inventories that enumerate ASSUMPTIONS rather than proved statements.
# Pinned by name, deliberately.  Trusting the manifest's own `kind` field would
# let a theorem inventory be labelled `assumptionLedger` (or `unregistered`)
# with a zero count and vanish from the total while every check still passed —
# the gate would be taking the word of the thing it is checking.
KNOWN_ASSUMPTION_LEDGERS = {"smpLatentInventory", "smpRetiredInventory"}


def parse_manifest_text(
    src: str,
) -> tuple[list[dict[str, object]], list[str], int | None, list[str]]:
    """Parse an already-stripped Lean manifest source.

    Split from the file read for the same reason as `discover_in`: the
    self-test drives this parser over fixtures.
    """
    errors: list[str] = []
    am = PHASE_ALL_RE.search(src)
    if am is None:
        errors.append(
            "Lean manifest has no readable `def SmpCompletionPhase.all : "
            "List SmpCompletionPhase := [...]`"
        )
        ctors: list[str] = []
    else:
        ctors = PHASE_CTOR_RE.findall(am.group("body"))
    entries: list[dict[str, object]] = []
    for m in ENTRY_RE.finditer(src):
        entries.append(
            {
                "phase": m.group("phase"),
                "label": m.group("label"),
                "kind": m.group("kind"),
                "inventories": INV_NAME_RE.findall(m.group("invs")),
                "entryCount": int(m.group("entries")),
                "theoremCount": int(m.group("count")),
            }
        )
    tm = TOTAL_RE.search(src)
    total = int(tm.group(1)) if tm else None
    if total is None:
        errors.append(
            "Lean manifest has no readable "
            "`theorem smp_inventoried_entry_count : smpInventoriedEntryCount = N`"
        )
    ttm = THEOREM_TOTAL_RE.search(src)
    if ttm is None:
        errors.append(
            "Lean manifest has no readable "
            "`theorem smp_inventoried_theorem_count : smpInventoriedTheoremCount = N`"
        )
    elif total is not None and int(ttm.group(1)) > total:
        errors.append(
            f"smpInventoriedTheoremCount ({ttm.group(1)}) exceeds "
            f"smpInventoriedEntryCount ({total}): a subset cannot be larger than "
            f"the set it is drawn from"
        )
    return entries, ctors, total, errors


def parse_lean_manifest() -> tuple[list[dict[str, object]], list[str], int | None, list[str]]:
    """`parse_manifest_text` over the Lean manifest module."""
    if not LEAN_MANIFEST.is_file():
        return [], [], None, [f"missing Lean manifest: {LEAN_MANIFEST}"]
    return parse_manifest_text(read_code(LEAN_MANIFEST))


def phase_code(label: str) -> str:
    """The phase code a manifest entry's label carries, e.g. `SM3`."""
    return label.split(None, 1)[0] if label else ""


# ---------------------------------------------------------------------------
# Cross-check
# ---------------------------------------------------------------------------


def build_manifest(
    inventories: dict[str, dict[str, object]],
    entries: list[dict[str, object]],
    ctors: list[str],
) -> tuple[dict[str, object], list[str]]:
    """Attribute every discovered inventory to its phase, per the Lean claims."""
    errors: list[str] = []

    claimed: dict[str, str] = {}
    for e in entries:
        for inv in e["inventories"]:  # type: ignore[index]
            if inv in claimed:
                errors.append(
                    f"inventory {inv!r} claimed by two phases: "
                    f"{claimed[inv]} and {e['phase']}"
                )
            claimed[inv] = str(e["phase"])
            if inv not in inventories:
                errors.append(
                    f"phase {e['phase']} claims inventory {inv!r}, which the tree "
                    f"does not define (renamed or deleted?)"
                )

    for inv in sorted(inventories):
        if inv not in claimed:
            errors.append(
                f"inventory {inv!r} ({inventories[inv]['module']}) is claimed by no "
                f"WS-SM phase — add it to smpPhaseTheoremManifest"
            )

    # Two independent completeness checks.  The first holds the manifest to the
    # Lean inductive: a constructor added to `SmpCompletionPhase.all` with no
    # entry is caught here as well as by `smpPhaseTheoremManifest_covers_all`.
    # Validate the declared kind against the pinned ledger set.  An inventory
    # that is not one of the two assumption ledgers is a theorem inventory, and
    # the phase claiming it must say so — otherwise its entries silently leave
    # the total.
    for e in entries:
        invs = [str(i) for i in e["inventories"]]  # type: ignore[arg-type]
        ledgers = [i for i in invs if i in KNOWN_ASSUMPTION_LEDGERS]
        others = [i for i in invs if i not in KNOWN_ASSUMPTION_LEDGERS]
        if e["kind"] == "assumptionLedger" and others:
            errors.append(
                f"phase {e['phase']} is declared assumptionLedger but claims "
                f"{others}, which are not among the known assumption ledgers "
                f"{sorted(KNOWN_ASSUMPTION_LEDGERS)} — their entries would leave "
                f"the total unnoticed"
            )
        if e["kind"] == "unregistered" and invs:
            errors.append(
                f"phase {e['phase']} is declared unregistered but claims {invs}"
            )
        if e["kind"] == "theoremInventory" and ledgers:
            errors.append(
                f"phase {e['phase']} is declared theoremInventory but claims the "
                f"assumption ledger(s) {ledgers}"
            )

    seen_phases = [str(e["phase"]) for e in entries]
    for ctor in ctors:
        if seen_phases.count(ctor) == 0:
            errors.append(f"phase constructor .{ctor} has no manifest entry")
        elif seen_phases.count(ctor) > 1:
            errors.append(
                f"phase constructor .{ctor} has {seen_phases.count(ctor)} entries; expected 1"
            )
    for ctor in seen_phases:
        if ctors and ctor not in ctors:
            errors.append(
                f"manifest entry names .{ctor}, which is not in SmpCompletionPhase.all"
            )

    # The second holds the *phase codes* to WS-SM's eleven.  Renaming a
    # constructor cannot hide a missing phase, because the codes are checked
    # against a set this gate states rather than reads.
    seen_codes = [phase_code(str(e["label"])) for e in entries]
    for code in PHASE_CODES:
        if seen_codes.count(code) != 1:
            errors.append(
                f"WS-SM phase {code} has {seen_codes.count(code)} manifest entries; expected 1"
            )
    for code in seen_codes:
        if code not in PHASE_CODES:
            errors.append(
                f"manifest entry labelled {code!r} names no WS-SM phase "
                f"(labels must begin with the phase code, e.g. \"SM3 — …\")"
            )

    # The binding itself: this constructor must carry this code.  Without it,
    # swapping two entries' labels leaves both completeness checks satisfied.
    for e in entries:
        ctor = str(e["phase"])
        code = phase_code(str(e["label"]))
        expected = EXPECTED_PHASE_CODES.get(ctor)
        if expected is None:
            errors.append(
                f"phase constructor .{ctor} is not a known WS-SM phase — if it "
                f"was renamed, update EXPECTED_PHASE_CODES so the binding stays "
                f"checked"
            )
        elif code != expected:
            errors.append(
                f"phase constructor .{ctor} is labelled {code!r} but belongs to "
                f"{expected!r} — the manifest attributes its inventories to the "
                f"wrong phase"
            )

    phases: list[dict[str, object]] = []
    total = 0
    for e in entries:
        invs = [str(i) for i in e["inventories"]]  # type: ignore[arg-type]
        measured = sum(int(inventories[i]["count"]) for i in invs if i in inventories)
        contributes = e["kind"] == "theoremInventory"
        if int(e["entryCount"]) != measured:
            breakdown = "+".join(
                "{}={}".format(i, inventories[i]["count"])
                for i in invs
                if i in inventories
            ) or "no inventories"
            errors.append(
                f"phase {e['phase']} declares entryCount = {e['entryCount']}, "
                f"tree measures {measured} ({breakdown})"
            )
        if contributes and int(e["theoremCount"]) > int(e["entryCount"]):
            errors.append(
                f"phase {e['phase']} declares theoremCount = {e['theoremCount']} > "
                f"entryCount = {e['entryCount']}"
            )
        if not contributes and int(e["theoremCount"]) != 0:
            errors.append(
                f"phase {e['phase']} is {e['kind']} yet declares theoremCount = "
                f"{e['theoremCount']}"
            )
        if contributes:
            total += measured
        phases.append(
            {
                "phase": phase_code(str(e["label"])),
                "constructor": e["phase"],
                "label": e["label"],
                "kind": e["kind"],
                "inventories": [
                    {
                        "name": i,
                        "module": inventories[i]["module"] if i in inventories else None,
                        "count": inventories[i]["count"] if i in inventories else None,
                    }
                    for i in invs
                ],
                "entryCount": measured,
                "theoremCount": int(e["theoremCount"]) if contributes else 0,
            }
        )

    return {
        "schema": "wsm-theorem-manifest/1",
        "generator": "scripts/generate_smp_theorem_manifest.py",
        "note": (
            "Generated from the tree, not hand-summed. `entryCount` is the number "
            "a Lean size witness proves for that inventory — every registered "
            "declaration, whatever its type. `theoremCount` is the subset whose "
            "declaration type is a Prop, verified by the propositionality census "
            "in SeLe4n/Kernel/Concurrency/PhaseTheoremManifest.lean (this script "
            "reads text and has no elaborator, so it cannot check that itself). "
            "Quote theoremTotal, not entryTotal: the inventories register a "
            "phase's whole surface, so 209 entries are defs rather than proofs. "
            "Regenerate with `python3 scripts/generate_smp_theorem_manifest.py "
            "--write`."
        ),
        "phases": phases,
        "entryTotal": total,
        "theoremTotal": sum(
            int(p["theoremCount"]) for p in phases  # type: ignore[index,call-overload]
        ),
    }, errors



# ---------------------------------------------------------------------------
# Self-test
# ---------------------------------------------------------------------------
#
# A scanner that under-reaches fails silently, which is the failure this whole
# mechanism exists to stop happening to a theorem count.  So the gate carries
# witnesses in BOTH directions: every defect it claims to catch is reproduced
# and must be caught, and every shape it must NOT flag is reproduced and must
# pass.  The second half matters as much as the first — a stripper that
# over-reaches, or a discovery regex that fires on a docstring, would push an
# author to contort prose to satisfy a scanner, which CLAUDE.md forbids.

_CLEAN_MANIFEST = """
def SmpCompletionPhase.all : List SmpCompletionPhase :=
  [ .alpha, .beta ]

def smpPhaseTheoremManifest : List PhaseTheoremEntry :=
  [ { phase := .alpha,
      label := "SM0 - alpha",
      kind := .theoremInventory,
      inventories := ["aTheorems"],
      entryCount := 3,
      theoremCount := 3 },
    { phase := .beta,
      label := "SM1 - beta",
      kind := .assumptionLedger,
      inventories := ["smpLatentInventory"],
      entryCount := 9,
      theoremCount := 0 } ]

theorem smp_inventoried_entry_count : smpInventoriedEntryCount = 3 := by
  decide

theorem smp_inventoried_theorem_count : smpInventoriedTheoremCount = 3 := by
  decide
"""

_CLEAN_SOURCES = {
    "A.lean": "theorem aTheorems_identifiers_nodup :\n    True := trivial\n"
              "theorem aTheorems_count :\n    aTheorems.length = 3 := by decide\n",
    # `bInventory` is one of the pinned assumption ledgers, so the fixtures use
    # a real ledger name: the kind check below is only meaningful against the
    # set the production gate pins.
    "B.lean": "theorem smpLatentInventory_identifiers_nodup : True := trivial\n"
              "theorem smpLatentInventory_count : smpLatentInventory.length = 9 := by decide\n",
}


def _run(sources: dict[str, str], manifest: str, codes: list[str] | None = None):
    """Run the whole pipeline over fixtures; return (manifest, errors)."""
    global PHASE_CODES, EXPECTED_PHASE_CODES
    saved = PHASE_CODES
    saved_binding = EXPECTED_PHASE_CODES
    PHASE_CODES = codes if codes is not None else ["SM0", "SM1"]
    EXPECTED_PHASE_CODES = {"alpha": "SM0", "beta": "SM1"}
    try:
        inv, errs = discover_in(sources)
        entries, ctors, total, perrs = parse_manifest_text(manifest)
        built, berrs = build_manifest(inv, entries, ctors)
        errs = errs + perrs + berrs
        if total is not None and total != built["entryTotal"]:
            errs.append("total mismatch")
        return built, errs
    finally:
        PHASE_CODES = saved
        EXPECTED_PHASE_CODES = saved_binding


def _self_test() -> int:
    cases: list[tuple[str, bool, str]] = []

    def check(name: str, ok: bool, detail: str = "") -> None:
        cases.append((name, ok, detail))

    # 1. A clean manifest reports nothing, and measures what the tree proves.
    built, errs = _run(dict(_CLEAN_SOURCES), _CLEAN_MANIFEST)
    check("a clean manifest reports nothing", not errs, "; ".join(errs))
    check("the total is measured, not read", built["entryTotal"] == 3,
          f"got {built['entryTotal']}")

    # 2. An inventory no phase claims is caught.  This is the shape Lean cannot
    #    see: a manifest that never mentions an inventory elaborates perfectly.
    src = dict(_CLEAN_SOURCES)
    src["C.lean"] = ("theorem cTheorems_identifiers_nodup : True := trivial\n"
                     "theorem cTheorems_count : cTheorems.length = 5 := by decide\n")
    _, errs = _run(src, _CLEAN_MANIFEST)
    check("an unclaimed inventory is caught",
          any("claimed by no" in e for e in errs), "; ".join(errs))

    # 3. A phase with no entry is caught — the SM9 shape — by BOTH the
    #    constructor check and the phase-code check, which are independent.
    dropped = _CLEAN_MANIFEST.replace(
        """    { phase := .beta,
      label := "SM1 - beta",
      kind := .assumptionLedger,
      inventories := ["smpLatentInventory"],
      entryCount := 9,
      theoremCount := 0 } ]""", "  ]")
    _, errs = _run(dict(_CLEAN_SOURCES), dropped)
    check("a dropped phase is caught by constructor",
          any("constructor .beta has no manifest entry" in e for e in errs),
          "; ".join(errs))
    check("a dropped phase is caught by phase code",
          any("WS-SM phase SM1 has 0 manifest entries" in e for e in errs),
          "; ".join(errs))

    # 4. A declared count the tree does not measure is caught.
    wrong = _CLEAN_MANIFEST.replace("entryCount := 3,", "entryCount := 4,")
    _, errs = _run(dict(_CLEAN_SOURCES), wrong)
    check("a wrong declared count is caught",
          any("declares entryCount = 4" in e for e in errs), "; ".join(errs))

    # 5. A Lean total that disagrees with the measurement is caught.
    bad_total = _CLEAN_MANIFEST.replace(
        "smpInventoriedEntryCount = 3", "smpInventoriedEntryCount = 4")
    _, errs = _run(dict(_CLEAN_SOURCES), bad_total)
    check("a drifted Lean total is caught",
          any("total mismatch" in e for e in errs), "; ".join(errs))

    # 6. Assumption ledgers are claimed but contribute nothing: B's inventory
    #    proves 9, and the total stays 3.
    built, errs = _run(dict(_CLEAN_SOURCES), _CLEAN_MANIFEST)
    check("an assumption ledger contributes zero",
          built["entryTotal"] == 3 and not errs, f"got {built['entryTotal']}")

    # 7. A witness that survives only in a comment must NOT be discovered.
    #    The real gate reads through `lean_code_view.strip`, so this drives the
    #    stripper too rather than assuming it.
    commented = lean_code_view.strip(
        "/-!\ntheorem ghostTheorems_identifiers_nodup : True := trivial\n"
        "theorem ghostTheorems_count : ghostTheorems.length = 99 := by decide\n-/\n"
        "-- theorem alsoGhostTheorems_identifiers_nodup : True := trivial\n")
    src = dict(_CLEAN_SOURCES)
    src["Ghost.lean"] = commented
    _, errs = _run(src, _CLEAN_MANIFEST)
    check("a comment-only witness is not discovered", not errs, "; ".join(errs))

    # 8. A nodup witness with no size witness is a hard failure, not a skip.
    src = dict(_CLEAN_SOURCES)
    src["D.lean"] = "theorem dTheorems_identifiers_nodup : True := trivial\n"
    _, errs = _run(src, _CLEAN_MANIFEST)
    check("a sizeless inventory is a hard failure",
          any("no readable size witness" in e for e in errs), "; ".join(errs))

    # 9. Declaration modifiers do not hide an inventory.
    src = dict(_CLEAN_SOURCES)
    src["E.lean"] = ("@[simp] private theorem eTheorems_identifiers_nodup : True := trivial\n"
                     "private theorem eTheorems_count : eTheorems.length = 2 := by decide\n")
    _, errs = _run(src, _CLEAN_MANIFEST)
    check("a modifier does not hide an inventory",
          any("'eTheorems'" in e and "claimed by no" in e for e in errs),
          "; ".join(errs))

    # 10. One inventory claimed by two phases is caught (it would be counted twice).
    twice = _CLEAN_MANIFEST.replace('inventories := ["smpLatentInventory"]',
                                    'inventories := ["bInventory", "aTheorems"]')
    _, errs = _run(dict(_CLEAN_SOURCES), twice)
    check("an inventory claimed twice is caught",
          any("claimed by two phases" in e for e in errs), "; ".join(errs))

    # 11. A claimed inventory the tree does not define is caught (a rename).
    renamed = _CLEAN_MANIFEST.replace('"aTheorems"', '"aTheoremsRenamed"')
    _, errs = _run(dict(_CLEAN_SOURCES), renamed)
    check("a claim on a nonexistent inventory is caught",
          any("does not define" in e for e in errs), "; ".join(errs))

    # 12. The same inventory name declared in two modules is caught.
    src = dict(_CLEAN_SOURCES)
    src["A2.lean"] = _CLEAN_SOURCES["A.lean"]
    _, errs = _run(src, _CLEAN_MANIFEST)
    check("a duplicated inventory name is caught",
          any("declared in two modules" in e for e in errs), "; ".join(errs))

    # 13. A label that names no WS-SM phase is caught.
    mislabelled = _CLEAN_MANIFEST.replace('label := "SM1 - beta"',
                                          'label := "beta"')
    _, errs = _run(dict(_CLEAN_SOURCES), mislabelled)
    check("a label naming no phase is caught",
          any("names no WS-SM phase" in e for e in errs), "; ".join(errs))

    # 14. `lemma` is a theorem form.  An inventory declaring its witnesses with
    #     `lemma` must still be discovered — otherwise it can stay unclaimed
    #     while the gate reports PASS.  (Codex review, PR #882.)
    src = dict(_CLEAN_SOURCES)
    src["F.lean"] = ("lemma fTheorems_identifiers_nodup : True := trivial\n"
                     "lemma fTheorems_count : fTheorems.length = 4 := by decide\n")
    _, errs = _run(src, _CLEAN_MANIFEST)
    check("a lemma-form witness is discovered",
          any("'fTheorems'" in e and "claimed by no" in e for e in errs),
          "; ".join(errs))

    # 15. The manifest's own `kind` must not be taken on trust.  Codex's
    #     reproduction: relabel a theorem inventory `assumptionLedger` with a
    #     zero count and its entries leave the total with nothing reported.
    mislabelled = _CLEAN_MANIFEST.replace(
        """      kind := .theoremInventory,
      inventories := ["aTheorems"],
      entryCount := 3,
      theoremCount := 3 },""",
        """      kind := .assumptionLedger,
      inventories := ["aTheorems"],
      entryCount := 3,
      theoremCount := 0 },""")
    _, errs = _run(dict(_CLEAN_SOURCES), mislabelled)
    check("a theorem inventory mislabelled as a ledger is caught",
          any("not among the known assumption ledgers" in e for e in errs),
          "; ".join(errs))

    # 16. The same dodge via `unregistered`: claim the inventory but declare the
    #     phase as carrying none.
    hidden = _CLEAN_MANIFEST.replace(
        """      kind := .theoremInventory,
      inventories := ["aTheorems"],
      entryCount := 3,
      theoremCount := 3 },""",
        """      kind := .unregistered,
      inventories := ["aTheorems"],
      entryCount := 3,
      theoremCount := 0 },""")
    _, errs = _run(dict(_CLEAN_SOURCES), hidden)
    check("an inventory hidden behind `unregistered` is caught",
          any("declared unregistered but claims" in e for e in errs),
          "; ".join(errs))

    # 17. A theorem count larger than the entry count it is drawn from.
    impossible = _CLEAN_MANIFEST.replace("theoremCount := 3 },", "theoremCount := 5 },")
    _, errs = _run(dict(_CLEAN_SOURCES), impossible)
    check("a theorem count exceeding its entry count is caught",
          any("theoremCount = 5 > entryCount" in e for e in errs), "; ".join(errs))

    # 18. Lean accepts an indented top-level declaration, so an inventory whose
    #     witnesses happen to be indented is a real inventory.  Anchoring
    #     discovery at column zero made the completeness guarantee depend on
    #     formatting: the inventory went undiscovered and the gate reported
    #     PASS.  (Codex review round 2, PR #882.)
    src = dict(_CLEAN_SOURCES)
    src["G.lean"] = ("  theorem gTheorems_identifiers_nodup : True := trivial\n"
                     "\ttheorem gTheorems_count : gTheorems.length = 7 := by decide\n")
    _, errs = _run(src, _CLEAN_MANIFEST)
    check("an indented witness is discovered",
          any("'gTheorems'" in e and "claimed by no" in e for e in errs),
          "; ".join(errs))

    # 19. Swapping two phases' labels leaves every count and every completeness
    #     check satisfied — each phase still exists, each inventory is still
    #     claimed exactly once, the totals still add up — while attributing one
    #     phase's theorems to another.  Only the constructor-to-code binding
    #     sees it.  (Codex review round 2, PR #882.)
    swapped = (_CLEAN_MANIFEST
               .replace('label := "SM0 - alpha"', 'label := "SM1 - alpha"')
               .replace('label := "SM1 - beta"', 'label := "SM0 - beta"'))
    _, errs = _run(dict(_CLEAN_SOURCES), swapped)
    check("swapped phase labels are caught",
          any("labelled 'SM1' but belongs to 'SM0'" in e for e in errs)
          and any("labelled 'SM0' but belongs to 'SM1'" in e for e in errs),
          "; ".join(errs))

    # 20. Lean accepts a qualified declaration name at the top level, so an
    #     inventory whose witnesses are written `theorem Foo.xTheorems_count`
    #     is a real inventory.  A capture that stopped at the dot matched
    #     neither form and the inventory vanished, unclaimed, with the gate
    #     reporting PASS.  (Codex review round 3, PR #882 — reproduced with
    #     the reviewer's own four-entry `Foo.xTheorems` fixture.)
    src = dict(_CLEAN_SOURCES)
    src["H.lean"] = (
        "theorem Foo.xTheorems_identifiers_nodup : True := trivial\n"
        "theorem Foo.xTheorems_count : Foo.xTheorems.length = 4 := by decide\n")
    _, errs = _run(src, _CLEAN_MANIFEST)
    check("a qualified witness is discovered",
          any("'xTheorems'" in e and "claimed by no" in e for e in errs),
          "; ".join(errs))

    # 21. The same inventory written the other legal way: the witness carries
    #     the namespace but the list is named bare, as it would be from inside
    #     `namespace Foo`.  Both spellings name one list, so both must resolve
    #     to the same inventory rather than one of them reading as sizeless.
    src = dict(_CLEAN_SOURCES)
    src["I.lean"] = (
        "theorem Foo.yTheorems_identifiers_nodup : True := trivial\n"
        "theorem yTheorems_count : yTheorems.length = 6 := by decide\n")
    _, errs = _run(src, _CLEAN_MANIFEST)
    check("a qualified witness finds its bare size witness",
          any("'yTheorems'" in e and "claimed by no" in e for e in errs)
          and not any("no readable size witness" in e for e in errs),
          "; ".join(errs))

    failed = [c for c in cases if not c[1]]
    for name, ok, detail in cases:
        print(f"  {'PASS' if ok else 'FAIL'}: {name}" + (f" -- {detail}" if not ok else ""))
    print(f"SMP theorem-manifest gate self-test: {len(cases)} cases, "
          f"{len(cases) - len(failed)} correct.")
    return 1 if failed else 0


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--write", action="store_true", help="write docs/smp_theorem_manifest.json")
    ap.add_argument("--check", action="store_true", help="fail on any drift (gate mode)")
    ap.add_argument("--list", action="store_true", help="print the discovered inventories")
    ap.add_argument("--self-test", action="store_true",
                    help="drive the parsers over fixtures; witnesses both directions")
    args = ap.parse_args(argv)

    if args.self_test:
        return _self_test()

    inventories, errors = discover()
    entries, ctors, lean_total, lerrors = parse_lean_manifest()
    errors += lerrors

    if args.list:
        for inv in sorted(inventories):
            d = inventories[inv]
            print(f"{d['count']:>6}  {inv}  ({d['module']})")

    manifest, berrors = build_manifest(inventories, entries, ctors)
    errors += berrors

    if lean_total is not None and lean_total != manifest["entryTotal"]:
        errors.append(
            f"Lean `smp_inventoried_entry_count` proves smpInventoriedEntryCount "
            f"= {lean_total}, tree measures {manifest['entryTotal']}"
        )

    if args.write:
        MANIFEST_JSON.parent.mkdir(parents=True, exist_ok=True)
        MANIFEST_JSON.write_text(
            json.dumps(manifest, indent=2, sort_keys=False) + "\n", encoding="utf-8"
        )
        print(f"wrote {MANIFEST_JSON.relative_to(REPO_ROOT)}")
    elif args.check:
        if not MANIFEST_JSON.is_file():
            errors.append(f"missing generated manifest: {MANIFEST_JSON}")
        else:
            on_disk = json.loads(MANIFEST_JSON.read_text(encoding="utf-8"))
            if on_disk != manifest:
                errors.append(
                    "docs/smp_theorem_manifest.json is stale — regenerate with "
                    "`python3 scripts/generate_smp_theorem_manifest.py --write`"
                )

    if errors:
        for e in errors:
            print(f"ERROR: {e}", file=sys.stderr)
        print(
            f"\nWS-SM theorem manifest: {len(errors)} problem(s).",
            file=sys.stderr,
        )
        return 1

    if args.check or args.write:
        n_inv = sum(1 for p in manifest["phases"] for _ in p["inventories"])
        print(
            f"OK: WS-SM theorem manifest consistent "
            f"({len(PHASE_CODES)} phases, {n_inv} inventories, "
            f"{manifest['entryTotal']} entries of which "
            f"{manifest['theoremTotal']} are theorems)."
        )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
