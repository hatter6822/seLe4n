#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Every `unsafe` site in the Rust tree carries a justification a reviewer reads.

`CLAUDE.md` states the HAL's discipline as *every unsafe block carries a
`// SAFETY:` comment*, and attributed its enforcement to
`scripts/check_arm_arm_citations.sh` — a gate the v0.30.11 audit planned as
R12.C, recorded in `docs/audits/AUDIT_v0.30.11_DISCHARGE_INDEX.md` row F.3 as
the discharge mechanism for DEEP-RUST-01/02, and **never written**: no commit on
any branch contains it and Tier 0 never ran it.  So the discipline was stated,
relied on by a discharge row, and checked by nothing.  This is that gate, written
against what the tree actually is.

## The relation, not a window

The audit plan specified "the preceding 5 lines contain the citation", and a
fixed window is a presence check: an unrelated comment five lines up satisfies
it, and a justification separated from its block by an intervening statement
does not fail it.  What a reviewer actually reads is the **contiguous comment run
immediately above the site** — comments and attributes only, no code between — so
that is the relation this gate asks.  A `SAFETY:` comment moved below the block,
or separated from it by a statement, is refused.

## Two disciplines, one enforced

`SAFETY` is required of every site: a justification is something a human writes
about any unsafe operation, and demanding it costs nothing correct.

`(ARM ARM <section>)` is **reported, not enforced**.  Requiring it everywhere
would demand an architecture-manual citation of a raw-pointer dereference that
touches no hardware, and deciding *which* sites touch hardware needs the body —
the analysis-instead-of-a-contract shape this project has retired twice.  So the
citation count is a diagnostic beside the enforced figure, exactly as
`STORE_READ_SPEC` sits beside `STORE_READ_CODE`.

## The floor is an inventory

`scripts/unsafe_justification_baseline.json` pins the unjustified sites per
`(file, enclosing declaration)` **with counts**, reconciled in both directions: a
key the baseline does not name fails outright, a key it names may only fall, and
a key that has gone to zero and stayed in the baseline is reported as stale.  A
set of keys alone cannot see a second unjustified site in a file that already has
one, and a count alone cannot see the first in a file that had none, so the floor
has to be both — the shape `scripts/identifier_naming_baseline.json` and
`scripts/store_reader_hygiene_baseline.txt` already use.

## Which view answers which question

Site *positions* come from the comment-blanked, string-blanked view
(`rust_code_view.code_no_strings`), so an `unsafe {` inside a string literal or a
comment is not a site.  The justification *text* is read from the raw file at the
same byte offsets, because the subject there genuinely is the comment.  Both
views are byte-aligned, which is what lets one walk use both.

    scripts/check_unsafe_block_justifications.py            # check
    scripts/check_unsafe_block_justifications.py --rows     # the inventory
    scripts/check_unsafe_block_justifications.py --update   # re-anchor
    scripts/check_unsafe_block_justifications.py --self-test
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import rust_code_view  # noqa: E402

REPO = Path(__file__).resolve().parent.parent
BASELINE = REPO / "scripts" / "unsafe_justification_baseline.json"

# An `unsafe` block, or an `unsafe fn` DECLARATION — `unsafe fn` followed by a
# name.  `unsafe impl` and `unsafe trait` are not operations and carry their own
# review story, and neither is `unsafe fn(u8) -> T`: that is a function-pointer
# **type**, which `tests::register_signature_pinned` uses to pin an ABI.  A type
# performs nothing, so demanding a justification of one is a scanner matching a
# keyword rather than asking about an operation.
UNSAFE_SITE = re.compile(r"\bunsafe\s*(?:\{|fn\s+(?:r#)?[A-Za-z_])")

# **The two kinds ask different questions, so the gate asks each its own.**
#
# An `unsafe` BLOCK *discharges* an obligation locally, and Rust's idiom for
# that — the one `clippy::undocumented_unsafe_blocks` reads — is a `// SAFETY:`
# comment on the block.  An `unsafe fn` DECLARATION *publishes* one to its
# callers, and Rust's idiom for that is a `# Safety` doc section.  A gate that
# demanded `// SAFETY:` of a declaration would report every correctly documented
# `unsafe fn` in the tree, which is a scanner asking the wrong question rather
# than a discipline the code fails.
SAFETY_BLOCK = re.compile(r"//[/!]?\s*SAFETY\b|/\*+\s*SAFETY\b", re.IGNORECASE)
SAFETY_DECL = re.compile(r"^\s*(?://[/!]|\*)?\s*#+\s*Safety\b", re.IGNORECASE | re.MULTILINE)
ARM_ARM = re.compile(r"\(ARM ARM [A-Z][0-9]+(?:\.[0-9]+)*\)")


def justified(run: str, is_declaration: bool) -> bool:
    """Does this run carry the justification its site kind calls for?"""
    if is_declaration:
        return bool(SAFETY_DECL.search(run) or SAFETY_BLOCK.search(run))
    return bool(SAFETY_BLOCK.search(run))


def justification_run(raw: str, view: str, at: int) -> str:
    """The contiguous comment-and-attribute run immediately above `at`.

    Walks upward line by line while each line is blank in the code view (a
    whole-line comment), is blank outright, or is an attribute, and stops at the
    first line carrying code.  Returns the RAW text of that run — the question is
    what a reviewer reads, so the answer comes from the real file.
    """
    line_start = raw.rfind("\n", 0, at) + 1
    # A trailing comment on the site's own line counts: `unsafe { … } // SAFETY: …`
    # does not, but `// SAFETY: …` before it on the same line does.
    run = [raw[line_start:at]]
    idx = line_start
    while idx > 0:
        prev_end = idx - 1
        prev_start = raw.rfind("\n", 0, prev_end) + 1
        raw_line = raw[prev_start:prev_end]
        view_line = view[prev_start:prev_end]
        stripped_code = view_line.strip()
        stripped_raw = raw_line.strip()
        is_comment_only = stripped_raw != "" and stripped_code == ""
        is_attribute = stripped_code.startswith("#[") or stripped_code.startswith("#![")
        # A blank line is TRANSPARENT: a doc block separated from its attribute
        # list by one is ordinary formatting, and treating it as a break would
        # refuse the tree's own convention.  What breaks the run is a line
        # carrying CODE — that is the relation, since nothing may execute
        # between the justification and the operation it justifies.
        is_blank = stripped_raw == ""
        if is_comment_only or is_attribute or is_blank:
            run.append(raw_line)
            idx = prev_start
            continue
        break
    return "\n".join(reversed(run))


UNSAFE_FN_NAME = re.compile(r"\bunsafe\s+fn\s+(r#)?([A-Za-z_][A-Za-z0-9_]*)")


def sites(path: Path):
    """Yield (offset, enclosing declaration, justification run) per unsafe site.

    An `unsafe fn` DECLARATION is keyed by its own name, not by the scope it sits
    in: its `unsafe` token is outside every function body, so keying it by the
    enclosing scope would collapse every `unsafe fn` of a file onto one key — a
    cardinality one level up, which cannot see one declaration gaining a site
    while another gives one up.
    """
    raw = path.read_text(encoding="utf-8")
    view = rust_code_view.code_no_strings(raw)
    aligned = rust_code_view.code(raw)
    bodies = rust_code_view.fn_bodies(raw)
    # **The run is the lines immediately above the site, and a line carrying
    # CODE ends it.**  An earlier cut anchored the run to the enclosing
    # top-level statement instead, on the reasoning that `let x =\n    unsafe
    # { … };` puts the justification above the statement rather than above the
    # token.  That is true, and it is the *code* that should move: Rust's own
    # convention — and the one `clippy::undocumented_unsafe_blocks` reads — puts
    # the `// SAFETY:` on the block.  Resolving it in the scanner instead buys
    # four sites and costs the relation its sharpness, since a statement can be
    # long and its run then sits arbitrarily far from the operation.
    for m in UNSAFE_SITE.finditer(view):
        named = UNSAFE_FN_NAME.match(view, m.start())
        if named:
            decl = named.group(2)
        else:
            decl = rust_code_view.enclosing_fn(raw, m.start(), bodies) or "<module scope>"
        yield (m.start(), decl, justification_run(raw, aligned, m.start()),
               named is not None)


def census(root: Path):
    """(unjustified inventory, total sites, sites carrying an ARM ARM citation)."""
    inventory: dict[str, int] = {}
    total = 0
    cited = 0
    for path in sorted(root.glob("*/src/**/*.rs")):
        rel = str(path.relative_to(REPO))
        for _off, decl, run, is_decl in sites(path):
            total += 1
            if ARM_ARM.search(run):
                cited += 1
            if not justified(run, is_decl):
                inventory[f"{rel}|{decl}"] = inventory.get(f"{rel}|{decl}", 0) + 1
    return inventory, total, cited


def reconcile(current: dict[str, int], baseline: dict[str, int]) -> list[str]:
    """Where the inventory and the floor disagree; `[]` when the floor holds."""
    problems = []
    for key, count in sorted(current.items()):
        if key not in baseline:
            problems.append(
                f"NEW unjustified unsafe site: {key} ({count}).  Every `unsafe` block and "
                f"`unsafe fn` needs a `// SAFETY:` comment in the contiguous comment run "
                f"immediately above it — what a reviewer reads before the operation."
            )
        elif count > baseline[key]:
            problems.append(
                f"GREW: {key} has {count} unjustified unsafe site(s), baseline {baseline[key]}"
            )
    for key, count in sorted(baseline.items()):
        if current.get(key, 0) > count:
            continue
        if current.get(key, 0) == 0 and count > 0:
            problems.append(
                f"STALE floor entry: {key} is fully justified now (baseline {count}).  "
                f"Re-anchor with --update; a floor above the tree reads like coverage."
            )
    return problems


# ---------------------------------------------------------------------------
# Self-test.  Every mutation is TOKEN-PRESERVING: it keeps the `SAFETY` comment
# the tree has and breaks the RELATION the gate asserts, because a fixture that
# mutated by deletion is satisfied by any presence check — which is precisely
# what the five-line window this gate replaces would have been.
# ---------------------------------------------------------------------------
_CASES = [
    ("justified", True, """
fn f() {
    // SAFETY: the pointer is valid for the lifetime of the call.
    unsafe { g() }
}
"""),
    ("the comment is BELOW the block", False, """
fn f() {
    unsafe { g() }
    // SAFETY: the pointer is valid for the lifetime of the call.
}
"""),
    ("a statement separates the comment from the block", False, """
fn f() {
    // SAFETY: the pointer is valid for the lifetime of the call.
    let x = h();
    unsafe { g(x) }
}
"""),
    ("the token is inside a string literal", False, """
fn f() {
    let msg = "SAFETY: not a justification";
    unsafe { g(msg) }
}
"""),
    ("an attribute between the comment and the block is fine", True, """
fn f() {
    // SAFETY: the pointer is valid for the lifetime of the call.
    #[allow(clippy::undocumented_unsafe_blocks)]
    unsafe { g() }
}
"""),
    ("an `unsafe fn` needs one too", False, """
// A declaration with no justification at all.
unsafe fn f() {}
"""),
    ("a justified `unsafe fn`", True, """
// SAFETY: the caller holds the lock this reads.
unsafe fn f() {}
"""),
    ("an `unsafe {` inside a comment is not a site", True, """
fn f() {
    // Historically this was `unsafe { g() }`; it no longer is.
    h()
}
"""),
    ("a doc-comment justification counts", True, """
fn f() {
    /// SAFETY: the pointer is valid for the lifetime of the call.
    unsafe { g() }
}
"""),
    ("a block-comment justification counts", True, """
fn f() {
    /* SAFETY: the pointer is valid for the lifetime of the call. */
    unsafe { g() }
}
"""),
    # The two kinds, and their two idioms.
    ("an `unsafe fn` documented with a `# Safety` section", True, """
/// Reads the register bank.
///
/// # Safety
///
/// The caller holds the per-core lock.
#[inline]
unsafe fn f() {}
"""),
    ("...and a `# Safety` section does NOT justify a block", False, """
fn f() {
    // # Safety
    // The caller holds the per-core lock.
    unsafe { g() }
}
"""),
    ("a blank line between the doc block and the attributes is transparent", True, """
/// # Safety
///
/// The caller holds the per-core lock.

#[inline]
unsafe fn f() {}
"""),
    ("an `unsafe fn` with a doc comment that never mentions safety", False, """
/// Reads the register bank.  Fast.
#[inline]
unsafe fn f() {}
"""),
    # A keyword in a TYPE performs nothing.
    ("an `unsafe fn` POINTER TYPE is not a site", True, """
fn pin_the_abi() {
    let _: unsafe fn(u8, Handler) = register;
}
"""),
    ("`unsafe impl` is not a site", True, """
unsafe impl Send for T {}
"""),
]


def _self_test() -> int:
    import tempfile

    failures = 0
    for name, expect_ok, src in _CASES:
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / "fixture.rs"
            p.write_text(src, encoding="utf-8")
            found = list(sites(p))
            has_site = bool(found)
            ok = all(justified(r, d) for _o, _n, r, d in found) if has_site else True
            # A case expecting rejection must HAVE a site; one that has none is
            # inert, and an inert case reads like coverage while asserting
            # nothing.
            if not expect_ok and not has_site:
                print(f"  SELF-TEST BROKEN: '{name}' found no unsafe site to judge")
                failures += 1
                continue
            if ok != expect_ok:
                verdict = "accepted" if ok else "rejected"
                want = "accepted" if expect_ok else "rejected"
                print(f"  SELF-TEST FAIL: '{name}' was {verdict}, want {want}")
                failures += 1
            else:
                print(f"  OK   self-test '{name}' ({'accept' if expect_ok else 'reject'})")
    # The reconciliation, on synthetic inventories.
    checks = [
        ("a clean tree passes", reconcile({"a|f": 1}, {"a|f": 1}), True),
        ("a NEW key fails", reconcile({"a|f": 1, "b|g": 1}, {"a|f": 1}), False),
        ("a GROWN key fails", reconcile({"a|f": 2}, {"a|f": 1}), False),
        ("a key that fell passes", reconcile({"a|f": 1}, {"a|f": 2}), True),
        ("a key gone to zero is reported stale", reconcile({}, {"a|f": 1}), False),
        ("empty and empty agree", reconcile({}, {}), True),
    ]
    for name, problems, want_clean in checks:
        if (not problems) != want_clean:
            print(f"  SELF-TEST FAIL: reconciliation '{name}'")
            failures += 1
        else:
            print(f"  OK   self-test '{name}'")
    if failures:
        print(f"unsafe-justification gate self-test FAILED ({failures})")
        return 1
    print(f"unsafe-justification gate self-test passed "
          f"({len(_CASES)} site cases, {len(checks)} reconciliation cases).")
    return 0


def main(argv: list[str]) -> int:
    if "--self-test" in argv:
        return _self_test()
    inventory, total, cited = census(REPO / "rust")
    if "--rows" in argv:
        for key, count in sorted(inventory.items()):
            print(f"UNJUSTIFIED_UNSAFE_SITE={key}|{count}")
        print(f"UNSAFE_SITES_TOTAL={total}")
        print(f"UNSAFE_SITES_UNJUSTIFIED={sum(inventory.values())}")
        print(f"UNSAFE_SITES_ARM_ARM_CITED={cited}  (diagnostic, not enforced)")
        return 0
    if "--update" in argv:
        BASELINE.write_text(json.dumps(inventory, indent=2, sort_keys=True) + "\n",
                            encoding="utf-8")
        print(f"re-anchored: {len(inventory)} key(s), "
              f"{sum(inventory.values())} unjustified site(s) of {total}")
        return 0
    if not BASELINE.exists():
        print(f"FAIL: baseline not found: {BASELINE.relative_to(REPO)}", file=sys.stderr)
        print("      create it with --update", file=sys.stderr)
        return 1
    baseline = json.loads(BASELINE.read_text(encoding="utf-8"))
    problems = reconcile(inventory, baseline)
    if problems:
        for p in problems:
            print(f"FAIL: {p}", file=sys.stderr)
        return 1
    justified = total - sum(inventory.values())
    print(f"PASS: {justified}/{total} unsafe sites carry a `// SAFETY:` justification in the "
          f"comment run above them; {sum(inventory.values())} pinned at or below the floor "
          f"across {len(baseline)} key(s).  {cited}/{total} also cite the ARM ARM "
          f"(diagnostic).")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
