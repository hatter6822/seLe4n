#!/usr/bin/env python3
"""Witnesses for the scenario-traceability manifest machinery (v0.35.109).

Every case that must REJECT is a mutation that **keeps the token and breaks the
relation** — `CLAUDE.md`'s rule, and the reason the drift this machinery exists
to catch shipped: the manifest rows were byte-perfect and the suite stopped
printing what they named, so any presence check over the fixture survived it.
Each check therefore carries at least one *preserving* case, and the accepting
cases are here too, because a checker that refuses everything reads exactly like
one that decides.

At `v0.35.111` this suite grew the cases that show the machinery ITSELF had
shipped three instances of the class it was written to close, and the case lists
are why they were not caught here: every case was drawn from the drift that had
already happened, so the boundary was probed and the property was not.  The
three were a fixture-index membership test that searched the JOINED table text
(so a name satisfied it whenever any cell quoted a longer one containing it) and
ran only over the directory (so a row naming a deleted file was never
inspected); a classifier whose parse failure was a silent `continue` (so a file
with a valid `# Suite:` header and one malformed row was swept as golden output
while the gate reported PASS); and a fragment relation with no binding to its own
row (so a cross-wired row witnessed another scenario and passed).  Each now has a
case that keeps every token, and the accepting controls beside them are what stop
the fixes from reading as refusals.

At `v0.35.116` it grew three more of the same kind.  A manifest declares ONE
producer and `suite is not None` is a presence check where the property is
"exactly one", so a copied second `# Suite:` header redirected every fragment
check to another executable.  A fragment's id was searched for anywhere in the
fragment rather than at a LABEL position, so a row whose evidence is another
scenario's assertion passed while still carrying its own id as prose.  And the
README's `Used by` column — which that file calls "the only place a reader learns
which gate compares a given fixture" — was read by nothing, so a new golden
fixture could be listed, hashed and compared by no gate at all with every fixture
gate green.  Each new case keeps every token and moves only the relation: a second
valid header, an id from the label into the prose beside it, a fixture name from
code into a comment.
"""

from __future__ import annotations

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
SCRIPT = REPO_ROOT / "scripts" / "scenario_catalog.py"
FIXTURES = REPO_ROOT / "tests" / "fixtures"

sys.path.insert(0, str(REPO_ROOT / "scripts"))
import scenario_catalog as sc  # noqa: E402

# The manifest the tree actually ships, in miniature.
MANIFEST = """\
# Robin Hood suite scenario traceability fixture
# Format: SCENARIO_ID | SUBSYSTEM | expected_trace_fragment
# Suite: robin_hood_suite

RH-001 | RobinHood | robin-hood check passed [RH-001a empty get? returns none]
RH-002 | RobinHood | robin-hood check passed [RH-002a insert then get]
"""

OUTPUT = """\
=== Robin Hood Hash Table Test Suite ===
robin-hood check passed [RH-001a empty get? returns none]
robin-hood check passed [RH-001b empty size is 0]
robin-hood check passed [RH-002a insert then get]
"""

# A trace fixture: golden suite output, never a manifest.
TRACE = """\
[PIP-005] A5 post-dispatch invariants preserved (29 checks)
[SCO-020b] donation holder resolves
"""


def run(*args: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        [sys.executable, str(SCRIPT), *args],
        cwd=REPO_ROOT, capture_output=True, text=True,
    )


class TestManifestClassification(unittest.TestCase):
    """`classify_fixture` decides by INTENT and then by well-formedness.

    Intent is a `# Suite:` declaration or content that is entirely rows; given
    it, anything short of a well-formed manifest is an error.  A trace fixture —
    no declaration, lines that are not rows — is the only silent skip, and these
    cases pin that it stays one.
    """

    def test_accepts_a_manifest(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "m.expected"
            p.write_text(MANIFEST, encoding="utf-8")
            shape = sc.classify_fixture(p)
            self.assertIsNone(shape.error)
            m = shape.manifest
            self.assertIsNotNone(m)
            assert m is not None
            self.assertEqual(m.suite, "robin_hood_suite")
            self.assertEqual([r[0] for r in m.rows], ["RH-001", "RH-002"])

    def test_rejects_a_trace_fixture(self) -> None:
        """A golden-output fixture must never be swept as a manifest.

        Preserving: the file is real fixture content, not an emptied stub.  It is
        a SKIP rather than an error, which is the one correct default branch
        here: it declares no producer and its lines are not rows, so nothing
        about it claims to be a manifest.
        """
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "t.expected"
            p.write_text(TRACE, encoding="utf-8")
            shape = sc.classify_fixture(p)
            self.assertTrue(shape.is_trace_fixture)

    def test_a_declared_manifest_with_one_bad_line_is_an_ERROR(self) -> None:
        """THE decisive case for the silent skip, and it keeps every token.

        Preserving: the `# Suite:` header and both rows survive byte for byte;
        one line of suite output is appended.  The superseded classifier answered
        "not a manifest" and `discover_manifests` did a bare `continue`, so this
        file was swept as golden output — its fragments never checked — while
        `manifest_count` stayed nonzero and the gate printed PASS.  A file that
        DECLARES a producer is never a trace fixture.
        """
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "m.expected"
            p.write_text(MANIFEST + "robin-hood check passed [RH-003a]\n",
                         encoding="utf-8")
            shape = sc.classify_fixture(p)
            self.assertIsNone(shape.manifest)
            self.assertIsNotNone(shape.error)
            assert shape.error is not None
            self.assertIn("declares `# Suite: robin_hood_suite`", shape.error)
            self.assertIn("is not a row", shape.error)
            self.assertFalse(shape.is_trace_fixture)

    def test_a_declared_manifest_with_no_rows_is_an_ERROR(self) -> None:
        """Preserving: the header block is untouched; only the rows are gone.

        `check-fragments` over a rowless manifest passes vacuously, so dropping
        the file would trade a visible failure for a silent one.
        """
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "m.expected"
            p.write_text("# Suite: robin_hood_suite\n# Format: ...\n",
                         encoding="utf-8")
            shape = sc.classify_fixture(p)
            self.assertIsNone(shape.manifest)
            self.assertIsNotNone(shape.error)
            assert shape.error is not None
            self.assertIn("no `SCENARIO_ID", shape.error)

    def test_a_second_suite_declaration_is_an_ERROR(self) -> None:
        """A manifest declares ONE producer, and `suite is not None` is a presence
        check where the property is "exactly one".

        Preserving: both headers are valid, every row is intact, and the file
        still parses — only the relation is broken.  Under the superseded
        last-one-wins reading this classified as a well-formed manifest whose
        producer was `other_suite`, so every fragment check ran against the wrong
        executable and passed whenever that one happened to emit the listed
        fragments, while the real producer was never built.
        """
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "m.expected"
            p.write_text(MANIFEST + "# Suite: other_suite\n", encoding="utf-8")
            shape = sc.classify_fixture(p)
            self.assertIsNone(shape.manifest)
            self.assertIsNotNone(shape.error)
            assert shape.error is not None
            self.assertIn("a second `# Suite:` declaration", shape.error)
            # The error names BOTH producers and both lines, because which one a
            # maintainer meant is the whole content of the failure.
            self.assertIn("other_suite", shape.error)
            self.assertIn("robin_hood_suite", shape.error)

    def test_a_duplicated_suite_declaration_is_an_ERROR(self) -> None:
        """Even naming the same suite: a copied header has no effect on which
        executable runs and is still a malformed manifest, and refusing both is
        the fail-closed direction — a maintainer deletes the duplicate rather than
        the gate deciding which of two declarations it prefers."""
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "m.expected"
            p.write_text(MANIFEST + "# Suite: robin_hood_suite\n", encoding="utf-8")
            shape = sc.classify_fixture(p)
            self.assertIsNone(shape.manifest)
            self.assertIsNotNone(shape.error)
            assert shape.error is not None
            self.assertIn("a second `# Suite:` declaration", shape.error)

    def test_an_undeclared_file_with_one_bad_line_is_still_a_trace_fixture(self) -> None:
        """The control for the case above: intent is what changes the verdict.

        Same content, `# Suite:` removed.  Without a declaration a file whose
        lines are not all rows claims nothing, so classifying it as a manifest
        would run a trace fixture against a producer it never named — which is
        the fail-CLOSED direction of the same question and must stay open.
        """
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "t.expected"
            p.write_text(
                MANIFEST.replace("# Suite: robin_hood_suite\n", "")
                + "robin-hood check passed [RH-003a]\n",
                encoding="utf-8")
            self.assertTrue(sc.classify_fixture(p).is_trace_fixture)

    def test_rows_without_a_producer_fail_discovery(self) -> None:
        """Preserving: the rows and the format header are untouched; only the
        `# Suite:` declaration is gone.

        Dropping such a manifest silently would make the swept set smaller than
        the manifest set while the gate still printed PASS — `CLAUDE.md`'s
        "a scanner's default branch is a decision".
        """
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "m.expected"
            p.write_text(MANIFEST.replace("# Suite: robin_hood_suite\n", ""),
                         encoding="utf-8")
            manifests, errors = sc.discover_manifests(Path(d))
            self.assertEqual(manifests, [])
            self.assertEqual(len(errors), 1)
            self.assertIn("declares no producer", errors[0])

    def test_discovery_reports_a_declared_manifest_that_does_not_parse(self) -> None:
        """The routing half of the decisive case: the error reaches the caller.

        Preserving: a well-formed manifest sits beside it, so the sweep is not
        empty — the superseded code returned that one manifest and no error at
        all, which is a PASS over an unchecked file.
        """
        with tempfile.TemporaryDirectory() as d:
            (Path(d) / "good.expected").write_text(MANIFEST, encoding="utf-8")
            (Path(d) / "bad.expected").write_text(
                MANIFEST + "robin-hood check passed [RH-003a]\n",
                encoding="utf-8")
            manifests, errors = sc.discover_manifests(Path(d))
            self.assertEqual([m.path.name for m in manifests], ["good.expected"])
            self.assertEqual(len(errors), 1)
            self.assertIn("bad.expected", errors[0])

    def test_discovery_reports_a_declared_manifest(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            (Path(d) / "m.expected").write_text(MANIFEST, encoding="utf-8")
            (Path(d) / "t.expected").write_text(TRACE, encoding="utf-8")
            manifests, errors = sc.discover_manifests(Path(d))
            self.assertEqual(errors, [])
            self.assertEqual([m.suite for m in manifests], ["robin_hood_suite"])


class TestFragmentRelation(unittest.TestCase):
    """The fragment column is a claim about a SUITE'S OUTPUT."""

    def _manifest(self, d: str, text: str = MANIFEST) -> sc.Manifest:
        p = Path(d) / "m.expected"
        p.write_text(text, encoding="utf-8")
        shape = sc.classify_fixture(p)
        assert shape.error is None, shape.error
        assert shape.manifest is not None
        return shape.manifest

    def test_accepts_emitted_fragments(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            self.assertEqual(sc.check_fragments(self._manifest(d), OUTPUT), [])

    def test_rejects_a_renamed_label(self) -> None:
        """THE decisive case, and the drift that actually shipped.

        Preserving: the manifest is byte-identical and every row is still
        parsed; the suite prints the same assertion under a label without its
        scenario id.  19 of 19 real fragments were in exactly this state.
        """
        with tempfile.TemporaryDirectory() as d:
            mutated = OUTPUT.replace("[RH-001a ", "[")
            errors = sc.check_fragments(self._manifest(d), mutated)
            self.assertEqual(len(errors), 1)
            self.assertIn("RH-001", errors[0])
            self.assertIn("not emitted", errors[0])

    def test_rejects_a_reordered_letter(self) -> None:
        """Preserving: the label keeps its scenario id and its text; only the
        assertion letter moves, which is what a reordered `expect` produces."""
        with tempfile.TemporaryDirectory() as d:
            mutated = OUTPUT.replace("[RH-001a ", "[RH-001c ")
            errors = sc.check_fragments(self._manifest(d), mutated)
            self.assertEqual(len(errors), 1)
            self.assertIn("RH-001", errors[0])

    def test_rejects_a_fragment_emitted_under_a_LONGER_scenario_id(self) -> None:
        """`v0.35.119`: containment credits the row to another scenario's line.

        The row's claim is that ITS scenario was traced.  A bare `fragment in
        output_text` is satisfied by whichever line happens to carry those bytes,
        so a fragment short enough to prefix another id — `RH-001` against an
        emitted `[RH-0010a insert then get]` — passed while scenario `RH-001`
        emitted nothing and could have been deleted from the suite outright.

        Preserving: the manifest is byte-identical, the row is parsed, and the
        fragment really does occur in the output.  Only which scenario's line
        carries it changes, which is exactly what the pre-fix containment could
        not see.
        """
        with tempfile.TemporaryDirectory() as d:
            manifest = self._manifest(
                d, "# Suite: robin_hood_suite\nRH-001 | RobinHood | RH-001\n")
            collision = "robin-hood check passed [RH-0010a insert then get]\n"
            # The pre-fix relation: the bytes are there.
            self.assertIn("RH-001", collision)
            errors = sc.check_fragments(manifest, collision)
            self.assertEqual(len(errors), 1)
            self.assertIn("RH-001", errors[0])
            self.assertIn("label position", errors[0])

    def test_accepts_that_same_row_against_its_OWN_line(self) -> None:
        """The control, so the rejection above is attributable to the collision
        and not to the row's shape.  A fragment that IS its own id is a
        well-formed row (`classify_fixture` accepts it), and it must pass when
        the scenario really is traced."""
        with tempfile.TemporaryDirectory() as d:
            manifest = self._manifest(
                d, "# Suite: robin_hood_suite\nRH-001 | RobinHood | RH-001\n")
            own = "robin-hood check passed [RH-001a empty get? returns none]\n"
            self.assertEqual(sc.check_fragments(manifest, own), [])

    def test_accepts_the_unbracketed_label_shape(self) -> None:
        """The second live manifest quotes the label without brackets, and
        `expectCond` emits `{tag} check passed [{label}]` — so the id sits
        immediately inside a `[` in the OUTPUT even though the fragment starts
        with it.  Kept because asking the label relation of the output line is
        what makes that work, and a narrowing that broke it would pass every
        case above."""
        with tempfile.TemporaryDirectory() as d:
            manifest = self._manifest(
                d, "# Suite: two_phase_arch_suite\n"
                   "TPH-001 | TwoPhaseArch | TPH-001a empty builder valid\n")
            emitted = "two-phase check passed [TPH-001a empty builder valid]\n"
            self.assertEqual(sc.check_fragments(manifest, emitted), [])

    def test_a_rowless_manifest_cannot_pass_vacuously(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            empty = sc.Manifest(Path(d) / "m.expected", "robin_hood_suite", [])
            errors = sc.check_fragments(empty, OUTPUT)
            self.assertEqual(len(errors), 1)
            self.assertIn("vacuously", errors[0])

    def test_rejects_a_cross_wired_row(self) -> None:
        """THE decisive case for the missing binding, and it keeps every token.

        Preserving: both ids stay in the ID column, both fragments are real lines
        the suite emits, and the suite output is byte-identical — only the PAIRING
        is broken, `RH-001`'s row now naming `RH-002`'s assertion.  A containment
        test over the output passes: the fragment IS emitted.  What it stops being
        is evidence that `RH-001` is traced, so `RH-001` could be deleted from the
        suite entirely with this gate still green.

        The verdict is `classify_fixture`'s, not `check_fragments`': a cross-wired
        row is a malformed manifest rather than a failed comparison, so it fails
        before any suite is built.
        """
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "m.expected"
            p.write_text(
                MANIFEST.replace(
                    "RH-001 | RobinHood | robin-hood check passed "
                    "[RH-001a empty get? returns none]",
                    "RH-001 | RobinHood | robin-hood check passed "
                    "[RH-002a insert then get]"),
                encoding="utf-8")
            shape = sc.classify_fixture(p)
            self.assertIsNone(shape.manifest)
            self.assertIsNotNone(shape.error)
            assert shape.error is not None
            self.assertIn("does not name RH-001", shape.error)
            # The superseded relation passed this: the fragment is emitted.
            self.assertIn("[RH-002a insert then get]", OUTPUT)

    def test_the_id_must_sit_at_a_label_position(self) -> None:
        """A region is not a position: the id must be at the start of the fragment
        or immediately inside a `[`, not anywhere in it.

        Preserving: the row's own id is still IN its fragment and the fragment is
        still a line the suite emits — what moves is where the id sits, from the
        label to the prose beside it, so the evidence now witnesses `RH-002`.  The
        previous fix narrowed the id's SPELLING (no prefix collisions) and left
        the position unasked.

        The two accepting forms are the ones the shipped manifests use, measured
        rather than chosen: the label IS the fragment, or the label is bracketed.
        """
        # Rejected: the id is present, and not at a label position.
        self.assertFalse(sc.fragment_names_scenario(
            "RH-001", "[RH-002a insert then get] (covers RH-001)"))
        self.assertFalse(sc.fragment_names_scenario(
            "RH-001", "robin-hood check passed for RH-001"))
        # Accepted: both live forms, and the bracketed one with prose before it.
        self.assertTrue(sc.fragment_names_scenario(
            "RH-001", "robin-hood check passed [RH-001a empty get? returns none]"))
        self.assertTrue(sc.fragment_names_scenario(
            "TPH-001", "TPH-001a empty builder valid"))
        self.assertTrue(sc.fragment_names_scenario("RH-001", "[RH-001] ok"))

    def test_an_id_is_not_a_prefix_of_a_longer_one(self) -> None:
        """`RH-001` must not be satisfied by `RH-0010a` — the same defect, one
        character down, which a bare `in` test has."""
        self.assertTrue(sc.fragment_names_scenario("RH-001", "RH-001a insert"))
        self.assertTrue(sc.fragment_names_scenario("RH-001", "[RH-001] ok"))
        self.assertTrue(sc.fragment_names_scenario("RH-001", "RH-001 plain"))
        self.assertTrue(
            sc.fragment_names_scenario("TPH-001", "TPH-001a empty builder valid"))
        self.assertFalse(sc.fragment_names_scenario("RH-001", "RH-0010a insert"))
        self.assertFalse(sc.fragment_names_scenario("RH-001", "RH-002a insert"))
        self.assertFalse(sc.fragment_names_scenario("RH-001", "RH-001-b insert"))


class TestFixtureIndex(unittest.TestCase):
    """The README's `## Files` table must enumerate the fixture directory.

    It is hand-written, so it is an enumeration standing in for a derivation, and
    it had two omissions at `v0.35.109`.
    """

    TABLE = """\
## Files

| Fixture | Hash | Used by |
| --- | --- | --- |
| `a.expected` | `a.expected.sha256` | gate A |
| `b.txt` | *(none)* | gate B |
"""

    def _tree(self, d: str, *names: str, readme: str | None = None) -> Path:
        root = Path(d)
        for n in names:
            (root / n).write_text("x\n", encoding="utf-8")
        (root / "README.md").write_text(
            self.TABLE if readme is None else readme, encoding="utf-8")
        return root

    def test_accepts_a_complete_table(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            root = self._tree(d, "a.expected", "a.expected.sha256", "b.txt")
            self.assertEqual(
                sc.check_fixture_index(root, root / "README.md", exempt={}), [])

    def test_rejects_an_unlisted_file(self) -> None:
        """Preserving: the table is intact and every listed file still exists;
        one more fixture is present, which is exactly how the two real omissions
        arose."""
        with tempfile.TemporaryDirectory() as d:
            root = self._tree(d, "a.expected", "a.expected.sha256", "b.txt",
                              "c.expected")
            errors = sc.check_fixture_index(root, root / "README.md", exempt={})
            self.assertEqual(len(errors), 1)
            self.assertIn("c.expected", errors[0])

    def test_a_prose_mention_is_not_a_table_row(self) -> None:
        """Preserving: the file IS named in the README — in prose.

        A mention tells a reader nothing about which gate compares the fixture,
        so accepting one would be a presence check standing in for the relation
        the table asserts.
        """
        with tempfile.TemporaryDirectory() as d:
            root = self._tree(
                d, "a.expected", "a.expected.sha256", "b.txt", "c.expected",
                readme=self.TABLE + "\nSee also `c.expected`, which is nice.\n")
            errors = sc.check_fixture_index(root, root / "README.md", exempt={})
            self.assertEqual(len(errors), 1)
            self.assertIn("c.expected", errors[0])

    def test_an_exempt_file_needs_no_row(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            root = self._tree(d, "a.expected", "a.expected.sha256", "b.txt",
                              "extra.yaml")
            self.assertEqual(
                sc.check_fixture_index(root, root / "README.md",
                                       exempt={"extra.yaml": "a reason"}), [])

    def test_a_stale_exemption_fails(self) -> None:
        """An exemption nobody reconciles reads exactly like coverage."""
        with tempfile.TemporaryDirectory() as d:
            root = self._tree(d, "a.expected", "a.expected.sha256", "b.txt")
            errors = sc.check_fixture_index(
                root, root / "README.md", exempt={"gone.yaml": "a reason"})
            self.assertEqual(len(errors), 1)
            self.assertIn("stale FIXTURE_INDEX_EXEMPT", errors[0])

    def test_a_substring_mention_is_not_a_row(self) -> None:
        """THE decisive case for the substring membership test.

        Preserving: `c.expected` really does occur in the table — inside another
        row's `xc.expected` and its companion — and that table is **fully
        well-formed**, so the case survives the `v0.35.136` row-shape contract
        rather than being refused before the membership question is asked.  The
        superseded check joined the table's lines and asked `name not in rows`,
        so `c.expected` passed while no row said which gate compares it, and an
        omission of exactly this shape is invisible.

        (Until `v0.35.136` this case was written with a `| *(pending)* |
        `c.expected.sha256` |` row, which reproduced the same substring but is
        now malformed in its own right — a companion whose fixture has no row —
        and is covered by `TestFixtureRowShape`.  Restating it over a legal table
        is what keeps the two properties separately witnessed.)
        """
        with tempfile.TemporaryDirectory() as d:
            root = self._tree(
                d, "a.expected", "a.expected.sha256", "b.txt",
                "c.expected", "xc.expected", "xc.expected.sha256",
                readme=self.TABLE
                + "| `xc.expected` | `xc.expected.sha256` | gate C |\n")
            errors = sc.check_fixture_index(root, root / "README.md", exempt={})
            self.assertEqual(len(errors), 1)
            self.assertIn("c.expected:", errors[0])
            self.assertIn("not a row", errors[0])

    def test_rejects_a_row_naming_a_deleted_file(self) -> None:
        """The reverse direction, which the superseded check could not ask.

        Preserving: every present file is still a row and the table is otherwise
        untouched; one extra row names a file that is gone.  The loop ran over the
        DIRECTORY, so a stale row was never inspected — and a row is the only
        place a reader learns which gate reads a fixture, so one naming nothing
        describes a gate reading a file that does not exist.
        """
        with tempfile.TemporaryDirectory() as d:
            root = self._tree(
                d, "a.expected", "a.expected.sha256", "b.txt",
                readme=self.TABLE + "| `gone.expected` | *(none)* | gate G |\n")
            errors = sc.check_fixture_index(root, root / "README.md", exempt={})
            self.assertEqual(len(errors), 1)
            self.assertIn("gone.expected", errors[0])
            self.assertIn("absent from the directory", errors[0])

    def test_a_second_table_does_not_declare_a_fixture(self) -> None:
        """Preserving: `c.expected` is backticked in a real markdown table cell.

        The read is scoped to the `## Files` section, so a table of gates cannot
        satisfy a fixture's membership — the derived-domain rule applied to which
        table the claim is about.
        """
        with tempfile.TemporaryDirectory() as d:
            root = self._tree(
                d, "a.expected", "a.expected.sha256", "b.txt", "c.expected",
                readme=self.TABLE + "\n## Gates\n\n| Gate | Reads |\n"
                       "| --- | --- |\n| `g.sh` | `c.expected` |\n")
            errors = sc.check_fixture_index(root, root / "README.md", exempt={})
            self.assertEqual(len(errors), 1)
            self.assertIn("c.expected", errors[0])
            self.assertIn("not a row", errors[0])

    def test_a_file_classified_both_ways_fails(self) -> None:
        """One file, two classifications, so it has none.

        Preserving: the exemption carries a reason and the row is well formed —
        each half is individually valid, and their coexistence is the defect.
        """
        with tempfile.TemporaryDirectory() as d:
            root = self._tree(d, "a.expected", "a.expected.sha256", "b.txt")
            errors = sc.check_fixture_index(
                root, root / "README.md", exempt={"b.txt": "a reason"})
            self.assertEqual(len(errors), 1)
            self.assertIn("classified BOTH", errors[0])

    def test_a_missing_files_heading_is_an_error(self) -> None:
        """Fail closed on input the scanner cannot read.

        Preserving: the table itself is byte-identical; only the heading the read
        is scoped to is renamed.  Answering "no files are declared" would report
        every fixture as unlisted, which names the wrong cause; answering
        "nothing to check" would be a silent pass.
        """
        with tempfile.TemporaryDirectory() as d:
            root = self._tree(
                d, "a.expected", "a.expected.sha256", "b.txt",
                readme=self.TABLE.replace("## Files", "## Fixture inventory"))
            errors = sc.check_fixture_index(root, root / "README.md", exempt={})
            self.assertEqual(len(errors), 1)
            self.assertIn("no `## Files` section", errors[0])

    def test_the_hash_column_counts_as_a_row(self) -> None:
        """The accepting control for the cell parse: a `.sha256` companion is
        declared by its own cell of its fixture's row, not by a row of its own."""
        with tempfile.TemporaryDirectory() as d:
            root = self._tree(d, "a.expected", "a.expected.sha256", "b.txt")
            declared, errors = sc.fixture_table_filenames(root / "README.md")
            self.assertEqual(errors, [])
            self.assertEqual(declared,
                             {"a.expected", "a.expected.sha256", "b.txt"})

    def test_a_used_by_cell_declares_nothing(self) -> None:
        """Preserving: the `Used by` column quotes a real filename, as the real
        README's does (`scenario_registry.yaml`).  Only the first two cells
        declare, so prose cannot stand in for a row."""
        with tempfile.TemporaryDirectory() as d:
            root = self._tree(
                d, "a.expected", "a.expected.sha256", "b.txt",
                readme=self.TABLE.replace(
                    "| `b.txt` | *(none)* | gate B |",
                    "| `b.txt` | *(none)* | gate B, against `c.expected` |"))
            declared, _ = sc.fixture_table_filenames(root / "README.md")
            self.assertNotIn("c.expected", declared)

    def test_every_exemption_carries_a_reason(self) -> None:
        for name, reason in sc.FIXTURE_INDEX_EXEMPT.items():
            self.assertTrue(reason.strip(), name)

    def test_the_real_tree_is_complete(self) -> None:
        self.assertEqual(sc.check_fixture_index(FIXTURES, FIXTURES / "README.md"), [])


class TestFixtureRowShape(unittest.TestCase):
    """One fixture per row, and the `Hash` cell holds only its own companion.

    PR #897's review, `v0.35.136`.  The table answers two questions -- *which
    files does it enumerate* and *which gate reads each one* -- and they were
    asked of the same row in two different ways: `names` is the SET of filenames
    in the `Fixture` and `Hash` cells, which `check_fixture_index` accounts for,
    while `fixture` was `fixture_cell[0]`, a positional pick out of that set,
    which is the only file `check_fixture_consumers` validates.  So a row naming
    two fixtures, or an `.expected` sitting in the `Hash` cell, is accounted for
    whole and validated in part: a new golden fixture can be listed, hashed and
    compared by nothing with both gates green.

    The remedy is the canonical spelling every live row already uses -- measured
    before it was required, which is what makes it free -- so `names` is
    `{fixture}` or `{fixture, fixture + ".sha256"}` by construction and there is
    no second reading left to differ.  Each rejecting case below keeps a
    well-formed row beside the malformed one, so it fails on the shape rather
    than on the table being empty.
    """

    HEAD = "## Files\n\n| Fixture | Hash | Used by |\n| --- | --- | --- |\n"
    GOOD = "| `a.expected` | `a.expected.sha256` | `gates/r.lean` |\n"

    def _errors(self, d: str, table: str, *present: str) -> list[str]:
        root = Path(d)
        for n in present:
            (root / n).write_text("x\n", encoding="utf-8")
        readme = root / "README.md"
        readme.write_text(table, encoding="utf-8")
        return sc.check_fixture_index(root, readme, exempt={})

    def test_accepts_the_canonical_row(self) -> None:
        """The control: without it every rejecting case below is satisfied by a
        parser that refuses every row."""
        with tempfile.TemporaryDirectory() as d:
            self.assertEqual(
                self._errors(d, self.HEAD + self.GOOD,
                             "a.expected", "a.expected.sha256"), [])

    def test_accepts_a_row_with_no_hash_companion(self) -> None:
        """The second control, and a shape the live table really has: the QEMU
        boot fixture's `Hash` cell reads *(none -- see below)*, which names no
        file.  A contract requiring a companion would refuse it."""
        with tempfile.TemporaryDirectory() as d:
            self.assertEqual(
                self._errors(d, self.HEAD + "| `b.txt` | *(none)* | `g` |\n",
                             "b.txt"), [])

    def test_rejects_two_fixtures_in_one_row(self) -> None:
        """The reported defect, reproduced: both files are accounted for by
        `check_fixture_index` and only the first is ever handed to
        `check_fixture_consumers`, so the second is listed, hashed and validated
        against nothing."""
        with tempfile.TemporaryDirectory() as d:
            errors = self._errors(
                d,
                self.HEAD + self.GOOD
                + "| `foo.expected` `bar.expected` | | `gates/r.lean` |\n",
                "a.expected", "a.expected.sha256", "foo.expected",
                "bar.expected")
            self.assertTrue(errors)
            self.assertIn("declares 2 filename(s)", errors[0])

    def test_rejects_a_fixture_in_the_hash_cell(self) -> None:
        """The other half of the same defect: a name in the `Hash` cell is in
        `names`, so it is accounted for, and it is never the row's `fixture`, so
        no `Used by` claim is ever checked against it."""
        with tempfile.TemporaryDirectory() as d:
            errors = self._errors(
                d,
                self.HEAD + self.GOOD
                + "| `c.expected` | `d.expected` | `gates/r.lean` |\n",
                "a.expected", "a.expected.sha256", "c.expected", "d.expected")
            self.assertTrue(errors)
            self.assertIn("d.expected", errors[0])

    def test_rejects_a_checksum_declared_as_the_fixture(self) -> None:
        """A `.sha256` pins a fixture against itself and has no consumer of its
        own, so a row about one describes no comparison -- and its `Used by`
        cell would be validated as though it did."""
        with tempfile.TemporaryDirectory() as d:
            errors = self._errors(
                d, self.HEAD + self.GOOD
                + "| `e.expected.sha256` | | `gates/r.lean` |\n",
                "a.expected", "a.expected.sha256", "e.expected.sha256")
            self.assertTrue(errors)
            self.assertIn("checksum companion", errors[0])

    def test_rejects_a_companion_belonging_to_another_fixture(self) -> None:
        """Preserving: both cells hold exactly one name and both files exist --
        the companion simply is not this fixture's, so the `.sha256` gate pins
        it against a fixture no row validates."""
        with tempfile.TemporaryDirectory() as d:
            errors = self._errors(
                d, self.HEAD + self.GOOD
                + "| `f.expected` | `g.expected.sha256` | `gates/r.lean` |\n",
                "a.expected", "a.expected.sha256", "f.expected",
                "g.expected.sha256")
            self.assertTrue(errors)
            self.assertIn("f.expected.sha256", errors[0])

    def test_rejects_a_companion_named_twice(self) -> None:
        """The witness for the `len(hash_cell) > 1` conjunct, which `stray`
        cannot rescue: repeating the *right* companion leaves `stray` empty, so
        without the count the cell would pass.  A conjunct no case can reach is
        indistinguishable from a wrong one, and `names` being a set is exactly
        what hides a duplicated cell from every other check."""
        with tempfile.TemporaryDirectory() as d:
            errors = self._errors(
                d, self.HEAD + self.GOOD
                + "| `h.expected` | `h.expected.sha256` `h.expected.sha256` "
                  "| `gates/r.lean` |\n",
                "a.expected", "a.expected.sha256", "h.expected",
                "h.expected.sha256")
            self.assertTrue(errors)
            self.assertIn("h.expected.sha256", errors[0])

    def test_the_header_and_separator_declare_nothing(self) -> None:
        """They carry no backticked filename, so the shape contract has no
        subject there -- and a contract that fired on them would refuse every
        table."""
        with tempfile.TemporaryDirectory() as d:
            rows, errors = sc.fixture_table_rows(
                self._readme(d, self.HEAD + self.GOOD))
            self.assertEqual(errors, [])
            self.assertEqual([r.fixture for r in rows],
                             [None, None, "a.expected"])

    def test_the_consumer_check_also_refuses_a_malformed_row(self) -> None:
        """Both questions read `fixture_table_rows`, so the shape is enforced
        once and neither check can proceed on a row the other refused -- which is
        what stops the fix from closing one gate and leaving its sibling."""
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            errors, validated = sc.check_fixture_consumers(
                root,
                self._readme(
                    d, self.HEAD + "| `p.expected` `q.expected` | | `g` |\n"),
                repo_root=root)
            self.assertTrue(errors)
            self.assertEqual(validated, 0)

    def _readme(self, d: str, table: str) -> Path:
        readme = Path(d) / "README.md"
        readme.write_text(table, encoding="utf-8")
        return readme


class TestFixtureConsumers(unittest.TestCase):
    """The README's `Used by` column is a CLAIM, and it was read by nothing.

    The README says that table "is the only place a reader learns which gate
    compares a given fixture", and `check_fixture_index` parses the first two
    cells and ignores the third — so a new golden fixture could be listed, hashed
    and compared by no gate at all with every fixture gate green.  The same cut
    that wrote the sentence *measured* the column false for two fixtures, which is
    what makes this a claim rather than a hypothetical.

    The relation is per fixture KIND, because what "its consumer" means differs: a
    manifest is found by a glob that names no file, so its cell must name that
    gate; every other fixture is opened by name, so a path its cell names must
    exist and must mention it in CODE.
    """

    # A consumer BINDS the path and reads the name elsewhere, which is what all
    # five live consumers do.  The previous `READER` bound `g` and read it
    # nowhere -- a dead binding, and so the CONTROL for every rejecting case
    # below was itself the defect `v0.35.123` closes.  A witness that is the
    # defect proves the rejecting cases fail for the wrong reason.
    READER = ('def fixturePath : String := "a.expected"\n'
              'def main : IO Unit := IO.FS.readFile fixturePath\n')
    #: Bound and never read: the path is spelled and the file opens nothing.
    DEAD_BINDING = 'def unusedFixture := "a.expected"\ndef f : Nat := 0\n'
    #: A mention that binds NO name -- an argument -- which is a use by
    #: construction and must not need a second occurrence.
    INLINE = 'def main : IO Unit := compareAgainst "a.expected"\n'
    #: A STANDALONE LITERAL: it binds no name and nothing consumes it, so
    #: `consumer_bound_name` answers `None` and the pre-`v0.35.138` reading
    #: credited it as a use by construction.  This is what the file a gate
    #: *mentions* a fixture in without ever opening it looks like.
    STANDALONE = 'def f : Nat := 0\n"a.expected"\n'
    #: The control for it: the SAME bare position, with a callee in front, which
    #: is what makes the refusal about consumption rather than about the mention
    #: sitting at the start of a line.
    STANDALONE_CONSUMED = 'def f : Nat := 0\ncompareAgainst "a.expected"\n'
    SILENT = "def f : Nat := 0\n"
    COMMENTED = "-- the gate compares a.expected\ndef f : Nat := 0\n"
    MANIFEST_FIXTURE = (
        "# Suite: rh_suite\nRH-001 | RobinHood | RH-001a insert\n")

    def _case(self, d: str, fixture: str, content: str, cell: str,
              consumers: dict[str, str]) -> list[str]:
        root = Path(d)
        directory = root / "tests" / "fixtures"
        directory.mkdir(parents=True)
        (directory / fixture).write_text(content, encoding="utf-8")
        for rel, text in consumers.items():
            path = root / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text, encoding="utf-8")
        readme = directory / "README.md"
        readme.write_text(
            "## Files\n\n| Fixture | Hash | Used by |\n| --- | --- | --- |\n"
            f"| `{fixture}` | | {cell} |\n", encoding="utf-8")
        errors, _ = sc.check_fixture_consumers(directory, readme, repo_root=root)
        return errors

    def test_accepts_a_consumer_that_reads_the_fixture(self) -> None:
        """The control: without it, every rejecting case below is satisfied by a
        check that refuses everything."""
        with tempfile.TemporaryDirectory() as d:
            self.assertEqual(
                self._case(d, "a.expected", "x\n", "`gates/r.lean`",
                           {"gates/r.lean": self.READER}), [])

    def test_rejects_a_consumer_that_does_not_read_the_fixture(self) -> None:
        """Preserving: the cell names a path that exists and is a real gate-shaped
        file — it simply never opens this fixture, which is what "a fabricated
        consumer" looks like once the typo case is ruled out."""
        with tempfile.TemporaryDirectory() as d:
            errors = self._case(d, "a.expected", "x\n", "`gates/r.lean`",
                                {"gates/r.lean": self.SILENT})
            self.assertTrue(errors)
            self.assertIn("mentions it in code", " ".join(errors))

    def test_rejects_a_DEAD_BINDING(self) -> None:
        """`UNUSED_FIXTURE = "foo.expected"` is not a consumer.

        Preserving: the fixture's name is still in the named path, still in its
        CODE view, and the path still exists -- only the bound name's second
        occurrence is gone.  A mention-only check passes this, which is what the
        gate did until `v0.35.123` while its PASS line said the row names a gate
        that *reads* the fixture.
        """
        with tempfile.TemporaryDirectory() as d:
            errors = self._case(d, "a.expected", "x\n", "`gates/r.lean`",
                                {"gates/r.lean": self.DEAD_BINDING})
            self.assertTrue(errors)
            self.assertIn("binds it to a name nothing else", " ".join(errors))

    def test_accepts_a_mention_that_BINDS_NOTHING(self) -> None:
        """An argument is a use, so it needs no second occurrence.

        Without this the dead-binding rule would be satisfied by refusing every
        `include_str!`-shaped consumer -- and `conformance.rs` is one.
        """
        with tempfile.TemporaryDirectory() as d:
            self.assertEqual(
                self._case(d, "a.expected", "x\n", "`gates/r.lean`",
                           {"gates/r.lean": self.INLINE}), [])

    def test_rejects_a_STANDALONE_LITERAL(self) -> None:
        """PR #897's review, `v0.35.138`: `v0.35.123` closed the dead-binding half
        and left the other in a default.

        A mention that binds no name was credited unconditionally, which is true
        of an argument, a comparison and a call and **false of a standalone
        literal** -- so a consumer whose content is `"a.expected"` and nothing
        else passed the same claim by the other branch, and a new golden fixture
        could be indexed, hashed and assigned to a gate that never opens it.

        Preserving: the path is spelled, in full, in a real repository file the
        row names -- exactly as the accepted `include_str!` idiom spells it.  Only
        the thing that would consume it is missing.
        """
        with tempfile.TemporaryDirectory() as d:
            errors = self._case(d, "a.expected", "x\n", "`gates/r.lean`",
                                {"gates/r.lean": self.STANDALONE})
            self.assertTrue(errors)

    def test_accepts_that_same_literal_with_a_CALLEE_in_front(self) -> None:
        """The control, and what makes the refusal about consumption: the mention
        is at the same bare position, in the same file shape, and the only
        difference is the identifier that consumes it.  Without this the rejecting
        case above is satisfied by a rule that refuses every line-initial
        mention."""
        with tempfile.TemporaryDirectory() as d:
            self.assertEqual(
                self._case(d, "a.expected", "x\n", "`gates/r.lean`",
                           {"gates/r.lean": self.STANDALONE_CONSUMED}), [])

    def test_the_operand_question_is_asked_of_the_HEAD(self) -> None:
        """Both verdicts, directly, so the split is pinned at the predicate rather
        than only through a whole check: whitespace, quotes and opening delimiters
        consume nothing; an identifier or a closing delimiter does."""
        self.assertFalse(sc.consumer_mention_is_operand('  "'))
        self.assertFalse(sc.consumer_mention_is_operand(""))
        self.assertFalse(sc.consumer_mention_is_operand('  ("'))
        self.assertTrue(sc.consumer_mention_is_operand('include_str!("'))
        self.assertTrue(sc.consumer_mention_is_operand('compareAgainst "'))
        self.assertTrue(sc.consumer_mention_is_operand('diff "${X}" '))

    def test_the_bound_name_is_found_across_a_continuation(self) -> None:
        """A `def … :=` whose string is on the NEXT line still binds its name.

        `SmpInformationFlowSuite.lean` is exactly this shape, so without the
        bounded look-back the mention would bind nothing and a dead multi-line
        binding would pass.  Asserted on BOTH verdicts, because a look-back that
        always answered `None` would satisfy the acceptance alone.
        """
        live = ('def fixturePath : String :=\n  "a.expected"\n'
                'def main : IO Unit := IO.FS.readFile fixturePath\n')
        dead = 'def unusedFixture : String :=\n  "a.expected"\ndef f : Nat := 0\n'
        self.assertIs(sc.fixture_mention_consumed(live, "a.expected"), True)
        self.assertIs(sc.fixture_mention_consumed(dead, "a.expected"), False)
        self.assertIsNone(sc.fixture_mention_consumed("def f := 0\n", "a.expected"))

    def test_every_live_consumer_idiom_is_admitted(self) -> None:
        """The measurement that licensed the rule: all five shipped idioms bind
        the path and read the name elsewhere, so requiring a read AT the mention
        would have refused every one of them."""
        for consumer, fixture in (
            ("scripts/test_tier2_trace.sh", "main_trace_smoke.expected"),
            ("tests/SmpSchedulerSuite.lean", "smp_4core_scheduler.expected"),
            ("rust/sele4n-abi/tests/conformance.rs",
             "syscall_return_shape.expected"),
            ("scripts/test_qemu.sh", "qemu_boot_expected.txt"),
            ("tests/SmpInformationFlowSuite.lean",
             "declassification_taint.expected"),
        ):
            view = sc.consumer_code_view(REPO_ROOT / consumer)
            self.assertIs(sc.fixture_mention_consumed(view, fixture), True,
                          f"{consumer} no longer reads {fixture}")

    def test_rejects_a_consumer_that_does_not_exist(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            errors = self._case(d, "a.expected", "x\n", "`gates/typo.lean`", {})
            self.assertTrue(errors)
            self.assertIn("does not exist", " ".join(errors))

    def test_rejects_a_cell_naming_no_repository_path(self) -> None:
        """The `two_phase_arch_smoke.expected` case: its cell read "same two
        gates", a back-reference to the row above that a reader resolves by eye
        and a check cannot resolve at all."""
        with tempfile.TemporaryDirectory() as d:
            errors = self._case(d, "a.expected", "x\n", "same two gates",
                                {"gates/r.lean": self.READER})
            self.assertTrue(errors)
            self.assertIn("names no repository path", " ".join(errors))

    def test_a_comment_is_not_a_gate_opening_a_file(self) -> None:
        """Gates read code, prose reads prose.

        Preserving: the fixture's name is still in the named consumer, and the
        consumer still exists — only its POSITION moves, from code into a comment.
        A raw-text search passes this.
        """
        with tempfile.TemporaryDirectory() as d:
            errors = self._case(d, "a.expected", "x\n", "`gates/r.lean`",
                                {"gates/r.lean": self.COMMENTED})
            self.assertTrue(errors)
            self.assertIn("mentions it in code", " ".join(errors))

    def test_accepts_a_manifest_naming_its_discovery_gate(self) -> None:
        """A manifest's consumer globs the directory and names no file, so looking
        for the fixture's name in it would refuse every manifest.  The control for
        the arm below."""
        with tempfile.TemporaryDirectory() as d:
            self.assertEqual(
                self._case(d, "a.expected", self.MANIFEST_FIXTURE,
                           "`scripts/scenario_catalog.py check-fragments`", {}), [])

    def test_rejects_a_manifest_naming_some_other_reader(self) -> None:
        """Preserving: the cell names a real path that really does mention the
        fixture — which would satisfy the other arm — while the gate that actually
        reads every manifest goes unnamed."""
        with tempfile.TemporaryDirectory() as d:
            errors = self._case(d, "a.expected", self.MANIFEST_FIXTURE,
                                "`gates/r.lean`", {"gates/r.lean": self.READER})
            self.assertTrue(errors)
            self.assertIn("scenario-traceability manifest", " ".join(errors))

    def test_the_real_tree_names_a_real_reader_for_every_fixture(self) -> None:
        """The claim holds on the shipped README, so the fix is not a refusal."""
        errors, claims = sc.check_fixture_consumers(
            FIXTURES, FIXTURES / "README.md")
        self.assertEqual(errors, [])
        # The count is the CHECK's, not the table's: a minimum, so a fixture
        # added later needs no edit here and losing the population still fails.
        self.assertGreaterEqual(claims, 15)


class TestTreeState(unittest.TestCase):
    """Pins against the real tree, so losing a manifest is visible."""

    def test_both_shipped_manifests_are_discovered(self) -> None:
        """A minimum rather than an equality: a third manifest is swept with no
        edit here, and losing one of these two fails."""
        manifests, errors = sc.discover_manifests(FIXTURES)
        self.assertEqual(errors, [])
        found = {m.path.name: m.suite for m in manifests}
        self.assertEqual(found.get("robin_hood_smoke.expected"), "robin_hood_suite")
        self.assertEqual(found.get("two_phase_arch_smoke.expected"),
                         "two_phase_arch_suite")

    def test_every_shipped_row_names_its_own_scenario(self) -> None:
        """The binding holds on the real manifests, so the fix is not a refusal.

        `discover_manifests` returning no errors above already implies it —
        `classify_fixture` refuses a cross-wired row — and this asserts it of
        every row directly, because a claim inherited from another check's
        silence is not a measurement.
        """
        manifests, errors = sc.discover_manifests(FIXTURES)
        self.assertEqual(errors, [])
        rows = 0
        for manifest in manifests:
            for scenario_id, _subsystem, fragment in manifest.rows:
                self.assertTrue(
                    sc.fragment_names_scenario(scenario_id, fragment),
                    f"{manifest.path}: {scenario_id} -> {fragment!r}")
                rows += 1
        # 19 rows: the same 19 whose fragments were ALL stale at `v0.35.109`.
        # A minimum rather than an equality, so a row added later needs no edit
        # here and losing the population entirely still fails.
        self.assertGreaterEqual(rows, 19)

    def test_no_trace_fixture_is_classified_as_a_manifest(self) -> None:
        manifests, _ = sc.discover_manifests(FIXTURES)
        names = {m.path.name for m in manifests}
        self.assertNotIn("main_trace_smoke.expected", names)
        self.assertNotIn("smp_ipc_4core.expected", names)

    def test_registry_gate_is_unchanged_by_the_shared_id_parser(self) -> None:
        """No `--extra-fixtures`: the manifests are DERIVED since `v0.35.123`."""
        result = run("validate-registry")
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_the_derived_manifest_set_is_what_Tier_0_used_to_hand_list(self) -> None:
        """The measurement that made deriving free.

        `manifest_fixture_paths` must return exactly the two paths Tier 0 listed
        by hand, so the derivation is a removal of a hole and not a change of
        input.  Asserted as an EQUALITY: a superset would silently widen the
        registry's domain and a subset would narrow it.
        """
        paths, errors = sc.manifest_fixture_paths(FIXTURES)
        self.assertEqual(errors, [])
        self.assertEqual(
            sorted(p.name for p in paths),
            ["robin_hood_smoke.expected", "two_phase_arch_smoke.expected"])

    def test_the_derivation_fails_closed_on_a_discovery_error(self) -> None:
        """A partial list that reads as a clean pass is the silence `v0.35.111`
        found in this same discovery, so a directory holding one unparseable
        declared manifest yields NO paths and the error -- not the good ones."""
        with tempfile.TemporaryDirectory() as d:
            directory = Path(d)
            (directory / "good.expected").write_text(
                "# Suite: s\nRH-001 | rh | [RH-001] ok\n", encoding="utf-8")
            (directory / "bad.expected").write_text(
                "# Suite: s\nRH-002 | rh | [RH-002] ok\nnot a row\n",
                encoding="utf-8")
            paths, errors = sc.manifest_fixture_paths(directory)
            self.assertEqual(paths, [])
            self.assertTrue(errors)

    def test_a_golden_line_with_pipes_is_not_a_manifest_row(self) -> None:
        """Tier 0 passes `main_trace_smoke.expected` through the id parser, and a
        golden line `cap | badge | ok` used to put `cap` in `fixture_ids`.

        Preserving: the pipes stay, the bracketed ids stay, and only the
        CLASSIFICATION decides -- which is what a shape-blind split cannot do.
        """
        with tempfile.TemporaryDirectory() as d:
            golden = Path(d) / "gold.expected"
            golden.write_text("[RH-001] insert then get\ncap | badge | ok\n",
                              encoding="utf-8")
            ids, error = sc.scenario_ids_in(golden)
            self.assertIsNone(error)
            self.assertEqual(ids, {"RH-001"})

    def test_a_declared_manifest_that_does_not_parse_yields_no_ids(self) -> None:
        """Fail closed: reading it as golden output would take its rows' first
        fields as scenario ids, which is the same fail-open one field over."""
        with tempfile.TemporaryDirectory() as d:
            bad = Path(d) / "b.expected"
            bad.write_text("# Suite: s\nRH-001 | rh | [RH-001] ok\nnot a row\n",
                           encoding="utf-8")
            ids, error = sc.scenario_ids_in(bad)
            self.assertEqual(ids, set())
            self.assertIsNotNone(error)

    def test_the_pass_line_says_what_the_check_DECIDES(self) -> None:
        """`reads the fixture` over-claimed, and nothing asserted the wording.

        Resolving a bound path to a read across shell, Lean, Rust and Python is a
        dataflow question this gate does not answer; what it decides is that the
        cell names a path whose code mentions the fixture and whose binding is
        consumed.  A number that implies an authority it does not have is the
        defect this project keeps recording, so the sentence is pinned here --
        found by a mutation that changed only the message and was caught by
        nothing.
        """
        result = run("check-fixture-index")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn(
            "name a path that mentions the fixture in code and consumes the "
            "name it binds it to", result.stdout)
        self.assertNotIn("name a gate that reads the fixture", result.stdout)

    def test_cli_requires_both_fragment_arguments(self) -> None:
        self.assertEqual(run("check-fragments").returncode, 1)
        self.assertEqual(
            run("check-fragments", "--manifest",
                "tests/fixtures/robin_hood_smoke.expected").returncode, 1)


if __name__ == "__main__":
    unittest.main()
