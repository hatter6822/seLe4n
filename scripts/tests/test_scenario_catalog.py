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
already happened, so the boundary was probed and the property was not.  Among
them were a classifier whose parse failure was a silent `continue` (so a file
with a valid `# Suite:` header and one malformed row was swept as golden output
while the gate reported PASS) and a fragment relation with no binding to its own
row (so a cross-wired row witnessed another scenario and passed).  Each now has a
case that keeps every token, and the accepting controls beside them are what stop
the fixes from reading as refusals.

At `v0.35.116` it grew more of the same kind.  A manifest declares ONE
producer and `suite is not None` is a presence check where the property is
"exactly one", so a copied second `# Suite:` header redirected every fragment
check to another executable.  A fragment's id was searched for anywhere in the
fragment rather than at a LABEL position, so a row whose evidence is another
scenario's assertion passed while still carrying its own id as prose.  Each new
case keeps every token and moves only the relation: a second valid header, an
id from the label into the prose beside it.
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

    def test_a_repeated_scenario_id_is_an_ERROR(self) -> None:
        """PR #897's review, `v0.35.139`: the id set collapses the repetition.

        Two rows for one id classify successfully under the superseded parse, the
        registry can supply ONE metadata entry for them, `scenario_ids_in`
        returns a set so `validate-registry` cannot see the second, and
        `check_fragments` loops rows, so both can be credited to the same emitted
        line.  Preserving: both rows are well-formed and both fragments name
        their own scenario — they simply name the same one.
        """
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "m.expected"
            p.write_text(
                MANIFEST
                + "RH-001 | RobinHood | robin-hood check passed "
                  "[RH-001b empty size is 0]\n",
                encoding="utf-8")
            shape = sc.classify_fixture(p)
            self.assertIsNotNone(shape.error)
            self.assertIn("repeats scenario id RH-001", shape.error)

    def test_a_scenario_id_repeated_ACROSS_fixtures_is_an_ERROR(self) -> None:
        """The other half: `classify_fixture` refuses a repeat inside one
        manifest, and `fixture_ids_and_errors` is where two fixtures declaring
        one id collapse — `ids |= found`.  The registry then describes one of the
        two scenarios while `validate-registry` compares sets and agrees."""
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            first = root / "a.expected"
            second = root / "b.expected"
            first.write_text(MANIFEST, encoding="utf-8")
            second.write_text(
                MANIFEST.replace("Suite: robin_hood_suite", "Suite: other_suite"),
                encoding="utf-8")
            ids, errors = sc.fixture_ids_and_errors([first, second])
            self.assertTrue(errors)
            self.assertIn("already declared by", errors[0])

    def test_two_fixtures_with_DISJOINT_ids_are_accepted(self) -> None:
        """The control: without it the case above is satisfied by a union that
        refuses any second fixture at all, and the live tree has two manifests."""
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            first = root / "a.expected"
            second = root / "b.expected"
            first.write_text(MANIFEST, encoding="utf-8")
            second.write_text(
                MANIFEST.replace("Suite: robin_hood_suite", "Suite: other_suite")
                        .replace("RH-00", "TPH-00"),
                encoding="utf-8")
            ids, errors = sc.fixture_ids_and_errors([first, second])
            self.assertEqual(errors, [])
            self.assertEqual(ids, {"RH-001", "RH-002", "TPH-001", "TPH-002"})

    def test_a_scenario_id_with_no_FAMILY_is_an_ERROR(self) -> None:
        """The family is what bounds the reverse scan's domain, so an id without
        one would take its manifest out of that scan silently — the shape of
        defect the reverse direction exists to close, arriving through its own
        domain.  Every live row already matches, so requiring it is free."""
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "m.expected"
            p.write_text(
                "# Suite: robin_hood_suite\n"
                "Legacy | RobinHood | Legacy check passed\n", encoding="utf-8")
            shape = sc.classify_fixture(p)
            self.assertIsNotNone(shape.error)
            self.assertIn("is not `<FAMILY>-<number>`", shape.error)

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

    def test_rejects_an_EMITTED_scenario_with_no_row(self) -> None:
        """PR #897's review, `v0.35.139`, and it was LIVE.

        The forward loop asks only whether every ROW is traced, so a suite that
        adds a labelled scenario without adding its row passes: every old
        fragment still matches, and `validate-registry` sees only the id set the
        manifest itself declares.  The manifest claims to enumerate its
        producer's scenarios, and that claim was made by nothing.

        Measured on the real tree rather than constructed: `two_phase_arch_suite`
        had emitted `TPH-015` with thirteen sub-case labels and no manifest row
        since it was written, so the registry silently stopped describing it.
        That row and its registry entry land in the same cut.

        Preserving: every declared row is still emitted and still passes the
        forward direction — the output simply carries one scenario more.
        """
        with tempfile.TemporaryDirectory() as d:
            extra = OUTPUT + "robin-hood check passed [RH-003a resize keeps order]\n"
            errors = sc.check_fragments(self._manifest(d), extra)
            self.assertEqual(len(errors), 1)
            self.assertIn("RH-003", errors[0])
            self.assertIn("does not declare", errors[0])

    def test_an_emitted_label_of_ANOTHER_family_IS_reported(self) -> None:
        """`v0.35.142`: the scan's domain is the producer's OUTPUT.

        Until this cut the families the manifest's own rows declare bounded the
        scan, so this case asserted `[]` — and that bound is derived from the very
        set the scan exists to contradict, so a producer's FIRST scenario in a new
        family defined itself out of it.  The manifest is a claim about what *its*
        producer traces, so a label-position id it does not declare is a finding
        whatever family it names: either the row is missing or the label is wrong.
        Measured before choosing: over both live producers the family filter
        dropped **none** of the 12 and 8 label-position ids, so the bound cost the
        tree nothing and bought it only the hole.
        """
        with tempfile.TemporaryDirectory() as d:
            other = OUTPUT + "two-phase check passed [TPH-015a boot succeeds]\n"
            errors = sc.check_fragments(self._manifest(d), other)
            self.assertEqual(len(errors), 1, errors)
            self.assertIn("TPH-015", errors[0])

    def test_an_emitted_id_NOT_at_a_label_position_is_not_a_claim(self) -> None:
        """Both directions read one `LABEL_POSITION`, so a mid-line mention is no
        more a claim here than it is evidence there: `(covers RH-003)` says the
        suite mentioned a scenario, not that it traced one."""
        with tempfile.TemporaryDirectory() as d:
            mention = OUTPUT + "robin-hood check passed [RH-002b get (covers RH-003)]\n"
            self.assertEqual(sc.check_fragments(self._manifest(d), mention), [])

    def test_the_emitted_extractor_reads_every_family(self) -> None:
        """The predicate, directly — the scan's domain is the OUTPUT.

        `v0.35.139` bounded this by the manifest's own families, which is a domain
        derived from the thing the scan exists to contradict: a producer's FIRST
        scenario in a new family named no declared family and was discarded.  The
        line-start id and the parenthesised mention are what pin `LABEL_POSITION`
        at this function rather than only through a whole check.
        """
        text = "a [RH-001a x]\nb [TPH-002c y]\nRH-003a z\nq (covers RH-009) r\n"
        self.assertEqual(sc.emitted_scenario_ids(text),
                         {"RH-001", "TPH-002", "RH-003"})
        self.assertEqual(sc.emitted_scenario_ids(""), set())

    def test_reports_a_scenario_in_a_family_no_row_declares(self) -> None:
        """THE decisive case for `v0.35.142`: a NEW family.

        Under the family bound this passed — `NEW` is in no row, so the filter
        discarded the emitted id and the reconciliation saw nothing.  The control
        is `test_rejects_a_renamed_label` beside it, which the bound did catch, so
        this case is known to be about the *domain* rather than about the scan.
        """
        with tempfile.TemporaryDirectory() as d:
            fresh = OUTPUT + "robin-hood check passed [NEW-001a a brand new family]\n"
            errors = sc.check_fragments(self._manifest(d), fresh)
            self.assertEqual(len(errors), 1, errors)
            self.assertIn("NEW-001", errors[0])
            self.assertIn("does not declare", errors[0])

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
            # TWO findings since `v0.35.139`, and the second is the reverse
            # direction agreeing: the row is not emitted, AND the suite labels a
            # scenario (`RH-0010`) this manifest does not declare.  Both are true
            # of this output and the pair is strictly more informative than the
            # one; the assertion names each rather than counting, so a later cut
            # that adds a third finding is not forced to edit a number.
            self.assertTrue(any("RH-001 expected_trace_fragment not emitted" in e
                                and "label position" in e for e in errors))
            self.assertTrue(any("RH-0010" in e and "does not declare" in e
                                for e in errors))

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

    def test_cli_requires_both_fragment_arguments(self) -> None:
        self.assertEqual(run("check-fragments").returncode, 1)
        self.assertEqual(
            run("check-fragments", "--manifest",
                "tests/fixtures/robin_hood_smoke.expected").returncode, 1)


if __name__ == "__main__":
    unittest.main()
