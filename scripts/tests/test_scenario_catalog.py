#!/usr/bin/env python3
"""Witnesses for the scenario-traceability manifest machinery (v0.35.109).

Every case that must REJECT is a mutation that **keeps the token and breaks the
relation** — `CLAUDE.md`'s rule, and the reason the drift this machinery exists
to catch shipped: the manifest rows were byte-perfect and the suite stopped
printing what they named, so any presence check over the fixture survived it.
Each check therefore carries at least one *preserving* case, and the accepting
cases are here too, because a checker that refuses everything reads exactly like
one that decides.
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
    """`parse_manifest` decides by ROW SHAPE, so classification is derived."""

    def test_accepts_a_manifest(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "m.expected"
            p.write_text(MANIFEST, encoding="utf-8")
            m = sc.parse_manifest(p)
            self.assertIsNotNone(m)
            assert m is not None
            self.assertEqual(m.suite, "robin_hood_suite")
            self.assertEqual([r[0] for r in m.rows], ["RH-001", "RH-002"])

    def test_rejects_a_trace_fixture(self) -> None:
        """A golden-output fixture must never be swept as a manifest.

        Preserving: the file is real fixture content, not an emptied stub.
        """
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "t.expected"
            p.write_text(TRACE, encoding="utf-8")
            self.assertIsNone(sc.parse_manifest(p))

    def test_one_non_row_line_disqualifies(self) -> None:
        """Preserving: every row survives; one line of suite output is added.

        A file that is *mostly* rows is not a manifest — otherwise a trace
        fixture that happened to contain a pipe would be run against a producer
        it never declared.
        """
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "m.expected"
            p.write_text(MANIFEST + "robin-hood check passed [RH-003a]\n",
                         encoding="utf-8")
            self.assertIsNone(sc.parse_manifest(p))

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
        m = sc.parse_manifest(p)
        assert m is not None
        return m

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

    def test_a_rowless_manifest_cannot_pass_vacuously(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            empty = sc.Manifest(Path(d) / "m.expected", "robin_hood_suite", [])
            errors = sc.check_fragments(empty, OUTPUT)
            self.assertEqual(len(errors), 1)
            self.assertIn("vacuously", errors[0])


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

    def test_every_exemption_carries_a_reason(self) -> None:
        for name, reason in sc.FIXTURE_INDEX_EXEMPT.items():
            self.assertTrue(reason.strip(), name)

    def test_the_real_tree_is_complete(self) -> None:
        self.assertEqual(sc.check_fixture_index(FIXTURES, FIXTURES / "README.md"), [])


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

    def test_no_trace_fixture_is_classified_as_a_manifest(self) -> None:
        manifests, _ = sc.discover_manifests(FIXTURES)
        names = {m.path.name for m in manifests}
        self.assertNotIn("main_trace_smoke.expected", names)
        self.assertNotIn("smp_ipc_4core.expected", names)

    def test_registry_gate_is_unchanged_by_the_shared_id_parser(self) -> None:
        result = run("validate-registry",
                     "--extra-fixtures",
                     "tests/fixtures/robin_hood_smoke.expected",
                     "tests/fixtures/two_phase_arch_smoke.expected")
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_cli_requires_both_fragment_arguments(self) -> None:
        self.assertEqual(run("check-fragments").returncode, 1)
        self.assertEqual(
            run("check-fragments", "--manifest",
                "tests/fixtures/robin_hood_smoke.expected").returncode, 1)


if __name__ == "__main__":
    unittest.main()
