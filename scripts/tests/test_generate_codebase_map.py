import unittest
from tempfile import TemporaryDirectory
from pathlib import Path

import scripts.generate_codebase_map as m


class GenerateCodebaseMapTests(unittest.TestCase):
    def test_parse_declarations_detects_supported_kinds(self) -> None:
        fixture = Path("/tmp/test_generate_codebase_map_fixture.lean")
        fixture.write_text(
            """
inductive MyType
structure Bundle where
private def hidden : Nat := 1
theorem stable : True := by trivial
class Marker where
  x : Nat
""".strip()
            + "\n",
            encoding="utf-8",
        )
        decls = m.parse_declarations(fixture)
        self.assertEqual(
            [(d.kind, d.name) for d in decls],
            [
                ("inductive", "MyType"),
                ("structure", "Bundle"),
                ("def", "hidden"),
                ("theorem", "stable"),
                ("class", "Marker"),
            ],
        )

    def test_module_name_is_repo_relative(self) -> None:
        self.assertEqual(
            m.module_name(m.ROOT / "SeLe4n/Kernel/API.lean"),
            "SeLe4n.Kernel.API",
        )

    def test_render_json_pretty_and_compact(self) -> None:
        payload = {"k": 1, "v": [1, 2]}
        pretty = m.render_json(payload, pretty=True)
        compact = m.render_json(payload, pretty=False)
        self.assertTrue(pretty.endswith("\n"))
        self.assertTrue(compact.endswith("\n"))
        self.assertIn('\n  "k": 1,', pretty)
        self.assertEqual(compact, '{"k": 1, "v": [1, 2]}\n')

    def test_source_fingerprint_depends_on_paths_and_contents(self) -> None:
        with TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            file_a = root / "SeLe4n/A.lean"
            file_b = root / "tests/B.lean"
            file_a.parent.mkdir(parents=True)
            file_b.parent.mkdir(parents=True)
            file_a.write_text("def a := 1\n", encoding="utf-8")
            file_b.write_text("def b := 2\n", encoding="utf-8")

            old_root = m.ROOT
            try:
                m.ROOT = root
                digest1 = m.source_fingerprint([file_a, file_b])
                digest2 = m.source_fingerprint([file_a, file_b])
                self.assertEqual(digest1, digest2)

                file_b.write_text("def b := 3\n", encoding="utf-8")
                digest3 = m.source_fingerprint([file_a, file_b])
                self.assertNotEqual(digest1, digest3)
            finally:
                m.ROOT = old_root

    def test_normalized_for_check_ignores_repository_head(self) -> None:
        base = {
            "schema_version": "1.0.0",
            "repository": {
                "name": "hatter6822/seLe4n",
                "url": "https://github.com/hatter6822/seLe4n",
                "head": {
                    "branch": "feature/x",
                    "commit_sha": "111",
                    "tree_sha": "222",
                    "committed_at_utc": "2026-01-01T00:00:00Z",
                },
            },
            "source_sync": {"source_digest": "abc"},
            "summary": {"module_count": 1, "declaration_count": 2},
            "modules": [{"module": "Main", "path": "Main.lean", "declaration_count": 0, "declarations": []}],
        }
        changed_head = {
            **base,
            "repository": {
                **base["repository"],
                "head": {
                    "branch": "main",
                    "commit_sha": "333",
                    "tree_sha": "444",
                    "committed_at_utc": "2026-01-02T00:00:00Z",
                },
            },
        }
        self.assertEqual(m.normalized_for_check(base), m.normalized_for_check(changed_head))

    def test_normalized_for_check_detects_source_or_module_drift(self) -> None:
        base = {
            "schema_version": "1.0.0",
            "repository": {"name": "hatter6822/seLe4n", "url": "https://github.com/hatter6822/seLe4n"},
            "source_sync": {"source_digest": "abc"},
            "summary": {"module_count": 1, "declaration_count": 2},
            "modules": [{"module": "Main", "path": "Main.lean", "declaration_count": 0, "declarations": []}],
        }
        changed_source = {**base, "source_sync": {"source_digest": "def"}}
        self.assertNotEqual(m.normalized_for_check(base), m.normalized_for_check(changed_source))


if __name__ == "__main__":
    unittest.main()
