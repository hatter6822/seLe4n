import unittest
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


if __name__ == "__main__":
    unittest.main()
