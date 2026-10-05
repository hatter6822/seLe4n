import textwrap
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

import scripts.generate_codebase_map as m


def decls_of(sources: dict[str, str]) -> dict[str, dict[str, m.Decl]]:
    """`{module: {full_name or kind@line: Decl}}` for in-memory sources."""
    out = {}
    for module, decls in m.build_declarations(
        {k: textwrap.dedent(v).lstrip("\n") for k, v in sources.items()}
    ).items():
        out[module] = {(d.full_name or f"{d.kind}@{d.line}"): d for d in decls}
    return out


class GenerateCodebaseMapTests(unittest.TestCase):
    def test_declarations_carry_their_namespace(self) -> None:
        got = decls_of({"A": """
            namespace Outer.Inner
            inductive MyType
              | one
            structure Bundle where
              x : Nat
            private def hidden : Nat := 1
            theorem Bundle.stable : True := trivial
            def _root_.rootLevel : Nat := 2
            end Outer.Inner
            class Marker where
              x : Nat
            """})["A"]
        self.assertEqual(
            [(d.kind, d.name, d.full_name) for d in got.values()],
            [
                ("inductive", "MyType", "Outer.Inner.MyType"),
                ("structure", "Bundle", "Outer.Inner.Bundle"),
                ("def", "hidden", "Outer.Inner.hidden"),
                ("theorem", "Bundle.stable", "Outer.Inner.Bundle.stable"),
                ("def", "rootLevel", "rootLevel"),
                ("class", "Marker", "Marker"),
            ],
        )

    def test_identifiers_are_read_whole(self) -> None:
        # `?`, `!`, `'`, subscripts, Greek letters and «quoted» names are all
        # identifier characters; the line-regex reader cut `get?` to `get` and
        # recorded `τW5a` as anonymous.
        got = decls_of({"A": """
            def get? : Option Nat := none
            def get! : Nat := 0
            def f₁' : Nat := 0
            def τW5a : Nat := 0
            def «weird name» : Nat := 0
            """})["A"]
        self.assertEqual(sorted(got), sorted(["get?", "get!", "f₁'", "τW5a", "weird name"]))

    def test_headers_may_span_lines_and_carry_attributes(self) -> None:
        got = decls_of({"A": """
            @[simp,
              inline]
            protected noncomputable def
                spread : Nat := 1
            set_option maxHeartbeats 0 in
            @[simp] theorem afterOption : True := trivial
            """})["A"]
        self.assertEqual(got["spread"].line, 3)
        self.assertEqual(got["afterOption"].line, 6)

    def test_comments_and_literals_declare_nothing(self) -> None:
        got = decls_of({"A": r"""
            -- def commentedOut := 0
            /- theorem hiddenInBlock : True := by trivial
               /- nested -/ def stillHidden := 0 -/
            def s : String := "
            namespace Fake
            theorem inString : True := trivial"
            def r : String := r#"def inRaw " := 0"#
            def c : Char := '"'
            def visible : Nat := 1
            """})["A"]
        self.assertEqual(sorted(got), ["c", "r", "s", "visible"])

    def test_scope_commands_are_not_declarations(self) -> None:
        got = decls_of({"A": """
            universe u
            variable (x : Nat)
            section S
            open Nat in
            def a : Nat := 1
            end S
            namespace N
            example : True := trivial
            end N
            """})["A"]
        self.assertEqual([(d.kind, d.full_name) for d in got.values()], [("def", "a"), ("example", None)])

    def test_helpers_are_declarations_of_their_own(self) -> None:
        got = decls_of({"A": """
            def outer (n : Nat) : Nat := go n
            where
              go : Nat → Nat
                | 0 => 0
                | k + 1 => go k
            def loop (n : Nat) : Nat :=
              let rec walk : Nat → Nat
                | 0 => 0
                | k + 1 => walk k
              walk n
            instance : Inhabited Nat where
              default := 0
            """})["A"]
        self.assertIn("outer.go", got)
        self.assertIn("loop.walk", got)
        self.assertNotIn("default", {d.name for d in got.values()})

    def test_references_resolve_through_namespaces(self) -> None:
        got = decls_of({"A": """
            namespace X
            def leaf : Nat := 1
            def helper : Nat := leaf + leaf
            end X
            namespace Y
            def leaf : Nat := 2
            def root : Nat := X.helper + leaf
            end Y
            """})["A"]
        self.assertEqual(got["X.helper"].called, ["X.leaf"])
        # `leaf` inside `Y` is `Y.leaf`; a short-name reader linked both.
        self.assertEqual(got["Y.root"].called, ["X.helper", "Y.leaf"])

    def test_admitted_proofs_record_sorry_ax(self) -> None:
        got = decls_of({"A": """
            theorem admitted : 1 = 2 := by sorry
            theorem proved : 1 = 1 := rfl
            -- sorry in a comment admits nothing
            theorem commented : True := trivial
            """})["A"]
        # Lean elaborates `sorry` to `sorryAx`; it is the one core constant
        # `called` records, so a consumer can count admitted proofs.
        self.assertEqual(got["admitted"].called, ["sorryAx"])
        self.assertEqual(got["proved"].called, [])
        self.assertEqual(got["commented"].called, [])

    def test_references_skip_bound_variables_and_suffixes(self) -> None:
        got = decls_of({"A": """
            def get : Nat := 0
            def get? : Option Nat := none
            def x : Nat := 0
            def usesQuestion : Option Nat := get?
            def shadows (x : Nat) : Nat := x
            def lambda : Nat → Nat := fun get => get
            """})["A"]
        self.assertEqual(got["usesQuestion"].called, ["get?"])
        self.assertEqual(got["shadows"].called, [])
        self.assertEqual(got["lambda"].called, [])

    def test_references_follow_field_types_and_constructors(self) -> None:
        got = decls_of({"A": """
            structure Table where
              size : Nat
            def Table.invExt (t : Table) : Prop := t.size = 0
            structure State where
              objects : Table
            inductive Op
              | send
            theorem keeps (st : State) : st.objects.invExt := trivial
            def pick : Op := .send
            """})["A"]
        self.assertEqual(got["keeps"].called, ["State", "Table.invExt"])
        self.assertEqual(got["pick"].called, ["Op"])

    def test_references_respect_imports_and_privacy(self) -> None:
        got = decls_of({
            "Base": "def shared : Nat := 1\nprivate def secret : Nat := 2\n",
            "Other": "def stray : Nat := 3\n",
            "User": "import Base\ndef use : Nat := shared + secret + stray\n",
        })
        self.assertEqual(got["User"]["use"].called, ["shared"])

    def test_anonymous_instances(self) -> None:
        got = decls_of({"A": """
            namespace N
            structure Obj where
              v : Nat
            instance : Inhabited Obj := ⟨⟨0⟩⟩
            namespace Obj
            instance : Repr Obj := ⟨fun _ _ => "o"⟩
            end Obj
            instance (o : Obj) : Decidable (o.v = 0) := inferInstance
            end N
            """})["A"]
        self.assertIn("N.instInhabitedObj", got)
        self.assertIn("N.Obj.instRepr", got)
        # A binder decides the generated name only after elaboration: no guess.
        self.assertEqual([d.name for d in got.values() if d.kind == "instance" and d.full_name is None], [""])

    def test_unterminated_comment_is_refused(self) -> None:
        with self.assertRaises(m.LexError):
            m.build_declarations({"A": "/- never closed\ndef a := 1\n"})

    def test_parse_declarations_reads_one_file(self) -> None:
        with TemporaryDirectory() as tmpdir:
            fixture = Path(tmpdir) / "Fixture.lean"
            fixture.write_text("def leaf : Nat := 1\ndef root : Nat := leaf\n", encoding="utf-8")
            decls = m.parse_declarations(fixture)
        self.assertEqual([(d.name, d.called) for d in decls], [("leaf", []), ("root", ["leaf"])])

    def test_module_name_is_repo_relative(self) -> None:
        self.assertEqual(m.module_name(m.ROOT / "SeLe4n/Kernel/API.lean"), "SeLe4n.Kernel.API")

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
        readme_sync = {
            "version": "0.14.4",
            "lean_toolchain": "v4.28.0",
            "production_files": 41,
            "production_loc": 31000,
            "test_files": 3,
            "test_loc": 2400,
            "proved_theorem_lemma_decls": 958,
            "hardware_target": "Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A)",
        }
        base = {
            "schema_version": m.SCHEMA_VERSION,
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
            "readme_sync": readme_sync,
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
        readme_sync = {
            "version": "0.14.4",
            "lean_toolchain": "v4.28.0",
            "production_files": 41,
            "production_loc": 31000,
            "test_files": 3,
            "test_loc": 2400,
            "proved_theorem_lemma_decls": 958,
            "hardware_target": "Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A)",
        }
        base = {
            "schema_version": m.SCHEMA_VERSION,
            "repository": {"name": "hatter6822/seLe4n", "url": "https://github.com/hatter6822/seLe4n"},
            "source_sync": {"source_digest": "abc"},
            "summary": {"module_count": 1, "declaration_count": 2},
            "readme_sync": readme_sync,
            "modules": [{"module": "Main", "path": "Main.lean", "declaration_count": 0, "declarations": []}],
        }
        changed_source = {**base, "source_sync": {"source_digest": "def"}}
        self.assertNotEqual(m.normalized_for_check(base), m.normalized_for_check(changed_source))


if __name__ == "__main__":
    unittest.main()
