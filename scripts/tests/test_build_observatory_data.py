"""Tests for scripts/build_observatory_data.py (the Observatory data pipeline).

Run from the repo root:  python3 -m unittest scripts.tests.test_build_observatory_data
"""
import json
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

import scripts.build_observatory_data as bod

ROOT = Path(__file__).resolve().parents[2]


class ClassifierTests(unittest.TestCase):
    """Pure, repo-independent classification of checkpoint values/outcomes."""

    def test_value_registers(self) -> None:
        self.assertEqual(bod.classify_value("[100, 200]"),
                         {"type": "registers", "data": [100, 200], "raw": "[100, 200]"})
        self.assertEqual(bod.classify_value("#[111, 222, 333]")["data"], [111, 222, 333])
        self.assertEqual(bod.classify_value("[]")["data"], [])

    def test_value_bool_nat_option(self) -> None:
        self.assertEqual(bod.classify_value("true")["data"], True)
        self.assertEqual(bod.classify_value("false")["data"], False)
        self.assertEqual(bod.classify_value("64")["data"], 64)
        self.assertEqual(bod.classify_value("none")["type"], "option")
        self.assertEqual(bod.classify_value("some 12")["type"], "option")
        self.assertEqual(bod.classify_value("some [100, 200]")["data"], [100, 200])

    def test_value_error(self) -> None:
        v = bod.classify_value("SeLe4n.Model.KernelError.policyDenied")
        self.assertEqual(v, {"type": "error", "data": "policyDenied",
                             "raw": "SeLe4n.Model.KernelError.policyDenied"})

    def test_outcome(self) -> None:
        self.assertEqual(bod.classify_outcome("true")["status"], "ok")
        out = bod.classify_outcome("Except.error (SeLe4n.Model.KernelError.invalidArgument)")
        self.assertEqual(out, {"status": "expectedError", "error": "invalidArgument"})

    def test_kind(self) -> None:
        ok = {"status": "ok"}
        err = {"status": "expectedError", "error": "x"}
        self.assertEqual(bod.classify_kind("ITR", "inter-transition invariant checks: 38 passed", ok),
                         "invariantCheck")
        self.assertEqual(bod.classify_kind("XVAL", "MessageInfo roundtrip ok", ok), "conformance")
        self.assertEqual(bod.classify_kind("STD", "EDF tie-break chosen thread", ok), "scheduling")
        self.assertEqual(bod.classify_kind("CAT", "W^X rejected", err), "guard")
        self.assertEqual(bod.classify_kind("IMT", "call/reply response registers", ok), "transition")

    def test_module_subsystem(self) -> None:
        self.assertEqual(bod.module_subsystem("SeLe4n.Kernel.IPC.Operations.Endpoint"), "IPC")
        self.assertEqual(bod.module_subsystem("SeLe4n.Kernel.Scheduler.Operations.Core"), "Scheduler")
        self.assertEqual(bod.module_subsystem("SeLe4n.Kernel.CrossSubsystem"), "CrossSubsystem")
        # exact-override seam module (would otherwise be Unknown):
        self.assertEqual(bod.module_subsystem("SeLe4n.Kernel.CrossSubsystemPerCore"), "CrossSubsystem")
        self.assertEqual(bod.module_subsystem("SeLe4n.Kernel.SyscallDispatchEntry"), "API")


class BundleTests(unittest.TestCase):
    """Integration tests against the live repository artifacts."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.outputs = bod.build_bundle(ROOT)
        cls.manifest = cls.outputs["manifest.json"]
        cls.atlas = cls.outputs["atlas/index.json"]
        cls.events = cls.outputs["traces/main_trace_smoke/events.json"]["events"]

    def test_manifest_schema(self) -> None:
        m = self.manifest
        self.assertEqual(m["schemaVersion"], bod.SCHEMA_VERSION)
        self.assertTrue(m["bundleHash"].startswith("sha256:"))
        for key in ("modules", "declarations", "provedTheorems", "hardwareTarget"):
            self.assertIn(key, m["metrics"])
        self.assertGreater(m["metrics"]["modules"], 0)
        self.assertTrue(any(t["id"] == "main_trace_smoke" for t in m["traces"]))

    def test_deterministic(self) -> None:
        again = bod.build_bundle(ROOT)
        self.assertEqual(again["manifest.json"]["bundleHash"], self.manifest["bundleHash"])
        for rel in self.outputs:
            self.assertEqual(bod.canonical_bytes(again[rel]), bod.canonical_bytes(self.outputs[rel]),
                             f"non-deterministic output for {rel}")

    def test_write_roundtrip(self) -> None:
        with TemporaryDirectory() as d:
            bod.write_bundle(self.outputs, Path(d))
            man = json.loads((Path(d) / "manifest.json").read_text())
            self.assertEqual(man["bundleHash"], self.manifest["bundleHash"])
            self.assertTrue((Path(d) / "traces/main_trace_smoke/events.json").exists())

    def test_events_well_formed(self) -> None:
        self.assertGreater(len(self.events), 200)
        for e in self.events:
            for key in ("seq", "scenarioId", "subsystem", "kind", "label", "text",
                        "value", "outcome", "registered"):
                self.assertIn(key, e, f"event {e.get('scenarioId')} missing {key}")
        seqs = [e["seq"] for e in self.events]
        self.assertEqual(seqs, list(range(1, len(self.events) + 1)), "seq must be 1..N contiguous")

    def test_registry_join_complete(self) -> None:
        # Every main-trace event must join a registry entry (guards the
        # uncatalogued-scenario gap closed alongside this pipeline).
        unregistered = [e["scenarioId"] for e in self.events if not e["registered"]]
        self.assertEqual(unregistered, [],
                         f"uncatalogued main-trace scenarios: {unregistered}")

    def test_worked_example_event(self) -> None:
        imt014 = next(e for e in self.events if e["scenarioId"] == "IMT-014")
        self.assertEqual(imt014["subsystem"], "IPC")
        self.assertEqual(imt014["value"]["type"], "registers")
        self.assertEqual(imt014["value"]["data"], [100, 200])

    def test_atlas_fully_classified(self) -> None:
        mods = self.atlas["modules"]
        self.assertGreater(len(mods), 0)
        unknown = [m["module"] for m in mods if m["subsystem"] == "Unknown"]
        self.assertEqual(unknown, [],
                         f"unclassified modules (add to MODULE_SUBSYSTEM_*): {unknown}")
        for m in mods:
            self.assertIn(m["subsystem"], bod.SUBSYSTEM_PALETTE)
        # module dependency edges resolve to real modules
        names = {m["module"] for m in mods}
        for m in mods:
            for dep in m["deps"]:
                self.assertIn(dep, names)


if __name__ == "__main__":
    unittest.main()
