#!/usr/bin/env python3
"""Build the seLe4n Observatory web-data bundle from repository artifacts.

Transforms the kernel's existing, deterministic artifacts into a versioned
JSON bundle that the Observatory SPA consumes (the three "layers" of the
spec's Trinity model):

  - tests/fixtures/*.expected               -> traces/<id>/events.json
        (Execution layer: the deterministic transition stream)
  - tests/fixtures/scenario_registry.yaml   -> per-event join metadata
        (subsystem / source module / source function / description)
  - docs/codebase_map.json                  -> manifest metrics + atlas/index.json
        (Structure layer: modules, subsystems, module dependency edges)

Properties:
  * Deterministic   — identical inputs yield an identical bundle and the
                      same `bundleHash` (asserted by the unit test and
                      intended as a CI anti-drift anchor).
  * Non-invasive    — reads only; never modifies the kernel, its proofs,
                      or the byte-stable trace fixtures.
  * Stdlib-only     — PyYAML if available, else a tiny registry parser.

See docs/planning/KERNEL_OBSERVATORY_WEBAPP_SPEC.md (sections 6 and 14).
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCHEMA_VERSION = "1.0.0"

# --- Canonical subsystem palette (spec Appendix A). Colour is illustrative;
#     every hue is paired with an icon + the label so colour is never the
#     sole channel (spec section 11/12). ----------------------------------
SUBSYSTEM_PALETTE: dict[str, dict[str, str]] = {
    "Entry":            {"color": "#8A94A6", "icon": "power"},
    "Scheduler":        {"color": "#27C5B8", "icon": "clock"},
    "IPC":              {"color": "#5BA8FF", "icon": "envelope"},
    "Capability":       {"color": "#E7B53C", "icon": "key"},
    "Lifecycle":        {"color": "#9B7BE0", "icon": "recycle"},
    "SchedContext":     {"color": "#E08A2B", "icon": "gauge"},
    "Architecture":     {"color": "#4FB477", "icon": "map"},
    "Service":          {"color": "#6C72E0", "icon": "hexagon"},
    "ServiceRegistry":  {"color": "#5660C9", "icon": "hexagon-grid"},
    "InformationFlow":  {"color": "#E0556B", "icon": "lock"},
    "Concurrency":      {"color": "#D957C6", "icon": "cores"},
    "RobinHood":        {"color": "#C98A5B", "icon": "hash"},
    "RadixTree":        {"color": "#B07D4A", "icon": "tree"},
    "FrozenOps":        {"color": "#7FA6C9", "icon": "snowflake"},
    "CrossSubsystem":   {"color": "#A0A6B4", "icon": "link"},
    "API":              {"color": "#7C8696", "icon": "gateway"},
    "ABI":              {"color": "#7C8696", "icon": "gear"},
    "Platform":         {"color": "#6FA0A8", "icon": "chip"},
    "TwoPhaseArch":     {"color": "#8FB07D", "icon": "layers"},
    "Model":            {"color": "#9AA0AE", "icon": "cube"},
    "Core":             {"color": "#7E8493", "icon": "atom"},
    "Testing":          {"color": "#B6BCC8", "icon": "flask"},
    "Unknown":          {"color": "#5A5F6B", "icon": "question"},
}

# Fallback tag -> subsystem (used only when a scenario is absent from the
# registry; the registry's per-scenario `subsystem` field is authoritative).
TAG_SUBSYSTEM: dict[str, str] = {
    "ENT": "Entry", "CAT": "Architecture", "RCF": "Architecture",
    "SST": "Service", "SRG": "ServiceRegistry",
    "LEP": "Lifecycle", "UMT": "Lifecycle",
    "CIC": "Capability", "SGT": "Capability", "MOV": "Capability",
    "IMT": "IPC", "IMB": "IPC", "RRC": "IPC", "ELC": "IPC", "MEI": "IPC",
    "DDT": "Scheduler", "ICS": "Scheduler", "BME": "Scheduler",
    "STD": "Scheduler", "IDLE": "Scheduler",
    "RDT": "ABI", "KSD": "ABI", "PIP": "ABI", "XVAL": "ABI",
    "SCO": "SchedContext", "Z7D": "SchedContext", "Z8J": "SchedContext",
    "ITR": "Testing", "PTY": "Testing",
    "RH": "RobinHood", "TPH": "TwoPhaseArch",
}

# Ordered module-path-prefix -> subsystem (first match wins).
MODULE_SUBSYSTEM_PREFIXES: list[tuple[str, str]] = [
    ("SeLe4n.Kernel.Scheduler", "Scheduler"),
    ("SeLe4n.Kernel.IPC", "IPC"),
    ("SeLe4n.Kernel.Capability", "Capability"),
    ("SeLe4n.Kernel.Lifecycle", "Lifecycle"),
    ("SeLe4n.Kernel.SchedContext", "SchedContext"),
    ("SeLe4n.Kernel.Service", "Service"),
    ("SeLe4n.Kernel.Architecture", "Architecture"),
    ("SeLe4n.Kernel.InformationFlow", "InformationFlow"),
    ("SeLe4n.Kernel.Concurrency", "Concurrency"),
    ("SeLe4n.Kernel.RobinHood", "RobinHood"),
    ("SeLe4n.Kernel.RadixTree", "RadixTree"),
    ("SeLe4n.Kernel.FrozenOps", "FrozenOps"),
    ("SeLe4n.Kernel.CrossSubsystem", "CrossSubsystem"),
    ("SeLe4n.Kernel.API", "API"),
    ("SeLe4n.Platform", "Platform"),
    ("SeLe4n.Model", "Model"),
    ("SeLe4n.Testing", "Testing"),
    ("SeLe4n.Prelude", "Core"),
    ("SeLe4n.Machine", "Core"),
    ("Main", "Entry"),
    ("tests", "Testing"),
]

# Exact module-name overrides for top-level files directly under
# SeLe4n/Kernel/ whose names extend a subsystem prefix without a separating
# dot (e.g. `CrossSubsystemPerCore` vs the `CrossSubsystem` prefix), so the
# prefix matcher would otherwise leave them Unknown. These are the SMP
# entry-seam and per-core cross-subsystem modules.
MODULE_SUBSYSTEM_EXACT: dict[str, str] = {
    "SeLe4n.Kernel.CrossSubsystemPerCore": "CrossSubsystem",
    "SeLe4n.Kernel.CrossSubsystemPerCorePreservation": "CrossSubsystem",
    "SeLe4n.Kernel.PerCoreTimerEntry": "Scheduler",
    "SeLe4n.Kernel.SecondaryEntry": "Concurrency",
    "SeLe4n.Kernel.SyscallDispatchEntry": "API",
}

TRACE_LINE_RE = re.compile(r"^\[([A-Za-z0-9]+-\d+[a-z]?)\]\s*(.*)$")
KERNEL_ERROR_RE = re.compile(r"KernelError\.([A-Za-z0-9_]+)")
INT_LIST_RE = re.compile(r"^#?\[\s*(-?\d+(?:\s*,\s*-?\d+)*)?\s*\]$")


def module_subsystem(module: str) -> str:
    exact = MODULE_SUBSYSTEM_EXACT.get(module)
    if exact is not None:
        return exact
    for prefix, sub in MODULE_SUBSYSTEM_PREFIXES:
        if module == prefix or module.startswith(prefix + "."):
            return sub
    return "Unknown"


def classify_value(value_text: str) -> dict:
    """Best-effort structured classification of a checkpoint's value.

    The raw text is always preserved by the caller, so this never loses
    information — it only enriches rendering.
    """
    v = value_text.strip()
    if v == "":
        return {"type": "none", "raw": value_text}
    if v in ("true", "false"):
        return {"type": "bool", "data": v == "true", "raw": value_text}
    m = KERNEL_ERROR_RE.search(v)
    if m:
        return {"type": "error", "data": m.group(1), "raw": value_text}
    if v.startswith("Except.ok"):
        return {"type": "ok", "raw": value_text}
    if v.startswith("none"):
        return {"type": "option", "data": None, "raw": value_text}
    lm = INT_LIST_RE.match(v)
    if lm:
        nums = [int(x) for x in lm.group(1).split(",")] if lm.group(1) else []
        return {"type": "registers", "data": nums, "raw": value_text}
    if v.startswith("some "):
        inner = v[5:].strip()
        im = INT_LIST_RE.match(inner)
        if im:
            nums = [int(x) for x in im.group(1).split(",")] if im.group(1) else []
            return {"type": "option", "data": nums, "raw": value_text}
        return {"type": "option", "data": inner, "raw": value_text}
    if re.fullmatch(r"-?\d+", v):
        return {"type": "nat", "data": int(v), "raw": value_text}
    return {"type": "text", "data": v, "raw": value_text}


def classify_outcome(value_text: str) -> dict:
    v = value_text.strip()
    if "Except.error" in v or KERNEL_ERROR_RE.search(v):
        m = KERNEL_ERROR_RE.search(v)
        return {"status": "expectedError", "error": m.group(1) if m else None}
    return {"status": "ok"}


def classify_kind(tag_prefix: str, text: str, outcome: dict) -> str:
    low = text.lower()
    if tag_prefix == "ITR" or ("invariant" in low and ("preserved" in low or "checks" in low)):
        return "invariantCheck"
    if tag_prefix == "XVAL":
        return "conformance"
    if tag_prefix == "PTY":
        return "topology"
    if tag_prefix in ("DDT", "ICS", "STD", "IDLE", "BME"):
        return "scheduling"
    if outcome["status"] == "expectedError":
        return "guard"
    return "transition"


def load_registry(path: Path) -> dict[str, dict]:
    """Load scenario_registry.yaml -> {id: {subsystem, source, function,
    description}}. Uses PyYAML when available; otherwise a small line parser
    for the registry's regular 2-space/4-space layout."""
    text = path.read_text(encoding="utf-8")
    try:
        import yaml  # type: ignore
        data = yaml.safe_load(text) or {}
        return dict(data.get("scenarios", {}))
    except Exception:
        scenarios: dict[str, dict] = {}
        current: str | None = None
        for line in text.splitlines():
            mid = re.match(r"^  ([A-Za-z0-9]+-\d+[a-z]?):\s*$", line)
            if mid:
                current = mid.group(1)
                scenarios[current] = {}
                continue
            mf = re.match(r'^    (\w+):\s*"?(.*?)"?\s*$', line)
            if mf and current:
                scenarios[current][mf.group(1)] = mf.group(2)
        return scenarios


def parse_trace(path: Path, registry: dict[str, dict]) -> list[dict]:
    events: list[dict] = []
    seq = 0
    for line in path.read_text(encoding="utf-8").splitlines():
        m = TRACE_LINE_RE.match(line.rstrip("\n"))
        if not m:
            continue
        seq += 1
        scenario_id, rest = m.group(1), m.group(2)
        tag_prefix = scenario_id.split("-", 1)[0]
        if ": " in rest:
            label, value_text = rest.split(": ", 1)
        else:
            label, value_text = rest, ""
        reg = registry.get(scenario_id, {})
        subsystem = reg.get("subsystem") or TAG_SUBSYSTEM.get(tag_prefix, "Unknown")
        outcome = classify_outcome(value_text if value_text else rest)
        events.append({
            "seq": seq,
            "tag": scenario_id,
            "scenarioId": scenario_id,
            "tagPrefix": tag_prefix,
            "subsystem": subsystem,
            "registered": scenario_id in registry,
            "sourceModule": reg.get("source"),
            "sourceFn": reg.get("function"),
            "kind": classify_kind(tag_prefix, rest, outcome),
            "label": label,
            "text": rest,
            "value": classify_value(value_text),
            "outcome": outcome,
        })
    return events


def build_trace_bundle(trace_id: str, title: str, path: Path,
                       registry: dict[str, dict]) -> dict:
    events = parse_trace(path, registry)
    return {"schemaVersion": SCHEMA_VERSION, "traceId": trace_id,
            "title": title, "eventCount": len(events), "events": events}


def build_atlas(codebase_map: dict) -> dict:
    modules = codebase_map.get("modules", [])
    # Global declaration-name -> module index, for resolving `called[]` to
    # module-level dependency edges.
    name_to_module: dict[str, str] = {}
    for mod in modules:
        mname = mod["module"]
        for decl in mod.get("declarations", []):
            name_to_module.setdefault(decl["name"], mname)

    atlas_modules: list[dict] = []
    subsystem_agg: dict[str, dict] = {}
    for mod in modules:
        mname = mod["module"]
        sub = module_subsystem(mname)
        decls = mod.get("declarations", [])
        theorem_count = sum(1 for d in decls if d["kind"] in ("theorem", "lemma"))
        def_count = sum(1 for d in decls if d["kind"] == "def")
        max_line = max((d.get("line", 0) for d in decls), default=0)
        deps: set[str] = set()
        for d in decls:
            for callee in d.get("called", []):
                tgt = name_to_module.get(callee)
                if tgt and tgt != mname:
                    deps.add(tgt)
        atlas_modules.append({
            "module": mname,
            "path": mod.get("path"),
            "subsystem": sub,
            "declarationCount": len(decls),
            "theoremCount": theorem_count,
            "defCount": def_count,
            "maxLine": max_line,
            "deps": sorted(deps),
        })
        agg = subsystem_agg.setdefault(sub, {
            "id": sub, "moduleCount": 0, "declarationCount": 0,
            "theoremCount": 0})
        agg["moduleCount"] += 1
        agg["declarationCount"] += len(decls)
        agg["theoremCount"] += theorem_count

    for sub, agg in subsystem_agg.items():
        pal = SUBSYSTEM_PALETTE.get(sub, SUBSYSTEM_PALETTE["Unknown"])
        agg["color"] = pal["color"]
        agg["icon"] = pal["icon"]

    atlas_modules.sort(key=lambda m: m["module"])
    subsystems = sorted(subsystem_agg.values(), key=lambda s: s["id"])
    module_edges = sum(len(m["deps"]) for m in atlas_modules)
    return {
        "schemaVersion": SCHEMA_VERSION,
        "subsystems": subsystems,
        "modules": atlas_modules,
        "moduleEdgeCount": module_edges,
    }


def canonical_bytes(obj: object) -> bytes:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"),
                      ensure_ascii=False).encode("utf-8")


def sha256_hex(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def build_bundle(repo: Path) -> dict[str, dict]:
    """Return {relative_output_path: json_object} for the whole bundle
    (everything except the manifest, whose hash covers these)."""
    codebase_map = json.loads((repo / "docs/codebase_map.json").read_text())
    registry = load_registry(repo / "tests/fixtures/scenario_registry.yaml")

    trace_specs = [
        ("main_trace_smoke", "Smoke trace",
         repo / "tests/fixtures/main_trace_smoke.expected"),
    ]
    outputs: dict[str, dict] = {}
    traces_meta: list[dict] = []
    for trace_id, title, path in trace_specs:
        if not path.exists():
            continue
        bundle = build_trace_bundle(trace_id, title, path, registry)
        rel = f"traces/{trace_id}/events.json"
        outputs[rel] = bundle
        traces_meta.append({
            "id": trace_id, "title": title,
            "eventCount": bundle["eventCount"],
            "hasState": False,
            "eventsUrl": rel,
        })

    atlas = build_atlas(codebase_map)
    outputs["atlas/index.json"] = atlas

    rs = codebase_map.get("readme_sync", {})
    summary = codebase_map.get("summary", {})
    manifest = {
        "schemaVersion": SCHEMA_VERSION,
        "bundleHash": None,  # filled below
        "sourceCommit": codebase_map.get("repository", {}).get("head", {}).get("commit_sha"),
        "codebaseMapDigest": codebase_map.get("source_sync", {}).get("source_digest"),
        "kernelVersion": rs.get("version"),
        "leanToolchain": rs.get("lean_toolchain"),
        "metrics": {
            "modules": summary.get("module_count"),
            "declarations": summary.get("declaration_count"),
            "moduleEdges": atlas["moduleEdgeCount"],
            "provedTheorems": rs.get("proved_theorem_lemma_decls"),
            "productionFiles": rs.get("production_files"),
            "productionLoc": rs.get("production_loc"),
            "hardwareTarget": rs.get("hardware_target"),
        },
        "subsystems": [
            {"id": s["id"], "color": s["color"], "icon": s["icon"],
             "moduleCount": s["moduleCount"], "theoremCount": s["theoremCount"]}
            for s in atlas["subsystems"]
        ],
        "traces": traces_meta,
        "chunks": {"atlas": "atlas/index.json"},
    }

    # Deterministic bundle hash over every non-manifest output.
    digest = hashlib.sha256()
    for rel in sorted(outputs):
        digest.update(rel.encode("utf-8"))
        digest.update(b"\0")
        digest.update(sha256_hex(canonical_bytes(outputs[rel])).encode("utf-8"))
        digest.update(b"\0")
    manifest["bundleHash"] = "sha256:" + digest.hexdigest()
    outputs["manifest.json"] = manifest
    return outputs


def write_bundle(outputs: dict[str, dict], out_dir: Path) -> None:
    for rel, obj in sorted(outputs.items()):
        dest = out_dir / rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(
            json.dumps(obj, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
            encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="Build the seLe4n Observatory data bundle.")
    ap.add_argument("--out", default=str(ROOT / "web/public/data"),
                    help="output directory for the bundle")
    ap.add_argument("--print-hash", action="store_true",
                    help="print only the deterministic bundleHash and exit")
    args = ap.parse_args(argv)

    outputs = build_bundle(ROOT)
    if args.print_hash:
        print(outputs["manifest.json"]["bundleHash"])
        return 0
    out_dir = Path(args.out)
    write_bundle(outputs, out_dir)
    man = outputs["manifest.json"]
    traces = outputs and man["traces"]
    nevents = sum(t["eventCount"] for t in traces)
    print(f"wrote bundle to {out_dir}")
    print(f"  bundleHash:   {man['bundleHash']}")
    print(f"  traces:       {len(traces)} ({nevents} events)")
    print(f"  atlas:        {len(outputs['atlas/index.json']['modules'])} modules, "
          f"{len(outputs['atlas/index.json']['subsystems'])} subsystems, "
          f"{outputs['atlas/index.json']['moduleEdgeCount']} module edges")
    print(f"  files:        {len(outputs)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
