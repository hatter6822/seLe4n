# seLe4n Observatory — web application

This directory hosts the **seLe4n Observatory**, the kernel-visualization
web application specified in
[`docs/planning/KERNEL_OBSERVATORY_WEBAPP_SPEC.md`](../docs/planning/KERNEL_OBSERVATORY_WEBAPP_SPEC.md).

The Observatory fuses three layers — **Execution** (the deterministic
trace), **State** (the kernel heap it mutates), and **Proof** (the
machine-checked theorems that prove each step safe) — and lets you pivot
between them. See the spec for the full design.

## Status

Early implementation, tracking the spec's phased roadmap (§16):

| Component | State | Notes |
|-----------|-------|-------|
| **P0 data pipeline** | ✅ landed | `scripts/build_observatory_data.py` + unit test |
| Trace Theater (reference viewer) | 🛠 prototype | `web/prototype/` — zero-dependency, validates the data contract |
| State exporter (E2) / Proof index (E3) | ⏳ planned | enable the State & Proof tabs |
| Production SPA (React + TS) | ⏳ planned | supersedes the prototype |

## The data pipeline (P0)

`scripts/build_observatory_data.py` transforms the kernel's existing,
deterministic artifacts into a web-consumable JSON bundle. It reads only
(never modifies the kernel or its fixtures) and is deterministic —
identical inputs yield an identical `bundleHash`.

```bash
# Build the bundle into web/public/data/ (git-ignored; rebuilt on demand)
python3 scripts/build_observatory_data.py

# Print only the deterministic bundle hash (CI anti-drift anchor)
python3 scripts/build_observatory_data.py --print-hash

# Validate the pipeline
python3 -m unittest scripts.tests.test_build_observatory_data
```

### Bundle layout

```
web/public/data/
  manifest.json                    # metrics, subsystem palette, trace index, bundleHash
  atlas/index.json                 # 312 modules + 19 subsystems + module dependency edges
  traces/main_trace_smoke/
    events.json                    # the 233 deterministic trace events, joined to the
                                   #   scenario registry (subsystem/source/function)
```

Inputs (all already in the repo):
`docs/codebase_map.json`,
`tests/fixtures/scenario_registry.yaml`,
`tests/fixtures/main_trace_smoke.expected`.
Data contracts are specified in the spec, §14.

## The prototype viewer

`web/prototype/index.html` is a **zero-dependency** reference
implementation of the Trace Theater. It loads the generated bundle and
renders the execution stream, transport controls, and per-event detail.
It exists to validate the data contract and demonstrate the flagship view;
the **production** Observatory uses the React + TypeScript stack defined in
the spec (§7) and supersedes it.

```bash
python3 scripts/build_observatory_data.py          # 1. build the bundle
cd web && python3 -m http.server 8080              # 2. serve this directory
# 3. open http://localhost:8080/prototype/
```

(A static file server is needed because the viewer `fetch`es the JSON
bundle; opening via `file://` is blocked by browser CORS rules.)
