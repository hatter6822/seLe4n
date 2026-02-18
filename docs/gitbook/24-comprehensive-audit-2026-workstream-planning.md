# Comprehensive Audit 2026 Workstream Planning

This is the GitBook mirror of the canonical planning backbone:
[`docs/audits/AUDIT_v0.9.0_WORKSTREAM_PLAN.md`](../audits/AUDIT_v0.9.0_WORKSTREAM_PLAN.md).

## 1) Why this chapter exists

- make the active slice obvious for new contributors,
- provide one-page navigation for WS-B workstreams,
- keep handbook structure aligned with the normative/audit docs.

## 2) Active workstream index (WS-B)

### High priority

- **WS-B1:** VSpace + memory model foundation ✅ completed
- **WS-B2:** Generative + negative testing expansion ✅ completed
- **WS-B3:** Main trace harness refactor ✅ completed
- **WS-B4:** Remaining type-wrapper migration ✅ completed

### Medium priority

- **WS-B5:** CSpace guard/radix semantics completion ✅ completed
- **WS-B6:** Notification-object IPC completion ✅ completed
- **WS-B7:** Information-flow proof-track start ✅ completed
- **WS-B8:** Documentation automation + consolidation ✅ completed
- **WS-B9:** Threat model and security hardening ✅ completed

### Low priority

- **WS-B10:** CI maturity upgrades ✅ completed
- **WS-B11:** Scenario framework finalization ✅ completed

## 3) Sequencing

- **Phase P1:** WS-B4 + WS-B3 + WS-B8 (WS-B3/WS-B4/WS-B8 completed)
- **Phase P2:** WS-B5 + WS-B6 + WS-B2 (WS-B1/WS-B2/WS-B5/WS-B6 complete; WS-B7 completed)
- **Phase P3:** WS-B7 + WS-B9 + WS-B10 + WS-B11 (WS-B7/WS-B9/WS-B10/WS-B11 completed)

## 4) Evidence expectations for milestone-moving PRs

- workstream ID mapping,
- implementation/proof/test evidence,
- docs synchronization,
- explicit deferred items,
- no regression of stable M4–M7 baseline contracts.

## 5) Where to update status

When status changes, update together:

1. `docs/audits/AUDIT_v0.9.0_WORKSTREAM_PLAN.md` (canonical)
2. `README.md` active-slice snapshot
3. `docs/SEL4_SPEC.md` milestone state
4. this chapter


## 6) WS-B1 closure evidence

- executable VSpace transitions: `SeLe4n/Kernel/Architecture/VSpace.lean`,
- VSpace invariant bundle and preservation anchors: `SeLe4n/Kernel/Architecture/VSpaceInvariant.lean`,
- deterministic map/unmap trace path in `Main.lean` + fixture update,
- ADR published: [`docs/VSPACE_MEMORY_MODEL_ADR.md`](../VSPACE_MEMORY_MODEL_ADR.md).

## 7) WS-B2 closure evidence

- bootstrap-state builder DSL published in `SeLe4n/Testing/StateBuilder.lean`,
- malformed-state negative suite published in `tests/NegativeStateSuite.lean` and enforced in smoke/full gates via `scripts/test_tier2_negative.sh`,
- nightly experimental replay now persists stochastic seed logs and `trace_sequence_probe_manifest.csv` for deterministic triage.

## 8) WS-B3 closure evidence

- `Main.lean` now provides a minimal executable entrypoint and delegates trace orchestration to `SeLe4n/Testing/MainTraceHarness.lean` (with dedicated scenario functions),
- bootstrap state construction moved to list/builder composition via `SeLe4n/Testing/StateBuilder.lean`,
- Tier 2 trace fixture expectations remain stable (`tests/fixtures/main_trace_smoke.expected`) under `scripts/test_tier2_trace.sh` and full-suite execution.


## 9) WS-B4 closure evidence

- `SeLe4n/Prelude.lean` upgrades `DomainId`, `Priority`, `Irq`, `Badge`, `ASID`, `VAddr`, and `PAddr` from `Nat` aliases to dedicated wrapper structures with explicit `ofNat`/`toNat` helpers.
- Compatibility ergonomics are preserved via targeted `OfNat` and `ToString` instances, so existing deterministic fixtures remain readable while retaining type separation.
- Tier 0 now includes a WS-B4 regression guard in `scripts/test_tier0_hygiene.sh` that fails if any of the migrated wrappers revert to `abbrev ... := Nat`.


## 10) WS-B5 closure evidence

- `SeLe4n/Model/Object.lean` now includes `CNode.resolveSlot` with explicit guard/radix resolution and depth/guard failure branches.
- `SeLe4n/Kernel/Capability/Operations.lean` adds `CSpacePathAddr`, `cspaceResolvePath`, and `cspaceLookupPath` so CSpace pointer-path traversal is executable alongside direct slot lookups.
- `tests/NegativeStateSuite.lean` now enforces WS-B5 negative-path checks for depth mismatch and guard mismatch outcomes in `scripts/test_tier2_negative.sh`.
- `tests/fixtures/main_trace_smoke.expected` now includes source/deep CSpace path anchors enforced by `scripts/test_tier2_trace.sh`.

## 11) WS-B6 closure evidence

- `SeLe4n/Model/Object.lean` now includes `NotificationState` + `Notification` and extends `KernelObject` with a notification variant.
- `SeLe4n/Kernel/IPC/Operations.lean` adds executable `notificationSignal` and `notificationWait` semantics with runnable-queue interactions (block on wait, wake on signal).
- `SeLe4n/Kernel/IPC/Invariant.lean` now includes `notificationQueueWellFormed`/`notificationInvariant`, and `ipcInvariant` now covers both endpoint and notification object classes.
- `SeLe4n/Testing/MainTraceHarness.lean` and `tests/fixtures/main_trace_smoke.expected` now exercise composed endpoint + notification flows.
- `tests/NegativeStateSuite.lean` adds positive/negative notification-path checks in Tier 2 negative validation.

## 12) WS-B7 closure evidence

- IF-M1 baseline primitives are implemented in:
  - `SeLe4n/Kernel/InformationFlow/Policy.lean` (labels + flow relation + algebraic lemmas),
  - `SeLe4n/Kernel/InformationFlow/Projection.lean` (observer projection + low-equivalence scaffold).
- theorem targets and assumptions ledger are published in [`docs/IF_M1_BASELINE_PACKAGE.md`](../IF_M1_BASELINE_PACKAGE.md).
- roadmap/proof-map sync now includes IF-M1 completion markers in:
  - `docs/INFORMATION_FLOW_ROADMAP.md`,
  - `docs/gitbook/12-proof-and-invariant-map.md`.
- Tier 2 includes IF-M1 runtime sanity checks via `tests/InformationFlowSuite.lean` (`lake exe information_flow_suite`) in `scripts/test_tier2_negative.sh`.
- Tier 3 invariant/doc anchors now check IF-M1 surfaces in `scripts/test_tier3_invariant_surface.sh`.



## 13) WS-B8 closure evidence

- GitBook navigation pages are generated from `docs/gitbook/navigation_manifest.json` via `scripts/generate_doc_navigation.py` (`docs/gitbook/README.md`, `docs/gitbook/SUMMARY.md`).
- Markdown link validation now runs in `scripts/check_markdown_links.py` through `scripts/test_docs_sync.sh`, and Tier 0 executes it by default via `scripts/test_tier0_hygiene.sh`.
- CI now includes a docs lane (`Docs Automation / Navigation + Links + DocGen Probe`) in `.github/workflows/lean_action_ci.yml` to enforce documentation automation before smoke/full lanes.
- Root↔GitBook dedup ownership is captured in [`docs/DOCS_DEDUPLICATION_MAP.md`](../DOCS_DEDUPLICATION_MAP.md) and mirrored in chapter 27.
- Planning/doc PR checklist enforcement is codified in `.github/pull_request_template.md`.


## 14) WS-B9 closure evidence

- Threat assumptions/trust boundaries are now canonicalized in [`docs/THREAT_MODEL.md`](../THREAT_MODEL.md) with GitBook mirror [Threat Model and Security Hardening (WS-B9)](28-threat-model-and-security-hardening.md).
- Repository hygiene now excludes common local secret/config and scanner artifacts via `.gitignore` denylist expansion.
- `scripts/setup_lean_env.sh` now enforces installer integrity by downloading elan installer content to a temporary file and validating `ELAN_INSTALLER_SHA256` before execution.
- CI policy linkage is synchronized in [`docs/CI_POLICY.md`](../CI_POLICY.md), and Tier 3 invariant/doc anchors continuously enforce WS-B9 security-surface markers.

## 15) WS-B10 closure evidence

- CodeQL required-vs-informational policy is explicitly documented in [`docs/CI_POLICY.md`](../CI_POLICY.md) and reflected in workflow step naming at `.github/workflows/platform_security_baseline.yml`.
- Lean/toolchain update automation now includes Dependabot for GitHub Actions (`.github/dependabot.yml`) and scheduled Lean release drift proposals via `.github/workflows/lean_toolchain_update_proposal.yml`.
- CI timing + flake telemetry is now collected by `scripts/ci_capture_timing.sh` and `scripts/ci_flake_probe.sh`, wired into Lean CI and nightly workflows.
- Canonical telemetry interpretation guidance is published in [`docs/CI_TELEMETRY_BASELINE.md`](../CI_TELEMETRY_BASELINE.md) with GitBook mirror [CI Maturity and Telemetry Baseline (WS-B10)](29-ci-maturity-and-telemetry-baseline.md).

## 16) WS-B11 closure evidence

- scenario metadata is now canonicalized in `tests/scenarios/scenario_catalog.json` with explicit fields for scenario IDs, subsystem ownership, risk tags, replay tier, deterministic seeds, and fixture anchors.
- `scripts/scenario_catalog.py` enforces schema and fixture-anchor validation (`validate`) and exports nightly deterministic seeds (`nightly-seeds`).
- smoke and nightly paths now exercise the scenario framework directly:
  - `scripts/test_smoke.sh` runs catalog validation,
  - `scripts/test_tier4_nightly_candidates.sh` materializes nightly seeds from the catalog and replays `trace_sequence_probe` from generated metadata.
- maintenance ownership and cadence are documented in `tests/scenarios/README.md` (`testing-maintainers`, `per-slice` review).
