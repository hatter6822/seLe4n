# `docs/audits/` — Active audit artefacts

This directory holds the **single active audit's** artefacts plus any
errata, deferred-tracking, or discharge-index files that the active
workstream produces. When a new audit cuts and a new workstream opens, the
prior audit's artefacts are archived under
[`docs/dev_history/audits/`](../dev_history/audits/) so that
`docs/audits/` never accumulates stale documents.

This convention is the **"one active audit at a time" rule** (DOC LOW
batch, WS-AN AN12-D).

## Audit lifecycle

A typical audit goes through four stages:

| Stage | Files in `docs/audits/` | Notes |
|-------|-------------------------|-------|
| **Audit cut** | `AUDIT_v<X>_COMPREHENSIVE.md` | Initial finding inventory + severity table. |
| **Workstream planning** | `+ AUDIT_v<X>_WORKSTREAM_PLAN.md`, `+ AUDIT_v<X>_WS_*_BASELINE.txt` | Per-phase decomposition + numeric snapshot at workstream start. |
| **In-flight remediation** | `+ AUDIT_v<X>_DISCHARGE_INDEX.md`, `+ AUDIT_v<X>_DEFERRED.md` (if any items defer past this workstream) | Discharge index aggregates the closure-form proof obligations; deferred file lists items pushed to a future workstream. |
| **Workstream closure** | `+ AUDIT_v<X>_ERRATA.md` (if any) | Audit-text corrections discovered during remediation. |

Once the workstream closes:

1. The plan + comprehensive + (optionally) errata + deferred files are
   moved to `docs/dev_history/audits/` (see WS-AK closure commits for
   the precedent).
2. `docs/WORKSTREAM_HISTORY.md` records the closure with cross-references
   to the archived files.
3. `scripts/website_link_manifest.txt` is updated so the website's
   "Latest audit" link points at the next active audit (or its archived
   location while there is no successor).

## Files currently live (v0.30.11 pre-1.0 cut, WS-RC IN FLIGHT)

- `AUDIT_v0.30.11_COMPREHENSIVE.md` — **active pre-1.0 readiness audit
  cut (2026-04-26)**. Succeeds `AUDIT_v0.30.6_COMPREHENSIVE.md` (now
  archived under `docs/dev_history/audits/`). Identifies the DEBT-*
  inventory (17 items: 3 pre-v1.0, 1 v1.0, 13 post-1.0).
- `AUDIT_v0.30.11_DEEP_VERIFICATION.md` — **deep verification pass on
  the same v0.30.11 cut (2026-04-28)**, done at user request to
  re-derive every claim from source rather than trust the comprehensive
  audit's documented findings. Builds on (does not supersede) the
  comprehensive audit; introduces ~52 new finding IDs (DEEP-*) including
  two H-severity items the predecessor missed: DEEP-FFI-01 (Lean ↔
  Rust syscall-dispatch glue is a stub returning `NotImplemented = 17`
  on hardware) and DEEP-DOC-01 (README internally inconsistent on the
  proved-declaration count). Both predecessor and verification audit
  feed the WS-RC remediation plan.
- `AUDIT_v0.30.11_WORKSTREAM_PLAN.md` — **WS-RC remediation plan**
  (15 phases R0..R14, ~68 active items). Decomposes the comprehensive
  + deep audits into per-phase implementation slices with verified
  file/line targets, validation gates, dependencies, and commit-message
  scaffolding. Applies the CLAUDE.md "implement-the-improvement rule"
  uniformly: even false-positive audit findings receive structural
  enforcement gates (§1.5 policy).
- `AUDIT_v0.30.11_ERRATA.md` — audit-text corrections discovered during
  WS-RC remediation planning (E-1: DEEP-ARCH-01 verification rationale
  incorrect; E-2: DEEP-ARCH-02 consumer count refined; E-3: DEEP-RUST-01/02
  partial verification refined to two-tier rule; E-4: plan-internal
  corrections from live-tree verification).
- `AUDIT_v0.30.11_WS_RC_BASELINE.txt` — **WS-RC numeric baseline at
  workstream start (R0.1, 2026-04-29)**. LoC, file/module counts,
  declaration histogram, source-purity metrics (sorry/axiom/Classical/
  native_decide/partial def all 0 or comment-only), Rust unsafe-block
  census, build/test gate state (302 lake jobs / 462 cargo tests / 0
  clippy warnings), production/staged module partition (158/10),
  audit-finding tally, predecessor closure reconfirmation
  (DEBT-RUST-02 / H-24, 0 hits). Machine-diffable KEY=value tail.
- `AUDIT_v0.30.11_DISCHARGE_INDEX.md` — **WS-RC closure-form discharge
  index (R0.3 seed)**. Empty at R0; populated incrementally as R4 / R12
  produce closure-form theorems and structural witnesses. §3.A–§3.C
  carry forward the predecessor v0.30.6 inventory unchanged; §3.D
  (NoDup / structural promotions), §3.E (predecessor reroutings), §3.F
  (false-positive structural witnesses) are WS-RC-introduced sections;
  §3.G records the DEBT-RUST-02 / H-24 reconfirmation landed at R0.4.

## Recently archived (WS-AN closure, v0.30.11)

The following predecessor artefacts were archived to
[`docs/dev_history/audits/`](../dev_history/audits/) once WS-AN closed
at v0.30.11 (every absorbed `AUDIT_v0.29.0_DEFERRED.md` row landed
RESOLVED in-place except DEF-F-L9 which is retained post-v1.0 as a
cosmetic refactor with no correctness impact):

- `AUDIT_v0.30.6_COMPREHENSIVE.md` — predecessor active audit (196
  findings; remediated by WS-AN AN0..AN12).
- `AUDIT_v0.30.6_WORKSTREAM_PLAN.md` — WS-AN remediation plan
  (AN0..AN12).
- `AUDIT_v0.30.6_WS_AN_BASELINE.txt` — numeric baseline at WS-AN start.
- `AUDIT_v0.30.6_DISCHARGE_INDEX.md` — Theme 4.1 closure-form discharge
  index (landed at AN12-A; see also the marker theorem
  `closureForm_discharge_index_documented` in
  `SeLe4n/Kernel/CrossSubsystem.lean`).
- `AUDIT_v0.29.0_COMPREHENSIVE.md` — pre-1.0 full-kernel audit
  (remediated by WS-AK AK1..AK10).
- `AUDIT_v0.29.0_DEFERRED.md` — deferred-item tracking absorbed by
  WS-AN; every row RESOLVED at v0.30.11 (closure summary at the top of
  the file). DEF-F-L9 retained as a post-v1.0 cosmetic refactor with
  no correctness impact.
- `AUDIT_v0.29.0_ERRATA.md` — errata for the v0.29.0 audit (E-1..E-6).
- `AL0_baseline.txt` — AL0 monotonicity baseline (re-anchored at every
  WS-AN AN10 commit; the AK7 cascade gate
  `scripts/ak7_cascade_check_monotonic.sh` reads it from the archived
  path until the next workstream cuts a fresh baseline).

## Archival policy

Archive a file to `docs/dev_history/audits/` only when:

1. The associated workstream has closed (gate-state table in
   `docs/WORKSTREAM_HISTORY.md`).
2. The artefact is no longer the **canonical** reference for an active
   workstream.
3. `scripts/website_link_manifest.txt` no longer references it OR every
   reference to it has been rewritten to the archived path.

The CI gate `scripts/check_website_links.sh` enforces consistency between
the manifest and the on-disk tree, so archive moves and manifest updates
must happen in the same PR.

## See also

- [`docs/WORKSTREAM_HISTORY.md`](../WORKSTREAM_HISTORY.md) — canonical
  workstream closure record.
- [`docs/dev_history/audits/`](../dev_history/audits/) — archived audits.
- [`scripts/website_link_manifest.txt`](../../scripts/website_link_manifest.txt) — protected paths.
