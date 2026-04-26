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

## Files currently live (v0.30.6 → v0.30.11)

- `AUDIT_v0.30.6_COMPREHENSIVE.md` — the active comprehensive audit.
- `AUDIT_v0.30.6_WORKSTREAM_PLAN.md` — WS-AN remediation plan
  (AN0..AN12).
- `AUDIT_v0.30.6_WS_AN_BASELINE.txt` — numeric baseline at WS-AN start.
- `AUDIT_v0.30.6_DISCHARGE_INDEX.md` — Theme 4.1 closure-form discharge
  index (landed at AN12-A; see also the marker theorem
  `closureForm_discharge_index_documented` in
  `SeLe4n/Kernel/CrossSubsystem.lean`).
- `AUDIT_v0.29.0_COMPREHENSIVE.md` — predecessor audit (kept here while
  WS-AN absorbs items from `AUDIT_v0.29.0_DEFERRED.md`).
- `AUDIT_v0.29.0_DEFERRED.md` — deferred-item tracking; every row is
  RESOLVED at v0.30.11 (WS-AN closure). Closure summary at the top of
  the file.
- `AUDIT_v0.29.0_ERRATA.md` — errata for the v0.29.0 audit (E-1..E-6).
- `AL0_baseline.txt` — historical AL0 monotonicity baseline (re-anchored
  at every WS-AN AN10 commit).

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
