# CLAUDE.md — Active Workstream Context (Archive)

This file archives prose from the `## Active workstream context` section of
`CLAUDE.md` once the section grows past the easy-to-skim threshold. It is
the historical record of "what was the recent active workstream slice"
across releases.

The convention (per WS-AN AN12-D / DOC LOW batch):

- **Active**: the most recent 3 release cuts (or the most recent
  workstream's last 3 phases) live inline in `CLAUDE.md`.
- **Archive**: everything older lives here, in inverse-chronological
  order. Each entry preserves the original workstream paragraph
  verbatim, prefixed by its release version + branch.

Cross-reference for canonical workstream history: see
[`docs/WORKSTREAM_HISTORY.md`](WORKSTREAM_HISTORY.md). This file holds
prose only — the `WORKSTREAM_HISTORY.md` document remains the canonical
source of truth for workstream status.

---

## Archived: WS-AN Phases AN0..AN11 (v0.30.6 → v0.30.10)

The verbose per-phase entries for WS-AN AN0 through AN11 (including the
post-delivery audit pass entries for AN5, AN6, AN8, AN9, AN10, and AN11)
were archived from `CLAUDE.md` at the AN12 closure. The canonical
record is:

- [`docs/WORKSTREAM_HISTORY.md`](WORKSTREAM_HISTORY.md) — phase-by-phase
  closure with gate-state tables.
- [`CHANGELOG.md`](../CHANGELOG.md) — per-version release notes.
- [`docs/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md`](audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md)
  — original 13-phase plan with sub-task breakdown.
- [`docs/audits/AUDIT_v0.30.6_DISCHARGE_INDEX.md`](audits/AUDIT_v0.30.6_DISCHARGE_INDEX.md)
  — closure-form discharge index landed at AN12-A.

Each WS-AN phase landed under a dedicated branch on
`hatter6822/seLe4n`; the branches are preserved in git history.

---

## Archived: Pre-WS-AN workstreams (WS-AK / WS-AM / WS-AL and earlier)

The cumulative active-workstream prose for WS-AK Phase AK10 (v0.30.6
closure), WS-AM (v0.30.0 cascade hygiene closure), WS-AL (v0.29.14 AK7
cascade closure via AL1b/AL8), the WS-AJ portfolio (v0.28.1 → v0.29.0
post-audit comprehensive remediation), the WS-AI portfolio (v0.27.7 →
v0.28.0), the WS-AH portfolio (v0.27.2 → v0.27.6), the WS-AG portfolio
(v0.26.0 → v0.27.0 H3 hardware-binding audit remediation), the WS-AF
portfolio (v0.25.22 → v0.25.27), and the prior WS-AC / WS-AD / WS-AE /
WS-AB / WS-AA cycles is archived under
[`docs/WORKSTREAM_HISTORY.md`](WORKSTREAM_HISTORY.md). Each portfolio
has its own canonical section in that file with full gate results and
finding disposition.

---

## How to use this file

- **Casual lookup**: skim `CLAUDE.md` for the active workstream — that's
  always the current slice.
- **Audit / git-archeology**: use `WORKSTREAM_HISTORY.md` for the
  canonical record across all closed workstreams.
- **Per-finding traceability**: use the discharge index
  (`AUDIT_v0.30.6_DISCHARGE_INDEX.md`) and the deferred-tracking file
  (`AUDIT_v0.29.0_DEFERRED.md`) for closed-finding cross-references.

When future workstreams open, the active-workstream paragraphs land in
`CLAUDE.md` first; once the workstream closes, its entries get summarised
into a single paragraph in this file with cross-references to
`WORKSTREAM_HISTORY.md`.
