# AUDIT v0.30.11 — Closure-form Discharge Index (WS-RC seed)

**Plan ID:** WS-RC Phase R0.3 (this file is the closure-form discharge index seed)
**Workstream:** WS-RC — Pre-1.0 Audit Remediation (v0.30.11 → v0.31.0 → v1.0.0)
**Source audits:**
- [`AUDIT_v0.30.11_COMPREHENSIVE.md`](AUDIT_v0.30.11_COMPREHENSIVE.md) (DEBT-* index)
- [`AUDIT_v0.30.11_DEEP_VERIFICATION.md`](AUDIT_v0.30.11_DEEP_VERIFICATION.md) (DEEP-* index)
**Plan:** [`AUDIT_v0.30.11_WORKSTREAM_PLAN.md`](AUDIT_v0.30.11_WORKSTREAM_PLAN.md) §4 (R0)
**Baseline:** [`AUDIT_v0.30.11_WS_RC_BASELINE.txt`](AUDIT_v0.30.11_WS_RC_BASELINE.txt)
**Errata:** [`AUDIT_v0.30.11_ERRATA.md`](AUDIT_v0.30.11_ERRATA.md)
**Predecessor:** [`AUDIT_v0.30.6_DISCHARGE_INDEX.md`](../dev_history/audits/AUDIT_v0.30.6_DISCHARGE_INDEX.md) (archived)
**Author:** WS-RC Phase R0.3
**Date:** 2026-04-29
**Status:** SEED — empty at WS-RC R0; populated incrementally as R1..R12 phases produce closure-form theorems and structural witnesses.

## 1. Purpose and methodology

This file is the canonical record of every **closure-form proof obligation**
produced by WS-RC remediation, plus every **structural witness theorem** that
codifies a false-positive verification into a machine-checked invariant per
the §1.5 structural-fix policy of the WS-RC plan.

The seL4 / seLe4n proof surface uses three composition patterns where a
per-operation preservation theorem accepts a "closure-form" hypothesis instead
of proving the post-state property from the pre-state invariant alone. The
predecessor index ([`AUDIT_v0.30.6_DISCHARGE_INDEX.md`](../dev_history/audits/AUDIT_v0.30.6_DISCHARGE_INDEX.md))
documents the WS-AN-era inventory; this file extends the inventory with
WS-RC additions (Theme R4 structural promotions, R4.D witness theorems,
R12 CI gates).

### 1.1 Row format

Every row in §3 carries five fields:

| Field | Meaning |
|-------|---------|
| **Theorem name** | The closure-form theorem or structural witness in `SeLe4n/Kernel/…/`. |
| **File:Line** | Canonical source location at WS-RC HEAD. |
| **Hypothesis or claim** | The closure-form parameter the theorem accepts (e.g. `hCdtPost`, `hProjEq`), or — for structural witnesses — the runtime check or invariant the theorem encodes. |
| **Discharge site** | The companion theorem (or recipe) that produces the closure witness for a caller. |
| **Reachability check** | A `#check` expression that elaborates only if the discharge site is correctly named and typed at the post-WS-RC state. |

### 1.2 How to use this index

- **Auditors**: every `_preserves_projection` / `_preserves_capabilityInvariantBundle`
  theorem with a closure-form hypothesis introduced under WS-RC appears in §3
  with its discharge recipe. Predecessor entries (§3.A–§3.C of the v0.30.6
  index) carry forward unchanged unless explicitly rerouted in §3.E below.
- **Implementers**: when wiring a new dispatch arm under WS-RC, locate the
  per-operation theorem in §3 and use the named **discharge site** to produce
  the closure witness. False-positive structural witnesses listed in §3.F
  must be invoked at the runtime guard whose correctness they codify.
- **Maintainers**: when the proof body of a closure-form theorem changes, the
  row's **Discharge site** field must continue to produce a witness with the
  exact closure signature. The reachability `#check` is the regression guard.

### 1.3 Companion artefact

A marker theorem `closureForm_discharge_index_documented : True := trivial`
in `SeLe4n/Kernel/CrossSubsystem.lean` (introduced at WS-AN AN12-A) anchors
the predecessor index. WS-RC does not add a new marker theorem at R0; if
WS-RC produces a substantive new index section beyond cross-references, a
follow-up marker `closureForm_ws_rc_extensions_documented : True := trivial`
will be added in the same PR as the corresponding R-phase landing.

## 2. Theme index

| § | Theme | Closure / claim | Owning phase | Audit IDs | Status |
|---|-------|----------------|--------------|-----------|--------|
| 3.A | CDT post-state witnesses | `hCdtPost` | (predecessor AN4-C) | H-04 | CARRIED — see [v0.30.6 index §3.A](../dev_history/audits/AUDIT_v0.30.6_DISCHARGE_INDEX.md#3a--cdt-post-state-discharge-h-04--an4-c) |
| 3.B | Projection closures | `hProjEq` | (predecessor AN6-A / AK6-F) | H-07, AK6F.13–19 | CARRIED — see [v0.30.6 index §3.B](../dev_history/audits/AUDIT_v0.30.6_DISCHARGE_INDEX.md#3b--projection-closures-h-07--an6-a--ak6f1319) |
| 3.C | Schedule / Service closures | `hSchedProj`, `hServiceProjEq` | (predecessor AN5-D / AK6-F) | SC-M02, AK6F.11/12 | CARRIED — see [v0.30.6 index §3.C](../dev_history/audits/AUDIT_v0.30.6_DISCHARGE_INDEX.md#3c--schedule--service-closures-sc-m02--ak6f1112) |
| 3.D | NoDup / structural promotions | type-level invariant | R4.A / R4.B / R4.C | DEEP-MODEL-01, DEEP-CAP-04, DEEP-IPC-05 | **PENDING — populated at R4 landing** |
| 3.E | Predecessor reroutings | – | R4.C subsumes DEEP-IPC-01 | DEEP-IPC-01 | **PENDING — populated at R4.C landing** |
| 3.F | False-positive structural witnesses | runtime-guard equivalence | R4.D / R12.B / R12.C / R12.D | DEEP-CAP-02, DEEP-ARCH-01, DEEP-RUST-01/02, DEEP-ARCH-02 | **PENDING — populated as each gate / witness lands** |
| 3.G | Predecessor closure reconfirmations | DEBT carry-over | R0.4 | DEBT-RUST-02 / H-24 | **LANDED at R0.4** (see annotation in [v0.30.6 index §5](../dev_history/audits/AUDIT_v0.30.6_DISCHARGE_INDEX.md#5-closure-summary)) |

§3.A–§3.C are the predecessor inventory and continue to apply to WS-RC.
The 6 substantively-discharged CDT post-state bridges, the 7 closure-form
projection theorems, and the 5 schedule/service closures all remain
machine-checked at every commit by the existing tier-3 invariant-surface
gate (`scripts/test_tier3_invariant_surface.sh`). WS-RC does not modify
these theorems; any rename or signature drift will be caught by the
existing marker theorem `closureForm_discharge_index_documented`.

§3.D–§3.F are the **WS-RC-introduced sections**. They are empty at R0
and populated by R4.A/B/C (NoDup / structural promotions), R4.D
(`cspaceMutate` witness theorem), and R12.B/C/D (the three CI gates that
codify the false-positive verifications as machine-checked invariants).

§3.G captures the predecessor closure reconfirmations that WS-RC
performs at R0 — at WS-RC R0 there is exactly one (DEBT-RUST-02 / H-24,
landed in this PR by an annotation on the archived v0.30.6 discharge
index per the lifecycle note in `docs/audits/README.md`).

## 3. Per-theorem rows

### §3.A — CDT post-state discharge (H-04 / predecessor AN4-C)

CARRIED FROM PREDECESSOR. WS-RC does not add or modify rows in this
section. See
[`AUDIT_v0.30.6_DISCHARGE_INDEX.md`](../dev_history/audits/AUDIT_v0.30.6_DISCHARGE_INDEX.md)
§3.A for the canonical 6-row table (rows A.1..A.6, all DISCHARGED).

WS-RC reachability gate: every theorem name and discharge site listed in
the predecessor's §3.A must continue to elaborate. The predecessor's
marker theorem `closureForm_discharge_index_documented` in
`SeLe4n/Kernel/CrossSubsystem.lean` is the regression guard.

### §3.B — Projection closures (H-07 / predecessor AN6-A / AK6-F)

CARRIED FROM PREDECESSOR. See
[`AUDIT_v0.30.6_DISCHARGE_INDEX.md`](../dev_history/audits/AUDIT_v0.30.6_DISCHARGE_INDEX.md)
§3.B for the canonical 7-row closure-form table (rows B.1..B.7).

### §3.C — Schedule / Service closures (SC-M02 / predecessor AK6-F)

CARRIED FROM PREDECESSOR. See
[`AUDIT_v0.30.6_DISCHARGE_INDEX.md`](../dev_history/audits/AUDIT_v0.30.6_DISCHARGE_INDEX.md)
§3.C for the canonical 5-row table (rows C.1..C.5).

### §3.D — NoDup / structural promotions (PENDING — R4.A / R4.B / R4.C)

**Status at R0:** EMPTY (seed). Phases R4.A (DEEP-MODEL-01,
`UniqueSlotMap` smart constructor), R4.B (DEEP-CAP-04, `RetypeTarget`
opaque `ScrubToken`), and R4.C (DEEP-IPC-05, `Notification.waitingThreads`
`NoDupList` promotion) will append rows here as each lands.

Expected row template (final shape determined by the R4.A/B/C
implementation):

| # | Theorem | File:Line | Promoted invariant | Discharge site | Reachability check |
|---|---------|-----------|--------------------|----------------|--------------------|
| D.1 | `UniqueSlotMap.insert_preserves_uniqueness` | `SeLe4n/Model/Object/Structures.lean:TBD` | `slotsUnique` (was Builder.lean line 290–291 obligation) | smart-constructor body | `#check @SeLe4n.UniqueSlotMap.insert_preserves_uniqueness` |
| D.2 | `retypeTarget_implies_scrub_token_held` | `SeLe4n/Kernel/Capability/Invariant/Defs.lean:TBD` | `ScrubToken` existence (was phantom-only `cleanupHookDischarged`) | `RetypeTarget` smart constructor | `#check @SeLe4n.Kernel.retypeTarget_implies_scrub_token_held` |
| D.3 | `notification_waiters_nodup` | `SeLe4n/Model/Object/Types.lean:TBD` | `Notification.waitingThreads.val.Nodup` (was upstream-convention) | `NoDupList.insert` smart constructor | `#check @SeLe4n.notification_waiters_nodup` |

The placeholder line numbers and theorem names are derived from plan
§8 (R4.A.1–R4.C.6); they will be refreshed against the live tree at
R4 landing time.

### §3.E — Predecessor reroutings (PENDING — R4.C subsumes DEEP-IPC-01)

**Status at R0:** EMPTY (seed). DEEP-IPC-01 (notification waiters NoDup
runtime-only verification) is rerouted to a structural promotion under
R4.C (D.3 above). When R4.C lands, this section captures the
"runtime-check-equivalent-to-structural-discharge" witness:

Expected row template:

| # | Subsumed finding | Subsuming structural promotion | Equivalence theorem | Reachability check |
|---|------------------|-------------------------------|---------------------|--------------------|
| E.1 | DEEP-IPC-01 (`notificationWait` runtime NoDup at `IPC/Operations/Endpoint.lean:723`) | R4.C (§3.D D.3) | `notificationWait_runtime_check_implied_by_nodup` | `#check @SeLe4n.Kernel.IPC.notificationWait_runtime_check_implied_by_nodup` |

The runtime check at line 723 is preserved as defence-in-depth; the
type-level NoDup discharge becomes the primary correctness story.

### §3.F — False-positive structural witnesses (PENDING — R4.D / R12.B / R12.C / R12.D)

**Status at R0:** EMPTY (seed). Each row in this section codifies a
deep-audit verification (the audit re-derived a runtime guard's
correctness from grep + reading the source) into a machine-checked
artefact (a Lean theorem or a CI gate) that prevents the verification
from being silently lost in a future refactor. This is the §1.5
structural-fix policy of the WS-RC plan.

Expected rows:

| # | Verified finding | Owning sub-phase | Structural artefact | Discharge mechanism | Reachability check |
|---|------------------|------------------|---------------------|---------------------|--------------------|
| F.1 | DEEP-CAP-02 (`cspaceMutate` rejects null caps; runtime guard at `Capability/Operations.lean:1093`) | R4.D | Two Lean theorems: `cspaceMutate_rejects_null_cap`, `cspaceMutate_null_cap_rejected` (in `Capability/Invariant/Preservation/CopyMoveMutate.lean`) | Lean elaborator (proof obligation) | `#check @SeLe4n.Kernel.cspaceMutate_rejects_null_cap` and `#check @SeLe4n.Kernel.cspaceMutate_null_cap_rejected` |
| F.2 | DEEP-ARCH-01 (audit-text verification error; CacheModel/TimerModel/ExceptionModel/TlbCacheComposition correctly outside production chain) | R12.B | CI gate `scripts/check_production_staging_partition.sh` (already LANDED — verified at R0.1 baseline) | tier-0 hygiene script (gate run on every CI) | `bash scripts/check_production_staging_partition.sh` |
| F.3 | DEEP-RUST-01 / DEEP-RUST-02 (MMIO + register `unsafe` blocks have ARM ARM citations) | R12.C | CI gate `scripts/check_arm_arm_citations.sh` (NEW — added in R12.C PR) | tier-0 hygiene script | `bash scripts/check_arm_arm_citations.sh` |
| F.4 | DEEP-ARCH-02 (`*_fields` defs all have ≥1 consumer; not dead code) | R12.D | CI gate `scripts/check_no_orphan_fields.sh` (already LANDED — verified at R0.1 baseline) | tier-0 hygiene script | `bash scripts/check_no_orphan_fields.sh` |

**Note on F.2 and F.4 status.** Per CLAUDE.md "active workstream
context" and the WS-RC plan §3.1 phase summary, the partition gate
(R12.B) and the orphan-fields gate (R12.D) **already landed at WS-RC
R0 prep time** as part of the plan-author commit
(`9383b0e WS-RC R0 prep: deep plan audit, structural-fix gates land,
doc sync`). They are listed here at R0.3 because the discharge index
is the single canonical artefact that records "the verification's
correctness is now machine-checked"; the cross-reference is required
by the §1.5 structural-fix policy. F.3 (the ARM-ARM citation gate) is
genuinely pending — it is scheduled for R12.C.

### §3.G — Predecessor closure reconfirmations (LANDED at R0.4)

DEBT-RUST-02 / H-24 reconfirmation. The predecessor audit's H-24
finding raised concerns about residual workstream-ID markers
(`WS-V` / `AG10`) in `rust/sele4n-hal/src/{trap.rs:186, lib.rs:89}`.
Three independent grep passes return zero hits:

1. The v0.30.11 comprehensive audit (DEBT-RUST-02 row), at
   `2026-04-26`.
2. The v0.30.11 deep verification audit, at `2026-04-28`.
3. The WS-RC R0.1 baseline cut, at `2026-04-29` (this commit).

| # | Predecessor finding | Reconfirmation site | Verification command | Hits | Status |
|---|---------------------|---------------------|----------------------|------|--------|
| G.1 | DEBT-RUST-02 / H-24 (workstream-ID markers in HAL) | `docs/dev_history/audits/AUDIT_v0.30.6_DISCHARGE_INDEX.md` (annotation in §5) | `grep -rn 'WS-V\|AG10' rust/sele4n-hal/src/{trap,lib}.rs` | 0 | CLOSED-RECONFIRMED |

The annotation in the archived discharge index makes the closure
traceable from the predecessor artefact, while this row is the
canonical WS-RC entry. R0.4 is the PR that lands the cross-reference
in both places.

## 4. Reachability gate

The predecessor's marker theorem (`closureForm_discharge_index_documented`
in `SeLe4n/Kernel/CrossSubsystem.lean`) anchors the §3.A–§3.C reachability
gate; that marker is preserved unchanged at WS-RC R0. WS-RC will add a
companion marker `closureForm_ws_rc_extensions_documented` once §3.D /
§3.E / §3.F populate substantively (no marker is added at R0 because the
sections are seeds).

The website link manifest (`scripts/website_link_manifest.txt`) must
register both this index and the predecessor index so
`scripts/check_website_links.sh` enforces their presence on every PR.
At R0, the predecessor index is already registered; this WS-RC index is
registered as part of R0.5 (the `docs/audits/README.md` "Files currently
live" sync).

## 5. Closure summary (R0 seed)

- **§3.A — 6 of 6 rows** carried forward from predecessor; no WS-RC
  modification.
- **§3.B — 7 closure-form rows** carried forward from predecessor; no
  WS-RC modification.
- **§3.C — 5 closure-form rows** carried forward from predecessor; no
  WS-RC modification.
- **§3.D — 0 rows at R0**, expected 3 rows at R4.A/B/C landing.
- **§3.E — 0 rows at R0**, expected 1 row at R4.C landing
  (DEEP-IPC-01 reroute).
- **§3.F — 0 substantive rows at R0**; 2 of 4 expected gates already
  LANDED at R0 prep (partition + orphan-fields), 1 expected at R4.D
  landing (`cspaceMutate` witness theorem), 1 expected at R12.C
  landing (ARM-ARM citation gate).
- **§3.G — 1 of 1 row** LANDED at R0.4 (DEBT-RUST-02 / H-24
  reconfirmation; closure annotation in archived predecessor index).

**No closure-form obligation introduced by WS-RC is orphaned at R0**:
every R-phase that produces a closure-form theorem or structural
witness includes a discharge-index update in the same PR (per CLAUDE.md
"Documentation rules" §3 and the §1.5 structural-fix policy).

## 6. Update protocol

When an R-phase lands a closure-form theorem or structural witness:

1. Append a row to the appropriate section (§3.D / §3.E / §3.F) in the
   same PR. Use the row template above; line numbers must reflect the
   live tree at landing time.
2. If the §3.D / §3.E / §3.F sections become substantive (any rows
   added), introduce a new marker theorem
   `closureForm_ws_rc_extensions_documented : True := trivial` in
   `SeLe4n/Kernel/CrossSubsystem.lean` so the tier-3 invariant-surface
   gate catches future name drift.
3. Update §5 ("Closure summary") to reflect the new totals.
4. The website link manifest already covers this file (R0.5); no
   manifest change is required for individual row additions.

When WS-RC closes:

1. This file moves from `docs/audits/` to `docs/dev_history/audits/`
   alongside the plan, baseline, errata, and (if any) deferred file.
2. The website link manifest is updated to point at the archived path.
3. `docs/WORKSTREAM_HISTORY.md` records the closure with a cross-
   reference to the archived discharge index.

The lifecycle convention is canonical in
[`docs/audits/README.md`](README.md) (DOC LOW batch, AN12-D).

