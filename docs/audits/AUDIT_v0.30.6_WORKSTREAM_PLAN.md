# seLe4n WS-AN — v0.30.6 Pre-1.0 Audit Remediation Workstream Plan

**Plan ID**: `AUDIT_v0.30.6_WORKSTREAM_PLAN`
**Workstream**: **WS-AN** (next sequential after WS-AM, WS-AK; one-active-audit-at-a-time convention per `AUDIT_v0.30.6_COMPREHENSIVE.md` §2.10 LOW item)
**Source audit**: [`docs/audits/AUDIT_v0.30.6_COMPREHENSIVE.md`](AUDIT_v0.30.6_COMPREHENSIVE.md) — 196 findings (initial scoring 3 CRITICAL + 24 HIGH + 71 MEDIUM + 58 LOW + 40 INFO; post-verification 2 actionable CRITICAL + 1 pre-resolved (C-02) + 23 HIGH + 71 MEDIUM + 59 LOW (H-22 downgraded) + 40 INFO = 196 total)
**Carried forward**: [`docs/audits/AUDIT_v0.29.0_DEFERRED.md`](AUDIT_v0.29.0_DEFERRED.md) — 11 deferred items (7 hardware-binding, 4 proof-hygiene)
**Errata reference**: [`docs/audits/AUDIT_v0.29.0_ERRATA.md`](AUDIT_v0.29.0_ERRATA.md) — 6 informational entries (no actionable work)
**Baseline**: `v0.30.6` at commit `1a86dbc` on branch `claude/audit-workstream-planning-AUBX4`
**Target release**: `v1.0.0` (patch-only bump trajectory; final tag is a maintainer manual action per AK10-C precedent)
**Author**: Claude (Opus 4.7), 2026-04-21
**Scope summary**: 196 audit findings (after C-02 resolved, H-22 downgraded) plus 11 carried-forward deferred items, organized into **11 phases (AN0..AN10)** with **79 named sub-tasks**. Foundation hardening (AN2) lands first so type-level changes cascade exactly once; cross-cutting structural refactors (Theme 4.2 named projections, Theme 4.3 subtype gates) are sequenced into the earliest phase whose subsystem they touch. AN10 closes the workstream with documentation sync, a new `AUDIT_v0.30.6_DEFERRED.md`, and the v1.0.0-ready gate.

---

## TL;DR (one-page executive view)

**Status of inputs**: All audit findings spot-checked against live tree at `1a86dbc`. **No erroneous findings**. Self-corrections inside the audit (C-02 resolved, H-13 file-path corrected, H-20 quantification corrected, H-22 severity downgraded) are accepted as-is. All six entries in `AUDIT_v0.29.0_ERRATA.md` are informational closures requiring no work. All 11 entries in `AUDIT_v0.29.0_DEFERRED.md` are dispositioned in §16: 6 carry-forward, 1 RESOLVED in AN2-G, 1 by-design, 2 partial-progress, 1 hardware-binding (DEF-R-HAL-L14) gets its source-side TODO retargeted in AN1-C.

**Scope of work**:
- 2 actionable CRITICAL (C-01 README, C-03 hook)
- 23 actionable HIGH
- 71 MEDIUM, 59 LOW (after H-22 downgrade), 40 INFO (no work)
- 11 carry-forward DEFERRED items + 7 newly-DEFERRED from WS-AN

**Phases & PR sequence**:
1. **AN0** — Plan + baseline (PR-1)
2. **AN1** — Critical-path: README, pre-commit hook, stale TODOs (PR-2)
3. **AN2** — Foundation hardening: subtype gates, typedIdDisjointness, named structures (PR-3..5)
4. **AN3..AN5, AN7** — Subsystem phases (parallelizable post-AN2): IPC, Cap/Lif/Svc, Sched/SC, Plat/API (PR-7..10)
5. **AN6** — CrossSubsystem composition (closes H-07/H-08/H-09) (PR-11)
6. **AN8** — Rust HAL hardening, runs in parallel with Lean phases (PR-6)
7. **AN9** — Test/CI surface incl. KernelError matrix, lake-exe timeout (PR-12)
8. **AN10** — Closure: discharge index, SMP inventory, doc batch, version bump, archive (PR-13/14)

**Estimated effort**: ~34–40 dev-days, can compress to ~3 calendar weeks with two contributors (one Lean, one Rust HAL).

**Final gate** (per §15.2): all tier scripts green, zero `sorry`/`axiom`/`native_decide`, fixture byte-identical, all 10 i18n READMEs synced, version bump to v0.30.7 (or maintainer-chosen v1.0.0).

---

## 0. Reading guide

This document is intended to be readable end-to-end OR jumped into per-phase.
Recommended reading order for a contributor picking up a sub-task:

1. **§1 Pre-flight verification** — confirms no audit finding is erroneous; lists what was spot-checked.
2. **§2 Workstream organization & dependency graph** — phase-level layout and cross-phase blockers.
3. **§3..§13 per-phase plans** — for the phase you are working on; each sub-task lists file:line anchors, acceptance criteria, and the regression-test recipe.
4. **§14 Cross-cutting theme handling** — explains why Theme 4.2 (named projections), 4.3 (subtype gates), 4.4 (SMP inventory), 4.7 (file splits) are folded into the per-subsystem phases rather than siloed.
5. **§15 Closure criteria & gate** — the v1.0.0 release-readiness checklist.
6. **§16 Deferred items carry-forward** — items that intentionally remain post-1.0.

The plan supersedes nothing. All audit findings retain their original IDs (C-01..C-03, H-01..H-24, IPC-M01..M09, etc.) for traceability; phase sub-task IDs are formatted `AN{phase}-{letter}` (e.g., AN1-A) and cross-reference the audit ID in their headline.

---

## 1. Pre-flight verification — no finding is erroneous

The audit document was independently re-checked against the live tree at commit `1a86dbc` before this plan was authored. Every claim spot-checked produced the cited evidence; this section records the checks so a reviewer can reproduce them and so contributors do not waste cycles re-verifying.

### 1.1 Audit-document corrections already applied (no further action)

The audit's own §0.4 self-verification pass made these corrections — they are NOT outstanding work:

| Original claim | Resolution | Evidence |
|----------------|-----------|----------|
| **C-02** missing scripts | RESOLVED in same PR: `find_large_lean_files.sh`, `sync_readme_from_codebase_map.sh`, `sync_documentation_metrics.sh` shipped; `AUDIT_v0.29.0_WORKSTREAM_PLAN.md` archived | `ls scripts/` confirms all three present at this commit |
| **H-13** cited `Model/Object/Types.lean:548-614` | Corrected: `Badge` is in `Prelude.lean:548-550` | `grep -n "structure Badge" SeLe4n/Prelude.lean` → line 548 |
| **H-20** "2 of 51 variants" | Corrected to "~14 of 51"; severity HIGH retained as the 37-variant gap is still dominant | Re-count `.error .X` patterns across `tests/` |
| **H-22** "no `.sha256` companion" | Corrected: `main_trace_smoke.expected.sha256` exists and is enforced; only `robin_hood_smoke.expected` and `two_phase_arch_smoke.expected` lack companions; severity downgraded HIGH→LOW | `ls tests/fixtures/*.sha256` |

After these self-corrections, the actionable HIGH count is 23 (H-01..H-21, H-23, H-24; H-22 is LOW).

### 1.2 Spot-checks performed for this plan (all confirmed)

| Audit ID | Claim | Verification | Result |
|----------|-------|--------------|--------|
| C-01 | `README.md:96` cites `AUDIT_COMPREHENSIVE_v0.23.21` | `grep -n "Latest audit" README.md` | **Confirmed** — line 96 cites v0.23.21 |
| C-03 | Pre-commit hook not installed | `ls .git/hooks/` shows only `*.sample` | **Confirmed** — hook absent |
| H-01 | `Operations.lean:12-14` documents Donation re-export omission | `grep -n "Donation.lean is NOT" SeLe4n/Kernel/IPC/Operations.lean` | **Confirmed** — line 12 |
| H-02 | `lifecycleRetypeObject` public for proof access | `grep -n "L-26\|lifecycleRetypeObject" SeLe4n/Kernel/Lifecycle/Operations.lean` | **Confirmed** — lines 468, 478, 484 |
| H-09 | `untypedRegionsDisjoint` direct-child-only scope | `grep -n "untypedRegionsDisjoint" SeLe4n/Kernel/CrossSubsystem.lean` | **Confirmed** — definition at line 476; transitive scope absent |
| H-13 | `Badge.mk` public, `valid` advisory | `Read SeLe4n/Prelude.lean:540-575` | **Confirmed** — `structure Badge where val : Nat`, no `private mk ::` |
| H-24 | Stale `WS-V/AG10` TODOs in trap.rs/lib.rs | `grep -n "WS-V\|AG10" rust/sele4n-hal/src/{trap,lib}.rs` | **Confirmed** — 6 stale references |
| Theme 4.7 | File LOC ceilings | `wc -l` on the 5 cited monolithic files | **Confirmed** — 7626/3768/3633/2461/1473 |
| DOC-M01 | i18n READMEs mirror C-01 | `grep -l "Latest audit\|AUDIT_COMPREHENSIVE_v0.23.21" docs/i18n/*/README.md` | **Confirmed** — all 10 i18n READMEs flagged |

No finding contradicted live evidence. Where the audit author corrected themselves (H-13's file path), the corrected location is what this plan tracks.

### 1.3 Items NOT erroneous but out of remediation scope

Some findings document by-design choices the audit explicitly accepted; the plan re-records them so contributors do not over-fix:

- **H-19** *design-intent context*: panic = "abort" + Drop-not-run-on-panic is acknowledged as a **fatal-invariant abort by design** at `gic.rs:299-308`. Plan addresses the documentation surfacing only, not the underlying behavior. (See AN8-C.)
- **DEF-AK2-K.4** `eventuallyExits` — **by-design externalization** per `docs/spec/SELE4N_SPEC.md` §5.7. Carried forward unchanged; no remediation.
- **PLT-M02 / PLT-M03** VSpaceRoot boot-bridge gap — depends on RPi5/VSpaceBoot shim that requires real-silicon bring-up. Carried into AN10's new DEFERRED file, NOT scheduled in AN1..AN9.
- **ARCH-M01** `VSpaceBackend` typeclass currently unused — explicitly forward-looking H3 infrastructure. AN6 tags it; does not delete it.

### 1.4 Errata acknowledgement (`AUDIT_v0.29.0_ERRATA.md`)

Each of the six errata entries is **closed informational** under v0.30.6:

| Errata ID | Status under WS-AN | Action |
|-----------|--------------------|--------|
| **E-1** S-H03 verification clarification | Closed; no work | None — recorded in `AUDIT_v0.29.0_ERRATA.md` |
| **E-2** R-HAL-M12 dead-code removal | Closed in AK10 (b . supersedes annotated fall-through) | None |
| **E-3** A-H01 three-layer extent | Closed in AK3-B + AK5-C (`wxInvariant_fourLayer_defense`) | None |
| **E-4** R-HAL-H02 partial | Closed in AK5-D (`tlbi vmalle1` + `dc cvac` sequence) | None |
| **E-5** NI-H02 composition | Closed in AK6-F (`dispatchCapabilityOnly_preserves_projection`) — but AK6F.20b residual covered by H-07 in AN6 | Track via H-07 only |
| **E-6** finding-count arithmetic 202 vs 201 | Informational only | None |

E-5 has the only forward link: its residual closure-form gap is the same gap H-07 tracks. AN6-A handles it; ERRATA needs no update.

---

## 2. Workstream organization & dependency graph

### 2.1 Phase summary

| Phase | Theme | Scope | Sub-tasks | Estimated effort | Blocks |
|-------|-------|-------|-----------|------------------:|--------|
| **AN0** | Pre-flight | Branch policy, baseline metrics, sub-task inventory commit | 3 (A–C) | 0.5 day | AN1..AN10 |
| **AN1** | Critical-path blockers | C-01, C-03, H-24 + RUST-M06 | 4 (A–D) | 0.5 day | (none) — independent |
| **AN2** | Foundation hardening | H-10..H-13, FND-M01..M08, Theme 4.3 (subtype gates), DEF-F-L9 prep | 8 (A–H) | 4–5 days | AN3..AN7 (downstream cascades) |
| **AN3** | IPC subsystem | H-01, IPC-M01..M09, IPC LOWs, Theme 4.2 (named projections for `ipcInvariantFull`), Theme 4.7 (Structural.lean split) | 7 (A–G) | 4–5 days | AN6 (CrossSubsystem composition) |
| **AN4** | Capability / Lifecycle / Service | H-02..H-06, CAP-M01..M05, LIF-M01..M06, SVC-M01..M04, Cap LOWs, Theme 4.7 (Lifecycle/Operations.lean split) | 10 (A–J) | 5–6 days | AN6 |
| **AN5** | Scheduler / SchedContext | SCH-M01..M05, SC-M01..M03, Sched LOWs, Theme 4.7 (Preservation.lean split) | 5 (A–E) | 3–4 days | AN6 |
| **AN6** | Architecture / IF / CrossSubsystem | H-07 (template discharge), H-08, H-09, ARCH-M01..M03, IF-M01..M03, CX-M01..M05, IF Operations.lean split | 8 (A–H) | 5–6 days | AN10 |
| **AN7** | Platform / API | H-14..H-16, PLT-M01..M07, API-M01..M02, Platform LOWs | 7 (A–G) | 2–3 days | AN9 |
| **AN8** | Rust HAL | H-17..H-19, RUST-M01..M08, Rust LOWs | 6 (A–F) | 3–4 days | AN9 |
| **AN9** | Tests / CI / Scripts | H-20 (KernelError matrix), H-21, H-22 (downgraded), H-23, TST-M01..M13, Test LOWs | 7 (A–G) | 4–5 days | AN10 |
| **AN10** | Documentation, themes, closure | DOC-M01..M08, Theme 4.1 (discharge index), Theme 4.4 (SMP inventory), DOC LOWs, version bump, new `AUDIT_v0.30.6_DEFERRED.md`, WORKSTREAM_HISTORY entry, gate | 14 (A–N) | 3 days | (closes WS-AN) |
| **TOTAL** | | | **79 sub-tasks** | **~34–40 dev-days** | |

### 2.2 Dependency graph

```
                        ┌────────────────────────┐
                        │      AN0 — pre-flight  │
                        └──────────┬─────────────┘
                                   │
       ┌───────────────────────────┼──────────────────────────────┐
       ▼                           ▼                              ▼
 ┌──────────┐            ┌────────────────────┐          ┌────────────────────┐
 │  AN1     │            │  AN2 — Foundation  │          │  AN8 — Rust HAL    │
 │ Critical │            │  (subtype gates,   │          │  (independent of   │
 │ blockers │            │   named structs)   │          │   Lean phases)     │
 └────┬─────┘            └─────────┬──────────┘          └─────────┬──────────┘
      │                            │                               │
      │                ┌───────────┼────────────┬─────────────┐    │
      │                ▼           ▼            ▼             ▼    │
      │           ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌─────────┐  │
      │           │  AN3    │ │  AN4    │ │  AN5    │ │  AN7    │  │
      │           │ IPC     │ │ Cap/Lif │ │ Sched/  │ │ Plat/   │  │
      │           │         │ │ /Svc    │ │ SC      │ │ API     │  │
      │           └────┬────┘ └────┬────┘ └────┬────┘ └────┬────┘  │
      │                └───────────┼───────────┘            │       │
      │                            ▼                        │       │
      │                  ┌────────────────────┐             │       │
      │                  │  AN6 — Arch / IF / │             │       │
      │                  │     CrossSubsystem │             │       │
      │                  └─────────┬──────────┘             │       │
      │                            │                        │       │
      │                            └──────────┬─────────────┴───────┘
      │                                       ▼
      │                             ┌────────────────────┐
      │                             │  AN9 — Tests / CI  │
      │                             └─────────┬──────────┘
      │                                       │
      └──────────────────────────────────────►┴──┬───────┐
                                                 ▼       │
                                       ┌────────────────────┐
                                       │  AN10 — Doc/Theme/ │
                                       │       Closure      │
                                       └────────────────────┘
```

**Critical dependency edges** explained:

- **AN2 → AN3..AN7**: foundation type changes (e.g., `Badge` private mk discipline H-13, `RegisterFile.gpr : Fin 32` H-11, `untypedRegionsDisjoint` strengthening H-09 partial, named-projection refactor scaffolding) cascade through every kernel subsystem's preservation chain. Doing AN2 first means each cascade lands once.
- **AN3..AN5 → AN6**: CrossSubsystem composition theorems (H-07 template, H-09 transitive scope) consume the per-subsystem invariants. CX bridges depend on the named-projection layout established in AN3 (IPC-M01).
- **AN8 ⫫ AN3..AN7**: Rust HAL work is independent of Lean kernel work. Can run in parallel (different contributor or background-safe, no shared files).
- **AN9 ⫫ AN3..AN8 (mostly)**: Test additions (H-20 KernelError matrix) depend on the existing kernel API surface; doing it after AN3..AN7 lets the new tests cover any new error variants those phases introduce. H-21/H-23 are independent.
- **AN10 last**: documentation sync, version bump, new DEFERRED file, gate.

### 2.3 Sequencing rationale

- **AN1 first, but optional-blocking**: C-01 (README pointer) is a 10-minute fix and takes immediate visible pressure off the project's public face. It can land as a standalone PR and is not a dependency for AN2..AN9. Treat AN1 as "land before any other public-facing PR merges."
- **AN2 second**: Foundation refactors are the highest-leverage cascading work. Doing them once now beats spreading the cascade across AN3..AN7 piecemeal.
- **AN3..AN7 in parallel where possible**: After AN2 completes, the four subsystem phases (AN3 IPC, AN4 Cap/Lif/Svc, AN5 Sched/SC, AN7 Platform/API) touch disjoint files and can land in parallel PRs. AN6 (CrossSubsystem) sequences AFTER all four because it composes them.
- **AN8 background**: Rust HAL changes touch only `rust/` and don't affect `SeLe4n/` build. Run in parallel with AN2..AN7.
- **AN9 then AN10**: Tests depend on the kernel surface, then docs synthesize and close.

### 2.4 Risk register

| Risk | Likelihood | Impact | Mitigation |
|------|-----------:|-------:|------------|
| AN2 named-projection refactor cascade (Theme 4.2) breaks 60+ destructure sites | Medium | High | Land projection theorems as `@[simp] abbrev` first (no behavioral change), migrate consumers in subsequent commits, retain tuple form as deprecated until last migration commit |
| AN3 IPC `Structural.lean` split (Theme 4.7) drops a theorem during move | Medium | High | Use `git mv`-equivalent (commit move + commit split separately so review can verify nothing dropped); add `lake build SeLe4n.Kernel.IPC.Invariant.Structural` as pre-PR check |
| AN6 H-09 transitive disjointness requires `UntypedObject.children` ancestor tracking | High | Medium | Two-track: (a) rename existing predicate to `_directParentChildExcluded` and document gap (low effort, gate-passing); (b) implement `untypedAncestorRegionsDisjoint` if effort budget allows. Plan defaults to (a) with (b) as stretch goal. |
| AN8 H-17 UartLock RAII refactor changes `kprint!` macro signature | Low | Medium | Keep `with(...)` as thin wrapper around new `with_guard()`; `kprint!` macro unchanged; only internal restructure |
| AN9 H-20 KernelError matrix test surface explosion | Medium | Medium | Target ≥35 of 51 variants per audit recommendation; partition by syscall in NegativeStateSuite extension or new `KernelErrorMatrixSuite.lean` |
| Lean 4.28.0 elaborator regression on named-structure `extends` patterns | Low | High | Use plain `structure` (no `extends`) for invariant bundles; verify build under target toolchain in AN0 baseline capture |
| Hidden audit finding interaction (e.g., H-13 Badge private mk breaks DS-L9 high-heartbeat proof) | Medium | Medium | Run `test_full.sh` after every AN2 sub-task lands, not only at end of phase; FND-M05 high-heartbeat profile is the canary |
| Closure-form proof template (AN6-A / H-07) blocked by Lean 4.28.0 `split` tactic | Medium | Low | Use `split_ifs` per the audit's own recommendation; if both fail, the AK6F.20b CLAUDE.md tracking entry already documents the toolchain blocker — close as "deferred until 4.x" with the residual closure-form pattern preserved as today |

### 2.5 Conventions used throughout the per-phase plans

- **Sub-task ID** `AN{n}-{letter}` (e.g., `AN2-C`). Each sub-task lists:
  - **Audit ID(s)** it addresses (e.g., `H-13`, `FND-M03`)
  - **Severity** at finding time
  - **Files** touched (paths only; line numbers re-verified before edit)
  - **Plan** — the substantive change
  - **Acceptance criteria** — what must be true post-commit
  - **Regression test** — the script command(s) that gate the sub-task
  - **Cascade size** — estimate of downstream proof updates
- **Acceptance gates** are tiered:
  - **module gate**: `lake build <Module.Path>` for the touched module
  - **smoke gate**: `./scripts/test_smoke.sh`
  - **full gate**: `./scripts/test_full.sh`
  - **rust gate**: `cargo test --workspace` + `cargo clippy --workspace -- -D warnings`
  - **all gate**: smoke + full + rust + `check_version_sync.sh` + `check_website_links.sh` + `ak7_cascade_check_monotonic.sh` + zero `sorry`/`axiom`/`native_decide`
- **Cascade size** annotations: `~N` means N proof sites are likely to need a one-line edit; `cascade-heavy` means N ≥ 50 (caution: spread across multiple commits).

---

## 3. Phase AN0 — Pre-flight

**Goal**: capture the baseline state, confirm the branch policy, install local guards, commit a sub-task inventory so progress can be tracked across PRs.

**Effort**: 0.5 day. **Blocks**: all subsequent phases. **Branch**: `claude/audit-workstream-planning-AUBX4` (already created per task description).

### AN0-A — Baseline capture

- **Files**: `docs/audits/AUDIT_v0.30.6_WS_AN_BASELINE.txt` (new)
- **Plan**: capture metrics at WS-AN start so AN10 can diff:
  - `lake build` job count, warning count
  - `cargo test --workspace` test count
  - 17 metrics from `scripts/ak7_cascade_baseline.sh` rerun
  - `wc -l` of the 5 monolithic files cited in Theme 4.7 (split-progress baseline)
  - Test-suite count and per-suite assertion counts (parsed from `lake exe` JSON output)
- **Acceptance**: file committed with timestamp + commit SHA; cited from `WORKSTREAM_HISTORY.md` AN entry
- **Regression test**: human review only; no script gate
- **Cascade**: none

### AN0-B — Sub-task inventory commit

- **Files**: this plan (`docs/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md`) — already drafted; commit it
- **Plan**: land the plan as a single PR titled `WS-AN AN0: workstream plan for v0.30.6 audit remediation`. No code changes in this PR.
- **Acceptance**: plan visible in `docs/audits/`; cross-referenced from `CLAUDE.md` "Active workstream context" with a one-paragraph WS-AN entry replacing the WS-AK closure paragraph at the top
- **Regression test**: smoke gate (no code changed); `check_website_links.sh` PASS
- **Cascade**: none

### AN0-C — Branch policy reminder

- **Files**: none modified; reminder issued in the PR description
- **Plan**: confirm with maintainer that AN1..AN10 all land on the same branch `claude/audit-workstream-planning-AUBX4` until WS-AN closes. Per task description's `Git Development Branch Requirements` section.
- **Acceptance**: verbal/written confirmation; no PR force-pushed elsewhere
- **Regression test**: n/a

---

## 4. Phase AN1 — Critical-path blockers

**Goal**: unblock the v1.0 release gate's CRITICAL items (post C-02 resolution: C-01, C-03) plus the trivially actionable HIGH-24 (stale TODO targets).

**Effort**: 0.5 day. **Blocks**: nothing (independent). **PR sequencing**: lands as a single PR per the audit's §5.1 "BLOCKING" priority.

### AN1-A — README "Latest audit" pointer (C-01)

- **Audit IDs**: C-01 (CRITICAL), DOC-M01 (MEDIUM cascade)
- **Files**:
  - `README.md:96`
  - `docs/i18n/{ar,de,es,fr,hi,ja,ko,pt-BR,ru,zh-CN}/README.md` — equivalent line in each translation (line numbers vary per language)
- **Plan**:
  1. Replace stale `AUDIT_COMPREHENSIVE_v0.23.21` link with two-row entry:
     - Current canonical audit: `AUDIT_v0.29.0_COMPREHENSIVE.md` (202 findings)
     - Latest published audit: `AUDIT_v0.30.6_COMPREHENSIVE.md` (196 findings)
  2. Phrase: `| **Latest audit** | [\`AUDIT_v0.30.6_COMPREHENSIVE\`](docs/audits/AUDIT_v0.30.6_COMPREHENSIVE.md) — pre-1.0 hardening audit (3 CRIT, 24 HIGH, 71 MED, 58 LOW, 40 INFO) |`
  3. Mirror to every i18n README — search anchor `Latest audit` is identical across languages.
  4. The historical v0.23.21 link is preserved in `docs/dev_history/audits/`; do NOT delete it.
- **Acceptance**:
  - `grep -l "AUDIT_COMPREHENSIVE_v0.23.21" README.md docs/i18n/*/README.md` returns empty
  - Each updated file points at the v0.30.6 audit
  - Numbers in the phrase match audit §0.4 totals (3/24/71/58/40 — note: the **initial** scoring before C-02 resolution; after C-02 resolution the active CRITICAL count is 2; phrase intentionally uses initial scoring for traceability with the audit's own §0.4 self-table)
- **Regression test**: smoke gate; `check_website_links.sh` PASS (the new path is in `scripts/website_link_manifest.txt` — verify and add if missing)
- **Cascade**: ~11 files, mechanical

### AN1-B — Pre-commit hook auto-installer (C-03)

- **Audit ID**: C-03 (CRITICAL)
- **Files**:
  - `scripts/install_git_hooks.sh` (new) — installer
  - `scripts/setup_lean_env.sh` — invoke installer post-elan-bootstrap
  - `scripts/pre-commit-lean-build.sh` — already exists; no change
  - `.github/workflows/lean_action_ci.yml` — invoke installer in CI bootstrap so any cloned-by-CI checkout is also guarded
  - `CLAUDE.md:53-61` — replace manual `cp` instruction with `scripts/install_git_hooks.sh` invocation reference
- **Plan**:
  1. New `scripts/install_git_hooks.sh`:
     - Idempotent: checks if `.git/hooks/pre-commit` already exists and links to `pre-commit-lean-build.sh`
     - If absent: symlink (preferred — auto-tracks future hook updates) or copy with sentinel marker
     - If present and DIFFERENT: prompt-or-fail (interactive vs `--check` mode)
     - GPL-3.0+ header, `set -euo pipefail`, shellcheck-clean (matches the C-02 resolution scripts' style)
  2. Extend `scripts/setup_lean_env.sh`:
     - After elan + lake initialization, call `./scripts/install_git_hooks.sh`
     - Skip-with-warning if `.git/` is absent (e.g., Lean Lake build inside a non-git tarball)
  3. Update `CLAUDE.md:53-61`: change "Install it: `cp …`" to "Install it: `./scripts/install_git_hooks.sh` (run automatically by `setup_lean_env.sh`)"
- **Acceptance**:
  - Fresh clone + `setup_lean_env.sh` results in `.git/hooks/pre-commit` linked or copied
  - `install_git_hooks.sh --check` returns 0 if installed, non-zero otherwise (CI-friendly)
  - `pre-commit-lean-build.sh` continues to fire on staged `.lean` files (verified by deliberately staging a sorry-bearing file → commit rejected)
  - Idempotency: second run is no-op
- **Regression test**: smoke gate; manual one-shot verification of fresh-clone scenario
- **Cascade**: 0 (no kernel-side changes)

### AN1-C — Stale `WS-V/AG10` TODO retargeting (H-24, RUST-M06)

- **Audit IDs**: H-24 (HIGH), RUST-M06 (MEDIUM, same root cause)
- **Files**:
  - `rust/sele4n-hal/src/trap.rs:186` — `TODO(WS-V/AG10): Wire Lean FFI dispatch via @[extern] bridge`
  - `rust/sele4n-hal/src/lib.rs:62, 69, 84, 87, 91` — five additional `WS-V` references
- **Plan**:
  1. Repoint each TODO to the canonical deferred-tracking entry. Mapping:
     - `trap.rs:186` SVC FFI → `TODO(DEF-R-HAL-L14): Wire Lean FFI dispatch — see docs/audits/AUDIT_v0.30.6_DEFERRED.md`
     - `lib.rs:62` bounded WFE → new ID `DEF-R-HAL-L17` (deferred — interrupt-wait optimization). Add row to AN10 DEFERRED file.
     - `lib.rs:69` parameterized barriers → `DEF-R-HAL-L18` (deferred — H3-PLAT)
     - `lib.rs:84` widen barriers to OSH → `DEF-R-HAL-L19` (deferred — SMP)
     - `lib.rs:87` SVC FFI deferred → `DEF-R-HAL-L14` (already exists)
     - `lib.rs:91` Secondary core bring-up → `DEF-R-HAL-L20` (deferred — SMP)
  2. The new DEF-R-HAL-L17..L20 entries land in the new `AUDIT_v0.30.6_DEFERRED.md` per AN10-G.
  3. Repo-wide grep for `WS-V|AG10` outside `docs/dev_history/`, `docs/WORKSTREAM_HISTORY.md` (active log), and the audit/errata/deferred docs themselves; retarget any remaining stragglers.
- **Acceptance**:
  - `grep -rn "WS-V\|AG10" rust/ SeLe4n/` returns only completed-work historical comments (e.g., "WS-V completed at v0.21.7"), NOT deferred-work TODOs
  - Each retargeted TODO references a live `DEF-*` ID that exists in `AUDIT_v0.29.0_DEFERRED.md` or the new `AUDIT_v0.30.6_DEFERRED.md` (created in AN10-G; for AN1-C land the source-side retarget first, the file-creation lands in AN10)
- **Regression test**: rust gate; smoke gate
- **Cascade**: ~6 lines

### AN1-D — AN1 closure

- **Files**: `CHANGELOG.md` — new entry under `[Unreleased]`
- **Plan**: single combined commit message documenting AN1-A/B/C deltas; reference audit IDs C-01, C-03, H-24, RUST-M06
- **Acceptance**: PR merged; CI green on the AN1 branch
- **Gate**: smoke gate + rust gate + `check_website_links.sh` + `check_version_sync.sh` + `ak7_cascade_check_monotonic.sh`

---

## 5. Phase AN2 — Foundation hardening

**Goal**: Land the type-level changes that downstream phases will depend on. This phase implements **Theme 4.3 (advisory predicates → subtype gates)** uniformly so AN3..AN7 inherit a tightened foundation; it also addresses cross-cutting H-10..H-13 and FND-M01..M08.

**Effort**: 4–5 days. **Blocks**: AN3..AN7 cascade through these types. **Branch**: same WS-AN branch.

### AN2-A — Badge private mk discipline + cascading typed-constructors (H-13)

- **Audit IDs**: H-13 (HIGH); also closes Theme 4.3 first-instance pattern
- **Files**:
  - `SeLe4n/Prelude.lean:548-577` (`Badge` structure + smart constructors)
  - `tests/BadgeOverflowSuite.lean` (existing 22 tests; extend to cover private-mk rejection)
  - All call sites of `Badge.mk` (grep + migrate; expected ~5 sites in non-test code)
- **Plan**:
  1. Restructure `Badge` to use `private mk ::`:
     ```lean
     structure Badge where private mk ::
       val : Nat
     deriving DecidableEq, Repr, Inhabited
     ```
  2. Promote `Badge.ofNatMasked`, `Badge.ofNat`, and `Badge.zero` (literal builder if not present) as the only public constructors. Each MUST return a `Badge.valid` witness or a `Badge` that has `valid` provable by reduction.
  3. Migrate every external `Badge.mk` call site to `Badge.ofNatMasked` (or `ofNat` where the bound is statically clear). Likely sites: test fixtures, decode helpers.
  4. Add a regression test in `BadgeOverflowSuite`: `#eval Badge.mk` must produce a "constructor is private" elaboration error (use `set_option pp.privateNames true` to verify the symbol is hidden).
- **Acceptance**:
  - Repo-wide grep `grep -rn "Badge.mk" SeLe4n/ tests/` returns only the structure declaration site (and explicit-allowed test files using `Badge.mkUnsafe` if introduced as a fresh internal helper for proof-side reduction)
  - `tests/BadgeOverflowSuite.lean` passes; new "private mk" test added (compile-time rejection or `Badge.valid` provable by construction)
  - Module gate: `lake build SeLe4n.Prelude`; smoke gate; full gate
- **Regression test**: full gate + `lake exe badge_overflow_suite`
- **Cascade**: ~5 sites; LOW-cost. Pattern applied recursively in AN2-B for VAddr/PAddr/CPtr/Slot.

### AN2-B — Subtype-gate cascade for `VAddr`/`PAddr`/`CPtr`/`Slot` (Theme 4.3, H-13 follow-on)

- **Audit IDs**: Theme 4.3 (cross-cutting), supports H-13
- **Files**:
  - `SeLe4n/Prelude.lean:463-500` (`CPtr`, `Slot`, `VAddr`, `PAddr` structures)
  - All call sites — grep `\.mk\b` per type
- **Plan**:
  1. Apply the same `private mk ::` pattern to each type whose `valid` predicate is currently advisory. List in priority order:
     - `CPtr` (lines 463-468): `isWord64Bounded` advisory → enforce via `private mk ::` + `CPtr.ofNat` smart constructor
     - `Slot` (lines 490-495): same treatment
     - `VAddr` (lines 671-679): `canonicalBound` 2^48 advisory → enforce via `VAddr.ofNat`
     - `PAddr`: enforce 2^52 (or `physicalAddressWidth` parameterized) bound via `PAddr.ofNat`
  2. Land migrations bottom-up: each type's smart constructor takes a `Nat` and produces `Option T`/`Except _ T`; an `unsafeMk` proof-side variant retained `private` for invariants that destructure a known-valid value.
  3. The cascade through preservation theorems is mostly mechanical: theorems that use `CPtr.mk n` become `(CPtr.ofNat n).get!` or are rewritten to take a `CPtr` parameter. Cap the per-commit footprint at 1 type per commit so review scopes stay tight.
- **Acceptance**:
  - Per-type: `grep -rn "CPtr\.mk\|Slot\.mk\|VAddr\.mk\|PAddr\.mk" SeLe4n/ tests/` produces only expected proof-side `unsafeMk` patterns
  - All `valid` predicates become provable-by-construction at every public entry
- **Regression test**: full gate per type; ABI conformance suite (`lake exe abi_roundtrip_suite`) PASS
- **Cascade**: ~30 sites total across the four types, batched 1-type-per-commit

### AN2-C — `RegisterFile.gpr : Fin 32` refactor + `LawfulBEq (RHTable α β)` instance (H-11)

- **Audit ID**: H-11 (HIGH)
- **Files**:
  - `SeLe4n/Machine.lean:254-304` (`RegisterFile`)
  - `SeLe4n/Kernel/RobinHood/Bridge.lean:136-153` (`RHTable.BEq`)
  - All call sites of `RegisterFile.gpr i` (most are bounded by inspection; need migration to `Fin 32`)
- **Plan**:
  1. Refactor `RegisterFile.gpr : Nat → RegValue` to `gpr : Fin 32 → RegValue`. The 32-GPR convention is hardcoded; make the typing reflect it.
  2. Introduce `RegisterFile.gprNat : Nat → Option RegValue` for legacy callers that need to pass a `Nat` (returns `none` for indices ≥ 32). Migrate callers incrementally.
  3. Derive `BEq` and `LawfulBEq` for the refactored `RegisterFile` automatically.
  4. Delete the `RegisterFile.not_lawfulBEq` negative witness (it served as a guard against accidentally relying on the unlawful instance; the new instance is lawful).
  5. For `RHTable.BEq`: add the `instance : LawfulBEq (RHTable κ β)` derivation under `[LawfulBEq κ] [LawfulBEq β]`. This is mechanical given the value-type pairing; ensure the `BEq` body is structural.
  6. Verify any `DecidableEq SystemState` consumers no longer require manual witness threading.
- **Acceptance**:
  - `lake build SeLe4n.Machine` PASS
  - `LawfulBEq (RHTable κ β)` derivable instance present and used by `SystemState`-touching proofs
  - No regression in `cargo test --workspace` (Rust ABI's `RegValue` round-trip unchanged)
- **Regression test**: full gate; rust gate
- **Cascade**: ~20 call sites in scheduler/IPC for `RegisterFile.gpr`; ~5 for `RHTable.BEq`

### AN2-D — Typed-identifier disjointness as Prop-level invariant (H-10)

- **Audit ID**: H-10 (HIGH)
- **Files**:
  - `SeLe4n/Prelude.lean:111-135` (`ThreadId.toObjId`, `SchedContextId.toObjId`, `ServiceId.toObjId`)
  - `SeLe4n/Kernel/CrossSubsystem.lean` — extend `crossSubsystemInvariant` from 11 conjuncts to 12 with `typedIdDisjointness` as the new conjunct
  - `SeLe4n/Kernel/Lifecycle/Operations.lean:retypeFromUntyped` — verify `retypeFromUntyped_childId_fresh` discharges the new conjunct
- **Plan**:
  1. Promote `typedIdDisjointness_trivial` (existing weak witness from AJ2-D) into a substantive `typedIdDisjointness : SystemState → Prop`:
     ```lean
     def typedIdDisjointness (st : SystemState) : Prop :=
       ∀ tid : ThreadId, ∀ scId : SchedContextId,
         st.objects.get? tid.toObjId = some _.tcb _ →
         st.objects.get? scId.toObjId = some _.schedContext _ →
         tid.toObjId ≠ scId.toObjId
     ```
     and analogous for `ServiceId` (when service objects are stored under shared IDs).
  2. Add as 12th conjunct of `crossSubsystemInvariant` (mirrors WS-AM AM4 pattern of adding `lifecycleObjectTypeLockstep` as 11th conjunct).
  3. Frame lemmas:
     - `default_typedIdDisjointness` (vacuous on empty state)
     - `storeObject_preserves_typedIdDisjointness` for same-kind writes
     - `retypeFromUntyped_preserves_typedIdDisjointness` via `retypeFromUntyped_childId_fresh` (new ID is provably absent pre-state)
  4. Cascade through the 5 core bridges (`_objects_change_bridge`, `_retype_bridge`, `_objects_frame`, `_services_change`, `_composition_gap_documented`) and the ~34 per-operation bridge lemmas — same playbook as AM4-D/E.
  5. Update `crossSubsystemInvariant_default` to 12 cases.
  6. Bump `crossSubsystemFieldSets` count to 12; update `crossSubsystem_pairwise_coverage_complete` to C(12,2)=66 disjoint pairs (extend from 18 to 21 disjoint pairs — typedIdDisjointness is disjoint from at least 3 other field-sets).
- **Acceptance**:
  - `lake build SeLe4n.Kernel.CrossSubsystem` PASS
  - 3 new runtime tests (`an2d_01..03`) in `tests/Ak7RegressionSuite.lean`: predicate true on default; predicate detects deliberate aliasing; preservation through `retypeFromUntyped` for non-overlapping IDs
  - `checkCrossSubsystemInvariant` in `SeLe4n/Testing/InvariantChecks.lean` extended to 12 predicates
  - V6-A runtime assertion in `tests/InformationFlowSuite.lean` updated 11→12 entries
- **Regression test**: full gate; `lake exe ak7_regression_suite`
- **Cascade**: cascade-heavy (~50 preservation proofs); split across 3-4 commits matching AM4-D/E pattern

### AN2-E — Badge intermediate-overflow tightening (H-12)

- **Audit ID**: H-12 (HIGH)
- **Files**: `SeLe4n/Prelude.lean:520-543`
- **Plan**:
  1. Add `Badge.ofUInt64Pair (a b : UInt64) : Badge` that performs the bitwise OR on `UInt64` (bounded intermediate) before wrapping into `Badge`. Provide `bor_valid` analog proven via `UInt64`'s bitwise-bound facts.
  2. Mark the existing `Badge.ofNatMasked` as `@[deprecated]` with message "use `Badge.ofUInt64Pair` for production paths; legacy `Nat`-wrapped variant retained for proof convenience". Migrate ABI/decode call sites to the new variant.
  3. The deprecation does not delete `ofNatMasked`; it keeps it usable for proof-side rewriting where the abstract `Nat` is more tractable than `UInt64`.
- **Acceptance**:
  - `Badge.ofUInt64Pair_bor_valid` proven; intermediate value never escapes 2^64
  - All ABI-side call sites migrated; `lake exe abi_roundtrip_suite` PASS
- **Regression test**: smoke gate; `lake exe abi_roundtrip_suite`
- **Cascade**: ~3 sites in ABI decode

### AN2-F — Foundation MEDIUM batch (FND-M01..M08)

- **Audit IDs**: FND-M01..M08
- **Files**: scattered; per-finding below
- **Plan** (one commit per ID, batched into a single PR):
  - **FND-M01**: `Prelude.lean:463-468, 490-495` — refactor `CPtr.isWord64Bounded` and `Slot.isWord64Bounded` to delegate via `@[inline] def isWord64Bounded := isWord64Dec ·.val`. Trivially follows from the AN2-B refactor.
  - **FND-M02**: `Prelude.lean:671-679` — replace hardcoded `2^48` in `VAddr.canonicalBound` with `MachineState.virtualAddressWidth`-derived computation. Add `virtualAddressWidthDefault := 48` constant and a parameterized version. Verify no decode site silently mismatches the default.
  - **FND-M03**: `Model/Object/Types.lean:1017-1043` — add `UntypedObjectValid := { ut : UntypedObject // ut.wellFormed }` subtype; tighten `allocate`/`retypeFromUntyped` to take `UntypedObjectValid` at the entry point. Cascade is bounded because retype already validates `wellFormed` at admission; the change makes the precondition type-level rather than runtime.
  - **FND-M04**: `Kernel/RobinHood/Bridge.lean:88-94` — define `minPracticalRHCapacity : Nat := 16`; reference from `Inhabited` instance and bridge-lemma capacity bounds. Pure rename; no behavior change.
  - **FND-M05**: `Kernel/RobinHood/Bridge.lean:240-283` (DS-L5) — heartbeat budget profile and decompose. Approach: use `set_option profiler true` to identify the slow subproofs; extract them as named lemmas; target ≤200,000 heartbeats. If the decomposition is non-obvious, split this into AN2-F.5 as a stretch sub-task and document residual heartbeat budget.
  - **FND-M06**: `Kernel/FrozenOps/Core.lean:149-200` — gate unchecked FrozenOps. Two options: (a) `private` (preferred); (b) `set_option sele4n.frozenOps.unsafe true`. Per the audit's preference, mark `private`. The `*Checked` variants from AK8-G remain the public surface. Test sites that rely on unchecked variants migrate to the checked ones.
  - **FND-M07**: `Kernel/FrozenOps/Core.lean:285-344` — prove the AE2-D Phase-2 unreachable branch substantively rather than returning `.error`. Pattern: `... := by exact absurd hPhase2 (Phase1_covers_all hPhase1)`.
  - **FND-M08**: `Prelude.lean:149-198` — add Prelude docstring decision table for `toObjId`/`toObjIdChecked`/`toObjIdVerified`. Pure documentation.
- **Acceptance**: each FND-M item resolved per its plan; full gate green after PR merges
- **Regression test**: full gate; `lake exe frozen_ops_suite`
- **Cascade**: small per-item; total ~25 sites across the eight items

### AN2-G — DEF-F-L9 17-deep tuple refactor (cross-cutting prep — Theme 4.2 entrypoint)

- **Audit IDs**: DEF-F-L9 (carried forward from AUDIT_v0.29.0_DEFERRED.md), Theme 4.2 cross-cutting
- **Files**: `SeLe4n/Model/State.lean` (`allTablesInvExtK` 17-tuple)
- **Plan**:
  1. Convert `allTablesInvExtK` from a 17-tuple to a Lean `structure` with named fields:
     ```lean
     structure AllTablesInvExtK (st : SystemState) : Prop where
       objects_invExtK : st.objects.invExtK
       irqHandlers_invExtK : st.irqHandlers.invExtK
       ... (14 more)
     ```
  2. Update downstream callers to use `.objects_invExtK` field access instead of `.1`/`.2.1`/etc.
  3. The named-projection convention introduced here is the template for AN3-B (`ipcInvariantFull`) and AN4-G (`apiInvariantBundle_frozenDirect`).
  4. Estimated cascade: ~80 proof sites per the audit's WS-AF-26 design rationale. Land as 4-5 commits, each migrating one downstream consumer cluster.
- **Acceptance**:
  - `lake build SeLe4n.Model.State` PASS
  - All consumers use named field access; no `.1.2.2…` remains for `allTablesInvExtK` projections
  - Witness-equality theorem retained (no behavioral change)
- **Regression test**: full gate; `lake exe ak7_regression_suite`
- **Cascade**: ~80 sites; spread over 4-5 commits

### AN2-H — AN2 closure

- **Files**: `CHANGELOG.md` — entry under `[Unreleased]` summarizing AN2-A..G
- **Acceptance**: PR merged; full gate + rust gate PASS; AN2 baseline metrics in `AUDIT_v0.30.6_WS_AN_BASELINE.txt` updated to "post-AN2"

---

## 6. Phase AN3 — IPC subsystem

**Goal**: close H-01 (Donation re-export asymmetry), apply Theme 4.2 (named projections) to `ipcInvariantFull` (the IPC-M01 high-leverage fix), batch IPC-M02..M09 hygiene, and split the 7626-line `Structural.lean` per Theme 4.7.

**Effort**: 4–5 days. **Blocks**: AN6 CrossSubsystem composition. **Parallel-safe** with AN4, AN5, AN7, AN8.

### AN3-A — Donation re-export resolution (H-01)

- **Audit ID**: H-01 (HIGH)
- **Files**:
  - `SeLe4n/Kernel/IPC/Operations.lean:12-14` (hub)
  - `SeLe4n/Kernel/IPC/Operations/Donation.lean`
  - `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` (consumer of donation primitives via `cleanupPreReceiveDonation`)
  - Possibly new: `SeLe4n/Kernel/IPC/Operations/DonationPrimitives.lean`
- **Plan**:
  - **Option A (preferred)**: extract the subset of Transport primitives Donation depends on into a dependency-free `DonationPrimitives.lean` module. `Donation.lean` then depends on `DonationPrimitives.lean` (no longer on Transport.lean), so the hub `Operations.lean` can re-export Donation without cycling.
  - **Option B (fallback if extraction is non-obvious)**: add a top-of-hub doc block explicitly listing every IPC-adjacent module + which are re-exported. The asymmetry becomes discoverable from the hub itself even if not technically resolved. Add a `-- DO NOT MOVE: cycle constraint` banner on `Donation.lean`.
  - **Decision criterion**: time-box Option A at 1 day; if the Transport-Donation primitive extraction touches > 10 unrelated theorems, fall back to Option B and file the cycle as a post-1.0 architectural item.
- **Acceptance** (Option A): `import SeLe4n.Kernel.IPC.Operations` exposes `cleanupPreReceiveDonation`, `applyCallDonation`, `applyReplyDonation`, `cancelDonation` symbols without additional import; module gate `lake build SeLe4n.Kernel.IPC.Operations` PASS
- **Acceptance** (Option B): hub doc block lists 10+ IPC-Adjacent modules with status (`re-exported` / `import directly`); `cycle-banner` comment present
- **Regression test**: full gate; `lake exe negative_state_suite`
- **Cascade**: 0–10 sites depending on chosen option

### AN3-B — Named-projection refactor for `ipcInvariantFull` (IPC-M01, Theme 4.2 second instance)

- **Audit ID**: IPC-M01 (MEDIUM, but flagged as the single highest-leverage hygiene fix in IPC); Theme 4.2 cross-cutting
- **Files**:
  - `SeLe4n/Kernel/IPC/Invariant/Defs.lean:2483` (`ipcInvariantFull` 12-tuple definition)
  - All consumers using `.2.2.2.2.2.2.2.2.2.2.2.1` (`donationOwnerValid` extraction) and similar deep projections
- **Plan**:
  1. Promote `ipcInvariantFull` from a tuple to a `structure`:
     ```lean
     structure IpcInvariantFull (st : SystemState) : Prop where
       structuralBasic : ...
       endpointWaiterConsistent : ...
       notificationWaiterConsistent : ...
       ... (12 named fields total — match existing 12 conjuncts)
       donationOwnerValid : ...
     ```
  2. Provide forward-compat: keep the legacy tuple form as `ipcInvariantFullTuple` with a bidirectional bridge `ipcInvariantFull_iff_tuple : IpcInvariantFull st ↔ ipcInvariantFullTuple st`. Migrate downstream proofs in batches.
  3. Add `@[simp]` projection theorems: `ipcInvariantFull_donationOwnerValid : IpcInvariantFull st → donationOwnerValid st` (etc.) so callers can extract via `_.donationOwnerValid` instead of deep tuple projection.
  4. Update the 12 conjunct extractions in cross-file consumers (notably `IPC/Invariant/Structural.lean`, `Kernel/CrossSubsystem.lean`, `IPC/Invariant/EndpointPreservation.lean`).
- **Acceptance**:
  - No remaining `.2.2.2.2.2.2.2.2.2.2.2.1` projection on `ipcInvariantFull` outside the bridge theorem
  - `lake build SeLe4n.Kernel.IPC.Invariant.Defs` PASS
  - Compositional theorem `IpcInvariantFull.mk` constructible from the 12 base predicates
- **Regression test**: full gate; module gate on every cross-subsystem caller listed in CrossSubsystem.lean
- **Cascade**: cascade-heavy (~60 sites per CAP-M05 and IPC-M01 references); split across 5-6 commits

### AN3-C — IPC `Structural.lean` 7626-line split (Theme 4.7 first instance, IPC-M02)

- **Audit IDs**: IPC-M02 (MEDIUM), Theme 4.7 cross-cutting
- **Files**:
  - `SeLe4n/Kernel/IPC/Invariant/Structural.lean` (7626 lines) — split into 4 child modules
  - `SeLe4n/Kernel/IPC/Invariant.lean` — re-export hub gains 4 imports (or 1 import for an aggregator hub)
- **Plan**:
  1. Identify the four natural seams from the audit: (a) QueueNext{Path,Foo} transport lemmas, (b) store-object frame lemmas, (c) dual-queue membership proofs, (d) per-operation Structural witnesses.
  2. Create `SeLe4n/Kernel/IPC/Invariant/Structural/QueueNextTransport.lean`, `Structural/StoreObjectFrame.lean`, `Structural/DualQueueMembership.lean`, `Structural/PerOperation.lean`.
  3. Move declarations atomically per file (one commit per move + one verification commit after each); each child file MUST `import` exactly the modules its declarations reference.
  4. Convert `Structural.lean` to a thin re-export hub:
     ```lean
     import SeLe4n.Kernel.IPC.Invariant.Structural.QueueNextTransport
     import SeLe4n.Kernel.IPC.Invariant.Structural.StoreObjectFrame
     import SeLe4n.Kernel.IPC.Invariant.Structural.DualQueueMembership
     import SeLe4n.Kernel.IPC.Invariant.Structural.PerOperation
     ```
  5. Keep all theorem names and namespaces stable so external consumers see no change.
- **Acceptance**:
  - Each new file ≤ 2000 LOC (matches Theme 4.7 ceiling); `Structural.lean` shrinks to <50 LOC re-export hub
  - `lake build SeLe4n.Kernel.IPC.Invariant.Structural` PASS
  - All upstream IPC tests PASS
- **Regression test**: full gate
- **Cascade**: 0 (re-export pattern preserves all import paths)

### AN3-D — IPC `NotificationPreservation.lean` and `CallReplyRecv.lean` splits (IPC-M03, IPC-M04)

- **Audit IDs**: IPC-M03, IPC-M04 (both MEDIUM)
- **Files**:
  - `SeLe4n/Kernel/IPC/Invariant/NotificationPreservation.lean` (1490 LOC) → split into `Notification/Signal.lean` + `Notification/Wait.lean`
  - `SeLe4n/Kernel/IPC/Invariant/CallReplyRecv.lean` (1069 LOC) → split into `Call.lean` + `ReplyRecv.lean`
- **Plan**: same playbook as AN3-C — extract per-operation files, hub re-exports.
- **Acceptance**: each child file ≤ 1000 LOC; hub re-exports preserve all consumer imports
- **Regression test**: full gate
- **Cascade**: 0

### AN3-E — IPC MEDIUM batch (IPC-M05..M09)

- **Audit IDs**: IPC-M05..M09
- **Files**: scattered
- **Plan** (one commit per ID, single PR):
  - **IPC-M05**: `IPC/Invariant/QueueMembership.lean:31-78` — extract shared `transferAux` helper used by both `transfer`/`transferRecv`. Goal: collapse the duplicate ~40-LOC bodies to one shared definition.
  - **IPC-M06**: `IPC/Operations/Endpoint.lean:460` — promote `storeObject_scheduler_eq_z7` to public OR document the internality rationale in its docstring with a `-- INTENTIONALLY PRIVATE: see WH:Z7` cross-reference.
  - **IPC-M07**: `IPC/Invariant/Defs.lean:811-927` — strengthen queue-consistency predicates with a reachability precondition `∀ tid ∈ queue, st.objectIndex.contains tid.toObjId`. Verify no regression in preservation proofs that compose under `ipcInvariantFull`.
  - **IPC-M08**: `IPC/Invariant/Defs.lean:228-284` — strengthen `allPendingMessagesBounded` to cross-check endpoint reference liveness, OR explicitly weaken the docstring to acknowledge that liveness is a transitive property (not the predicate's own).
  - **IPC-M09**: `IPC/Operations/Endpoint.lean:1-20` — add `-- DO NOT MOVE: cleanupPreReceiveDonation must co-locate with Endpoint to avoid cycling Donation → Transport → Endpoint` banner. Also add a build-time check (a Lean `example` that triggers an import-cycle compile error if Donation is moved back).
- **Acceptance**: each MEDIUM addressed; full gate green
- **Regression test**: full gate; `lake exe negative_state_suite`
- **Cascade**: small (~5-10 sites per item)

### AN3-F — IPC LOW batch

- **Audit IDs**: IPC LOW (5 items per audit §2.1)
- **Files**: scattered
- **Plan** (single commit, batched):
  - Rename `IPC/Invariant/WaitingThreadHelpers.lean` → `NotificationWaitListHelpers.lean` OR add narrowing module-level docstring (preferred — file rename causes git churn for low value)
  - Add field-preservation lemma set in `IPC/Invariant/EndpointPreservation.lean:205-236` (`_ipcState_preserved`, `_queueNext_preserved`)
  - Factor `QueueNextPath` reconstruction in `IPC/Invariant/Structural.lean:946-957` into named helper
  - `IPC/DualQueue.lean:14-25`: upgrade informational note about asymmetry (parallel to H-01) to prescriptive
  - `IPC/Operations/CapTransfer.lean:55`: docstring for `fillRemainingNoSlot`
- **Acceptance**: each LOW addressed; smoke gate PASS
- **Regression test**: smoke gate
- **Cascade**: ~5 sites

### AN3-G — AN3 closure

- **Files**: `CHANGELOG.md` entry; `CLAUDE.md` large-files-list refresh (Structural.lean shrinks; new child modules added)
- **Acceptance**: PR merged; full gate + rust gate PASS

---

## 7. Phase AN4 — Capability / Lifecycle / Service

**Goal**: close the four HIGH capability findings (H-02..H-06), batch CAP/LIF/SVC MEDIUMs, address the Lifecycle.Operations.lean monolithic split (Theme 4.7), and document the CDT-discharge index pattern (Theme 4.1 anchor for AN10's broader index).

**Effort**: 5–6 days. **Blocks**: AN6 CrossSubsystem composition.

### AN4-A — `lifecycleRetypeObject` visibility hardening (H-02)

- **Audit ID**: H-02 (HIGH)
- **Files**:
  - `SeLe4n/Kernel/Lifecycle/Operations.lean:453-560` — `lifecycleRetypeObject` def + cluster
  - `SeLe4n/Kernel/Lifecycle/Operations/Internal.lean` (new) — moves the function into a `protected` namespace OR a sibling module not exported from the hub
  - 13+ proof-chain consumers (per the audit's count) — verify they import the new internal module
  - `scripts/test_tier0_hygiene.sh` — extend with a CI check
- **Plan**:
  1. Move `lifecycleRetypeObject` into `SeLe4n.Kernel.Lifecycle.Internal` namespace (under `Operations/Internal.lean` if file split is desired, else inline as `namespace Internal`).
  2. The hub `Lifecycle/Operations.lean` re-exports ONLY `lifecycleRetypeWithCleanup` and the cleanup primitives — NOT `lifecycleRetypeObject` directly.
  3. Proof-chain consumers update imports: `import SeLe4n.Kernel.Lifecycle.Operations.Internal` (or `import SeLe4n.Kernel.Lifecycle.Operations` and reference as `Lifecycle.Internal.lifecycleRetypeObject`).
  4. Add CI hygiene check in `test_tier0_hygiene.sh`:
     - Grep for `lifecycleRetypeObject` outside `SeLe4n/Kernel/Lifecycle/` — if any match exists in a non-Lifecycle file that is NOT a proof-internal site, fail.
     - Allowlist file: `scripts/lifecycle_internal_allowlist.txt` enumerating the legitimate proof-chain consumer paths.
- **Acceptance**:
  - `lifecycleRetypeObject` no longer visible from `Lifecycle.Operations` direct import (only via `Internal` sub-namespace)
  - Production callers (syscall arms in `API.lean`) verify they go through `lifecycleRetypeWithCleanup`
  - CI guard rejects new files that bypass the wrapper
- **Regression test**: full gate; new `lake exe negative_state_suite` scenario asserting cleanup-bypass attempt yields `.error`
- **Cascade**: ~13 import paths

### AN4-B — Redundant `lifecycleIdentityNoTypeAliasConflict` removal (H-03)

- **Audit ID**: H-03 (HIGH)
- **Files**: `SeLe4n/Kernel/Lifecycle/Invariant.lean:56-72`
- **Plan**:
  1. Prove the implication: `theorem lifecycleIdentityTypeExact_implies_noTypeAliasConflict (st : SystemState) : lifecycleIdentityTypeExact st → lifecycleIdentityNoTypeAliasConflict st`. Likely a one-liner via `intro hExact a b hTcb hSc; exact hExact …`.
  2. Once the implication is proven, delete the redundant conjunct from the bundle. Update bundle arity (one fewer field) and migrate ~5-10 destructure sites.
  3. If the arity change cascades through too many consumers, defer the deletion and ship only the implication theorem (achieves the audit's "at least commit the implication theorem so the redundancy is formally witnessed" fallback).
- **Acceptance**: implication theorem present and proven; bundle arity reduced (full path) OR implication-only (fallback path) with explicit AN4-B-fallback annotation
- **Regression test**: full gate
- **Cascade**: 5-10 sites if full path

### AN4-C — CDT discharge index theorem (H-04)

- **Audit ID**: H-04 (HIGH); also Theme 4.1 first instance
- **Files**:
  - `SeLe4n/Kernel/Capability/Invariant/Preservation.lean:15-48` — original site of the externalization
  - `SeLe4n/Kernel/CrossSubsystem.lean` — new index theorem
- **Plan**:
  1. Add to `CrossSubsystem.lean`:
     ```lean
     /-- AN4-C / H-04: Discharge index for CDT post-state hypotheses.
         Every CDT-modifying operation in `Capability/Operations.lean` takes
         `cdtCompleteness st' ∧ cdtAcyclicity st'` as a post-state hypothesis.
         This theorem witnesses that those hypotheses are discharged by the
         `crossSubsystemInvariant` bridge composition for each operation. -/
     theorem capabilityInvariantBundle_cdt_hypothesis_discharge_index : True := by trivial
     ```
     with a docstring listing each `(operation_name, file:line, discharge_site)` tuple. Use the marker-theorem pattern (per CAP-M01's preference for documentation-via-marker over vacuous Prop).
  2. For each cap operation taking a CDT post-state hypothesis (~6 operations: `cspaceCopy`, `cspaceMove`, `cspaceMutate`, `cspaceMint`, `cspaceDelete`, `cspaceRevoke`), add a `_cdt_hypothesis_discharged_at` companion theorem that bridges from `crossSubsystemInvariant` to the post-state CDT predicates. This makes the discharge mechanically searchable.
  3. The marker theorem becomes the anchor for AN10's broader Theme 4.1 discharge index (covering H-04 CDT, H-07 projection, SC-M02 `hSchedProj`).
- **Acceptance**: index theorem committed; each of the 6 cap operations has a named discharge witness; AN10 deliverable extends the index with H-07 + SC-M02 entries
- **Regression test**: full gate
- **Cascade**: ~12 sites (6 ops × 2 = base + companion)

### AN4-D — `cspaceLookupMultiLevel` SMP-precondition (H-05)

- **Audit ID**: H-05 (HIGH); cross-cutting Theme 4.4 single-core inventory
- **Files**: `SeLe4n/Kernel/Capability/Operations.lean:206`
- **Plan**:
  1. Add a precondition predicate `resolvedCnodeStillValid (st : SystemState) (resolvedRef : CapAddress) : Prop := ∃ cn, st.lookupKernelObject resolvedRef.cnode = some (.cnode cn)`.
  2. Refactor `cspaceLookupMultiLevel` to take this predicate as a hypothesis (or to assert it inside via an `if .. then .. else` returning `.error .invalidCapability`).
  3. Prove the precondition holds in the single-core kernel via "no retype between resolveCapAddress and cspaceLookupSlot in the absence of concurrency". This becomes the first formalised entry in the AN10 SMP inventory (Theme 4.4).
  4. Document the SMP-side discharge: at SMP boundary, the predicate becomes a critical-section obligation managed by an interrupt-disable bracket.
- **Acceptance**: precondition predicate defined; single-core proof present; SMP discharge documented
- **Regression test**: full gate; `lake exe negative_state_suite`
- **Cascade**: ~3 sites (lookup helper definition + 1-2 callers)

### AN4-E — `mintDerivedCap` non-null output witness (H-06)

- **Audit ID**: H-06 (HIGH)
- **Files**: `SeLe4n/Kernel/Capability/Operations.lean:641-649`
- **Plan**:
  1. Add theorem:
     ```lean
     theorem mintDerivedCap_preserves_non_null
         (parent : NonNullCap) (badge : Badge) :
         (mintDerivedCap parent badge).isNull = false := by
       cases parent with | mk cap hNonNull => simp [mintDerivedCap, Capability.isNull]
     ```
  2. Optionally tighten the return type: `mintDerivedCap : NonNullCap → Badge → NonNullCap` so the post-condition is type-level. Cascade through `cspaceMint` consumer (currently uses the value via `Capability` projection; with the tightened return, the wrapper unwraps once).
  3. If the type-tightening cascade is non-trivial, ship only the theorem (audit's "at minimum" recommendation).
- **Acceptance**: theorem proven; return-type tightened OR theorem-only with annotation
- **Regression test**: full gate; `lake exe ak7_regression_suite`
- **Cascade**: ~2 sites

### AN4-F — Capability MEDIUM batch (CAP-M01..M05)

- **Audit IDs**: CAP-M01..M05
- **Files**: scattered
- **Plan**:
  - **CAP-M01**: replace `resolveCapAddress_caller_rights_obligation : True := trivial` (vacuous Prop) with a `def` marker `… : Unit := ()` OR use a `@[documented_obligation]` attribute (define this attribute as a no-op tag in `SeLe4n/Prelude.lean`). Prefer the attribute approach because it makes the obligation tag-greppable without theorem-namespace pollution.
  - **CAP-M02**: prove `cspaceRevokeCdtTransactional_unreachable_fallback` substantively if the branch really is dead, OR document the invariant failure trigger if it isn't. Walk the validation path; if the absurdity is provable, prove it.
  - **CAP-M03**: split `Capability/Invariant/Preservation.lean` (2461 LOC) per operation: `Preservation/Insert.lean`, `Preservation/Delete.lean`, `Preservation/Revoke.lean`, `Preservation/CDT.lean`, `Preservation/CopyMoveMutate.lean`, `Preservation/MintLifecycle.lean`. Hub `Preservation.lean` becomes a re-export (Theme 4.7).
  - **CAP-M04**: introduce `RetypeTarget := { id : ObjId // cleanupHookDischarged id }` precondition type for retype paths. Cascade through `lifecyclePreRetypeCleanup` callers; update cleanup hook to produce the witness.
  - **CAP-M05**: apply the AN3-B named-projection treatment to `capabilityInvariantBundle` 6-tuple. Pattern is identical; smaller cascade because only 6 conjuncts.
- **Acceptance**: each MEDIUM addressed; full gate green after the CAP-M03 split is verified across all importers
- **Regression test**: full gate
- **Cascade**: CAP-M01 (~1), CAP-M02 (~1), CAP-M03 (~0 due to re-export pattern), CAP-M04 (~5-10), CAP-M05 (~30 destructure sites)

### AN4-G — Lifecycle MEDIUM batch (LIF-M01..M06)

- **Audit IDs**: LIF-M01..M06
- **Files**: `SeLe4n/Kernel/Lifecycle/Operations.lean` (1473 LOC) — split is LIF-M05
- **Plan**:
  - **LIF-M01**: prove `removeThreadFromQueue_unreachable_under_tcbExistsInvariant` substantively; remove the `(none, none)` defensive fallback (or prove it absurd).
  - **LIF-M02**: introduce `lifecycleCleanupPipeline` wrapper that composes the per-step cleanups with a fixed order; expose ONLY the pipeline.
  - **LIF-M03**: cross-reference scrub-address-formula limitation in `SELE4N_SPEC.md` §5; add a `// TODO(H3-binding): scrub address must map to physical via VSpace bridge` annotation.
  - **LIF-M04**: prove `retypeFromUntyped_atomicity_under_sequential_semantics` witnessing the watermark-advance + post-allocation-verify happens atomically in the sequential model, then add a TODO for H3 atomicity proof.
  - **LIF-M05**: split `Lifecycle/Operations.lean` (1473 LOC) into `Operations/Cleanup.lean`, `Operations/Retype.lean`, `Operations/Suspend.lean`, `Operations/Untyped.lean`. Hub re-exports.
  - **LIF-M06**: add docstring to `lifecycleRevokeDeleteRetype` documenting the no-rollback partial-failure contract; surface in `SELE4N_SPEC.md` §5.
- **Acceptance**: each LIF-M addressed
- **Regression test**: full gate
- **Cascade**: LIF-M01 (~1), LIF-M02 (~5), LIF-M03 (~0 doc), LIF-M04 (~1), LIF-M05 (~0 re-export), LIF-M06 (~0 doc)

### AN4-H — Service MEDIUM batch (SVC-M01..M04)

- **Audit IDs**: SVC-M01..M04
- **Plan**:
  - **SVC-M01**: add `bootFromPlatform_service_fuel_sufficient` witness theorem proving `serviceBfsFuel ≥ initial_service_count`; document in `SELE4N_SPEC.md` §5.
  - **SVC-M02**: rename `Bfs` suffix → `Dfs` (or drop suffix). Cascade through ~5 call sites.
  - **SVC-M03**: enrich dependency-add return type to distinguish "added" vs "no-op", OR document the collision semantics in the function docstring.
  - **SVC-M04**: split `Service/Invariant/Acyclicity.lean` (1012 LOC) by reachability-induction-principle factoring (deferrable; mark as AN4-H.4 stretch goal if effort budget allows).
- **Acceptance**: each SVC-M addressed
- **Regression test**: full gate
- **Cascade**: small per item

### AN4-I — Capability/Lifecycle/Service LOW batch

- **Audit IDs**: 5 LOW items per audit §2.3
- **Plan** (single batch commit):
  - Move `Capability/Operations.lean:1-62` C-L1..C-L10 file-level docstring → `docs/audits/CAPABILITY_AUDIT_NOTES.md`
  - Cross-reference `Capability/Operations.lean:939-941` direct-overwrite annotation with the CDT-preservation theorem name
  - Audit `cspaceRevokeCdt_lenient` callers; mark `@[deprecated]` if no production caller
  - Add SMP-assumption cross-reference at `Lifecycle/Invariant.lean:97-100` to the AN4-D inventory
  - Document `bfs_boundary_lemma` lemma-family taxonomy in `Service/Invariant/Acyclicity.lean:235-270`
- **Acceptance**: each LOW addressed
- **Regression test**: smoke gate

### AN4-J — AN4 closure

- **Files**: `CHANGELOG.md`; `CLAUDE.md` large-files-list refresh
- **Acceptance**: PR merged; full gate + rust gate PASS

---

## 8. Phase AN5 — Scheduler / SchedContext

**Goal**: Address SCH-M01..M05 hygiene and SC-M01..M03 (CBS witness, PIP closure-form, import-cycle banner). Split the 3633-line `Scheduler/Operations/Preservation.lean` per Theme 4.7.

**Effort**: 3–4 days. **Blocks**: AN6.

### AN5-A — Scheduler `Preservation.lean` 3633-line split (SCH dispatch + Theme 4.7)

- **Audit IDs**: SCH-M01 (factor TCB cases dispatch), Theme 4.7
- **Files**:
  - `SeLe4n/Kernel/Scheduler/Operations/Preservation.lean` (3633 LOC)
  - Hub `Scheduler/Operations.lean` re-export
- **Plan**:
  1. Identify natural seams: (a) per-operation `schedule`/`handleYield`/`timerTick`/`switchDomain` preservation theorems, (b) RunQueue helpers (`remove_preserves_nodup` etc.), (c) replenishment-pipeline preservation (`popDueReplenishments`, `refillSchedContext`), (d) cross-subsystem bridge witnesses.
  2. Extract:
     - `Preservation/Schedule.lean`
     - `Preservation/HandleYield.lean`
     - `Preservation/TimerTick.lean`
     - `Preservation/SwitchDomain.lean`
     - `Preservation/RunQueueHelpers.lean`
     - `Preservation/ReplenishmentPipeline.lean`
  3. Each ≤ 1000 LOC. Hub re-exports.
  4. SCH-M01: factor the duplicated `cases obj` dispatch into a helper macro `tcbCasesPreservation` in `Preservation/RunQueueHelpers.lean`. Apply at all 4 op call sites; recover ~80 LOC and eliminate the future-divergence risk.
- **Acceptance**: each child file ≤ 1000 LOC; SCH-M01 pattern factored; full gate
- **Regression test**: full gate
- **Cascade**: 0 (re-export pattern)

### AN5-B — Scheduler MEDIUM batch (SCH-M02..M05)

- **Audit IDs**: SCH-M02..M05
- **Plan**:
  - **SCH-M02**: prefix RunQueue implementation helpers with `_rq_internal_` OR add `private` where the proof chain allows. Spot-check `remove_preserves_nodup`, `insert_preserves_nodup`.
  - **SCH-M03**: introduce `replenishmentPipelineOrder : SystemState → Prop` capturing pop → refill → process; prove `timerTick_preserves_replenishmentPipelineOrder`.
  - **SCH-M04**: split `Scheduler/Operations/Core.lean:340-447` into pure `Operations.lean` and proof-harness `Wrappers.lean`. (Optional, deferrable; mark stretch.)
  - **SCH-M05**: rename `Scheduler/PriorityInheritance/BlockingGraph.lean:344` `tcbQueueChainAcyclic` → `blockingGraphAcyclic`. Cascade through ~10-15 references.
- **Acceptance**: each SCH-M addressed
- **Regression test**: full gate
- **Cascade**: SCH-M05 ~15 sites

### AN5-C — Scheduler LOW batch

- **Audit IDs**: 4 LOW items per audit §2.2
- **Plan** (single commit):
  - Add `-- safe under runQueueInvariant` annotation at `Scheduler/RunQueue.lean .getD ⟨0⟩` fallback
  - Rename `scheduleEffective`/`timerTickWithBudget` with `_budgetAware` suffix
  - Add docstring to `updatePipBoost` describing lifecycle relationship
  - Add module docstring to `Scheduler/Invariant.lean` re-export hub (invariant hierarchy explanation)
- **Acceptance**: each LOW addressed
- **Regression test**: smoke gate

### AN5-D — SchedContext MEDIUM batch (SC-M01..M03)

- **Audit IDs**: SC-M01..M03
- **Plan**:
  - **SC-M01**: add `rpi5_cbs_window_replenishments_bounded` witness theorem instantiating the externalised hypothesis for the canonical RPi5 timer config (54 MHz, default replenishment period). Discharges the `cbs_bandwidth_bounded_tight` conditional for the target platform. Update `docs/spec/SELE4N_SPEC.md` §5 accordingly.
  - **SC-M02**: closure-form pattern same as H-07; address there at AN6-A. Annotate SC-M02 with cross-reference.
  - **SC-M03**: add the explicit `-- DO NOT IMPORT Preservation.lean or PriorityPreservation.lean from this hub — see WS-AB.D2 import-cycle note` banner at `SchedContext/Invariant.lean` head. Add a Lean `example` that triggers a compile error if the import is reintroduced.
- **Acceptance**: each SC-M addressed
- **Regression test**: full gate; `lake exe priority_management_suite`
- **Cascade**: SC-M01 (~1 new theorem), SC-M02 (cross-ref only), SC-M03 (~1 banner + example)

### AN5-E — AN5 closure

- **Files**: `CHANGELOG.md`; `CLAUDE.md` large-files-list refresh
- **Acceptance**: PR merged; full gate + rust gate PASS

---

## 9. Phase AN6 — Architecture / InformationFlow / CrossSubsystem

**Goal**: Address H-07 (template substantive discharge of one closure-form projection theorem), H-08 (assumption consumption index), H-09 (untypedRegionsDisjoint scope clarification or transitive strengthening). Batch ARCH/IF/CX MEDIUMs. Split the 3768-line `InformationFlow/Invariant/Operations.lean`.

**Effort**: 5–6 days. **Blocks**: AN10.

### AN6-A — Substantive discharge of one `*_preserves_projection` theorem (H-07, also closes E-5 residual)

- **Audit ID**: H-07 (HIGH); also Theme 4.1 anchor; closes E-5 NI-H02 residual
- **Files**:
  - `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean` — pick ONE of: `schedContextConfigure_preserves_projection`, `schedContextBind_preserves_projection`, `schedContextUnbind_preserves_projection`, `lifecycleRetype_preserves_projection`, `tcbSuspend_preserves_projection`, `tcbResume_preserves_projection`
  - `SeLe4n/Kernel/API.lean:2114-2153` — once one is substantively proven, the master `dispatchCapabilityOnly_preserves_projection` arm for that operation drops its `hArmProj` closure
- **Plan**:
  1. Recommended target: `schedContextConfigure_preserves_projection`. Reasons:
     - Body uses well-named frame lemmas already proven in AK6-F (`schedContextBind_frame_runQueue_rebucket` and analogs)
     - The Except.ok-wrapped match structure is symmetric (configure has fewer branches than the suspend/resume paths)
  2. Use `split_ifs` per the audit's recommendation; if Lean 4.28.0's `split_ifs` cannot fully discharge, fall back to manual `cases hConfig : ...` destructuring with `Except.ok_eq_iff_get?` rewrites.
  3. The substantive proof becomes the template; document the discharge recipe at the top of the theorem body so the other 5 closure-form theorems can follow the pattern in a future workstream.
  4. If `split`/`split_ifs` are blocked by the toolchain, ship a "best-effort" partial discharge: convert ONE arm of the match to substantive, leave the others as the closure-form `hArmProj`, and update H-07 / AK6F.20b tracking to "partial discharge — toolchain pending 4.x".
- **Acceptance** (success path): one theorem substantively proven; `dispatchCapabilityOnly_preserves_projection` for that arm drops its `hArmProj` parameter; recipe documented
- **Acceptance** (toolchain-blocked path): partial discharge committed with explicit annotation; tracking entry preserved
- **Regression test**: full gate; `lake exe information_flow_suite`
- **Cascade**: ~5-15 cascading proof updates; potentially blocks if toolchain shifts

### AN6-B — Architecture assumption consumption index (H-08)

- **Audit ID**: H-08 (HIGH)
- **Files**: `SeLe4n/Kernel/Architecture/Assumptions.lean:132`
- **Plan**:
  1. Define an inductive type:
     ```lean
     inductive ArchAssumption where
       | deterministicTimerProgress
       | mmuPageTableWalkTotal
       | gicAcknowledgeIdempotent
       | tlbBarrierComplete
       | singleCoreOnly
     ```
  2. Define `archAssumptionConsumer : ArchAssumption → Lean.Name` mapping each assumption to the theorem that consumes it (e.g., `.deterministicTimerProgress → ``advanceTimerState_invariantBundle_preserved`).
  3. Add a marker theorem `architecture_assumptions_index : ∀ a : ArchAssumption, ∃ n : Lean.Name, archAssumptionConsumer a = n := by intro a; cases a <;> exact ⟨_, rfl⟩` that the elaborator can verify trivially.
  4. The `#eval` of `archAssumptionConsumer` produces the audit's machine-searchable index.
- **Acceptance**: index inductive defined; consumer mapping complete; marker theorem proven
- **Regression test**: full gate
- **Cascade**: ~1 file change

### AN6-C — `untypedRegionsDisjoint` scope hardening (H-09)

- **Audit ID**: H-09 (HIGH)
- **Files**:
  - `SeLe4n/Kernel/CrossSubsystem.lean:476-485`
  - `docs/spec/SELE4N_SPEC.md` §5
- **Plan** (two-track per §2.4 risk register):
  - **Track A (always land)**: rename `untypedRegionsDisjoint` → `untypedRegionsDisjoint_directParentChildExcluded`. Update all 50+ cascade sites mechanically (matching AM4-D/E pattern). Add `SELE4N_SPEC.md` §5 clarification that physical disjointness across transitive retype chains is an out-of-model obligation. Provide a deprecated alias `untypedRegionsDisjoint := untypedRegionsDisjoint_directParentChildExcluded` for one release cycle.
  - **Track B (stretch)**: add `untypedAncestorRegionsDisjoint` strengthening that requires `UntypedObject.children` to also track ancestors transitively (or to track a parent-pointer chain). Prove preservation through `retypeFromUntyped` recursively.
  - **Decision**: time-box Track B at 2 days; if not feasible, ship Track A and add an entry to the new `AUDIT_v0.30.6_DEFERRED.md` for Track B.
- **Acceptance** (Track A): rename complete; doc clarification in SPEC; deprecated alias preserves backward compat
- **Acceptance** (Track B): transitive predicate added as 13th conjunct of `crossSubsystemInvariant`; cascade complete
- **Regression test**: full gate
- **Cascade**: cascade-heavy (~50 sites for Track A rename; ~80 sites for Track B strengthening)

### AN6-D — Architecture MEDIUM batch (ARCH-M01..M03)

- **Audit IDs**: ARCH-M01..M03
- **Plan**:
  - **ARCH-M01**: tag `VSpaceBackend` with `-- STATUS: deferred; consumed at H3 real-hardware path` module-level comment. Add `#[allow(unused)]`-style tagging if Lean has an equivalent (it does not directly; just rely on the docstring + `--explicit-allow-unused-imports` if available).
  - **ARCH-M02**: add `pageTableWalk_depth_bound : ∀ d, depth d ≤ 4` theorem explicit witness for the structural-recursion depth bound.
  - **ARCH-M03**: introduce `KernelError.invalidMessageInfoDetailed` debug-only variant carrying the internal `IpcBufferReadError`. Gate behind `set_option sele4n.debug.detailedErrors true` so production preserves the ABI single-error convention.
- **Acceptance**: each ARCH-M addressed
- **Regression test**: full gate
- **Cascade**: ARCH-M01 (~0), ARCH-M02 (~1), ARCH-M03 (~3 if debug variant exposed at decode site)

### AN6-E — InformationFlow MEDIUM batch (IF-M01..M03)

- **Audit IDs**: IF-M01..M03
- **Plan**:
  - **IF-M01**: document `serviceObservable` covert-channel scope in `SELE4N_SPEC.md` §7 ("Non-interference scope and exclusions"). Cross-reference the module header.
  - **IF-M02**: add a "negative-case" test in `tests/InformationFlowSuite.lean` asserting the four NI-L3 accepted covert channels are observable today. Pattern: build two states differing only in scheduler-state-induced timing; project both; assert projections differ. This guards against an accidental future "fix" that silently closes the channel and invalidates the acceptance documentation.
  - **IF-M03**: split `InformationFlow/Invariant/Operations.lean` (3768 LOC) by `KernelOperation` constructor groups: `Operations/IPC.lean`, `Operations/Capability.lean`, `Operations/SchedContext.lean`, `Operations/Architecture.lean`. Hub re-exports.
- **Acceptance**: each IF-M addressed; AN6-E split keeps re-export semantics
- **Regression test**: full gate; `lake exe information_flow_suite`
- **Cascade**: IF-M01 (~0 doc), IF-M02 (~1 new test), IF-M03 (~0 re-export)

### AN6-F — CrossSubsystem MEDIUM batch (CX-M01..M05)

- **Audit IDs**: CX-M01..M05
- **Plan**:
  - **CX-M01**: formalize `collectQueueMembers` fuel-sufficiency by lifting `QueueNextPath` to a decidable reachability relation; prove `collectQueueMembers st q fuel = reachable_set st q ↔ fuel ≥ st.objectIndex.length`. Closes the remaining TPI-DOC item.
  - **CX-M02**: add cross-reference at `lifecycleObjectTypeLockstep` definition pointing to `storeObjectKindChecked` definition (and vice versa); both reference each other so a reader entering from either side discovers the pair.
  - **CX-M03**: add `bootFromPlatform_currentCore_is_zero_witness` theorem pinning the single-core MPIDR-mask assumption to the boot bridge.
  - **CX-M04**: compose the eight exception/interrupt preservation theorems into a single `archInvariantBundle_preserves_all_eight` theorem.
  - **CX-M05**: add a positive-state smoke test in `tests/MainTraceHarness.lean` (or a new test) that explicitly asserts `architectureInvariantBundle` holds on a post-boot state.
- **Acceptance**: each CX-M addressed
- **Regression test**: full gate; `lake exe ak7_regression_suite`
- **Cascade**: CX-M01 (~1 substantive proof), CX-M02 (~2 docstrings), CX-M03 (~1 theorem), CX-M04 (~1 composition), CX-M05 (~1 test)

### AN6-G — Architecture/IF/CX LOW batch

- **Audit IDs**: 2 LOW items per audit §2.5
- **Plan**: commit `TPI-002` doc to `docs/`, OR remove the cross-reference. Add `-- DO NOT REIMPORT` linter comment at `SchedContext/Invariant.lean` import-cycle note (overlap with SC-M03; verify single source of truth).
- **Acceptance**: addressed
- **Regression test**: smoke gate

### AN6-H — AN6 closure

- **Files**: `CHANGELOG.md`; `CLAUDE.md` large-files-list refresh (IF/Operations.lean shrinks; new child modules)
- **Acceptance**: PR merged; full gate + rust gate PASS

---

## 10. Phase AN7 — Platform / API

**Goal**: Address H-14 (DTB legacy `Option` deprecation), H-15 (`physicalAddressWidth` audit), H-16 (`_Check` predicates audit), batch PLT-M01..M07 and API-M01..M02.

**Effort**: 2–3 days. **Blocks**: AN9.

### AN7-A — DTB legacy `Option`-returning path deprecation (H-14, PLT-M04)

- **Audit IDs**: H-14 (HIGH), PLT-M04 (MEDIUM, same root cause)
- **Files**:
  - `SeLe4n/Platform/DeviceTree.lean:333-380` (`classifyMemoryRegion`)
  - `SeLe4n/Platform/DeviceTree.lean` (`findMemoryRegProperty`)
- **Plan**:
  1. Mark both `findMemoryRegProperty` and `classifyMemoryRegion` `@[deprecated]` with messages pointing to `findMemoryRegPropertyChecked` (AK9-F) and `classifyMemoryRegionChecked` (AK9-F) respectively.
  2. Migrate any Sim-path or test-path consumer in the same commit so the deprecation warning surfaces only at intentional legacy sites.
  3. Add a CI hygiene check: grep for `findMemoryRegProperty\b|classifyMemoryRegion\b` (without the `Checked` suffix) outside `DeviceTree.lean`; fail if any non-deprecated consumer exists.
- **Acceptance**:
  - `@[deprecated]` markers present
  - All non-test consumers migrated
  - CI guard active
- **Regression test**: full gate; `lake exe ak9_platform_suite`
- **Cascade**: ~3-5 sites

### AN7-B — `physicalAddressWidth` parameterization audit (H-15)

- **Audit ID**: H-15 (HIGH — verification finding)
- **Files**: repo-wide grep
- **Plan**:
  1. Grep for `physicalAddressWidth\s*:=\s*52` and `physicalAddressWidth\s*:=\s*48` across all `.lean`, `.rs`, `.toml`, `.md` files.
  2. Verify each call site supplies the correct value for its target platform:
     - RPi5 / BCM2712: 44 bits
     - Sim platform: 52 bits (max ARMv8 LPA) or test-specific
     - Generic stubs: explicit reject pattern (no default)
  3. Add a CI hygiene check: any code path that constructs a `MachineConfig` or `DeviceTree` MUST supply `physicalAddressWidth` explicitly; default-value usage is rejected.
- **Acceptance**: every call site explicit; CI guard active; spot-check of RPi5 path confirms 44
- **Regression test**: full gate
- **Cascade**: ~10 sites if any defaults remain

### AN7-C — `_Check` predicates silent-true audit (H-16)

- **Audit ID**: H-16 (HIGH — verification finding)
- **Files**: `SeLe4n/Platform/RPi5/RuntimeContract.lean:75-93` and similar
- **Plan**:
  1. Audit all `*Check` predicates in `RPi5/RuntimeContract.lean` and `Sim/RuntimeContract.lean`:
     - `registerContextStableCheck`
     - `dequeueOnDispatchCheck`
     - `timeSlicePositiveCheck`
     - `ipcReadinessCheck`
     - `edfCompatibleCheck`
  2. For each predicate, verify the "binding absent" branch returns `false` (fail-closed). If any returns `true` without explicit justification, tighten following the AK9-E pattern (`budgetSufficientCheck`).
  3. Add per-predicate soundness theorems mirroring `registerContextStableCheck_budget` so the predicate's behavior is mechanically verifiable.
- **Acceptance**: every `*Check` predicate fails closed on missing/wrong-variant bindings; new soundness theorems present
- **Regression test**: full gate; `lake exe ak9_platform_suite`
- **Cascade**: ~5-10 sites if any silent-true patterns present

### AN7-D — Platform MEDIUM batch (PLT-M01..M07)

- **Audit IDs**: PLT-M01..M07
- **Plan**:
  - **PLT-M01**: move `bootFromPlatformUnchecked` deprecated alias into `SeLe4n.Testing.Deprecated` namespace (or add `@[deprecated]` with explicit migration message).
  - **PLT-M02 / PLT-M03**: VSpaceRoot boot bridge gap is hardware-binding; carry into AN10's new `AUDIT_v0.30.6_DEFERRED.md` as `DEF-PLT-M02-V1.0` (out of scope for AN1..AN9). Add doc cross-reference at the theorem site to the new DEFERRED entry.
  - **PLT-M04**: covered by AN7-A. No additional work.
  - **PLT-M05**: `parseFdtNodes` default fuel migration to size-derived `hdr.sizeDtStruct / 4` for all callers.
  - **PLT-M06**: document `extractPeripherals` 2-level depth limitation in `SELE4N_SPEC.md` §6 with TODO for recursive extension.
  - **PLT-M07**: 6 unimported modules (`Platform/Sim/Contract.lean`, `Platform/FFI.lean`, `Platform/RPi5/Contract.lean`, `Architecture/CacheModel.lean`, `Architecture/ExceptionModel.lean`, `Architecture/TimerModel.lean`) — wire via a `Platform.Staged` module that imports them all; add to test harness build target so they are compile-checked. Mark each with a docstring `-- STATUS: staged for H3 hardware binding`. Alternative: move to `docs/dev_history/staged/` per audit's option (b). Recommendation: stage them (option a) so refactors in their dependencies break loudly.
- **Acceptance**: each PLT-M addressed; staged modules compile under build target
- **Regression test**: full gate; module gate per staged module
- **Cascade**: PLT-M07 (~6 staged modules become buildable)

### AN7-E — API MEDIUM batch (API-M01..M02)

- **Audit IDs**: API-M01..M02
- **Plan**:
  - **API-M01**: add `KernelError.partialResolution` (or analog) variant for `resolveExtraCaps` silent-drop semantics. Gate behind `set_option sele4n.debug.noisyResolution true` so the default ABI behavior matches seL4. Cascade: 1 new error-variant + Rust-side ABI sync.
  - **API-M02**: once H-07 (AN6-A) lands one substantively-discharged closure-form theorem, tighten `dispatchCapabilityOnly` signature for that arm to drop the closure. The other 5 arms remain on the AK6F.20b discharge recipe.
- **Acceptance**: each API-M addressed
- **Regression test**: full gate; rust gate (ABI sync verification)
- **Cascade**: API-M01 (~5 sites — error variant in Lean + Rust); API-M02 (~3 sites)

### AN7-F — Platform LOW batch

- **Audit IDs**: 3 LOW per audit §2.7
- **Plan**:
  - Document last-wins semantics on duplicate IRQ/object IDs at `Platform/Boot.lean` file header
  - Add CI check for BCM2712 datasheet reference list freshness (e.g., script that compares the date marker against current year and warns on > 1 year staleness)
  - `Main.lean` no change
- **Acceptance**: each LOW addressed
- **Regression test**: smoke gate

### AN7-G — AN7 closure

- **Files**: `CHANGELOG.md`
- **Acceptance**: PR merged; full gate + rust gate PASS

---

## 11. Phase AN8 — Rust HAL

**Goal**: Address H-17 (UartLock RAII), H-18 (MPIDR_CORE_ID_MASK shared symbol), H-19 (panic discipline doc + lint). Batch RUST-M01..M08 and Rust LOWs. Independent of Lean work — runs in parallel with AN3..AN7.

**Effort**: 3–4 days. **Blocks**: AN9 (Rust ABI changes affect cross-test coverage).

### AN8-A — `UartLock` RAII refactor (H-17)

- **Audit ID**: H-17 (HIGH)
- **Files**: `rust/sele4n-hal/src/uart.rs:238`
- **Plan**:
  1. Define `UartGuard<'a>` struct holding the spin-acquired pointer and implementing `Drop` to release the CAS:
     ```rust
     pub struct UartGuard<'a> {
         inner: &'a mut Uart,
         lock: &'a UartLock,
     }
     impl Drop for UartGuard<'_> {
         fn drop(&mut self) { self.lock.release(); }
     }
     ```
  2. Add `with_guard()` method returning `UartGuard<'_>` that acquires the spin lock at construction.
  3. Refactor `with()` to delegate: `pub fn with<F, R>(&self, f: F) -> R where F: FnOnce(&mut Uart) -> R { let mut guard = self.with_guard(); f(&mut guard.inner) }`.
  4. The SAFETY-comment thinness is eliminated because the lifetime-borrow is enforced by the `'a` annotation on `UartGuard`; the spin guard release is automatic.
  5. Mirror to `kprint!` macro consumers — should require zero call-site changes since they go through `with(...)`.
- **Acceptance**: `UartGuard<'_>` defined and Drop'ing releases the lock; `with()` is a thin wrapper; `kprint!` macro continues to work; rust gate PASS
- **Regression test**: rust gate; `cargo test --workspace` (any UART-touching tests)
- **Cascade**: ~5 sites

### AN8-B — MPIDR_CORE_ID_MASK shared symbol (H-18)

- **Audit ID**: H-18 (HIGH)
- **Files**: `rust/sele4n-hal/src/cpu.rs`, `rust/sele4n-hal/src/boot.S:39`
- **Plan**: Per audit's preferred Option (a): expose `MPIDR_CORE_ID_MASK` as a Rust `pub const` AND emit a `.rodata`-placed `u64` symbol that boot.S `ldr`'s. Eliminates drift entirely.
  1. In `cpu.rs`: `pub const MPIDR_CORE_ID_MASK: u64 = 0x00FFFFFF;` and `#[no_mangle] pub static MPIDR_CORE_ID_MASK_SYM: u64 = MPIDR_CORE_ID_MASK;`.
  2. In `boot.S:39`: replace the `mov`+`movk` immediate-build with `adrp x2, MPIDR_CORE_ID_MASK_SYM; ldr x2, [x2, :lo12:MPIDR_CORE_ID_MASK_SYM]` (or equivalent for the linker layout).
  3. If Option (a) is non-trivial (linker layout does not cooperate), fallback to Option (b): `const _: () = assert!(MPIDR_CORE_ID_MASK == 0x00FFFFFF)` in `cpu.rs` plus a `build.rs` step that scans `boot.S` for the literal `0xFFFF` + `0xFF, lsl #16` pattern and fails on mismatch.
- **Acceptance** (Option a): boot.S loads from shared symbol; runtime mask agrees with Rust constant trivially. (Option b): build-time assertion present and CI-enforced.
- **Regression test**: rust gate; QEMU boot test (`scripts/test_qemu.sh` if available)
- **Cascade**: ~2 files

### AN8-C — `dispatch_irq` panic discipline doc + lint (H-19)

- **Audit ID**: H-19 (HIGH — but design-intent already accepted per audit context)
- **Files**: `rust/sele4n-hal/src/gic.rs:362-386`
- **Plan**:
  1. Replicate the `EoiGuard` documentation paragraph into `dispatch_irq`'s top-level docstring. Make the constraint discoverable from the call site, not only from the type definition.
  2. Add `#![deny(clippy::panic)]` at the IRQ-handler-function level (audit's preferred Option a). This makes direct `panic!()` inside handler bodies a compile error.
  3. The audit's Option b (move EOI emission before handler invocation per GIC-400 spec) is a larger architectural change; defer to post-1.0 hardware-binding workstream.
- **Acceptance**: doc replication present; clippy-lint guard active; `cargo clippy --workspace -- -D warnings` PASS
- **Regression test**: rust gate
- **Cascade**: ~1 site

### AN8-D — Rust MEDIUM batch (RUST-M01..M08)

- **Audit IDs**: RUST-M01..M08
- **Plan**:
  - **RUST-M01**: `mmu.rs sctlr_bits` consolidate `#[allow(dead_code)]` constants into a doc comment explaining each excluded bit. Remove per-constant `#[allow]`.
  - **RUST-M02**: `uart.rs:71` — change `assert!` to `debug_assert!` + add boot-time alignment self-check. Document the throughput vs defense-in-depth trade-off.
  - **RUST-M03**: `timer.rs:311-318` — change `init_timer(1000).unwrap()` to `assert_eq!(init_timer(1000), Ok(()))` for explicit verification.
  - **RUST-M04**: verify AG6 page-level mappings actually shipped; remove or update the `mmu.rs:5` stale "AG6 replaces this" comment per the audit's verify-and-update directive. If the stale comment is wrong (AG6 already shipped), delete; if AG6 work is incomplete, retarget to a real DEFERRED entry.
  - **RUST-M05**: `gic.rs:155` — add a boot-time GICD_ITARGETSR self-check: write a known pattern, verify read-back matches the banked value. Halt boot on mismatch.
  - **RUST-M06**: covered by AN1-C. No additional work.
  - **RUST-M07**: `cache.rs:150-170` — add a separate `pub fn memory_fence()` helper distinct from `cache_range`; migrate callers that want a pure fence.
  - **RUST-M08**: audit `IpcBuffer` end-to-end; if EL0 usage is still stub, gate behind `#[cfg(feature = "ipc_buffer")]`. If consumed, document the consumer path.
- **Acceptance**: each RUST-M addressed
- **Regression test**: rust gate; `cargo test --workspace` (415 → ~420 tests with new self-checks)
- **Cascade**: small per item

### AN8-E — Rust LOW batch

- **Audit IDs**: 10 LOW items per audit §2.8
- **Plan** (single PR, batched commits):
  - Remove `#[allow(dead_code)]` on `gicd::ICENABLER_BASE` OR add forward-reference comment
  - Extract `sele4n-types/src/lib.rs:1-94` 52-line audit notes block to `docs/AUDIT_NOTES.md`; keep `lib.rs` lean
  - Pin `cc`, `find-msvc-tools`, `shlex` build dependencies explicitly in `Cargo.toml [build-dependencies]`
  - Document `init_with_baud` non-standard baud silent-incorrect behavior
  - Annotate `disable_interrupts()` DAIF-read-before-mask rationale
  - Cross-reference `link.ld:56-60` PageTableCell with `sele4n-hal/src/mmu.rs`
  - Add `// symbol resolved by Lean kernel link` annotation to `rust_boot_main`
  - Track `mmio.rs` MSRV-1.85 clippy allow for removal
  - Add `const _: () = assert!(align_of_val(&__exception_vectors) >= 2048);` at `vectors.S:28` if symbol accessible
  - Extend `mmu.rs:276-283` compile-time alignment assertions with kernel-entry alignment
  - Document `find-msvc-tools` non-Windows-host status in `THIRD_PARTY_LICENSES.md`
- **Acceptance**: each LOW addressed
- **Regression test**: rust gate

### AN8-F — AN8 closure

- **Files**: `CHANGELOG.md`; verify `cargo clippy --workspace -- -D warnings` 0 warnings; `cargo test --workspace` count update
- **Acceptance**: PR merged; rust gate PASS

---

## 12. Phase AN9 — Tests / CI / Scripts

**Goal**: close the four HIGH test findings (H-20 KernelError matrix, H-21 lake-exe timeout, H-22 small-fixture sha256, H-23 named AK6 tests), batch TST-M01..M13, and address Test LOWs. This phase exercises everything the prior phases shipped and gates AN10's closure.

**Effort**: 4–5 days. **Blocks**: AN10.

### AN9-A — KernelError variant cross-syscall coverage matrix (H-20)

- **Audit ID**: H-20 (HIGH)
- **Files**:
  - `tests/KernelErrorMatrixSuite.lean` (new) — dedicated suite for the rejection matrix
  - `scripts/test_tier2_negative.sh` — wire the new suite
  - `SeLe4n/Model/State.lean:34-97` — verify the 51-variant `KernelError` enumeration is the source-of-truth
- **Plan**:
  1. Build the rows-=-`SyscallId` × cols-=-`KernelError` matrix as a Lean `def errorMatrix : List (SyscallId × KernelError × String)` table where each row is `(syscall, expectedError, scenarioDescription)`.
  2. For each populated cell, write a scenario test that constructs a deliberately-failing input and asserts the dispatcher returns the expected `KernelError` variant.
  3. Target coverage per audit recommendation: **≥35 of 51 variants** with at least one per-syscall rejection test. Prioritize security-relevant variants explicitly named in the audit:
     `.revocationRequired`, `.asidNotBound`, `.schedulerInvariantViolation`, `.alignmentError`, `.vmFault`, `.targetSlotOccupied`, `.cyclicDependency`, `.dependencyViolation`, `.replyCapInvalid`.
  4. Verify the matrix is discoverable: a `#eval errorMatrix.length` shows the populated count; a `theorem errorMatrix_covers_at_least_35 : errorMatrix.length ≥ 35 := by decide` is the audit-deliverable witness.
  5. After AN3..AN8 introduce any new `KernelError` variants (e.g., AN6-E introduces `partialResolution` if API-M01 is taken), update the matrix in the same PR.
- **Acceptance**:
  - New suite added; ≥35 variants tested
  - `scripts/test_tier2_negative.sh` runs the new suite
  - `lake exe kernel_error_matrix_suite` PASS with explicit assertion count printed
- **Regression test**: full gate; new suite execution
- **Cascade**: ~50 new test scenarios; one new file

### AN9-B — `lake exe …` timeout wrapper (H-21)

- **Audit ID**: H-21 (HIGH)
- **Files**: `scripts/test_lib.sh`, possibly `scripts/test_smoke.sh` / `test_full.sh` / `test_nightly.sh`
- **Plan**:
  1. In `scripts/test_lib.sh`, define `LEAN_TEST_TIMEOUT_MINS=${LEAN_TEST_TIMEOUT_MINS:-30}` near the top.
  2. Wrap every `lake exe <suite>` invocation with `timeout "${LEAN_TEST_TIMEOUT_MINS}m" lake exe <suite>`.
  3. Add a `run_check_with_timeout()` helper that maps:
     - exit `0` → PASS
     - exit `124` → FAIL with explicit message: "Test timeout after ${LEAN_TEST_TIMEOUT_MINS}m — possible runaway proof / scenario; see scripts/test_lib.sh."
     - other non-zero → FAIL with original message
  4. CI workflows use the default 30 minutes; nightly may override to 120 minutes for slow suites.
  5. Verify per-suite that 30 minutes is generous: profile the slowest suite (`lake exe operation_chain_suite` or `negative_state_suite`) and assert it completes in < 5 min on CI hardware.
- **Acceptance**:
  - `timeout` wrapper present at every `lake exe` site
  - Synthetic test (deliberate `while true do ()` loop) exits `124` and is mapped to the explicit FAIL message
  - CI runs no longer hang past timeout boundary
- **Regression test**: smoke gate; manual timeout-hit verification with synthetic test
- **Cascade**: ~10-15 invocation sites

### AN9-C — Small-fixture sha256 companions (H-22 — downgraded LOW, addressed here)

- **Audit ID**: H-22 (downgraded HIGH→LOW per audit §0.4)
- **Files**:
  - `tests/fixtures/robin_hood_smoke.expected.sha256` (new)
  - `tests/fixtures/two_phase_arch_smoke.expected.sha256` (new)
  - `scripts/test_tier2_trace.sh:49-55` — extend `sha256sum -c` to cover the two new files
- **Plan**:
  1. Compute `sha256sum tests/fixtures/robin_hood_smoke.expected` and write the result to `robin_hood_smoke.expected.sha256` (single line: `<hash>  robin_hood_smoke.expected`).
  2. Same for `two_phase_arch_smoke.expected`.
  3. Extend `test_tier2_trace.sh` to validate all three sha256 companions in the same `sha256sum -c` invocation; emit the same "Fixture drift detected — to update: run sha256sum and update the .sha256 file" remediation message.
  4. Document the fixture-update workflow in a new `tests/fixtures/README.md` (closes TST-M10).
- **Acceptance**:
  - All three fixtures have `.sha256` companions
  - CI fails on a deliberate fixture edit unless the `.sha256` is also updated
  - `tests/fixtures/README.md` documents regeneration
- **Regression test**: smoke gate; manual fixture-edit-without-hash-update verification
- **Cascade**: 2 new files; 1 script extension

### AN9-D — Named test functions for AK6 sub-tests (H-23, TST-M11)

- **Audit IDs**: H-23 (HIGH), TST-M11 (MEDIUM, same root cause)
- **Files**: `tests/InformationFlowSuite.lean:1067-1114` (and adjacent comment-delimited blocks for AK6-A through AK6-F)
- **Plan**:
  1. For every comment-delimited test block in `InformationFlowSuite.lean`, wrap as a named `def test_AK6_<letter> : IO Bool := do …` function.
  2. Add a dispatch table `def ak6Tests : List (String × IO Bool) := [("AK6-A", test_AK6_A), …]` consumed by the suite's `main` so failures report the named sub-test (`AK6-G FAIL: …`).
  3. Apply the same pattern retroactively to AK6-A..F per TST-M11 (audit notes only AK6-G/H/I have visible tests today; A..F need named-test wrappers).
  4. Naming discipline: per CLAUDE.md "internal-first naming" rule, the function names describe semantics — `test_schedContext_param_validation` rather than `test_AK6_A`. The dispatch table maps the audit-ID label to the semantic function.
- **Acceptance**:
  - Every AK6-A..I sub-test is a named function with semantic name
  - Suite output reports per-sub-test PASS/FAIL with audit-ID label
- **Regression test**: full gate; `lake exe information_flow_suite`
- **Cascade**: ~9 test functions; ~1 dispatch table

### AN9-E — Test MEDIUM batch (TST-M01..M13)

- **Audit IDs**: TST-M01..M13 (subset; some already covered above)
- **Plan**:
  - **TST-M01**: extend AK8-B test pattern (atomicity + success paths) to other AK8 sub-items (C, D, E, F, G, H, I, J, K) that lack tests per audit.
  - **TST-M02**: add `assertCrossSubsystemInvariants` bundled assertion in `SeLe4n/Testing/InvariantChecks.lean` running all 12 (post-AN2-D) cross-subsystem invariants in one call with a single failure report.
  - **TST-M03**: `scripts/test_abi_roundtrip.sh:14` — either create `_common.sh` with shared helpers OR remove the `source … || true` line. Audit-preferred: create `_common.sh` and drop the swallow.
  - **TST-M04**: standardize `secrets.GITHUB_TOKEN` → `github.token` across `.github/workflows/*.yml`.
  - **TST-M05**: `scripts/test_docs_sync.sh:36-56` — promote GitBook drift check to hard failure (`exit 1`).
  - **TST-M06**: rename `test_tier3_invariant_surface.sh` description to "invariant-surface anchors" (already named correctly per CLAUDE.md; verify wording is consistent in script comments).
  - **TST-M07**: add idempotency guard to `setup_lean_env.sh` via sentinel file `~/.elan/.sele4n-bootstrap-marker`.
  - **TST-M08**: add 3-attempt `apt-get install` retry with backoff in `.github/workflows/lean_action_ci.yml:45-50`.
  - **TST-M09**: input-validate `expectCond`/`expectError` `tag`/`label` to reject empty strings (compile-time `String.length > 0` check).
  - **TST-M10**: covered by AN9-C (fixtures README).
  - **TST-M11**: covered by AN9-D.
  - **TST-M12**: audit `scripts/audit_testing_framework.sh`; document purpose & integrate, OR remove if unused. Audit-preferred: integrate (e.g., wire into `test_tier4_nightly_candidates.sh`).
  - **TST-M13**: promote `TraceSequenceProbe` to Tier 2 OR document why it's Tier-4-only in CLAUDE.md.
- **Acceptance**: each TST-M addressed
- **Regression test**: full gate; `scripts/test_tier0_hygiene.sh` PASS
- **Cascade**: ~10-15 sites; mostly script edits

### AN9-F — Test LOW batch

- **Audit IDs**: 7 LOW per audit §2.10
- **Plan**:
  - Cache-key separation in `lean_action_ci.yml`
  - Add live assertion in `LivenessSuite.lean:166`
  - Add generator rule for `tests/fixtures/scenario_registry.yaml`
  - Verify `test_tier0_hygiene.sh` shellcheck enforcement is comprehensive
  - OID range discipline runtime assertion at `withObject` entry
  - Verify `lean_toolchain_update_proposal.yml` cannot bypass branch protection
  - Verify `nightly_determinism.yml` actually compares trace outputs across commits
- **Acceptance**: each LOW addressed; smoke gate PASS
- **Regression test**: smoke gate

### AN9-G — AN9 closure

- **Files**: `CHANGELOG.md`; `scripts/test_lib.sh` final review
- **Acceptance**: PR merged; full gate + rust gate PASS; new suites registered in CI

---

## 13. Phase AN10 — Documentation, themes, closure

**Goal**: synthesise the AN1..AN9 deltas, deliver the cross-cutting Theme 4.1 (discharge index) and Theme 4.4 (SMP inventory) artifacts, batch DOC-M01..M08 + DOC LOWs, ship the new `AUDIT_v0.30.6_DEFERRED.md`, update `WORKSTREAM_HISTORY.md`, refresh `CLAUDE.md`, bump version, and close WS-AN.

**Effort**: 3 days. **Blocks**: workstream closure (final gate). **Branch**: same WS-AN branch.

### AN10-A — Theme 4.1 deliverable: closure-form discharge index

- **Audit reference**: §4.1 Cross-cutting theme
- **Files**:
  - `docs/audits/AUDIT_v0.30.6_DISCHARGE_INDEX.md` (new) — the discharge artifact
  - `SeLe4n/Kernel/CrossSubsystem.lean` — references the index from inline cross-references
- **Plan**:
  1. New deliverable doc enumerates every closure-form theorem in the codebase. For each theorem:
     - Theorem name (e.g., `cspaceCopy_preserves_capabilityInvariantBundle`)
     - File:line anchor
     - Hypothesis names (e.g., `hCdtCompleteness`, `hCdtAcyclicity`, `hProjEq`, `hSchedProj`, `hArmProj`)
     - Canonical discharge site (file:line of the caller that supplies the witness)
     - Reachability check: a Lean `example` or `#check` proving the discharge composes on one representative input
  2. Categorize by theme:
     - **CDT post-state witnesses** (H-04 / AN4-C): 6 entries
     - **`hProjEq`/`hArmProj` projection closures** (H-07 / AN6-A): 6 entries (1 substantively discharged in AN6-A; 5 remaining listed with their discharge recipes)
     - **`hSchedProj` schedule closures** (SC-M02): 5 entries
  3. The discharge index becomes the canonical reference cited from every closure-form theorem's docstring. Inline references read `-- Discharge: see docs/audits/AUDIT_v0.30.6_DISCHARGE_INDEX.md §<theme>-<entry>`.
  4. Format the index as a Markdown table grouped by theme; total length ~200 lines.
- **Acceptance**: file committed; every closure-form theorem in the codebase has a row; cross-references inserted at theorem docstrings
- **Regression test**: smoke gate; `check_website_links.sh` PASS
- **Cascade**: ~17 docstring updates

### AN10-B — Theme 4.4 deliverable: SMP-latent single-core inventory

- **Audit reference**: §4.4 Cross-cutting theme
- **Files**:
  - `SeLe4n/Kernel/Concurrency/Assumptions.lean` (new) — single-core inventory module
  - `docs/spec/SELE4N_SPEC.md` §6 — cross-reference
- **Plan**:
  1. New Lean module enumerates every site that depends on the single-core assumption:
     - `cspaceLookupMultiLevel` (H-05 / AN4-D) — resolved CNode validity across calls
     - `H-10 ThreadId.toObjId namespace` (AN2-D) — typed-id disjointness via functional-map uniqueness
     - `H-11 RegisterFile.BEq` — pre-AN2-C; once `Fin 32` lands, this drops out of inventory
     - `Architecture/Assumptions.lean :: singleCoreOnly` — already explicit
     - `Capability/Operations.lean :: cspaceCopy/Move/Mutate` — CDT post-state composition assumes no concurrent mutation
     - `Lifecycle/Operations.lean :: lifecyclePreRetypeCleanup` — sequential cleanup ordering
     - `serviceHasPathTo` (SVC-M01 / AN4-H) — graph traversal is non-atomic
     - `Scheduler/Operations/Core.lean :: timerTick` — timer + replenishment pipeline
  2. Each entry is a `def` carrying a docstring with:
     - Single-core precondition (what holds today)
     - SMP-side discharge obligation (what must hold under concurrency — typically a critical-section bracket)
     - Cross-reference to the source theorem
  3. The module is import-only documentation; no runtime semantics. Tag with `-- This module is post-1.0 SMP refactor surface. See SELE4N_SPEC.md §6.`
- **Acceptance**: module created; ≥8 inventory entries; SPEC §6 cross-reference added
- **Regression test**: smoke gate; module gate `lake build SeLe4n.Kernel.Concurrency.Assumptions`
- **Cascade**: 1 new file; 1 SPEC cross-reference

### AN10-C — Documentation MEDIUM batch (DOC-M01..M08)

- **Audit IDs**: DOC-M01..M08
- **Plan**:
  - **DOC-M01**: covered by AN1-A (i18n READMEs included).
  - **DOC-M02**: covered by AN7-D (PLT-M07 staged-modules wiring).
  - **DOC-M03**: add per-file SPDX headers `// SPDX-License-Identifier: GPL-3.0-or-later` to all Rust files (`rust/**/*.rs`); add `-- SPDX-License-Identifier: GPL-3.0-or-later` to all Lean files missing it. Mechanical pass; ~150 files.
  - **DOC-M04**: covered by AN0-A baseline + per-phase CLAUDE.md large-files-list refresh; AN10 final refresh consolidates.
  - **DOC-M05**: regenerate `docs/codebase_map.json` post AN1..AN9 via `scripts/generate_codebase_map.py`; verify README metric table matches via `scripts/sync_readme_from_codebase_map.sh --check`.
  - **DOC-M06**: covered by AN1-A (all 10 i18n READMEs verified).
  - **DOC-M07**: add new `WORKSTREAM_HISTORY.md` entry "WS-AN post-audit-remediation" enumerating C-01..C-03, H-01..H-24 finding IDs and their disposition.
  - **DOC-M08**: create `CONTRIBUTING.md` covering contributor expectations, branch policy, test gates, and the C-03 hook installation. Also document the `pull_request_target` non-use as a security decision.
- **Acceptance**: each DOC-M addressed
- **Regression test**: smoke gate; `check_website_links.sh` PASS; `check_version_sync.sh` PASS
- **Cascade**: DOC-M03 ~150 file headers (mechanical, low-risk)

### AN10-D — Documentation LOW batch

- **Audit IDs**: 5 LOW per audit §2.10
- **Plan**:
  - Annotate or remove `docs/dev_history/audits/audit_findings_provided_by_me.md`
  - Establish CLAUDE.md "Active workstream context" archive convention: keep last 3 releases inline, archive older to `docs/CLAUDE_HISTORY.md`
  - "One active audit at a time" convention documented in `docs/audits/README.md` (new short doc explaining the audit-doc lifecycle: COMPREHENSIVE → ERRATA → DEFERRED → archive into `docs/dev_history/audits/`)
  - `.gitignore` verified adequate (no change)
  - Test harness file naming discipline verified (no change)
- **Acceptance**: each LOW addressed
- **Regression test**: smoke gate

### AN10-E — Theme 4.5 / 4.6 inline-marker hygiene pass

- **Audit references**: §4.5 (workstream IDs in comments) and §4.6 (stale forward references)
- **Files**: codebase-wide comment grep
- **Plan**:
  1. `grep -rn "WS-[A-Z]\|AK[0-9]" SeLe4n/ rust/ tests/ scripts/ --include="*.lean" --include="*.rs" --include="*.sh"` to inventory the inline-marker count. Capture in `AUDIT_v0.30.6_WS_AN_BASELINE.txt` as the AN10 baseline.
  2. For each marker, classify:
     - **Completed-work historical**: leave alone (legitimate dev-history)
     - **Deferred-work pointer**: retarget to the canonical DEF-ID per AN1-C playbook
     - **Workstream-cadence rot**: convert to `// see WORKSTREAM_HISTORY:<id>` short cross-reference
  3. Land in batches of ≤50 changes per commit; each commit's diff is mechanically verifiable.
  4. Per audit guidance, this is a **hygiene pass**, not a behavior change. The total inline-marker count likely drops from 5000+ → ~3000 (rough estimate; baseline capture in step 1 finalizes the target).
- **Acceptance**: marker count reduced; no production code semantics altered; `WORKSTREAM_HISTORY.md` cross-refs are valid
- **Regression test**: smoke gate; `check_website_links.sh` PASS
- **Cascade**: cascade-heavy by line count (~2000+ comment edits) but trivially low-risk per commit; spread across 5-10 commits

### AN10-F — Theme 4.7 file-split completion pass

- **Audit reference**: §4.7
- **Files**: any kernel `.lean` file ≥ 2000 LOC after AN3-C/D, AN4-F (CAP-M03), AN5-A, AN6-E
- **Plan**:
  1. Re-scan with `wc -l` after AN3..AN6 splits land. Verify the original 5 monolithic files are below the 2000-LOC ceiling.
  2. If any file remains above ceiling (e.g., `Capability/Operations.lean` at 1651 LOC is borderline; `Model/Object/Structures.lean` at 2769 LOC may still need a split), schedule a mini-split commit here.
  3. Update `CLAUDE.md` "Known large files" list to reflect the post-AN10 sizes.
  4. Document the 2000-LOC ceiling convention in `CONTRIBUTING.md` (links to AN10-C / DOC-M08).
- **Acceptance**: no production `.lean` file > 2000 LOC except `CHANGELOG.md` and other documentation/historical content per audit's own exception
- **Regression test**: full gate
- **Cascade**: 0–2 additional file splits depending on residual sizes

### AN10-G — New `AUDIT_v0.30.6_DEFERRED.md`

- **Files**: `docs/audits/AUDIT_v0.30.6_DEFERRED.md` (new)
- **Plan**: parallel to `AUDIT_v0.29.0_DEFERRED.md`. Document every WS-AN deferred item:
  - **Carried-forward from AUDIT_v0.29.0_DEFERRED.md**:
    - DEF-A-M04 (TLB+Cache composition closure) — hardware-binding
    - DEF-A-M06 / DEF-AK3-I (`tlbBarrierComplete` substantive binding) — hardware-binding
    - DEF-A-M08 / DEF-A-M09 / DEF-AK3-K (MMU/Device BarrierKind) — hardware-binding
    - DEF-C-M04 (`suspendThread` atomicity Rust proof) — hardware-binding
    - DEF-P-L9 (VSpaceRoot boot exclusion) — hardware-binding
    - DEF-R-HAL-L14 (SVC FFI wiring) — hardware-binding
    - DEF-F-L9 — RESOLVED in AN2-G; mark as closed with commit SHA
    - DEF-AK2-K.4 (`eventuallyExits` by-design) — by-design; carry unchanged
    - DEF-AK7-E.cascade (`ValidObjId`/`ValidThreadId` rollout) — proof-hygiene; partial progress noted in AN10-E if any
    - DEF-AK7-F.cascade (`ObjKind` migration) — proof-hygiene
  - **New deferred items from WS-AN that could not close in AN1..AN9**:
    - DEF-PLT-M02 (VSpaceRoot boot bridge for non-empty configs) — hardware-binding
    - DEF-H-07.partial (5 remaining closure-form projection theorems) — toolchain-pending if AN6-A took the toolchain-blocked path
    - DEF-H-09.transitive (`untypedAncestorRegionsDisjoint` strengthening) — landed only if AN6-C Track B was deferred
    - DEF-R-HAL-L17..L20 (per AN1-C: bounded WFE, parameterized barriers, OSH widening, secondary core bring-up) — hardware-binding / SMP
  - **Closed in WS-AN** (recorded for traceability):
    - Every C-01..C-03, H-01..H-24, M-*, L-* finding from AUDIT_v0.30.6_COMPREHENSIVE.md that AN1..AN10 addressed; cross-reference each by AN sub-task ID and commit SHA
- **Acceptance**: file committed; all deferred IDs cross-reference live code; closed-items table lists every WS-AN sub-task disposition
- **Regression test**: smoke gate; `check_website_links.sh` PASS
- **Cascade**: 1 new file (~300 lines)

### AN10-H — `WORKSTREAM_HISTORY.md` WS-AN entry

- **Files**: `docs/WORKSTREAM_HISTORY.md`
- **Plan**: append the canonical WS-AN closure entry following the WS-AK/WS-AM precedent:
  - WS-AN identity: `v0.30.6 → v1.0.0` (or v0.30.7+ maintainer-selected patch-only sequence)
  - 11-phase breakdown (AN0..AN10) with gate-state table
  - Cross-reference to:
    - `docs/audits/AUDIT_v0.30.6_COMPREHENSIVE.md`
    - `docs/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md` (this doc)
    - `docs/audits/AUDIT_v0.30.6_DEFERRED.md` (AN10-G)
    - `docs/audits/AUDIT_v0.30.6_DISCHARGE_INDEX.md` (AN10-A)
  - Finding-count arithmetic: 196 findings addressed (2 actionable CRITICAL + 23 HIGH + 71 MEDIUM + 58 LOW + 40 INFO)
  - Deferred-items count: 11 carried forward + 0-4 new (depending on AN6-A / AN6-C / AN7-D outcomes)
- **Acceptance**: entry committed; gate-state table filled
- **Regression test**: smoke gate

### AN10-I — `CLAUDE.md` Active-workstream-context refresh

- **Files**: `CLAUDE.md`
- **Plan**:
  1. Replace the top "Active workstream context" paragraph with a WS-AN summary (parallel to the current WS-AK AK10 paragraph).
  2. Per AN10-D LOW item: archive pre-WS-AK paragraphs to `docs/CLAUDE_HISTORY.md` so the active file returns under the 500-line-chunked-read threshold.
  3. Update "Known large files" list — `CHANGELOG.md` grows, `Structural.lean`/`Preservation.lean`/`IF Operations.lean` shrink, new DEFERRED + DISCHARGE_INDEX + DISCHARGE_INDEX are small and don't qualify.
  4. Update "Next workstream" line: set to "WS-AO hardware-binding (post-1.0)" with cross-reference to `AUDIT_v0.30.6_DEFERRED.md`.
- **Acceptance**: CLAUDE.md active section reflects WS-AN closure; archive file created; large-files list refreshed
- **Regression test**: smoke gate

### AN10-J — Version bump and release trajectory

- **Files**: 15 version-bearing files (per `scripts/check_version_sync.sh` canonical list)
- **Plan**:
  1. Per AK10-C precedent, **do NOT tag v1.0.0 programmatically** — the v1.0.0 tag is a maintainer manual action.
  2. Instead, bump patch version `0.30.6 → 0.30.7` (or whatever sequence the maintainer selects) for the WS-AN release cut.
  3. `scripts/check_version_sync.sh` PASS at the new version across all 15 files (`lakefile.toml`, `rust/Cargo.toml`, `README.md` + 10 i18n READMEs, `docs/spec/SELE4N_SPEC.md`, `CLAUDE.md`, and any CHANGELOG header).
  4. If the maintainer chooses `v1.0.0` as the WS-AN cut, perform the tag in a separate commit after the plan lands.
- **Acceptance**: `check_version_sync.sh` PASS at the new version
- **Regression test**: full gate + rust gate + `check_version_sync.sh`

### AN10-K — CHANGELOG entry consolidation

- **Files**: `CHANGELOG.md`
- **Plan**: consolidate AN1..AN9 per-phase entries under a single `## [0.30.7] — 2026-MM-DD (WS-AN closure)` (or equivalent version) heading, structured as:
  ```
  ### Addressed (AUDIT_v0.30.6_COMPREHENSIVE.md)
   - Critical: C-01, C-03 (C-02 resolved in prior commit)
   - High: H-01..H-24 (22 closed in AN1..AN9; H-22 addressed post-downgrade in AN9-C)
   - Medium: 71 addressed across AN3..AN9 (per-ID disposition in AUDIT_v0.30.6_DEFERRED.md)
   - Low: 58 addressed (per-ID disposition in AUDIT_v0.30.6_DEFERRED.md)
  ### Carried forward
   - ...
  ### Thanks
   - ...
  ```
- **Acceptance**: single coherent entry; cross-references to AUDIT_v0.30.6_DEFERRED.md resolve
- **Regression test**: smoke gate; `check_website_links.sh` PASS

### AN10-L — Final release gate

- **Files**: none modified; gate execution only
- **Plan**: execute the full release gate:
  - `./scripts/test_fast.sh` PASS
  - `./scripts/test_smoke.sh` PASS
  - `./scripts/test_full.sh` PASS
  - `NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh` PASS
  - `cargo test --workspace` PASS (updated test count recorded)
  - `cargo clippy --workspace -- -D warnings` 0 warnings
  - `scripts/check_version_sync.sh` PASS at target version
  - `scripts/check_website_links.sh` PASS
  - `scripts/ak7_cascade_check_monotonic.sh` PASS against refreshed baseline
  - `scripts/test_tier0_hygiene.sh` PASS
  - `scripts/test_tier3_invariant_surface.sh` PASS
  - `scripts/test_rust_conformance.sh` PASS
  - `scripts/test_abi_roundtrip.sh` PASS
  - `scripts/audit_testing_framework.sh` PASS (wired per TST-M12)
  - QEMU boot verified via `scripts/test_qemu.sh` (skip with log if no emulator available)
  - Zero `sorry` / `axiom` / `native_decide` in `SeLe4n/` and `Main.lean` and `rust/`
  - Fixture byte-identity preserved (`tests/fixtures/main_trace_smoke.expected` matches `lake exe sele4n` output; sha256 companions valid)
  - All 10 i18n READMEs updated
  - `docs/audits/AUDIT_v0.30.6_COMPREHENSIVE.md` marked CLOSED with commit SHAs per finding
- **Acceptance**: every gate item PASS; PR merge eligible
- **Regression test**: the gate itself is the regression test

### AN10-M — Archive plan files

- **Files**:
  - `docs/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md` (this doc) → `docs/dev_history/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md`
  - `docs/audits/AUDIT_v0.29.0_COMPREHENSIVE.md` → `docs/dev_history/audits/AUDIT_v0.29.0_COMPREHENSIVE.md`
  - `docs/audits/AUDIT_v0.29.0_DEFERRED.md` → `docs/dev_history/audits/AUDIT_v0.29.0_DEFERRED.md`
  - `docs/audits/AUDIT_v0.29.0_ERRATA.md` → `docs/dev_history/audits/AUDIT_v0.29.0_ERRATA.md`
- **Plan**: per audit §2.10 "one active audit at a time" convention (new in AN10-D). When WS-AN closes, archive this plan + the v0.29.0 parent audit alongside it. The v0.30.6 COMPREHENSIVE stays in `docs/audits/` until the next audit cuts, then it archives too.
- **Acceptance**: files moved; every reference (CLAUDE.md, WORKSTREAM_HISTORY, README) updated to the archived paths; `check_website_links.sh` updated manifest; `scripts/website_link_manifest.txt` refreshed
- **Regression test**: smoke gate + `check_website_links.sh` PASS

### AN10-N — WS-AN closure

- **Files**: a final summary commit referencing the full WS-AN disposition
- **Acceptance**:
  - Every sub-task AN0-A..AN10-M accounted for
  - WORKSTREAM_HISTORY.md records closure with gate-state table
  - `docs/audits/` contains only the v0.30.6 comprehensive + the post-audit DISCHARGE_INDEX + the new DEFERRED
  - The plan itself is archived under `docs/dev_history/audits/`
- **Regression test**: the AN10-L final release gate

---

## 14. Cross-cutting theme handling — detailed placement rationale

This section explains why the seven cross-cutting themes identified in
`AUDIT_v0.30.6_COMPREHENSIVE.md` §4 are folded into the per-subsystem
phases rather than each given its own dedicated phase, plus how they
interact.

### 14.1 Theme 4.1 — Closure-form proof obligations

**Where addressed**: AN4-C (CDT bridges), AN6-A (one projection theorem), AN10-A (index artifact).

**Rationale**: the three sub-patterns (CDT post-state, `hProjEq`, `hSchedProj`) live in different subsystems and their discharges are
already different shapes. Addressing each in the phase that owns its
subsystem keeps the cascade bounded. The index artifact in AN10-A
aggregates the three into a single auditable deliverable without
forcing a monolithic phase.

**Interaction**: AN4-C's CDT bridge template informs AN6-A's choice of
which projection theorem to substantively discharge (pick one whose
frame lemmas mirror the CDT pattern). AN10-A then indexes both as a
single artifact.

### 14.2 Theme 4.2 — Tuple-projection brittleness → named structures

**Where addressed**: AN2-G (`allTablesInvExtK` — foundation anchor), AN3-B (`ipcInvariantFull`), AN4-F (CAP-M05 `capabilityInvariantBundle`), plus incidental at AN6-E (other bundles surfaced during IF split).

**Rationale**: named-structure refactor touches every consumer. Doing
it per-subsystem in the subsystem's own phase means each cascade runs
once against a stable set of imports. Doing it as a monolithic phase
would require all subsystem phases to pause while the refactor lands —
worse throughput.

**Interaction**: AN2-G establishes the convention (how to write the
bridge theorem, how to migrate destructures). AN3-B, AN4-F follow the
convention mechanically. AN10 does NOT need to re-run any
tuple→structure refactor.

### 14.3 Theme 4.3 — Advisory predicates → subtype gates

**Where addressed**: AN2-A (`Badge`), AN2-B (`CPtr`/`Slot`/`VAddr`/`PAddr`), AN2-F / FND-M03 (`UntypedObject`), AN4-F / CAP-M04 (`RetypeTarget`).

**Rationale**: all in AN2 because the smart constructors are the
foundation for every downstream consumer. Cascades flow outward from
AN2 once.

**Interaction**: AN4-F's `RetypeTarget` subtype depends on the
`UntypedObject` subtype from AN2-F. The phase order AN2 → AN4 ensures
the dependency.

### 14.4 Theme 4.4 — SMP-latent single-core assumptions

**Where addressed**: AN4-D (H-05 first inventory entry), AN6-F / CX-M03 (`bootFromPlatform_currentCore_is_zero_witness`), AN10-B (module artifact).

**Rationale**: the inventory is a docs/pre-SMP-checklist artifact, not
a behavior change. Per-subsystem entries land as the subsystem gets
touched; AN10-B aggregates into a single module.

**Interaction**: AN10-B's module imports no kernel modules — it is
docs-only. AN4-D / CX-M03 are the proof-level witnesses that AN10-B
indexes.

### 14.5 Theme 4.5 — Workstream IDs in comments

**Where addressed**: AN10-E.

**Rationale**: a mechanical inline-marker hygiene pass. Late-phase
because every prior phase introduces new AN-* markers; doing it once
at AN10 is more efficient than pausing to re-run it after each phase.

**Interaction**: AN10-E's grep baseline is captured in AN0-A and AN10's
AN1..AN9 cumulative inline-marker count.

### 14.6 Theme 4.6 — Stale forward references

**Where addressed**: AN1-C (source-side retarget of WS-V/AG10 TODOs), AN10-E (codebase-wide hygiene pass).

**Rationale**: the urgent retargets land in AN1 (closes H-24 CRITICAL-ish
gate item); the broader cleanup aggregates in AN10.

**Interaction**: AN1-C targets the 6 flagged sites; AN10-E catches the
remainder.

### 14.7 Theme 4.7 — Monolithic file splits

**Where addressed**: AN3-C (Structural.lean), AN3-D (NotificationPreservation + CallReplyRecv), AN4-F / CAP-M03 (Preservation.lean), AN4-G / LIF-M05 (Lifecycle/Operations.lean), AN5-A (Scheduler/Preservation.lean), AN6-E / IF-M03 (IF/Operations.lean), AN10-F (residual sweep).

**Rationale**: each split is subsystem-local; doing each in its own
phase preserves reviewability (smaller diffs, single reviewer domain).
AN10-F sweeps any remaining ≥ 2000 LOC files after AN3..AN6 land.

**Interaction**: AN10-F depends on all prior splits having landed.

---

## 15. Closure criteria & v1.0.0 release readiness checklist

This section is the **single canonical gate** for declaring WS-AN
complete. Every item below must be verifiable.

### 15.1 Audit finding disposition (mandatory)

| Severity | Audit count | WS-AN target | Verification |
|----------|------------:|--------------|--------------|
| CRITICAL | 3 (1 resolved pre-WS-AN) | 2/2 closed in AN1 | C-01 (AN1-A), C-03 (AN1-B); C-02 already resolved |
| HIGH | 24 | 23 closed in AN1..AN9 (H-22 downgraded LOW per audit, addressed AN9-C) | each has a sub-task ID; per-PR evidence |
| MEDIUM | 71 | ≥ 65 closed in AN3..AN9; ≤ 6 deferred to `AUDIT_v0.30.6_DEFERRED.md` with rationale | per-PR evidence + DEFERRED entries |
| LOW | 58 | ≥ 50 closed in batch commits | per-PR evidence |
| INFO | 40 | n/a — verifications, not work | (informational) |

**Rule**: any finding NOT closed must have a `DEF-*` entry in
`AUDIT_v0.30.6_DEFERRED.md` with explicit rationale and acceptance
criteria for a future workstream. No finding silently disappears.

### 15.2 Build & test gate (mandatory)

- [ ] `lake build` passes with 0 warnings (job count matches AN0-A baseline ± expected delta)
- [ ] `cargo build --workspace` passes
- [ ] `cargo test --workspace` PASS (415 → ~430 tests after AN9 additions)
- [ ] `cargo clippy --workspace -- -D warnings` 0 warnings
- [ ] `./scripts/test_smoke.sh` PASS
- [ ] `./scripts/test_full.sh` PASS
- [ ] `./scripts/test_tier0_hygiene.sh` PASS
- [ ] `./scripts/test_tier3_invariant_surface.sh` PASS
- [ ] `./scripts/test_rust_conformance.sh` PASS
- [ ] `./scripts/test_abi_roundtrip.sh` PASS
- [ ] `./scripts/audit_testing_framework.sh` PASS (TST-M12 wiring)
- [ ] `./scripts/check_version_sync.sh` PASS at target version
- [ ] `./scripts/check_website_links.sh` PASS
- [ ] `./scripts/ak7_cascade_check_monotonic.sh` PASS against refreshed baseline
- [ ] Synthetic timeout test (AN9-B) confirms exit-124 mapping

### 15.3 Source-purity gate (mandatory)

- [ ] Zero `sorry` in `SeLe4n/` and `Main.lean` and `rust/`
- [ ] Zero `axiom` in `SeLe4n/` (excluding documented `Architecture/Assumptions.lean` declarations)
- [ ] Zero `native_decide` in `SeLe4n/`
- [ ] Zero `unsafe` blocks in Rust without SAFETY comment
- [ ] Zero `#[allow(unused)]` without docstring rationale
- [ ] Zero `TODO(WS-V)` / `TODO(AG10)` / other closed-workstream references; all live TODOs point at `DEF-*` IDs

### 15.4 Documentation gate (mandatory)

- [ ] `README.md` "Latest audit" pointer updated to AUDIT_v0.30.6_COMPREHENSIVE.md
- [ ] All 10 i18n READMEs mirror the pointer change
- [ ] `CLAUDE.md` "Active workstream context" reflects WS-AN closure
- [ ] `docs/WORKSTREAM_HISTORY.md` WS-AN entry committed with gate-state table
- [ ] `docs/audits/AUDIT_v0.30.6_DEFERRED.md` committed with all post-1.0 items
- [ ] `docs/audits/AUDIT_v0.30.6_DISCHARGE_INDEX.md` committed
- [ ] `CONTRIBUTING.md` committed (DOC-M08)
- [ ] All Rust + Lean files have SPDX headers (DOC-M03)
- [ ] `docs/spec/SELE4N_SPEC.md` updated with §5/§6/§7 deltas referenced in AN3..AN6

### 15.5 Hardware-fidelity gate (advisory — pre-1.0 hardware-binding is post-WS-AN)

- [ ] BCM2712 hardware constants cross-checked (existing `scripts/test_hw_crosscheck.sh` PASS)
- [ ] QEMU boot if emulator available (`scripts/test_qemu.sh` PASS or skip-with-log)
- [ ] No regression in `docs/hardware_validation/*.md` reports

### 15.6 Fixture & determinism gate (mandatory)

- [ ] All 3 fixtures have sha256 companions and `test_tier2_trace.sh` enforces all 3
- [ ] `lake exe sele4n` byte-identical to `tests/fixtures/main_trace_smoke.expected`
- [ ] `nightly_determinism.yml` cross-commit drift check confirmed passing
- [ ] `tests/fixtures/README.md` documents regeneration (TST-M10)

### 15.7 Maintainer-decision items (NOT gated by WS-AN automation)

- Final v1.0.0 tag — manual maintainer action per AK10-C precedent
- Whether to ship a feature-flag for the AN6-A toolchain-blocked closure-form template
- Whether AN6-C Track B (`untypedAncestorRegionsDisjoint` strengthening) lands or defers
- Whether DOC-M03 SPDX header pass lands as a single mechanical PR or batched per-subsystem

---

## 16. Deferred items carry-forward — `AUDIT_v0.29.0_DEFERRED.md` disposition

This section establishes the WS-AN disposition for every item in the
parent `AUDIT_v0.29.0_DEFERRED.md` so AN10-G's new
`AUDIT_v0.30.6_DEFERRED.md` is built from a complete carry-forward map.

### 16.1 Hardware-binding category (carry forward unchanged)

These items require real-silicon bring-up and remain post-1.0
candidates. They are NOT scheduled in WS-AN.

| Deferred ID | Audit Finding | Why not in WS-AN | New disposition |
|-------------|---------------|------------------|-----------------|
| DEF-A-M04 | A-M04 (TLB+cache composition) | Requires HAL FFI sequence witness | Carry into AUDIT_v0.30.6_DEFERRED.md unchanged |
| DEF-A-M06 / DEF-AK3-I | A-M06 (`tlbBarrierComplete`) | Needs HAL call-graph static analysis | Carry unchanged |
| DEF-A-M08 / DEF-A-M09 / DEF-AK3-K | A-M08 / A-M09 (MMU/Device BarrierKind) | Needs FFI sequencing witness | Carry unchanged |
| DEF-C-M04 | C-M04 (`suspendThread` atomicity) | Requires interrupt-disable bracket on hardware | Carry unchanged |
| DEF-P-L9 | P-L9 (VSpaceRoot boot exclusion) | Requires `RPi5/VSpaceBoot` shim | Carry unchanged |
| DEF-R-HAL-L14 | R-HAL-L14 (SVC FFI wiring) | Requires full FFI bridge from userspace | Carry unchanged; AN1-C retargets the source-side TODO to this ID |

### 16.2 Proof-hygiene category

| Deferred ID | Audit Finding | WS-AN disposition |
|-------------|---------------|-------------------|
| DEF-F-L9 | F-L9 (17-deep tuple refactor) | **RESOLVED in AN2-G**; close in AUDIT_v0.30.6_DEFERRED.md with commit SHA |
| DEF-AK2-K.4 | AK2-K.4 (`eventuallyExits` by-design) | **By-design**; carry unchanged with explicit "no action" annotation |
| DEF-AK7-E.cascade | F-M03 (ValidObjId/ValidThreadId rollout) | **PARTIAL** — AN8-E (rust hygiene) does not affect this; AN10-E inline-marker hygiene does NOT migrate signatures. Cascade remains carry-forward; the metric `SENTINEL_CHECK_DISPATCH` continues to grow on opportunistic per-PR migrations gated by `ak7_cascade_check_monotonic.sh`. |
| DEF-AK7-F.cascade | F-M04 (ObjKind migration) | **PARTIAL** — same disposition as DEF-AK7-E.cascade. Reader-side typed-helper adoption (`getTcb?`, `getSchedContext?`, etc.) is encouraged opportunistically in AN3..AN6 commits via the `RAW_MATCH_TCB`/`GETTCB_ADOPTION` monotonicity metrics; explicit migration not required. Carry-forward unchanged. |

### 16.3 Newly-deferred items from WS-AN (added to AUDIT_v0.30.6_DEFERRED.md)

| New ID | Source | Reason for deferral |
|--------|--------|---------------------|
| DEF-PLT-M02 | PLT-M02 (VSpaceRoot boot bridge non-empty configs) | Hardware-binding |
| DEF-H-07.partial | AN6-A toolchain-blocked path (5 of 6 closure-form theorems) | Toolchain-pending Lean 4.x |
| DEF-H-09.transitive | AN6-C Track B (`untypedAncestorRegionsDisjoint`) | Effort budget; pre-AN6 risk-register decision |
| DEF-R-HAL-L17 | AN1-C (bounded WFE optimisation) | Hardware-binding |
| DEF-R-HAL-L18 | AN1-C (parameterized barriers) | Hardware-binding |
| DEF-R-HAL-L19 | AN1-C (OSH widening) | SMP / hardware-binding |
| DEF-R-HAL-L20 | AN1-C (secondary core bring-up) | SMP |

### 16.4 Errata acknowledgement (AUDIT_v0.29.0_ERRATA.md)

All six errata are informational closures under v0.30.6. WS-AN does
NOT modify the errata file. The closure note in AN10-N records that
the errata file remains as-is.

| Errata | WS-AN action |
|--------|--------------|
| E-1 (S-H03 verification) | None |
| E-2 (R-HAL-M12 dead-code) | None |
| E-3 (A-H01 three-layer extent) | None |
| E-4 (R-HAL-H02 partial) | None |
| E-5 (NI-H02 composition) | Closed in AN6-A residual; ERRATA needs no update |
| E-6 (finding-count arithmetic) | None |

---

## 17. PR mapping & commit ordering

This section sequences the AN0..AN10 sub-tasks into PR batches so a
project lead can plan reviews and contributors know which PRs depend
on which.

### 17.1 Recommended PR sequence

| PR | Phase | Sub-tasks | Title (suggested) | Depends on |
|----|-------|-----------|-------------------|------------|
| PR-1 | AN0 | AN0-A, AN0-B, AN0-C | `WS-AN AN0: workstream plan + baseline` | (none) |
| PR-2 | AN1 | AN1-A, AN1-B, AN1-C, AN1-D | `WS-AN AN1: critical-path blockers (C-01, C-03, H-24)` | PR-1 |
| PR-3 | AN2 (1/3) | AN2-A, AN2-B | `WS-AN AN2.1: Badge + wrapper-type private-mk discipline (H-13, Theme 4.3)` | PR-1 |
| PR-4 | AN2 (2/3) | AN2-C, AN2-D | `WS-AN AN2.2: RegisterFile Fin 32 + typedIdDisjointness (H-10, H-11)` | PR-3 |
| PR-5 | AN2 (3/3) | AN2-E, AN2-F, AN2-G, AN2-H | `WS-AN AN2.3: Foundation MEDIUM batch + 17-tuple refactor (FND-M01..M08, DEF-F-L9)` | PR-4 |
| PR-6 | AN8 (parallel) | AN8-A..F | `WS-AN AN8: Rust HAL hardening (H-17, H-18, H-19, RUST-M01..M08)` | PR-1 (independent of Lean phases) |
| PR-7 | AN3 | AN3-A..G | `WS-AN AN3: IPC subsystem (H-01, IPC-M01..M09, Theme 4.7 split)` | PR-5 |
| PR-8 | AN4 | AN4-A..J | `WS-AN AN4: Capability/Lifecycle/Service (H-02..H-06)` | PR-5 |
| PR-9 | AN5 | AN5-A..E | `WS-AN AN5: Scheduler/SchedContext (SCH/SC MEDIUMs)` | PR-5 |
| PR-10 | AN7 | AN7-A..G | `WS-AN AN7: Platform/API (H-14..H-16)` | PR-5 |
| PR-11 | AN6 | AN6-A..H | `WS-AN AN6: Architecture/IF/CrossSubsystem (H-07..H-09, Theme 4.1)` | PR-7, PR-8, PR-9, PR-10 |
| PR-12 | AN9 | AN9-A..G | `WS-AN AN9: Tests/CI/Scripts (H-20..H-23)` | PR-3..PR-11 |
| PR-13 | AN10 (1/2) | AN10-A..F | `WS-AN AN10.1: discharge index, SMP inventory, doc batch` | PR-12 |
| PR-14 | AN10 (2/2) | AN10-G..N | `WS-AN AN10.2: closure (DEFERRED, HISTORY, version, gate)` | PR-13 |

**Parallelism opportunity**: PR-6 (Rust HAL) is independent of all Lean
phases; can land any time after PR-1. PR-7..PR-10 (AN3, AN4, AN5, AN7)
are independent of each other and can land in any order or in parallel
once PR-5 (foundation hardening) merges.

### 17.2 Hot-path early landing

If reviewer bandwidth is constrained, prioritise:

1. PR-2 (AN1) — unblocks public-facing CRITICAL items
2. PR-6 (AN8) — independent, can land in background
3. PR-5 (AN2) — foundation; unblocks PR-7..PR-10

PR-12 (AN9) and PR-13/14 (AN10) cannot start until upstream phases land
because tests depend on the surface.

### 17.3 Per-PR review scope guidance

| PR | Approx LOC delta | Files touched | Reviewer focus |
|----|----:|----:|----------------|
| PR-1 | ~1800 | 1 (this plan) | Plan completeness, audit cross-refs |
| PR-2 | ~80 | ~15 | Stale-pointer correctness, hook idempotency |
| PR-3 | ~150 | ~10 | Subtype gate cascades, BadgeOverflowSuite extension |
| PR-4 | ~200 | ~25 | Fin 32 refactor cascade, typedIdDisjointness preservation cascade (cascade-heavy) |
| PR-5 | ~600 | ~80 | Heartbeat profile (FND-M05), 17-tuple → structure migration |
| PR-6 | ~400 | ~12 (rust/) | RAII refactor correctness, MPIDR symbol drift gate |
| PR-7 | ~700 | ~15 | Structural.lean split correctness (Theme 4.7), named projections |
| PR-8 | ~900 | ~20 | lifecycleRetypeObject visibility cascade, CDT discharge index |
| PR-9 | ~500 | ~12 | Scheduler split, blockingGraphAcyclic rename cascade |
| PR-10 | ~250 | ~10 | DTB deprecation correctness, Check predicate fail-closed |
| PR-11 | ~600 | ~25 | Closure-form template (toolchain-sensitive), CrossSubsystem index |
| PR-12 | ~1500 | ~10 (tests/scripts) | KernelError matrix coverage, timeout wrapper, named tests |
| PR-13 | ~600 | ~30 | Discharge index correctness, SMP inventory completeness |
| PR-14 | ~400 | ~25 | Version sync, archive moves, CHANGELOG consolidation |

### 17.4 PR-merge gate sequence (each PR's CI must pass)

For each PR:
1. `lake build` PASS
2. `cargo test --workspace` PASS
3. `cargo clippy --workspace -- -D warnings` 0 warnings
4. `./scripts/test_smoke.sh` PASS (smoke gate)
5. For PRs that touch theorems / invariants: `./scripts/test_full.sh` PASS (full gate)
6. For PRs that touch fixtures: `sha256sum -c` on companion files PASS
7. `./scripts/check_version_sync.sh` PASS at the prevailing version (no version bump until AN10-J)
8. `./scripts/check_website_links.sh` PASS

The AN10-L final release gate is the master verification; per-PR CI
is a per-step proxy.

---

## 18. Sub-task index — quick lookup by audit ID

This table is the inverse of the per-phase plan: given an audit-ID,
find its phase + sub-task. Use during PR review to confirm a finding
is addressed.

### 18.1 CRITICAL audit IDs

| Audit ID | Phase | Sub-task | Status |
|----------|-------|----------|--------|
| C-01 | AN1 | AN1-A | Scheduled |
| C-02 | (resolved pre-WS-AN) | — | RESOLVED in audit-cut PR |
| C-03 | AN1 | AN1-B | Scheduled |

### 18.2 HIGH audit IDs

| Audit ID | Phase | Sub-task |
|----------|-------|----------|
| H-01 | AN3 | AN3-A |
| H-02 | AN4 | AN4-A |
| H-03 | AN4 | AN4-B |
| H-04 | AN4 | AN4-C |
| H-05 | AN4 | AN4-D |
| H-06 | AN4 | AN4-E |
| H-07 | AN6 | AN6-A |
| H-08 | AN6 | AN6-B |
| H-09 | AN6 | AN6-C |
| H-10 | AN2 | AN2-D |
| H-11 | AN2 | AN2-C |
| H-12 | AN2 | AN2-E |
| H-13 | AN2 | AN2-A |
| H-14 | AN7 | AN7-A |
| H-15 | AN7 | AN7-B |
| H-16 | AN7 | AN7-C |
| H-17 | AN8 | AN8-A |
| H-18 | AN8 | AN8-B |
| H-19 | AN8 | AN8-C |
| H-20 | AN9 | AN9-A |
| H-21 | AN9 | AN9-B |
| H-22 (LOW post-downgrade) | AN9 | AN9-C |
| H-23 | AN9 | AN9-D |
| H-24 | AN1 | AN1-C |

### 18.3 MEDIUM audit IDs (grouped by subsystem)

**IPC (M01..M09)** — all in **AN3-B..F** (M01 in AN3-B; M02..M04 in AN3-C/D; M05..M09 in AN3-E)
**Scheduler (SCH-M01..M05)** — all in **AN5-A, AN5-B**
**Capability (CAP-M01..M05)** — all in **AN4-F**
**Lifecycle (LIF-M01..M06)** — all in **AN4-G**
**Service (SVC-M01..M04)** — all in **AN4-H**
**SchedContext (SC-M01..M03)** — **AN5-D** (SC-M02 cross-references AN6-A)
**Architecture (ARCH-M01..M03)** — **AN6-D**
**InformationFlow (IF-M01..M03)** — **AN6-E**
**CrossSubsystem (CX-M01..M05)** — **AN6-F**
**Foundation (FND-M01..M08)** — **AN2-F** (with M03 also touching AN2-B)
**Platform (PLT-M01..M07)** — **AN7-D** (with M02/M03 carried forward to DEFERRED via AN10-G)
**API (API-M01..M02)** — **AN7-E**
**Rust (RUST-M01..M08)** — **AN8-D** (with M06 covered by AN1-C)
**Tests (TST-M01..M13)** — **AN9-E** (with M10/M11 covered by AN9-C/D)
**Documentation (DOC-M01..M08)** — **AN10-C** (with M01/M06 covered by AN1-A; M02 by AN7-D; M04 by AN10 final refresh)

### 18.4 LOW audit IDs

LOW findings are batched per-subsystem. Lookup:

| Subsystem | Sub-task |
|-----------|----------|
| IPC | AN3-F |
| Scheduler | AN5-C |
| Capability/Lifecycle/Service | AN4-I |
| Architecture/IF/CrossSubsystem | AN6-G |
| SchedContext | (folded into AN5-D where applicable) |
| Foundation | AN2-F (LOW items combined with MEDIUM batch) |
| Platform | AN7-F |
| Rust | AN8-E |
| Tests/CI | AN9-F |
| Documentation | AN10-D |

### 18.5 Cross-cutting themes

| Theme | Phase(s) | Sub-task(s) |
|-------|----------|-------------|
| 4.1 Closure-form proofs | AN4, AN6, AN10 | AN4-C, AN6-A, AN10-A |
| 4.2 Tuple → structure | AN2, AN3, AN4 | AN2-G, AN3-B, AN4-F (CAP-M05) |
| 4.3 Subtype gates | AN2, AN4 | AN2-A, AN2-B, AN2-F (FND-M03), AN4-F (CAP-M04) |
| 4.4 SMP-latent assumptions | AN4, AN6, AN10 | AN4-D, AN6-F (CX-M03), AN10-B |
| 4.5 Workstream IDs in comments | AN10 | AN10-E |
| 4.6 Stale forward references | AN1, AN10 | AN1-C, AN10-E |
| 4.7 Monolithic file splits | AN3, AN4, AN5, AN6, AN10 | AN3-C/D, AN4-F (CAP-M03)/AN4-G (LIF-M05), AN5-A, AN6-E (IF-M03), AN10-F |

### 18.6 Carry-forward deferred IDs

| Source | Disposition | New ID (if any) |
|--------|-------------|-----------------|
| DEF-A-M04 | Carry unchanged | DEF-A-M04 (in AUDIT_v0.30.6_DEFERRED.md) |
| DEF-A-M06 | Carry unchanged | DEF-A-M06 |
| DEF-A-M08 | Carry unchanged | DEF-A-M08 |
| DEF-A-M09 | Carry unchanged | DEF-A-M09 |
| DEF-C-M04 | Carry unchanged | DEF-C-M04 |
| DEF-P-L9 | Carry unchanged | DEF-P-L9 |
| DEF-R-HAL-L14 | Carry unchanged | DEF-R-HAL-L14 |
| DEF-F-L9 | RESOLVED in AN2-G | (closed entry in new DEFERRED) |
| DEF-AK2-K.4 | By-design (carry) | DEF-AK2-K.4 |
| DEF-AK7-E.cascade | Partial / carry | DEF-AK7-E.cascade |
| DEF-AK7-F.cascade | Partial / carry | DEF-AK7-F.cascade |

### 18.7 Newly-deferred IDs (added by WS-AN)

| New ID | Source | Category |
|--------|--------|----------|
| DEF-PLT-M02 | PLT-M02 / AN7-D | Hardware-binding |
| DEF-H-07.partial | AN6-A toolchain-blocked | Toolchain-pending |
| DEF-H-09.transitive | AN6-C Track B | Effort-budget |
| DEF-R-HAL-L17 | AN1-C | Hardware / interrupt-wait |
| DEF-R-HAL-L18 | AN1-C | Hardware / barriers |
| DEF-R-HAL-L19 | AN1-C | SMP / barriers |
| DEF-R-HAL-L20 | AN1-C | SMP / multi-core |

---

## 19. Glossary and conventions

### 19.1 Severity ladder (per audit §0.3)

- **CRITICAL**: exploitable today against a non-malicious caller, or directly blocks v1.0 release
- **HIGH**: correctness / security gap that should not ship in v1.0
- **MEDIUM**: hardening / defense-in-depth gap, or organizational issue
- **LOW**: hygiene, clarity, or minor performance concern
- **INFO**: confirmed-clean check or strength

### 19.2 Cascade-size shorthand

- `~N`: N proof sites likely need a one-line edit
- `cascade-heavy`: N ≥ 50 sites; spread the change across ≥ 3 commits

### 19.3 Acceptance gate ladder

| Gate | Command | Latency |
|------|---------|--------:|
| module gate | `lake build <Module>` | seconds-minutes |
| smoke gate | `./scripts/test_smoke.sh` | < 5 min |
| full gate | `./scripts/test_full.sh` | 5-15 min |
| rust gate | `cargo test --workspace && cargo clippy --workspace -- -D warnings` | 2-5 min |
| all gate | smoke + full + rust + version-sync + website-links + cascade-monotonic + zero-sorry/axiom | 15-30 min |

### 19.4 Sub-task ID convention

- `AN{phase}-{letter}` — e.g., `AN3-B` is "Phase AN3, sub-task B"
- Sub-tasks are sequential within a phase; letter ordering reflects dependency
- "AN10-G" is "Phase AN10, sub-task G" — the new DEFERRED file
- Audit-ID cross-reference is recorded in the sub-task heading for forward and reverse traversal

### 19.5 PR title convention

- Format: `WS-AN <phase>: <one-line summary> (<comma-separated audit IDs>)`
- Example: `WS-AN AN1: critical-path blockers (C-01, C-03, H-24)`
- Per-PR-12 review-scope guidance per §17.3

---

## 20. Open questions for maintainer review

These are decisions that benefit from explicit maintainer
confirmation before WS-AN starts. None are blockers — sensible
defaults are noted.

1. **Final v1.0.0 tag timing** — per AK10-C precedent, v1.0.0 is a
   manual maintainer action. Does WS-AN target v1.0.0 directly, or
   does it land as v0.30.7 (or further patch increments) with v1.0.0
   tagged separately? Default: WS-AN targets v0.30.7 patch-bump per
   §15.7.

2. **AN6-A target theorem choice** — the plan recommends
   `schedContextConfigure_preserves_projection`. Alternatives:
   `tcbResume_preserves_projection` (simpler match structure) or
   `serviceQuery_preserves_projection` (already substantively proven
   per the post-AK6F audit; could be the template).

3. **AN6-C Track A vs B** — Track A (rename) is gate-passing; Track
   B (transitive disjointness) is correctness-strengthening but
   higher effort. Default: Track A; Track B as a stretch goal that
   can defer.

4. **PR-6 (AN8) parallel landing** — is there a separate Rust-focused
   contributor available? Default: assume same contributor; PR-6
   serializes after PR-1.

5. **DOC-M03 SPDX header pass** — single mechanical PR (~150 file
   header changes, easy review) or batched per-subsystem (more PRs,
   smaller diffs)? Default: single PR for review efficiency.

6. **AN10-E inline-marker hygiene scope** — full sweep or selective
   (only retarget closed-workstream pointers, leave per-feature
   markers)? Default: selective per audit guidance "after each
   portfolio closes, replace inline workstream markers" — ie selective.

7. **AUDIT_v0.30.6_DEFERRED.md format** — match the
   AUDIT_v0.29.0_DEFERRED.md structure exactly (Categories A/B,
   per-item rationale + acceptance criteria), or add additional
   structure? Default: match exactly for consistency.

---

## 21. Closure note

This plan is **single-source-of-truth** for WS-AN. Any AN-* sub-task
that is renamed, dropped, or split during execution must be
reflected by a same-PR edit to this file. The plan archives to
`docs/dev_history/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md` only after
AN10-N (the workstream closure) ships and `docs/WORKSTREAM_HISTORY.md`
records the WS-AN entry.

This document is GPL-3.0+ licensed (see `LICENSE`) per the project's
standard.

**End of plan.**









