# seLe4n WS-AN — v0.30.6 Pre-1.0 Audit Remediation Workstream Plan

**Plan ID**: `AUDIT_v0.30.6_WORKSTREAM_PLAN`
**Workstream**: **WS-AN** (next sequential after WS-AM, WS-AK; one-active-audit-at-a-time convention per `AUDIT_v0.30.6_COMPREHENSIVE.md` §2.10 LOW item)
**Source audit**: [`docs/audits/AUDIT_v0.30.6_COMPREHENSIVE.md`](AUDIT_v0.30.6_COMPREHENSIVE.md) — 196 findings (initial scoring 3 CRITICAL + 24 HIGH + 71 MEDIUM + 58 LOW + 40 INFO; post-verification 2 actionable CRITICAL + 1 pre-resolved (C-02) + 23 HIGH + 71 MEDIUM + 59 LOW (H-22 downgraded) + 40 INFO = 196 total)
**Carried forward**: [`docs/audits/AUDIT_v0.29.0_DEFERRED.md`](AUDIT_v0.29.0_DEFERRED.md) — 11 deferred items (7 hardware-binding, 4 proof-hygiene)
**Errata reference**: [`docs/audits/AUDIT_v0.29.0_ERRATA.md`](AUDIT_v0.29.0_ERRATA.md) — 6 informational entries (no actionable work)
**Baseline**: `v0.30.6` at commit `1a86dbc` on branch `claude/audit-workstream-planning-AUBX4`
**Target release**: `v1.0.0` (patch-only bump trajectory; final tag is a maintainer manual action per AK10-C precedent)
**Author**: Claude (Opus 4.7), 2026-04-21
**Scope summary**: 196 audit findings (after C-02 resolved, H-22 downgraded) PLUS 11 carried-forward items from `AUDIT_v0.29.0_DEFERRED.md` that are **absorbed in-scope** (no longer deferred), organized into **13 phases (AN0..AN12)** with **~105 named sub-tasks** decomposed into **~210 sub-sub-task commits**. Each complex sub-task lists explicit per-commit boundaries with acceptance criteria, effort estimates, and cascade sizes. Foundation hardening (AN2) lands first so type-level changes cascade exactly once; cross-cutting structural refactors (Theme 4.2 named projections, Theme 4.3 subtype gates) are sequenced into the earliest phase whose subsystem they touch. **AN9 closes every hardware-binding item from AUDIT_v0.29.0_DEFERRED.md (DEF-A-M04/M06/M08/M09, DEF-C-M04, DEF-P-L9, DEF-R-HAL-L14, plus new DEF-R-HAL-L17..L20 items surfaced by AN1-C); AN10 completes the AK7 cascade rollouts (DEF-AK7-E.cascade, DEF-AK7-F.cascade); AN12 closes the workstream with documentation sync and the v1.0.0-ready gate.** No finding in the comprehensive audit, no entry in the v0.29.0 DEFERRED file, and no errata residual remains unaddressed at WS-AN close.

---

## TL;DR (one-page executive view)

**Status of inputs**: All audit findings spot-checked against live tree at `1a86dbc`. **No erroneous findings**. Self-corrections inside the audit (C-02 resolved, H-13 file-path corrected, H-20 quantification corrected, H-22 severity downgraded) are accepted as-is. All six entries in `AUDIT_v0.29.0_ERRATA.md` are informational closures; E-5's residual (H-07 closure-form composition) is closed **fully** in AN6 (all six arms substantively discharged, not partially). All 11 entries in `AUDIT_v0.29.0_DEFERRED.md` are **absorbed as pre-1.0 work** per §16: DEF-F-L9 RESOLVED in AN2-G; DEF-A-M04/M06/M08/M09/C-M04/P-L9/R-HAL-L14 + four new DEF-R-HAL-L17..L20 items each closed substantively in AN9; DEF-AK7-E.cascade and DEF-AK7-F.cascade fully rolled out in AN10; DEF-AK2-K.4 `eventuallyExits` closed by RPi5 canonical-config witness in AN5-F. **Zero items carry past v1.0.0.**

**Scope of work**:
- 2 actionable CRITICAL (C-01 README, C-03 hook)
- 23 actionable HIGH (all closed substantively; no closure-form or partial-discharge fallbacks)
- 71 MEDIUM, 59 LOW (after H-22 downgrade), 40 INFO (no work)
- 11 absorbed items from `AUDIT_v0.29.0_DEFERRED.md` (7 hardware-binding in AN9, 2 cascades in AN10, 1 `eventuallyExits` in AN5-F, 1 `allTablesInvExtK` structure refactor in AN2-G)
- 4 new hardware-binding sub-tasks surfaced by AN1-C (bounded WFE, parameterized barriers, OSH widening, secondary-core bring-up / SMP) — all closed in AN9

**Phases & PR sequence**:
1. **AN0** — Plan + baseline (PR-1)
2. **AN1** — Critical-path: README, pre-commit hook, stale TODOs retargeted to live sub-task IDs (PR-2)
3. **AN2** — Foundation hardening: subtype gates, typedIdDisjointness, named structures, DEF-F-L9 tuple→structure (PR-3..5)
4. **AN3..AN5, AN7** — Subsystem phases (parallelizable post-AN2): IPC, Cap/Lif/Svc, Sched/SC + eventuallyExits, Plat/API + VSpaceBoot shim (PR-7..10)
5. **AN6** — Architecture / IF / CrossSubsystem composition: all 6 closure-form projection arms substantively discharged (no partial); H-08 index; H-09 transitive untypedAncestorRegionsDisjoint (Track B mandatory) (PR-11)
6. **AN8** — Rust HAL hardening, including EOI-before-handler semantic change (H-19 Option b): runs in parallel with Lean phases (PR-6)
7. **AN9** — **Hardware-binding closure (NEW)**: TLB+cache composition, tlbBarrierComplete, MMU/Device BarrierKind, suspendThread atomicity, VSpaceRoot boot bridge for non-empty configs, SVC FFI wiring, bounded WFE, parameterized barriers, OSH widening, secondary-core bring-up / SMP (PR-12)
8. **AN10** — **AK7 cascade completion (NEW)**: DEF-AK7-E.cascade (~240 handler signatures ObjId→ValidObjId), DEF-AK7-F.cascade reader side (~304+ raw-match→typed-helper sites), DEF-AK7-F.cascade writer side (~50 storeObject→storeObjectKindChecked sites) (PR-13)
9. **AN11** — Test/CI surface incl. KernelError matrix, lake-exe timeout, named AK6 tests (PR-14)
10. **AN12** — Closure: discharge index, SMP inventory confirmation (post-AN9 SMP work), doc batch, version bump, archive; all audit IDs closed; NO new DEFERRED file needed (PR-15/16)

**Estimated effort**: ~80–95 dev-days (major increase vs. prior plan because AN9/AN10 absorb all hardware-binding and cascade work previously deferred post-1.0). Can compress to ~5–7 calendar weeks with three contributors (one Lean, one Rust HAL/SMP, one cascade-migration). The ~210 sub-sub-task commits average ~30 minutes each (wall-clock commit + review + CI), which gates the minimum calendar timeline at ~7–9 working days of sequential commits assuming full review throughput.

**Granularity guarantee**: every sub-task with cascade size ≥ 10, LOC delta ≥ 200, or cross-file-refactor scope is broken into `.1/.2/.3/…` sub-sub-tasks so each commit is reviewable in isolation. See §3..§15 for per-phase detail and §17.3 for per-PR review-scope guidance.

**Final gate** (per §15.2): all tier scripts green, zero `sorry`/`axiom`/`native_decide`, fixture byte-identical, all 10 i18n READMEs synced, version bump to v0.30.7 (or maintainer-chosen v1.0.0), **zero entries in any new DEFERRED file** (no new deferred items created by WS-AN), all 11 old DEFERRED items closed with commit SHAs.

---

## 0. Reading guide

This document is intended to be readable end-to-end OR jumped into per-phase.
Recommended reading order for a contributor picking up a sub-task:

1. **§1 Pre-flight verification** — confirms no audit finding is erroneous; lists what was spot-checked.
2. **§2 Workstream organization & dependency graph** — phase-level layout and cross-phase blockers.
3. **§3..§13 per-phase plans** — for the phase you are working on; each sub-task lists file:line anchors, acceptance criteria, and the regression-test recipe.
4. **§14 Cross-cutting theme handling** — explains why Theme 4.2 (named projections), 4.3 (subtype gates), 4.4 (SMP inventory), 4.7 (file splits) are folded into the per-subsystem phases rather than siloed.
5. **§15 Closure criteria & gate** — the v1.0.0 release-readiness checklist.
6. **§16 Absorption map** — each item from `AUDIT_v0.29.0_DEFERRED.md` mapped to the live WS-AN sub-task that closes it; zero items carry past v1.0.0.

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

### 1.3 Items previously deferred — now in-scope (all addressed substantively)

Per maintainer directive, **every item previously documented as "by design", "out of scope", or deferred to a post-1.0 workstream is now scheduled in WS-AN**. The audit-authored acceptance of by-design choices and hardware-binding deferrals is NOT grounds for carrying past v1.0.0. Each item below gets a live sub-task:

- **H-19** panic = "abort" + Drop-not-run-on-panic: AN8-C takes the audit's **Option b** (migrate ack→handle→EOI sequence to emit EOI before handler invocation per GIC-400 spec) in addition to the documentation and clippy-lint guard. The fatal-invariant-abort design continues to halt the kernel on handler panic, but EOI is no longer lost because it was emitted prior to the handler body.
- **DEF-AK2-K.4** `eventuallyExits`: AN5-F proves the hypothesis **substantively** for the canonical RPi5 deployment configuration (54 MHz timer, default CBS period, default priority bands) as a named witness theorem `rpi5_canonicalConfig_eventuallyExits`. The `eventuallyExits` hypothesis remains parameterised in the general WCRT theorem (a deployment-schema property), but RPi5 deployments now ship with the witness discharged at boot-time.
- **PLT-M02 / PLT-M03** VSpaceRoot boot-bridge gap: AN7-D.2 now lands the full `Platform/RPi5/VSpaceBoot.lean` shim establishing the boot VSpaceRoot with full invariant witness, and `bootFromPlatformChecked` is refined to include VSpaceRoot in its per-object `bootSafeObject` check. No boot path remains proven for empty-config only.
- **ARCH-M01** `VSpaceBackend` typeclass currently unused: AN6-D **wires the typeclass into `VSpace.lean`** so `VSpace` operates on `VSpaceBackend` indirection instead of concrete `VSpaceRoot`. The typeclass ceases to be forward-looking infrastructure and becomes load-bearing production code. The ARMv8 instance from AG6-C/D remains the default production backend.

### 1.4 Errata acknowledgement (`AUDIT_v0.29.0_ERRATA.md`)

Each of the six errata entries is **closed informational** under v0.30.6:

| Errata ID | Status under WS-AN | Action |
|-----------|--------------------|--------|
| **E-1** S-H03 verification clarification | Closed; no work | None — recorded in `AUDIT_v0.29.0_ERRATA.md` |
| **E-2** R-HAL-M12 dead-code removal | Closed in AK10 (b . supersedes annotated fall-through) | None |
| **E-3** A-H01 three-layer extent | Closed in AK3-B + AK5-C (`wxInvariant_fourLayer_defense`) | None |
| **E-4** R-HAL-H02 partial | Closed in AK5-D (`tlbi vmalle1` + `dc cvac` sequence) | None |
| **E-5** NI-H02 composition | Closed in AK6-F composition theorem; AK6F.20b residual (6 closure-form arms) fully discharged in AN6-A | AN6-A substantively discharges **all 6 arms** (no partial); E-5 residual eliminated |
| **E-6** finding-count arithmetic 202 vs 201 | Informational only | None |

E-5 has the only forward link. AN6-A substantively discharges every one of the six closure-form theorems (`schedContextConfigure/Bind/Unbind_preserves_projection`, `lifecycleRetype_preserves_projection`, `tcbSuspend/Resume_preserves_projection`) via a six-commit template that eliminates the `hArmProj` closure uniformly. No residual or partial-discharge fallback remains; if the Lean 4.28.0 toolchain blocks any one arm, AN6-A escalates to a targeted toolchain workaround (manual `rcases` on `Except.ok`, `decide` + `Classical.byContradiction` for the equality, or a hand-unfolded structural proof) rather than deferring. See §20.2 for the escalation ladder.

---

## 2. Workstream organization & dependency graph

### 2.1 Phase summary

| Phase | Theme | Scope | Sub-tasks | Estimated effort | Blocks |
|-------|-------|-------|-----------|------------------:|--------|
| **AN0** | Pre-flight | Branch policy, baseline metrics, sub-task inventory commit | 3 (A–C) | 0.5 day | AN1..AN12 |
| **AN1** | Critical-path blockers | C-01, C-03, H-24 + RUST-M06; retarget stale TODOs to live sub-task IDs (not DEF-* IDs) | 4 (A–D) | 0.5 day | (none) — independent |
| **AN2** | Foundation hardening | H-10..H-13, FND-M01..M08, Theme 4.3 (subtype gates), DEF-F-L9 absorbed (Theme 4.2 anchor) | 8 (A–H) | 4–5 days | AN3..AN7 (downstream cascades) |
| **AN3** | IPC subsystem | H-01, IPC-M01..M09, IPC LOWs, Theme 4.2 (named projections for `ipcInvariantFull`), Theme 4.7 (Structural.lean split) | 7 (A–G) | 4–5 days | AN6 (CrossSubsystem composition) |
| **AN4** | Capability / Lifecycle / Service | H-02..H-06, CAP-M01..M05, LIF-M01..M06, SVC-M01..M04, Cap LOWs, Theme 4.7 (Lifecycle/Operations.lean split) | 10 (A–J) | 5–6 days | AN6 |
| **AN5** | Scheduler / SchedContext + `eventuallyExits` closure | SCH-M01..M05, SC-M01..M03, Sched LOWs, Theme 4.7 (Preservation.lean split), **DEF-AK2-K.4 RPi5-canonical-config witness** | 6 (A–F) | 4–5 days | AN6 |
| **AN6** | Architecture / IF / CrossSubsystem | H-07 (**all 6 arms substantively discharged**), H-08, H-09 (**Track B mandatory**: transitive untypedAncestorRegionsDisjoint), ARCH-M01..M03 (**VSpaceBackend wired production-live**), IF-M01..M03, CX-M01..M05, IF Operations.lean split | 8 (A–H) | 7–9 days | AN12 |
| **AN7** | Platform / API | H-14..H-16, PLT-M01..M07 (**including full `RPi5/VSpaceBoot.lean` shim closing PLT-M02/M03**), API-M01..M02, Platform LOWs | 7 (A–G) | 4–5 days | AN11 |
| **AN8** | Rust HAL | H-17..H-19 (**H-19 audit Option b: EOI before handler**), RUST-M01..M08, Rust LOWs | 6 (A–F) | 4–5 days | AN9 (Rust ABI changes cascade into AN9 HAL/FFI work) |
| **AN9** | **Hardware-binding closure (NEW)** | DEF-A-M04 (TLB+cache composition), DEF-A-M06 (tlbBarrierComplete), DEF-A-M08/M09 (MMU/Device BarrierKind), DEF-C-M04 (suspendThread atomicity via HAL bracket), DEF-P-L9 (VSpaceRoot boot exclusion — covered jointly with AN7-D.2), DEF-R-HAL-L14 (SVC FFI wiring to `sele4n_syscall_dispatch`), DEF-R-HAL-L17 (bounded WFE), DEF-R-HAL-L18 (parameterized barriers), DEF-R-HAL-L19 (OSH widening), DEF-R-HAL-L20 (secondary-core bring-up / SMP) | 10 (A–J) | 18–22 days (includes SMP) | AN11, AN12 |
| **AN10** | **AK7 cascade completion (NEW)** | DEF-AK7-E.cascade (~240 sites: handler signatures ObjId/ThreadId/SchedContextId → Valid* subtypes), DEF-AK7-F.cascade reader side (~304+ raw-match→typed-helper migration), DEF-AK7-F.cascade writer side (~50 storeObject→storeObjectKindChecked) | 4 (A–D) | 8–10 days | AN11 |
| **AN11** | Tests / CI / Scripts | H-20 (KernelError matrix), H-21 (`lake exe` timeout), H-22 (downgraded, addressed), H-23 (named AK6 tests), TST-M01..M13, Test LOWs | 7 (A–G) | 4–5 days | AN12 |
| **AN12** | Documentation, themes, closure | DOC-M01..M08, Theme 4.1 (discharge index), Theme 4.4 (SMP inventory confirms AN9 work landed), DOC LOWs, version bump, **NO new DEFERRED file** (all items closed), WORKSTREAM_HISTORY entry, gate | 14 (A–N) | 3 days | (closes WS-AN) |
| **TOTAL** | | | **~105 sub-tasks** | **~80–95 dev-days** | |

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
 │ Critical │            │  (subtype gates,   │          │  (parallel; feeds  │
 │ blockers │            │   named structs)   │          │   AN9 HAL/FFI)     │
 └────┬─────┘            └─────────┬──────────┘          └─────────┬──────────┘
      │                            │                               │
      │                ┌───────────┼────────────┬─────────────┐    │
      │                ▼           ▼            ▼             ▼    │
      │           ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌─────────┐  │
      │           │  AN3    │ │  AN4    │ │  AN5    │ │  AN7    │  │
      │           │ IPC     │ │ Cap/Lif │ │ Sched/  │ │ Plat/   │  │
      │           │         │ │ /Svc    │ │ SC + EE │ │ API +   │  │
      │           │         │ │         │ │         │ │ VSpBoot │  │
      │           └────┬────┘ └────┬────┘ └────┬────┘ └────┬────┘  │
      │                └───────────┼───────────┘            │       │
      │                            ▼                        │       │
      │                  ┌────────────────────┐             │       │
      │                  │  AN6 — Arch / IF / │             │       │
      │                  │     CrossSubsystem │             │       │
      │                  │  (all 6 arms, TrkB)│             │       │
      │                  └─────────┬──────────┘             │       │
      │                            │                        │       │
      │                            │    ┌───────────────────┴───────┘
      │                            ▼    ▼
      │                   ┌────────────────────┐
      │                   │ AN9 — HW-binding   │
      │                   │ (TLB/cache/barrier/│
      │                   │  SVC-FFI/SMP)      │
      │                   └─────────┬──────────┘
      │                             │
      │                             ▼
      │                   ┌────────────────────┐
      │                   │ AN10 — AK7 cascade │
      │                   │ (ValidObjId, etc.) │
      │                   └─────────┬──────────┘
      │                             │
      │                             ▼
      │                   ┌────────────────────┐
      └──────────────────►│ AN11 — Tests / CI  │
                          └─────────┬──────────┘
                                    │
                                    ▼
                          ┌────────────────────┐
                          │ AN12 — Doc/Theme/  │
                          │      Closure       │
                          └────────────────────┘
```

**Critical dependency edges** explained:

- **AN2 → AN3..AN7**: foundation type changes (e.g., `Badge` private mk discipline H-13, `RegisterFile.gpr : Fin 32` H-11, named-projection refactor scaffolding, `allTablesInvExtK` DEF-F-L9 tuple→structure) cascade through every kernel subsystem's preservation chain. Doing AN2 first means each cascade lands once.
- **AN3..AN5 + AN7 → AN6**: CrossSubsystem composition theorems (H-07 all-six-arms discharge, H-09 transitive Track B `untypedAncestorRegionsDisjoint`) consume the per-subsystem invariants. CX bridges depend on the named-projection layout established in AN3 (IPC-M01) and the VSpaceBoot shim established in AN7-D.2.
- **AN6 + AN8 → AN9**: hardware-binding composition requires both the CrossSubsystem composition layer (AN6) and the Rust HAL hardening (AN8) to be in place. AN9's TLB+cache composition theorem composes AN8's barriers-and-cache HAL primitives with AN6's architecture invariant bundle. AN9's SMP bring-up (DEF-R-HAL-L20) cannot begin until AN8's H-19 EOI-before-handler refactor lands (per-core IRQ paths).
- **AN9 → AN10**: AK7 cascade (ValidObjId/ValidThreadId rollout + typed-helper migration) depends on AN9's SMP-safe predicates so the migrated signatures carry the right concurrency witnesses.
- **AN10 → AN11**: Tests (H-20 KernelError matrix, AK6 named tests) cover the post-cascade kernel surface; doing tests after cascade means the KernelError matrix rows anchor on the Valid*-typed handlers.
- **AN11 → AN12**: documentation sync, version bump, archive; WS-AN closes with **no new DEFERRED file** because every DEF-* item has a closed sub-task with commit SHA.
- **AN8 ⫫ AN3..AN7**: Rust HAL work (AN8) is independent of Lean kernel work. Can run in parallel with AN2..AN7 (different contributor or background-safe, no shared files). AN8 merges before AN9 starts.

### 2.3 Sequencing rationale

- **AN1 first, but optional-blocking**: C-01 (README pointer) is a 10-minute fix and takes immediate visible pressure off the project's public face. It can land as a standalone PR and is not a dependency for AN2..AN12. Treat AN1 as "land before any other public-facing PR merges."
- **AN2 second**: Foundation refactors are the highest-leverage cascading work. Doing them once now beats spreading the cascade across AN3..AN7 piecemeal. AN2-G absorbs DEF-F-L9 (`allTablesInvExtK` 17-tuple → structure), which unblocks AN3-B / AN4-F.5 (`ipcInvariantFull` / `capabilityInvariantBundle` refactors following the same playbook).
- **AN3..AN7 in parallel where possible**: After AN2 completes, the four subsystem phases (AN3 IPC, AN4 Cap/Lif/Svc, AN5 Sched/SC, AN7 Platform/API) touch disjoint files and can land in parallel PRs. AN6 (CrossSubsystem) sequences AFTER all four because it composes them; AN6 also depends on AN7-D.2's full VSpaceBoot shim for the non-empty-config boot bridge.
- **AN8 background**: Rust HAL changes touch only `rust/` and don't affect `SeLe4n/` build. Run in parallel with AN2..AN7. AN8 must merge before AN9 starts because AN9's hardware-binding theorems compose AN8's barrier/EOI primitives.
- **AN9 after AN6+AN8**: Hardware-binding composition consumes both the Lean-side invariant layer (AN6) and the Rust HAL layer (AN8). AN9 is the longest and most complex phase because it includes SMP bring-up (DEF-R-HAL-L20).
- **AN10 after AN9**: AK7 cascade is mechanical but voluminous (~600+ call sites). Doing it after AN9 means the Valid*-typed handlers carry SMP-correct preconditions from AN9's interrupt-disable wrappers (DEF-C-M04 composition with suspendThread).
- **AN11 after AN10**: Tests depend on the final kernel surface (post-cascade, post-hardware-binding).
- **AN12 last**: documentation sync, version bump, close with zero new DEFERRED entries.

### 2.4 Risk register

| Risk | Likelihood | Impact | Mitigation |
|------|-----------:|-------:|------------|
| AN2 named-projection refactor cascade (Theme 4.2) breaks 60+ destructure sites | Medium | High | Land projection theorems as `@[simp] abbrev` first (no behavioral change), migrate consumers in subsequent commits, retain tuple form as deprecated until last migration commit |
| AN3 IPC `Structural.lean` split (Theme 4.7) drops a theorem during move | Medium | High | Use `git mv`-equivalent (commit move + commit split separately so review can verify nothing dropped); add `lake build SeLe4n.Kernel.IPC.Invariant.Structural` as pre-PR check |
| AN6 H-09 Track B transitive disjointness requires `UntypedObject.parent` or `.ancestors` tracking and cascades through all retype paths | High | High | Mandatory (no Track A fallback). Introduce `UntypedObject.parent : Option ObjId` field first (AN2-F.9 new sub-task), prove preservation via `retypeFromUntyped_parent_invariant` lemma, then predicate definition composes on parent-chain walk with fuel bound `maxRetypeDepth := 256`. Cascade batches across AN6-C.1..C.8 (eight commits). |
| AN8 H-17 UartLock RAII refactor changes `kprint!` macro signature | Low | Medium | Keep `with(...)` as thin wrapper around new `with_guard()`; `kprint!` macro unchanged; only internal restructure |
| AN9 DEF-R-HAL-L20 SMP secondary-core bring-up touches boot assembly, PSCI, per-core trap frame, per-core scheduler state | Medium | Very High | Multi-commit staging: (i) PSCI `CPU_ON` calls gated behind `smp_enabled` boot flag; (ii) per-core init paths land before touching scheduler data structures; (iii) single-core default is preserved (`smp_enabled := false` at v1.0.0 boot); (iv) SMP enablement is a separate QEMU-tested boot configuration, with explicit kernel-command-line flag. Fallback: v1.0.0 ships with `smp_enabled := false` but SMP code paths are reviewed, merged, and QEMU-tested — the runtime flag controls activation. |
| AN9 hardware-binding composition (TLB+cache+barriers) requires FFI sequence witness from Rust into Lean | Medium | High | Add `@[extern "sele4n_hal_barrier_kind_witness"]` FFI declaration that returns a Lean `BarrierKind` value. Rust-side implementation emits the barrier and returns the kind-tag. Lean-side theorem consumes the kind-tag as proof the sequence executed. `cargo test` covers the Rust emission; Lean model carries the witness through preservation proofs. |
| AN10 AK7 cascade blows up build time or introduces silent proof breakage | High | Medium | Batch by subsystem (AN10-A: handlers; AN10-B: readers; AN10-C: writers). Each batch ≤ 60 call sites with `lake build` after every ~10 sites. Monotonicity metrics (`SENTINEL_CHECK_DISPATCH`, `RAW_MATCH_TCB`, `STOREOBJECTCHECKED_ADOPTION`) give machine-visible progress; every commit advances a metric. |
| AN11 H-20 KernelError matrix test surface explosion | Medium | Medium | Target ≥35 of 51 variants per audit recommendation; partition by syscall in new `KernelErrorMatrixSuite.lean` |
| Lean 4.28.0 elaborator regression on named-structure `extends` patterns | Low | High | Use plain `structure` (no `extends`) for invariant bundles; verify build under target toolchain in AN0 baseline capture |
| Hidden audit finding interaction (e.g., H-13 Badge private mk breaks DS-L9 high-heartbeat proof) | Medium | Medium | Run `test_full.sh` after every AN2 sub-task lands, not only at end of phase; FND-M05 high-heartbeat profile is the canary |
| Closure-form proof template (AN6-A / H-07) blocked by Lean 4.28.0 `split` tactic for one or more arms | Medium | High | Escalation ladder (no defer): (1) `split_ifs`; (2) manual `rcases hConfig : … <;> ...` with `Except.ok_eq_iff_get?` rewrites; (3) `Classical.byContradiction` + `decide` on the boolean skeleton; (4) hand-unfolded structural proof using explicit `Except.bind_eq_ok` rewrites. At least one approach is guaranteed to close any given arm because Lean 4.28.0's elaborator is complete for first-order reasoning; the challenge is ergonomic, not logical. Budget: up to 1.5 days per arm on the toolchain workaround; if any arm exceeds 1.5 days, invoke AN6-A.ESCALATE (explicit manual proof). |

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
- **Plan**: capture metrics at WS-AN start so AN12 can diff:
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
- **Plan**: confirm with maintainer that AN1..AN12 all land on the same branch `claude/audit-workstream-planning-AUBX4` until WS-AN closes. Per task description's `Git Development Branch Requirements` section.
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
  2. Phrase (shown below with a space between `]` and `(` so the repo's markdown-link checker does not resolve the quoted target from this plan's location; the actual README edit omits the space): `| **Latest audit** | [\`AUDIT_v0.30.6_COMPREHENSIVE\`] (docs/audits/AUDIT_v0.30.6_COMPREHENSIVE.md) — pre-1.0 hardening audit (3 CRIT, 24 HIGH, 71 MED, 58 LOW, 40 INFO) |`
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
- **Total effort**: ~0.5 day (1 full PR-2 bundled with AN1-A/C/D).

**Sub-sub-task breakdown** (4 commits, bundled into single PR):

- **AN1-B.1 — Write `install_git_hooks.sh` with idempotent install + check mode** (0.2 day)
  - Script contract:
    - Default mode: install hook if absent; no-op if already present and identical; fail if present and different (with explanation).
    - `--check` mode: exit 0 if installed correctly; non-zero with actionable message otherwise (for CI).
    - `--force` mode: overwrite existing hook with backup to `.git/hooks/pre-commit.backup-<timestamp>`.
  - Implementation details:
    - Shebang `#!/usr/bin/env bash`; `set -euo pipefail`; GPL-3.0+ header (matches C-02-resolution scripts' style).
    - Prefer symlink (`ln -s`) over copy so future updates to `pre-commit-lean-build.sh` propagate automatically.
    - Handle non-git-repo scenario (e.g., tarball extract): skip with warning, exit 0.
    - Shellcheck-clean.
  - **Acceptance**: `scripts/install_git_hooks.sh --check` returns 0 when installed; fresh-clone simulation (remove `.git/hooks/pre-commit` then run installer) produces a working hook.

- **AN1-B.2 — Wire into `setup_lean_env.sh`** (0.1 day)
  - Append installer invocation after elan + lake bootstrap, before `--skip-test-deps` exit path.
  - Skip with informational log if `.git/` missing.
  - **Acceptance**: fresh `setup_lean_env.sh` run installs the hook automatically.

- **AN1-B.3 — Wire into CI and session-start hook** (0.1 day)
  - Extend `.github/workflows/lean_action_ci.yml` to run `./scripts/install_git_hooks.sh --check` after checkout. On CI the repo is fresh so the hook does not exist until the installer runs; the `--check` mode serves as a "did the installer run?" guard.
  - If the project has a `SessionStart` hook configured (e.g., `.claude/settings.json`), verify it invokes `setup_lean_env.sh` which in turn invokes the installer.
  - **Acceptance**: CI green; synthetic test where hook is deliberately absent produces explicit installer-ran log line.

- **AN1-B.4 — Update `CLAUDE.md` instructions** (0.1 day)
  - Replace lines 53-61's manual `cp` guidance with:
    ```markdown
    Install it automatically by running `./scripts/install_git_hooks.sh`
    (invoked by `setup_lean_env.sh` and by the SessionStart hook on
    fresh clones). For manual invocation in CI contexts use the
    `--check` mode.
    ```
  - Cross-reference `scripts/install_git_hooks.sh` from the website-link manifest.
  - **Acceptance**: CLAUDE.md reflects the new convention; `check_website_links.sh` PASS.

- **Regression test**: smoke gate; synthetic fresh-clone + setup verification; `install_git_hooks.sh --check` exit-code validation.
- **Cascade**: 0 kernel-side changes; 5 infrastructure files touched.

### AN1-C — Stale `WS-V/AG10` TODO retargeting (H-24, RUST-M06)

- **Audit IDs**: H-24 (HIGH), RUST-M06 (MEDIUM, same root cause)
- **Files**:
  - `rust/sele4n-hal/src/trap.rs:186` — `TODO(WS-V/AG10): Wire Lean FFI dispatch via @[extern] bridge`
  - `rust/sele4n-hal/src/lib.rs:62, 69, 84, 87, 91` — five additional `WS-V` references
- **Plan**:
  1. Repoint each TODO to a **live WS-AN sub-task ID** (not a DEF-* tracking entry — WS-AN absorbs all hardware-binding work in-scope per §1.3). Mapping:
     - `trap.rs:186` SVC FFI → `TODO(AN9-F): Wire Lean FFI dispatch via sele4n_syscall_dispatch (closes DEF-R-HAL-L14)`
     - `lib.rs:62` bounded WFE → `TODO(AN9-G): Add interrupt-wait timeout guard (closes DEF-R-HAL-L17)`
     - `lib.rs:69` parameterized barriers → `TODO(AN9-H): Accept BarrierKind parameter (closes DEF-R-HAL-L18)`
     - `lib.rs:84` widen barriers to OSH → `TODO(AN9-I): Widen DSB ISH to DSB OSH for multi-core (closes DEF-R-HAL-L19)`
     - `lib.rs:87` SVC FFI deferred → `TODO(AN9-F): same as trap.rs:186`
     - `lib.rs:91` Secondary core bring-up → `TODO(AN9-J): PSCI CPU_ON + per-core init (closes DEF-R-HAL-L20)`
  2. The phase AN9 is defined in §12; each of these AN9-F/G/H/I/J sub-tasks substantively closes the corresponding DEF-R-HAL-L14/L17/L18/L19/L20 item before v1.0.0 ships. **No new DEFERRED file is created.** AN1-C lands the source-side retarget first; AN9 lands the substantive work.
  3. Repo-wide grep for `WS-V|AG10` outside `docs/dev_history/`, `docs/WORKSTREAM_HISTORY.md` (active log), and the audit/errata/deferred docs themselves; retarget any remaining stragglers to the corresponding AN sub-task ID (usually AN9 for hardware-binding; AN5 for scheduler/liveness; AN10 for cascade hygiene).
- **Acceptance**:
  - `grep -rn "WS-V\|AG10" rust/ SeLe4n/` returns only completed-work historical comments (e.g., "WS-V completed at v0.21.7"), NOT deferred-work TODOs
  - Each retargeted TODO references a live `AN*` sub-task ID that is defined in this plan (§3..§15); no `DEF-*` form is used in the new TODOs (DEF-* appears only in the commit message referring to the original tracking doc for audit-trail traceability, but the source-code TODO points at live work)
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
- **Total effort**: ~0.5 day. **Cascade**: ~5 call sites; LOW-cost. Establishes the pattern AN2-B applies to VAddr/PAddr/CPtr/Slot.

**Sub-sub-task breakdown** (4 commits):

- **AN2-A.1 — Inventory `Badge.mk` external consumers** (0.1 day)
  - `grep -rn "Badge\.mk\b\|Badge\.mk\s" SeLe4n/ tests/ rust/` to list every call site.
  - Classify: (a) legitimate proof-side destructures that can migrate to a new `Badge.mkUnsafeForProof` (a private helper co-located with `Badge` inside the namespace); (b) ABI-decode sites that migrate to `Badge.ofNatMasked`; (c) test fixtures that migrate to `Badge.ofNatMasked` or `Badge.ofNat`.
  - **Acceptance**: inventory captured in commit message; call-site count and classification present.

- **AN2-A.2 — Introduce `private mk ::` + smart constructors** (0.15 day)
  - Restructure:
    ```lean
    structure Badge where private mk ::
      val : Nat
    deriving DecidableEq, Repr, Inhabited
    ```
  - If proof-side destructuring requires a non-private construction form, add a `private` helper:
    ```lean
    private def Badge.mkUnsafeForProof (n : Nat) : Badge := ⟨n⟩  -- proof-internal only
    ```
  - Ensure `Badge.ofNatMasked`, `Badge.ofNat`, `Badge.zero` are public and return `Badge.valid`-witnessed values.
  - **Acceptance**: `lake build SeLe4n.Prelude` PASS; external `Badge.mk` now rejected by the elaborator.

- **AN2-A.3 — Migrate external `Badge.mk` call sites** (0.15 day)
  - Walk the inventory from AN2-A.1. For each non-proof site, replace `Badge.mk n` with `Badge.ofNatMasked n 0` (or `Badge.ofNat n` + bound proof). For each proof site that needs destructuring, migrate to the new `mkUnsafeForProof` private helper.
  - **Acceptance**: `grep -rn "Badge\.mk\b" SeLe4n/ tests/ rust/` returns only the structure declaration site and the private helper (if introduced).

- **AN2-A.4 — Regression test + metric** (0.1 day)
  - Add regression test in `BadgeOverflowSuite`:
    - Elaboration-rejection test: `example : Badge := Badge.mk 42` should NOT compile outside the Prelude namespace — verify via a comment-level directive that would fail compile (or use a test scenario that constructs `Badge.ofNatMasked` and asserts `valid`).
    - Runtime test: `Badge.ofNatMasked (2^64) 0 |>.valid` asserts validity.
  - Extend `scripts/ak7_cascade_baseline.sh` with `BADGE_PUBLIC_MK_SITES` monotonicity metric (floor = 0; should never grow).
  - **Acceptance**: test extensions landed; metric added to baseline; full gate PASS.

- **Regression test**: full gate + `lake exe badge_overflow_suite`.
- **Cascade**: ~5 sites.

### AN2-B — Subtype-gate cascade for `VAddr`/`PAddr`/`CPtr`/`Slot` (Theme 4.3, H-13 follow-on)

- **Audit IDs**: Theme 4.3 (cross-cutting), supports H-13
- **Files**:
  - `SeLe4n/Prelude.lean:463-500` (`CPtr`, `Slot`, `VAddr`, `PAddr` structures)
  - All call sites — grep `\.mk\b` per type
- **Total effort**: ~1 day. **Cascade**: ~30 sites total across the 4 types; 1-type-per-commit batching so review scopes stay tight.

**Sub-sub-task breakdown** (4 commits — one per type, following AN2-A playbook):

- **AN2-B.1 — `CPtr` private mk + smart constructors** (0.25 day)
  - Apply AN2-A pattern to `CPtr`:
    ```lean
    structure CPtr where private mk ::
      val : Nat
    deriving DecidableEq, Repr, Inhabited
    ```
  - Add `CPtr.ofNat : Nat → Option CPtr` (rejects `val ≥ 2^64`); keep `isWord64Dec` as the runtime predicate.
  - Migrate ~8 call sites (estimated).
  - Delegate `CPtr.isWord64Bounded` to `isWord64Dec ·.val` (FND-M01 lands here).
  - **Acceptance**: `grep -rn "CPtr\.mk\b" SeLe4n/ tests/` returns only the structure + proof-side helper; full gate PASS; FND-M01 closed for CPtr.

- **AN2-B.2 — `Slot` private mk + smart constructors** (0.25 day)
  - Same pattern for `Slot`. Migrate ~6 call sites.
  - Delegate `Slot.isWord64Bounded` (FND-M01 closure for Slot).
  - **Acceptance**: as above; FND-M01 closed for Slot.

- **AN2-B.3 — `VAddr` private mk + canonicalBound parameterization** (0.25 day)
  - Same pattern for `VAddr`. Additional work: parameterize `canonicalBound` on `virtualAddressWidth` (FND-M02):
    ```lean
    def VAddr.canonicalBound (vw : Nat := virtualAddressWidthDefault) : Nat := 2 ^ vw
    ```
    with `virtualAddressWidthDefault : Nat := 48` constant. All existing canonicalBound usages accept the new default and preserve current behavior; any code needing LPA2 semantics passes `vw := 52` explicitly.
  - Migrate ~8 call sites; verify `MachineState.virtualAddressWidth` callers discovery.
  - **Acceptance**: FND-M02 closed; VAddr private-mk complete; decode sites spot-checked for default consistency.

- **AN2-B.4 — `PAddr` private mk + physicalAddressWidth gate** (0.25 day)
  - Same pattern for `PAddr`. Smart constructor `PAddr.ofNat` requires `physicalAddressWidth` parameter (no default — forces each caller to supply the target platform's width).
  - Cascade through AK3-E's `decodeVSpaceMapArgsChecked` and AJ4-C's `validateIpcBufferAddress` (both already check 2^pw bounds; verify they compose with the new smart constructor).
  - Migrate ~8 call sites.
  - **Acceptance**: PAddr private-mk complete; all callers explicit about PA width; full gate PASS.

- **Regression test (cumulative)**: full gate per commit; `lake exe abi_roundtrip_suite` after AN2-B.4.
- **Cascade**: ~30 sites (CPtr 8 + Slot 6 + VAddr 8 + PAddr 8).

### AN2-C — `RegisterFile.gpr : Fin 32` refactor + `LawfulBEq (RHTable α β)` instance (H-11)

- **Audit ID**: H-11 (HIGH)
- **Files**:
  - `SeLe4n/Machine.lean:254-304` (`RegisterFile`)
  - `SeLe4n/Kernel/RobinHood/Bridge.lean:136-153` (`RHTable.BEq`)
  - All call sites of `RegisterFile.gpr i` (most are bounded by inspection; need migration to `Fin 32`)
- **Total effort**: ~1 day. **Cascade**: ~20 RegisterFile sites + ~5 RHTable sites.

**Sub-sub-task breakdown** (5 commits):

- **AN2-C.1 — Add `RegisterFile.gprNat` legacy shim** (0.1 day)
  - Before changing the primary `gpr` signature, introduce a `RegisterFile.gprNat : Nat → Option RegValue` helper that returns `none` for indices ≥ 32. All existing `RegisterFile.gpr (n : Nat)` callers can migrate to `RegisterFile.gprNat n |>.get!` with an accompanying proof-obligation that `n < 32`.
  - **Acceptance**: shim added; builds unchanged.

- **AN2-C.2 — Refactor `RegisterFile.gpr` to `Fin 32 → RegValue`** (0.25 day)
  - Change signature. Bump downstream call sites using `⟨n, by decide⟩` proof-carrying construction or via the AN2-C.1 shim.
  - Verify cargo-side `RegValue` round-trip unchanged (the Rust ABI should not need updates — Rust already uses `[u64; 32]` which is `Fin 32`-equivalent).
  - **Acceptance**: `lake build SeLe4n.Machine` PASS.

- **AN2-C.3 — Derive `BEq` + `LawfulBEq` for `RegisterFile`** (0.15 day)
  - Add `deriving BEq, LawfulBEq` to the `RegisterFile` structure now that the refactored `Fin 32` representation supports it.
  - Delete the old `RegisterFile.not_lawfulBEq` negative witness (it was a guard against accidentally relying on the unlawful instance; the new instance IS lawful).
  - Spot-check that `RegisterFile.ext` (the AK7-G extensionality lemma) still composes.
  - **Acceptance**: `LawfulBEq RegisterFile` derivable; negative witness removed; `lake build` PASS.

- **AN2-C.4 — `RHTable.BEq` + `LawfulBEq (RHTable κ β)` derivation** (0.25 day)
  - In `Bridge.lean:136-153`, add:
    ```lean
    instance [LawfulBEq κ] [LawfulBEq β] : LawfulBEq (RHTable κ β) where
      eq_of_beq := ...  -- structural via field-by-field equality
      rfl := ...        -- structural reflexivity
    ```
  - Verify via `example : LawfulBEq (RHTable ObjId KernelObject)` — now that `LawfulBEq KernelObject` + `LawfulBEq RegisterFile` both hold (post AN2-C.3), the chain composes.
  - **Acceptance**: instance present; `#check @LawfulBEq (RHTable ObjId KernelObject)` succeeds.

- **AN2-C.5 — Migrate consumers + cleanup shim** (0.25 day)
  - Walk scheduler/IPC consumers of `RegisterFile.gpr`; migrate any that still use `gprNat` to direct `Fin 32` calls where the index is statically known.
  - Keep `gprNat` as a permanent convenience for code paths where the index is a runtime value needing validation.
  - Drop any manual `DecidableEq SystemState` witness-threading in downstream proofs; they compose automatically now.
  - **Acceptance**: `grep -rn "RegisterFile\.gprNat" SeLe4n/` shows only the legitimate runtime-index usage; full gate + rust gate PASS.

- **Regression test**: full gate + rust gate at each commit.
- **Cascade**: ~20 RegisterFile sites + ~5 RHTable sites; 1-per-commit batching unnecessary (types are different).

### AN2-D — Typed-identifier disjointness as Prop-level invariant (H-10)

- **Audit ID**: H-10 (HIGH)
- **Files**:
  - `SeLe4n/Prelude.lean:111-135` (`ThreadId.toObjId`, `SchedContextId.toObjId`, `ServiceId.toObjId`)
  - `SeLe4n/Kernel/CrossSubsystem.lean` — extend `crossSubsystemInvariant` from 11 conjuncts to 12 with `typedIdDisjointness` as the new conjunct
  - `SeLe4n/Kernel/Lifecycle/Operations.lean:retypeFromUntyped` — verify `retypeFromUntyped_childId_fresh` discharges the new conjunct
- **Total effort**: ~2.5 days. **Cascade**: cascade-heavy (~50 preservation proofs); split across 7 sub-sub-task commits matching AM4 playbook.

**Sub-sub-task breakdown** (7 commits, one per AN2-D.N):

- **AN2-D.1 — Predicate definition + default witness** (0.25 day)
  - New definition in `CrossSubsystem.lean`:
    ```lean
    def typedIdDisjointness (st : SystemState) : Prop :=
      (∀ tid : ThreadId, ∀ scId : SchedContextId,
        (∃ tcb, st.lookupKernelObject tid.toObjId = some (.tcb tcb)) →
        (∃ sc, st.lookupKernelObject scId.toObjId = some (.schedContext sc)) →
        tid.toObjId ≠ scId.toObjId)
      ∧ (∀ tid : ThreadId, ∀ svcId : ServiceId, /* ThreadId vs ServiceId */)
      ∧ (∀ scId : SchedContextId, ∀ svcId : ServiceId, /* SchedContextId vs ServiceId */)
    ```
  - Prove `default_typedIdDisjointness : typedIdDisjointness (default : SystemState)` by `simp [typedIdDisjointness, lookupKernelObject, default]` (vacuous over empty store).
  - **Acceptance**: `lake build SeLe4n.Kernel.CrossSubsystem` PASS; default witness present.

- **AN2-D.2 — Same-kind frame lemma** (0.25 day)
  - `storeObject_sameKind_preserves_typedIdDisjointness` — same-kind writes don't change which IDs resolve to which variants, so disjointness transfers.
  - **Acceptance**: frame lemma proven; `module gate` PASS.

- **AN2-D.3 — Cross-kind retype preservation** (0.5 day)
  - `retypeFromUntyped_preserves_typedIdDisjointness` via `retypeFromUntyped_childId_fresh`: the new child ID is absent pre-state, so pre-state disjointness + post-state presence in one variant only implies no aliasing with a different variant.
  - Case-split per `KernelObjectType` target variant (`.tcb`, `.schedContext`, `.endpoint`, `.notification`, `.cnode`, `.vspaceRoot`, `.service`): for each, the new ID enters one typed-ID namespace; prove no collision with the other two.
  - **Acceptance**: 7-case theorem proven; rounds out the retype preservation story.

- **AN2-D.4 — 12th conjunct of `crossSubsystemInvariant`** (0.25 day)
  - Extend `crossSubsystemInvariant` from 11 → 12 conjuncts (append at end so prefix-indexed projections remain unchanged — follows AM4 convention).
  - Add projection `crossSubsystemInvariant_to_typedIdDisjointness`.
  - Update `default_crossSubsystemInvariant` to 12 cases.
  - **Acceptance**: module gate PASS; projection accessor present.

- **AN2-D.5 — 5 core bridges** (0.5 day)
  - Extend the 5 core bridges (`_objects_change_bridge`, `_retype_bridge`, `_objects_frame`, `_services_change`, `_composition_gap_documented`) with a new `hTypedIdDisj : typedIdDisjointness st'` hypothesis where each bridge cannot discharge it from the pre-state alone.
  - `_retype_bridge` specifically discharges `hTypedIdDisj` from `retypeFromUntyped_preserves_typedIdDisjointness` (AN2-D.3) internally — no caller supplies it.
  - **Acceptance**: module gate PASS; retype bridge no longer requires caller-supplied `typedIdDisjointness` witness.

- **AN2-D.6 — 34 per-operation bridge lemmas (cascade)** (0.5 day — mechanical)
  - Uniform call-pattern edit across IPC/Scheduler/Lifecycle/Capability/SchedContext/Priority/VSpace/IPCBuffer/Retype/Interrupt bridge lemmas (follows AM4-E playbook).
  - Each bridge gains a new `hTypedIdDisj` hypothesis wiring either (a) forward from the caller, or (b) discharged internally via AN2-D.2/AN2-D.3 where applicable.
  - **Acceptance**: full gate PASS; cascade complete.

- **AN2-D.7 — Field-set catalog update + runtime checks + tests** (0.25 day)
  - Bump `crossSubsystemFieldSets` count 11 → 12; `typedIdDisjointness_fields := [.objects]` (or whichever fields the predicate touches).
  - Extend `crossSubsystem_pairwise_coverage_complete` from C(11,2)=55 disjoint pairs to C(12,2)=66 — add the 11 new pairs (typedIdDisjointness vs each of the 11 previous predicates, checking field-set disjointness).
  - Update runtime `checkCrossSubsystemInvariant` in `SeLe4n/Testing/InvariantChecks.lean` from 11 → 12 predicates.
  - Update V6-A runtime assertion in `tests/InformationFlowSuite.lean` from "11 entries" to "12 entries".
  - Add 3 new runtime tests in `tests/Ak7RegressionSuite.lean`:
    - `an2d_01_default_disjoint` — predicate holds on default state
    - `an2d_02_aliased_rejected` — deliberate ID-collision between TCB and SchedContext rejected
    - `an2d_03_retype_preserves` — retype from Untyped to `.tcb` preserves disjointness
  - Extend `scripts/ak7_cascade_baseline.sh` with `TYPEDIDDISJ_REFS` monotonicity metric (should grow as callers accumulate).
  - **Acceptance**: full gate; `lake exe ak7_regression_suite` PASS; `ak7_cascade_check_monotonic.sh` PASS against new baseline.

- **Regression test (cumulative)**: full gate at every sub-sub-task commit; `lake exe ak7_regression_suite` PASS at AN2-D.7
- **Cascade**: ~50 preservation sites, explicit counts per sub-sub-task above

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
- **Total effort**: ~1 day. **Cascade**: ~25 sites total across 8 items.

**Sub-sub-task breakdown** (8 commits, one per FND-M item):

- **AN2-F.1 — FND-M01 `isWord64Bounded` delegation** (0.05 day; already covered by AN2-B.1/B.2)
  - Verify AN2-B.1 (`CPtr`) and AN2-B.2 (`Slot`) have migrated `isWord64Bounded` to `@[inline] def isWord64Bounded := isWord64Dec ·.val`. No additional work if AN2-B landed correctly.
  - **Acceptance**: `grep -rn "isWord64Bounded" SeLe4n/Prelude.lean` shows delegated form.

- **AN2-F.2 — FND-M02 `VAddr.canonicalBound` parameterization** (0.1 day; already covered by AN2-B.3)
  - Verify AN2-B.3 replaced hardcoded 2^48 with `MachineState.virtualAddressWidth`-derived computation.
  - Confirm no decode site silently mismatches the default.
  - **Acceptance**: no hardcoded `2^48` remains for `canonicalBound`; decode-site audit pass.

- **AN2-F.3 — FND-M03 `UntypedObjectValid` subtype + retype precondition** (0.15 day)
  - Add subtype in `Model/Object/Types.lean:1017-1043`:
    ```lean
    def UntypedObjectValid := { ut : UntypedObject // ut.wellFormed }
    ```
  - Tighten `allocate` and `retypeFromUntyped` entry signatures to accept `UntypedObjectValid` (instead of bare `UntypedObject` + runtime `wellFormed` check).
  - Cascade through ~5-8 call sites at retype entry.
  - **Acceptance**: subtype defined; retype signatures tightened; full gate PASS.

- **AN2-F.4 — FND-M04 `minPracticalRHCapacity` constant** (0.05 day)
  - In `Kernel/RobinHood/Bridge.lean:88-94`, introduce:
    ```lean
    def minPracticalRHCapacity : Nat := 16
    ```
  - Reference from `Inhabited (RHTable κ β)` instance and the capacity-bound bridge lemmas.
  - **Acceptance**: no magic `16` literal remains in the `Inhabited` instance; `lake build` PASS.

- **AN2-F.5 — FND-M05 DS-L5 heartbeat profile + full decomposition** (0.5 day, mandatory)
  - In `Kernel/RobinHood/Bridge.lean:240-283` use `set_option profiler true` + `set_option trace.Meta.Tactic.simp` + `set_option pp.all true` to identify every subproof consuming ≥ 50,000 heartbeats. Produce a decomposition map in a scratch file (`docs/audits/AN2F5_HEARTBEAT_MAP.md`, ephemeral).
  - Extract each slow subgoal as a top-level named lemma with a targeted proof strategy. Typical extractions: `rhtable_ofList_insert_invariant`, `rhtable_ofList_probeChainDominant_transfer`, `rhtable_ofList_WF_induction`. Expect 5–8 named lemmas.
  - Each extracted lemma gets its own `set_option maxHeartbeats` appropriate to its size (≤ 100,000 per lemma); top-level theorem composes them under the Lean default (200,000).
  - **No partial fallback permitted**: the heartbeat budget MUST be reduced to ≤ 200,000 before AN2-F.5 is considered complete. If the toolchain blocks decomposition (unlikely given AK10 proved similar patterns work), invoke the escalation ladder: (i) rewrite the proof with explicit `exact` terms instead of tactic cascades; (ii) use `Classical.byContradiction` + `decide` on the boolean skeleton; (iii) hand-unfolded structural case analysis. Budget: up to 1 additional day for escalation.
  - **Acceptance**: `Kernel/RobinHood/Bridge.lean` has NO `set_option maxHeartbeats N` where `N > 200000`; every originally-slow proof now composes named lemmas; full gate PASS.

- **AN2-F.6 — FND-M06 gate unchecked FrozenOps** (0.1 day)
  - Mark unchecked `Kernel/FrozenOps/Core.lean:149-200` operations `private`. Public surface is the `*Checked` variants from AK8-G.
  - Migrate any test site that depends on an unchecked variant to the checked form. Since FrozenOps is experimental (per CLAUDE.md "FrozenOps status stays 'experimental — deferred to WS-V. Not in production import chain'"), the call-site count is likely zero or very small.
  - **Acceptance**: private marker applied; no production consumer references an unchecked variant.

- **AN2-F.7 — FND-M07 Phase-2 unreachable branch proof** (0.15 day)
  - In `Kernel/FrozenOps/Core.lean:285-344`, replace the AE2-D Phase-2 `.error .objectNotFound` fallback with a substantive impossibility proof:
    ```lean
    ... := by exact absurd hPhase2 (Phase1_covers_all hPhase1)
    ```
  - Need to first prove `Phase1_covers_all` as a named lemma (the covering property of Phase-1).
  - **Acceptance**: substantive proof present; no silent `.error` fallback in the two-phase validation path.

- **AN2-F.8 — FND-M08 `toObjId` decision-table docstring** (0.1 day)
  - Add to `Prelude.lean:149-198` a Markdown decision table in the `ObjId`-namespace docstring:
    | Variant | Checks sentinel | Checks store type | Use when |
    |---------|:---------------:|:-----------------:|----------|
    | `toObjId`         | no  | no  | Proof-side identity mapping |
    | `toObjIdChecked`  | yes | no  | Kernel entry (sentinel rejection) |
    | `toObjIdVerified` | yes | yes | Production API (full validation) |
  - **Acceptance**: table present; `check_website_links.sh` PASS.

- **Regression test**: full gate; `lake exe frozen_ops_suite`.
- **Cascade**: small per item; total ~25 sites (most in AN2-F.3 retype-entry tightening).

### AN2-G — DEF-F-L9 17-deep tuple refactor (cross-cutting prep — Theme 4.2 entrypoint)

- **Audit IDs**: DEF-F-L9 (carried forward from AUDIT_v0.29.0_DEFERRED.md), Theme 4.2 cross-cutting
- **Files**: `SeLe4n/Model/State.lean` (`allTablesInvExtK` 17-tuple)
- **Total effort**: ~1.5 days. **Cascade**: ~80 proof sites per the audit's WS-AF-26 design rationale; establishes the template for AN3-B and AN4-F (CAP-M05).

**Sub-sub-task breakdown** (7 commits):

- **AN2-G.1 — `AllTablesInvExtK` structure + bidirectional bridge** (0.25 day)
  - Define:
    ```lean
    structure AllTablesInvExtK (st : SystemState) : Prop where
      objects_invExtK : st.objects.invExtK
      irqHandlers_invExtK : st.irqHandlers.invExtK
      asidTable_invExtK : st.asidTable.invExtK
      serviceRegistry_invExtK : st.serviceRegistry.invExtK
      interfaceRegistry_invExtK : st.interfaceRegistry.invExtK
      services_invExtK : st.services.invExtK
      cdtChildMap_invExtK : st.cdtChildMap.invExtK
      cdtParentMap_invExtK : st.cdtParentMap.invExtK
      cdtSlotNode_invExtK : st.cdtSlotNode.invExtK
      cdtNodeSlot_invExtK : st.cdtNodeSlot.invExtK
      objectTypes_invExtK : st.lifecycle.objectTypes.invExtK
      capabilityRefs_invExtK : st.capabilityRefs.invExtK
      objectIndexSet_invExtK : st.objectIndexSet.invExtK
      scThreadIndex_invExtK : st.scThreadIndex.invExtK
      scheduler_byPriority_invExtK : st.scheduler.byPriority.invExtK
      scheduler_threadPriority_invExtK : st.scheduler.threadPriority.invExtK
      scheduler_membership_invExtK : st.scheduler.membership.invExtK
    ```
  - Rename original 17-tuple to `allTablesInvExtKTuple`; keep legacy definition building. Add bidirectional bridge `allTablesInvExtK_iff_tuple`.
  - **Acceptance**: structure + bridge compile; no downstream breakage (tuple form remains).

- **AN2-G.2 — `@[simp]` projection abbrevs** (0.15 day)
  - Add 17 projections matching AN3-B.2 pattern.
  - **Acceptance**: 17 `#check` statements elaborate.

- **AN2-G.3 — Define primary type as `AllTablesInvExtK`** (0.15 day)
  - Swap which name is primary; mark tuple form `@[deprecated]`.
  - **Acceptance**: `AllTablesInvExtK` is the canonical API; deprecation marker present.

- **AN2-G.4 — Migrate Model/FreezeProofs consumers (~20 sites)** (0.25 day)
  - `SeLe4n/Model/FreezeProofs.lean` (1660 LOC) is the heaviest consumer cluster. Replace deep projections with field access.
  - **Acceptance**: `lake build SeLe4n.Model.FreezeProofs` PASS; module gate PASS.

- **AN2-G.5 — Migrate Kernel subsystem consumers (~30 sites)** (0.3 day)
  - Walk `Kernel/CrossSubsystem.lean`, `Kernel/API.lean`, scheduler/IPC preservation chains.
  - Batch into 2 commits by file cluster.
  - **Acceptance**: full gate PASS after each batch.

- **AN2-G.6 — Migrate test consumers (~30 sites)** (0.25 day)
  - Walk `tests/*Suite.lean`, `SeLe4n/Testing/*.lean`.
  - **Acceptance**: all test suites PASS; full gate PASS.

- **AN2-G.7 — Delete deprecated tuple form + monotonicity metric** (0.15 day)
  - Confirm `grep -rn "allTablesInvExtKTuple" SeLe4n/ tests/` shows only definition site; delete it and the bridge.
  - Extend `scripts/ak7_cascade_baseline.sh` with `ALLTABLESINVEXTK_TUPLE_REFS` metric (floor = 0).
  - **Acceptance**: tuple form removed; monotonicity metric committed; full gate PASS.

- **Regression test (cumulative)**: `lake build SeLe4n.Model.State` + full gate at every commit; `lake exe ak7_regression_suite` at AN2-G.7.
- **Cascade**: ~80 sites, explicitly counted above (20+30+30).

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
- **Plan** (single path — Option A mandatory, no fallback):
  1. Extract the subset of Transport primitives Donation depends on into a dependency-free `DonationPrimitives.lean` module. Typical primitives: `returnDonatedSchedContext` (schedcontext store helper), `storeDonationTcbWithIpcState` (TCB store helper), plus the three frame lemmas `returnDonatedSchedContext_{notification,endpoint}_backward` and `cleanupPreReceiveDonation_tcb_forward`.
  2. `Donation.lean` imports `DonationPrimitives.lean` (NOT `Transport.lean`). The cycle is structurally broken.
  3. Hub `Operations.lean` re-exports Donation cleanly alongside Timeout and WithCaps. All three sibling modules become symmetric.
  4. **Budget**: up to 1.5 days for the extraction. If the extraction touches > 10 unrelated theorems, follow-up refactor commits partition the work, but the Option A outcome is mandatory — no Option B fallback.
  5. If primitives extraction truly cannot resolve the cycle for a subset of the Donation API (e.g., one primitive is irreducibly tied to Transport), partition Donation itself into Donation/Primitives.lean and Donation/Transport-Dependent.lean; the primitives-dependent subset joins the hub re-export, while the transport-dependent subset remains importable directly but is documented in the hub. This is still Option A (structural resolution), not Option B (doc-only).
- **Acceptance**: `import SeLe4n.Kernel.IPC.Operations` exposes `cleanupPreReceiveDonation`, `applyCallDonation`, `applyReplyDonation`, `cancelDonation` symbols without additional import; module gate `lake build SeLe4n.Kernel.IPC.Operations` PASS; hub symmetry restored (Timeout, WithCaps, Donation all re-exported identically)
- **Regression test**: full gate; `lake exe negative_state_suite`
- **Cascade**: 0–10 sites depending on chosen option

### AN3-B — Named-projection refactor for `ipcInvariantFull` (IPC-M01, Theme 4.2 second instance)

- **Audit ID**: IPC-M01 (MEDIUM, but flagged as the single highest-leverage hygiene fix in IPC); Theme 4.2 cross-cutting
- **Files**:
  - `SeLe4n/Kernel/IPC/Invariant/Defs.lean:2483` (`ipcInvariantFull` 12-tuple definition)
  - All consumers using `.2.2.2.2.2.2.2.2.2.2.2.1` (`donationOwnerValid` extraction) and similar deep projections
- **Total effort**: ~2 days. **Cascade**: cascade-heavy (~60 sites); split across 6 sub-sub-tasks matching AN2-G's tuple→structure playbook.

**Sub-sub-task breakdown** (6 commits, one per AN3-B.N):

- **AN3-B.1 — `IpcInvariantFull` structure + bidirectional bridge** (0.25 day)
  - Define `IpcInvariantFull` as a Lean `structure` with 12 named fields mirroring the existing 12 conjuncts (field names: `structuralBasic`, `endpointWaiterConsistent`, `notificationWaiterConsistent`, `queueMembershipConsistent`, `queueNextBlockingConsistent`, `uniqueWaiters`, `queueNoDup`, `allPendingMessagesBounded`, `blockedOnReplyHasTarget`, `ipcStateQueueMembershipConsistent`, `passiveServerIdle`, `donationOwnerValid`).
  - Rename original tuple-based definition to `ipcInvariantFullTuple` (keeps all existing callers building).
  - Add bidirectional bridge `ipcInvariantFull_iff_tuple : ipcInvariantFullTuple st ↔ IpcInvariantFull st` proven by `constructor <;> intro h <;> constructor <;> simp_all [IpcInvariantFull, ipcInvariantFullTuple]`.
  - **Acceptance**: `lake build SeLe4n.Kernel.IPC.Invariant.Defs` PASS; bridge theorem present; no downstream breakage (tuple form still callable).

- **AN3-B.2 — `@[simp]` projection abbrevs** (0.25 day)
  - Add 12 `@[simp] abbrev IpcInvariantFull.<field> (h : IpcInvariantFull st) : <PredType> st := h.<field>` projections so any legacy `.2.2...` projection can be rewritten as `h.fieldName` via mechanical find-replace.
  - **Acceptance**: 12 projection abbrevs committed; `#check IpcInvariantFull.donationOwnerValid` elaborates.

- **AN3-B.3 — Define primary type as `IpcInvariantFull`** (0.25 day)
  - Swap which name is the primary definition: `ipcInvariantFullTuple` remains callable via bridge; the canonical name used in new theorems is `IpcInvariantFull`.
  - Mark `ipcInvariantFullTuple` with `@[deprecated]` message pointing at `IpcInvariantFull`.
  - Update `Defs.lean` documentation to reference the named-field form.
  - **Acceptance**: `IpcInvariantFull` is the primary API; deprecation marker present; module gate PASS.

- **AN3-B.4 — Migrate IPC subsystem consumers (~25 sites)** (0.5 day — batched)
  - Walk IPC-internal consumers in `IPC/Invariant/Structural.lean` (many call sites), `EndpointPreservation.lean`, `CallReplyRecv.lean`, `NotificationPreservation.lean`, `QueueMembership.lean`, `QueueNextBlocking.lean`, `QueueNoDup.lean`, `WaitingThreadHelpers.lean`.
  - Replace `.2.2.2.2...` projections with `.fieldName` field access.
  - Commit in 2-3 grouped commits by file cluster to keep diffs reviewable.
  - **Acceptance**: IPC-internal consumers migrated; full gate PASS after each batch.

- **AN3-B.5 — Migrate cross-subsystem consumers (~25 sites)** (0.5 day — batched)
  - Walk `Kernel/CrossSubsystem.lean`, `Kernel/API.lean`, `Kernel/Architecture/Invariant.lean`, `Kernel/Lifecycle/Operations.lean`, `Kernel/Capability/Invariant/Preservation.lean`, test suites (`tests/*Suite.lean`).
  - Same find-replace pattern as AN3-B.4.
  - Commit in 2-3 grouped commits.
  - **Acceptance**: cross-subsystem consumers migrated; full gate PASS after each batch.

- **AN3-B.6 — Delete deprecated tuple form + monotonicity baseline** (0.25 day)
  - Confirm via `grep -rn "ipcInvariantFullTuple\|\.2\.2\.2\.2\.2\.2\.2\.2\.2\.2\.2\.1" SeLe4n/ tests/` that zero production consumers remain.
  - If grep is clean: delete `ipcInvariantFullTuple` and the bridge theorem entirely. Otherwise keep as vestigial with a tracking DEFERRED entry.
  - Extend `scripts/ak7_cascade_baseline.sh` with `IPCINVFULL_TUPLE_REFS` monotonicity metric (should DROP to zero once migration is complete).
  - **Acceptance**: tuple form removed or explicitly kept with DEFERRED tracking; `ak7_cascade_check_monotonic.sh` PASS against new baseline

- **Regression test (cumulative)**: `lake build SeLe4n.Kernel.IPC.Invariant.Defs` + full gate at every commit; `lake exe ak7_regression_suite` PASS at AN3-B.6
- **Cascade**: ~50-60 sites explicitly counted (25 IPC-internal in AN3-B.4 + 25 cross-subsystem in AN3-B.5)

### AN3-C — IPC `Structural.lean` 7626-line split (Theme 4.7 first instance, IPC-M02)

- **Audit IDs**: IPC-M02 (MEDIUM), Theme 4.7 cross-cutting
- **Files**:
  - `SeLe4n/Kernel/IPC/Invariant/Structural.lean` (7626 lines) — split into 4 child modules
  - `SeLe4n/Kernel/IPC/Invariant.lean` — re-export hub (no change needed if `Structural.lean` itself becomes the hub)
- **Total effort**: ~1.5 days. **Cascade**: 0 external sites (re-export pattern preserves all import paths); ~7500 lines moved in total.

**Sub-sub-task breakdown** (6 commits — Lean file splits must be done carefully; each move is its own commit so review can verify nothing dropped):

- **AN3-C.1 — Seam inventory + declaration catalog** (0.25 day — planning-only commit)
  - Produce a `docs/audits/AN3C_SEAM_MAP.md` (ephemeral; deleted at AN3-G closure) listing every declaration in `Structural.lean` tagged with its target child module. Four target categories:
    - `QueueNextTransport.lean` — `QueueNextPath`-related lemmas, `queueNextReflTrans`, queueNext / transport compositions
    - `StoreObjectFrame.lean` — `storeObject_*_preserves_*` frame lemmas (same-kind, cross-kind, TCB/endpoint/notification/schedcontext)
    - `DualQueueMembership.lean` — queue-membership preservation, `queueIndexBound`, `queueNoDupPreservation`
    - `PerOperation.lean` — per-operation Structural preservation witnesses (`endpointSendStructural`, `endpointReceiveStructural`, etc.)
  - Spot-check: run `grep -n "^theorem\|^lemma\|^def" SeLe4n/Kernel/IPC/Invariant/Structural.lean | wc -l` to get the total declaration count; verify the sum across 4 child categories equals the total.
  - **Acceptance**: seam map file committed; reviewer can verify every declaration has a target.

- **AN3-C.2 — Extract `QueueNextTransport.lean`** (0.25 day)
  - `git mv`-style: create `SeLe4n/Kernel/IPC/Invariant/Structural/QueueNextTransport.lean`; move ~1500-2000 lines.
  - Import minimal set from original parent file's imports.
  - Original `Structural.lean` gains `import SeLe4n.Kernel.IPC.Invariant.Structural.QueueNextTransport` at the top.
  - Verify: `lake build SeLe4n.Kernel.IPC.Invariant.Structural.QueueNextTransport` PASS; `lake build SeLe4n.Kernel.IPC.Invariant.Structural` PASS (composed via the new import).
  - **Acceptance**: child module builds; parent still builds via re-export; full gate PASS.

- **AN3-C.3 — Extract `StoreObjectFrame.lean`** (0.25 day)
  - Same pattern: create child module, move ~1500-2000 lines (frame lemmas), add import to parent.
  - Frame lemmas often depend on QueueNextTransport — verify import order.
  - **Acceptance**: child module builds; full gate PASS.

- **AN3-C.4 — Extract `DualQueueMembership.lean`** (0.25 day)
  - Same pattern: create child module, move ~1500-2000 lines (queue membership).
  - **Acceptance**: child module builds; full gate PASS.

- **AN3-C.5 — Extract `PerOperation.lean`** (0.25 day)
  - Same pattern: create child module, move remaining ~1500-2000 lines (per-operation witnesses).
  - **Acceptance**: child module builds; full gate PASS.

- **AN3-C.6 — Finalize as thin re-export hub** (0.25 day)
  - `Structural.lean` now contains only:
    ```lean
    import SeLe4n.Kernel.IPC.Invariant.Structural.QueueNextTransport
    import SeLe4n.Kernel.IPC.Invariant.Structural.StoreObjectFrame
    import SeLe4n.Kernel.IPC.Invariant.Structural.DualQueueMembership
    import SeLe4n.Kernel.IPC.Invariant.Structural.PerOperation
    ```
  - Verify `wc -l` on each child file ≤ 2000; verify `Structural.lean` ≤ 50 LOC.
  - Delete the ephemeral `AN3C_SEAM_MAP.md` (it was only useful during the split).
  - Refresh `CLAUDE.md` "Known large files" list: remove `Structural.lean 7626` and add the 4 new children.
  - **Acceptance**: file sizes at target; hub is re-export-only; full gate PASS.

- **Regression test (cumulative)**: `lake build SeLe4n.Kernel.IPC.Invariant.Structural` at every commit; full gate after each move verifies no theorem went missing.
- **Cascade**: 0 (no external import changes — re-export pattern)

### AN3-D — IPC `NotificationPreservation.lean` and `CallReplyRecv.lean` splits (IPC-M03, IPC-M04)

- **Audit IDs**: IPC-M03, IPC-M04 (both MEDIUM)
- **Files**:
  - `SeLe4n/Kernel/IPC/Invariant/NotificationPreservation.lean` (1490 LOC) → split into `Notification/Signal.lean` + `Notification/Wait.lean`
  - `SeLe4n/Kernel/IPC/Invariant/CallReplyRecv.lean` (1069 LOC) → split into `Call.lean` + `ReplyRecv.lean`
- **Total effort**: ~0.75 day. **Cascade**: 0 external (re-export pattern).

**Sub-sub-task breakdown** (5 commits, same AN3-C playbook adapted for 2 files × 2 children each):

- **AN3-D.1 — NotificationPreservation seam inventory + signal extract** (0.2 day)
  - Catalog declarations into `Notification/Signal.lean` (signal-family preservation theorems, ~750 LOC) vs `Notification/Wait.lean` (wait-family, ~740 LOC).
  - Extract `Notification/Signal.lean` as first child module; original hub gains import.
  - **Acceptance**: `lake build SeLe4n.Kernel.IPC.Invariant.NotificationPreservation.Signal` PASS; parent still builds.

- **AN3-D.2 — NotificationPreservation wait extract + hub conversion** (0.2 day)
  - Extract `Notification/Wait.lean`; `NotificationPreservation.lean` reduces to thin re-export hub (~20 LOC).
  - **Acceptance**: both children ≤ 1000 LOC; hub ≤ 30 LOC; full gate PASS.

- **AN3-D.3 — CallReplyRecv seam inventory + call extract** (0.15 day)
  - Catalog declarations. Extract `Call.lean` (call-family preservation theorems, ~550 LOC).
  - **Acceptance**: `lake build` PASS.

- **AN3-D.4 — CallReplyRecv replyrecv extract + hub conversion** (0.15 day)
  - Extract `ReplyRecv.lean`; `CallReplyRecv.lean` becomes thin re-export hub.
  - **Acceptance**: both children ≤ 600 LOC; hub ≤ 30 LOC; full gate PASS.

- **AN3-D.5 — CLAUDE.md large-files-list update** (0.05 day)
  - Remove `NotificationPreservation.lean 1490` + `CallReplyRecv.lean 1069` entries; verify none of the children exceed the 1000-LOC ceiling.
  - **Acceptance**: large-files list reflects new topology; full gate PASS.

- **Regression test**: full gate after each commit.
- **Cascade**: 0 external.

### AN3-E — IPC MEDIUM batch (IPC-M05..M09)

- **Audit IDs**: IPC-M05..M09
- **Files**: scattered
- **Total effort**: ~0.75 day.

**Sub-sub-task breakdown** (5 items, one commit each):

- **AN3-E.1 — IPC-M05 shared `transferAux` helper** (0.2 day)
  - In `IPC/Invariant/QueueMembership.lean:31-78`, extract the shared ~40-LOC body of `transfer`/`transferRecv` into a single `transferAux (... : QueueSide → ...) : ... := ...` helper parameterized on the queue side (send vs receive).
  - Both existing `transfer` and `transferRecv` become thin wrappers.
  - Verify downstream preservation proofs continue to compose.
  - **Acceptance**: ~40 LOC recovered; module gate PASS.

- **AN3-E.2 — IPC-M06 `storeObject_scheduler_eq_z7` visibility decision** (0.1 day)
  - Option A: promote to public if downstream consumers benefit.
  - Option B: keep private; add docstring `-- INTENTIONALLY PRIVATE: donation path consumes the general `storeObject_scheduler_eq_*` forms. Z7 variant is an optimization for the bound-SC case; see WH:Z7.`
  - Default: Option B (audit-aligned).
  - **Acceptance**: visibility decision documented.

- **AN3-E.3 — IPC-M07 queue-consistency reachability precondition** (0.2 day)
  - Strengthen predicates in `IPC/Invariant/Defs.lean:811-927` (queue-consistency): append `∀ tid ∈ queue, st.objectIndex.contains tid.toObjId`.
  - Verify the strengthening is discharged by the existing `objectsInvariant`/`objectIndexConsistent` predicates; downstream preservation proofs should go through unchanged.
  - If any preservation proof breaks: the callers were relying on the weaker form; patch them to thread the reachability witness.
  - **Acceptance**: strengthened predicate ships; full gate PASS.

- **AN3-E.4 — IPC-M08 `allPendingMessagesBounded` scope decision** (0.15 day)
  - Option A: strengthen to cross-check endpoint liveness.
  - Option B: weaken docstring to explicitly acknowledge liveness is a transitive property composed via `ipcStateQueueMembershipConsistent`.
  - Default: Option B (minimal change; matches the predicate's actual role).
  - **Acceptance**: docstring updated.

- **AN3-E.5 — IPC-M09 `cleanupPreReceiveDonation` co-location banner + import-cycle guard** (0.1 day)
  - Add banner comment at `IPC/Operations/Endpoint.lean:1-20`:
    ```
    -- DO NOT MOVE cleanupPreReceiveDonation out of this file.
    -- Rationale: Donation.lean → Transport.lean → Endpoint.lean; moving the
    -- cleanup helper back to Donation.lean reintroduces a cycle.
    ```
  - Add a Lean `example` that triggers a compile error if the function is relocated (e.g., a proof that the function is defined in this file via `#check @cleanupPreReceiveDonation`).
  - **Acceptance**: banner + guard present.

- **Regression test**: full gate; `lake exe negative_state_suite`.
- **Cascade**: ~5-10 sites per item.

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

**Goal**: close the four HIGH capability findings (H-02..H-06), batch CAP/LIF/SVC MEDIUMs, address the Lifecycle.Operations.lean monolithic split (Theme 4.7), and document the CDT-discharge index pattern (Theme 4.1 anchor for AN12-A's broader index).

**Effort**: 5–6 days. **Blocks**: AN6 CrossSubsystem composition.

### AN4-A — `lifecycleRetypeObject` visibility hardening (H-02)

- **Audit ID**: H-02 (HIGH)
- **Files**:
  - `SeLe4n/Kernel/Lifecycle/Operations.lean:453-560` — `lifecycleRetypeObject` def + cluster
  - `SeLe4n/Kernel/Lifecycle/Operations/Internal.lean` (new) — moves the function into a `protected` namespace OR a sibling module not exported from the hub
  - 13+ proof-chain consumers (per the audit's count) — verify they import the new internal module
  - `scripts/test_tier0_hygiene.sh` — extend with a CI check
- **Total effort**: ~1 day. **Cascade**: ~13 import paths; 1 new CI hygiene check.

**Sub-sub-task breakdown** (5 commits):

- **AN4-A.1 — Inventory production vs proof-chain consumers** (0.15 day)
  - `grep -rn "lifecycleRetypeObject" SeLe4n/` to list all 13+ references.
  - Classify each reference as either:
    - **Production caller (must bypass)** — any syscall dispatch arm in `API.lean` or any Kernel-level handler. These MUST go through `lifecycleRetypeWithCleanup`. Expected count: 0 (audit claims they already do; confirm).
    - **Proof-chain reference (must be explicit)** — every theorem that needs to reason about the internal step.
  - Capture inventory in `scripts/lifecycle_internal_allowlist.txt` with one path per line.
  - **Acceptance**: allowlist file committed; classification documented.

- **AN4-A.2 — Move `lifecycleRetypeObject` to `Internal` namespace** (0.25 day)
  - Option A (preferred — simpler): rewrap the existing def as `namespace Internal ... end Internal` inside `Lifecycle/Operations.lean`. Consumers reference as `Lifecycle.Internal.lifecycleRetypeObject`.
  - Option B (if file split desired): move to new `SeLe4n/Kernel/Lifecycle/Operations/Internal.lean`. Hub `Operations.lean` does NOT re-export `Internal`.
  - Hub `Operations.lean` continues to re-export `lifecycleRetypeWithCleanup` + cleanup primitives.
  - **Acceptance**: `lifecycleRetypeObject` no longer visible from direct `import SeLe4n.Kernel.Lifecycle.Operations`; accessible only via the explicit `Internal` sub-namespace.

- **AN4-A.3 — Migrate proof-chain consumer imports** (0.25 day)
  - Walk the 13 entries from AN4-A.1. For each, update its `import`/namespace reference to the new `Internal` sub-namespace.
  - Verify `lake build` passes after each batch of 3-4 consumers.
  - **Acceptance**: all proof-chain consumers updated; full gate PASS.

- **AN4-A.4 — CI hygiene check: reject unauthorized consumers** (0.2 day)
  - Extend `scripts/test_tier0_hygiene.sh` with:
    ```bash
    # AN4-A: enforce lifecycleRetypeObject visibility
    unauthorized=$(grep -rn "lifecycleRetypeObject" SeLe4n/ --include="*.lean" \
                   | grep -v -f scripts/lifecycle_internal_allowlist.txt || true)
    if [ -n "$unauthorized" ]; then
        echo "ERROR: unauthorized lifecycleRetypeObject consumer detected:"
        echo "$unauthorized"
        exit 1
    fi
    ```
  - Verify the check fails on a synthetic unauthorized usage and passes on the current tree.
  - **Acceptance**: CI hygiene check active; synthetic-violation test produces expected failure.

- **AN4-A.5 — Regression test for cleanup bypass** (0.15 day)
  - Add scenario test in `tests/NegativeStateSuite.lean`: synthesize a state where `lifecyclePreRetypeCleanup` WOULD have scrubbed a dangling capability reference; confirm that invoking `lifecycleRetypeWithCleanup` clears the reference but a hypothetical direct invocation of `Internal.lifecycleRetypeObject` (via a test-only namespace unfurl) does not. This documents the semantic difference.
  - **Acceptance**: test committed; scenario passes.

- **Regression test**: full gate; `lake exe negative_state_suite`.
- **Cascade**: ~13 import paths + 1 CI check + 1 regression test.

### AN4-B — Redundant `lifecycleIdentityNoTypeAliasConflict` removal (H-03)

- **Audit ID**: H-03 (HIGH)
- **Files**: `SeLe4n/Kernel/Lifecycle/Invariant.lean:56-72`
- **Plan** (single path — full removal mandatory, no fallback):
  1. Prove the implication: `theorem lifecycleIdentityTypeExact_implies_noTypeAliasConflict (st : SystemState) : lifecycleIdentityTypeExact st → lifecycleIdentityNoTypeAliasConflict st`. Likely a one-liner via `intro hExact a b hTcb hSc; exact hExact …`.
  2. Delete the redundant conjunct from the bundle. Update bundle arity (one fewer field) and migrate the ~5-10 destructure sites. The cascade is small enough that a single commit covers it cleanly.
  3. After the arity change lands, delete `lifecycleIdentityNoTypeAliasConflict` itself (the standalone predicate) so no caller can accidentally re-introduce the redundant conjunct.
  4. **No fallback**: the audit's "at minimum, commit the implication theorem" wording is superseded; WS-AN removes the redundancy, not just documents it.
- **Acceptance**: implication theorem present and proven; bundle arity reduced; standalone predicate removed; all destructures migrated; full gate PASS
- **Regression test**: full gate
- **Cascade**: 5-10 sites (landed in one commit because the cascade is small)

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
  3. The marker theorem becomes the anchor for AN12-A's broader Theme 4.1 discharge index (covering H-04 CDT, H-07 projection, SC-M02 `hSchedProj`).
- **Acceptance**: index theorem committed; each of the 6 cap operations has a named discharge witness; AN12-A deliverable extends the index with H-07 + SC-M02 entries
- **Regression test**: full gate
- **Cascade**: ~12 sites (6 ops × 2 = base + companion)

### AN4-D — `cspaceLookupMultiLevel` SMP-precondition (H-05)

- **Audit ID**: H-05 (HIGH); cross-cutting Theme 4.4 single-core inventory
- **Files**: `SeLe4n/Kernel/Capability/Operations.lean:206`
- **Plan**:
  1. Add a precondition predicate `resolvedCnodeStillValid (st : SystemState) (resolvedRef : CapAddress) : Prop := ∃ cn, st.lookupKernelObject resolvedRef.cnode = some (.cnode cn)`.
  2. Refactor `cspaceLookupMultiLevel` to take this predicate as a hypothesis (or to assert it inside via an `if .. then .. else` returning `.error .invalidCapability`).
  3. Prove the precondition holds in the single-core kernel via "no retype between resolveCapAddress and cspaceLookupSlot in the absence of concurrency". This becomes the first formalised entry in the AN12-B SMP inventory (Theme 4.4); after AN9-J ships SMP bring-up, this precondition is discharged at SMP boundary by AN9-D's interrupt-disable wrapper on the dispatch path.
  4. Document the SMP-side discharge: at SMP boundary, the predicate becomes a critical-section obligation managed by an interrupt-disable bracket.
- **Acceptance**: precondition predicate defined; single-core proof present; SMP discharge documented
- **Regression test**: full gate; `lake exe negative_state_suite`
- **Cascade**: ~3 sites (lookup helper definition + 1-2 callers)

### AN4-E — `mintDerivedCap` non-null output witness (H-06)

- **Audit ID**: H-06 (HIGH)
- **Files**: `SeLe4n/Kernel/Capability/Operations.lean:641-649`
- **Plan** (single path — type-tightening mandatory):
  1. Add theorem:
     ```lean
     theorem mintDerivedCap_preserves_non_null
         (parent : NonNullCap) (badge : Badge) :
         (mintDerivedCap parent badge).isNull = false := by
       cases parent with | mk cap hNonNull => simp [mintDerivedCap, Capability.isNull]
     ```
  2. Tighten the return type: `mintDerivedCap : NonNullCap → Badge → NonNullCap` so the post-condition is type-level and unfalsifiable. Cascade through `cspaceMint` consumer (currently uses the value via `Capability` projection; with the tightened return, the wrapper unwraps once via `.val`).
  3. **No fallback**: the audit's "at minimum, ship the theorem" wording is superseded. WS-AN tightens the type because the AL1b/AL8 post-cap-audit discipline has already established NonNullCap as a first-class subtype; dropping it at the `mintDerivedCap` return site would be an asymmetric gap.
  4. If any consumer breaks on the return-type change, migrate the consumer in the same commit (expected cascade is small: 2-3 sites).
- **Acceptance**: theorem proven; return type is `NonNullCap`; all consumers compile; full gate PASS
- **Regression test**: full gate; `lake exe ak7_regression_suite`
- **Cascade**: ~3 sites (landed in one commit)

### AN4-F — Capability MEDIUM batch (CAP-M01..M05)

- **Audit IDs**: CAP-M01..M05
- **Files**: scattered
- **Total effort**: ~1.5 days. **Cascade**: CAP-M03 split (0 external); CAP-M05 cascade-heavy (~30 sites).

**Sub-sub-task breakdown** (5 top-level commits, CAP-M05 expanded into its own 6 sub-sub-sub-tasks mirroring AN3-B):

- **AN4-F.1 — CAP-M01 documented-obligation attribute** (0.1 day)
  - Define a no-op attribute in `SeLe4n/Prelude.lean`:
    ```lean
    syntax (name := documented_obligation) "@[documented_obligation]" : attr
    ```
  - Tag `resolveCapAddress_caller_rights_obligation` with `@[documented_obligation]`; replace its body from `: True := trivial` to `: Unit := ()` marker constant (audit's preferred form over vacuous Prop).
  - **Acceptance**: attribute defined; obligation greppable via `grep -rn "@\[documented_obligation\]" SeLe4n/`.

- **AN4-F.2 — CAP-M02 dead-branch proof-or-doc** (0.25 day)
  - Walk `cspaceRevokeCdtTransactional` at lines 1231-1236 and trace the validation post-condition.
  - If dead: prove `cspaceRevokeCdtTransactional_unreachable_fallback` substantively using the post-condition of `validateRevokeCdtDescendants`.
  - If live: document the triggering invariant failure in the function docstring.
  - **Acceptance**: one path resolved; `lake build SeLe4n.Kernel.Capability.Operations` PASS.

- **AN4-F.3 — CAP-M03 Preservation.lean split (6 child files)** (0.75 day)
  - Follow AN3-C playbook; 6 child modules × ~400 LOC each:
    - `Preservation/Insert.lean`, `Preservation/Delete.lean`, `Preservation/Revoke.lean`, `Preservation/CDT.lean`, `Preservation/CopyMoveMutate.lean`, `Preservation/MintLifecycle.lean`
  - 7 commits: seam inventory, 6 extractions, one finalization.
  - **Acceptance**: each child ≤ 500 LOC; hub ≤ 50 LOC; full gate after each extraction.

- **AN4-F.4 — CAP-M04 `RetypeTarget` subtype precondition** (0.25 day)
  - Define subtype in `SeLe4n/Kernel/Capability/Invariant/Defs.lean`:
    ```lean
    structure RetypeTarget where
      id : ObjId
      cleanupHookDischarged : ... -- witness
    ```
  - Cascade through `lifecyclePreRetypeCleanup` callers producing the witness post-cleanup; proof-chain callers of `retypeFromUntyped` (limited after AN4-A visibility hardening) thread the precondition.
  - **Acceptance**: subtype defined; ~5-10 consumer sites migrated.

- **AN4-F.5 — CAP-M05 `capabilityInvariantBundle` named-projection refactor** (0.75 day)
  - Follow AN3-B playbook for the 6-tuple (smaller than ipcInvariantFull's 12-tuple). Sub-sub-sub-tasks:
    - **AN4-F.5.1** — Structure + bidirectional bridge (0.1 day)
    - **AN4-F.5.2** — `@[simp]` projection abbrevs (0.1 day)
    - **AN4-F.5.3** — Swap primary to named form; deprecate tuple (0.1 day)
    - **AN4-F.5.4** — Migrate Capability-internal consumers (~15 sites) (0.2 day)
    - **AN4-F.5.5** — Migrate cross-subsystem consumers (~15 sites) (0.15 day)
    - **AN4-F.5.6** — Delete tuple + monotonicity metric (0.1 day)
  - **Acceptance**: ~30 sites migrated; tuple form deleted; `CAPINVBUNDLE_TUPLE_REFS` monotonicity metric at 0.

- **Regression test**: full gate after each sub-sub-task.
- **Cascade**: CAP-M01 ~1, CAP-M02 ~1, CAP-M03 ~0 external, CAP-M04 ~5-10, CAP-M05 ~30.

### AN4-G — Lifecycle MEDIUM batch (LIF-M01..M06)

- **Audit IDs**: LIF-M01..M06
- **Files**: `SeLe4n/Kernel/Lifecycle/Operations.lean` (1473 LOC) — split is LIF-M05
- **Total effort**: ~1 day.

**Sub-sub-task breakdown** (6 commits):

- **AN4-G.1 — LIF-M01 prove `removeThreadFromQueue` fallback unreachable** (0.15 day)
  - Prove `removeThreadFromQueue_unreachable_under_tcbExistsInvariant` substantively: under `tcbExistsInvariant`, the `(none, none)` "TCB not found" path is absurd because the invariant guarantees the TCB's presence in the object store.
  - Replace the defensive fallback with an explicit `absurd` or error.
  - **Acceptance**: theorem proven; no silent queue-zeroing path remains.

- **AN4-G.2 — LIF-M02 `lifecycleCleanupPipeline` wrapper** (0.15 day)
  - Wrap the per-step cleanup sequence (donated SC return, TCB ref scrub, endpoint-service detach, CDT detach) into a single `lifecycleCleanupPipeline : RetypeTarget → Kernel Unit` definition.
  - Expose ONLY the pipeline from the hub; mark the per-step helpers as `private` (where proof chain permits) OR move to `Internal` namespace.
  - **Acceptance**: pipeline defined; ~5 consumer sites migrated; full gate PASS.

- **AN4-G.3 — LIF-M03 scrub-address H3-binding doc cross-reference** (0.05 day)
  - Add `-- TODO(H3-binding): scrubObjectMemory uses abstract formula; hardware path must map via VSpace bridge` annotation at `scrubObjectMemory`.
  - Add `SELE4N_SPEC.md` §5 subsection documenting the model-vs-hardware scrub bridge gap.
  - **Acceptance**: annotation + SPEC entry present.

- **AN4-G.4 — LIF-M04 retype atomicity theorem** (0.15 day)
  - Prove `retypeFromUntyped_atomicity_under_sequential_semantics` witnessing that the watermark-advance + post-allocation-verify appears atomic in the sequential Lean model (because Lean's deterministic evaluation collapses the window).
  - Add TODO annotation cross-referencing AN12-B's SMP inventory confirmation (the inventory anchors the AN9-D HAL-bracket atomicity guarantee, so the sequential-semantics theorem here and the hardware atomicity in AN9-D compose cleanly).
  - **Acceptance**: theorem proven; TODO annotation present.

- **AN4-G.5 — LIF-M05 Operations.lean 4-file split** (0.4 day)
  - Follow AN3-C playbook for 4 children (~370 LOC each):
    - `Operations/Cleanup.lean`
    - `Operations/Retype.lean`
    - `Operations/Suspend.lean`
    - `Operations/Untyped.lean`
  - 5 commits: seam inventory + 4 extractions + hub conversion.
  - Hub `Operations.lean` becomes thin re-export after `lifecycleRetypeObject` visibility hardening from AN4-A is preserved (the `Internal` namespace is extracted into one of the children — recommend `Operations/Retype.lean` given the `lifecycleRetypeObject` function lives in the retype cluster).
  - **Acceptance**: each child ≤ 500 LOC; hub ≤ 50 LOC; full gate after each extraction commit.

- **AN4-G.6 — LIF-M06 partial-failure contract docstring** (0.1 day)
  - Add explicit docstring on `lifecycleRevokeDeleteRetype` documenting the no-rollback contract on partial failure: early `.error` returns leave state in a partially-cleaned form the caller must handle.
  - Surface in `SELE4N_SPEC.md` §5 as part of the lifecycle semantics.
  - **Acceptance**: docstring + SPEC entry present.

- **Regression test**: full gate after each commit.
- **Cascade**: LIF-M01 ~1, LIF-M02 ~5, LIF-M03 ~0, LIF-M04 ~1, LIF-M05 ~0 external, LIF-M06 ~0.

### AN4-H — Service MEDIUM batch (SVC-M01..M04)

- **Audit IDs**: SVC-M01..M04
- **Plan**:
  - **SVC-M01**: add `bootFromPlatform_service_fuel_sufficient` witness theorem proving `serviceBfsFuel ≥ initial_service_count`; document in `SELE4N_SPEC.md` §5.
  - **SVC-M02**: rename `Bfs` suffix → `Dfs` (or drop suffix). Cascade through ~5 call sites.
  - **SVC-M03**: enrich dependency-add return type to distinguish "added" vs "no-op", OR document the collision semantics in the function docstring.
  - **SVC-M04**: split `Service/Invariant/Acyclicity.lean` (1012 LOC) by reachability-induction-principle factoring. Mandatory — no stretch-goal framing. Follow the AN3-C playbook (seam inventory + 3 child extracts: `Acyclicity/BfsBoundary.lean`, `Acyclicity/ReachabilityInduction.lean`, `Acyclicity/PreservationWitnesses.lean`). The 1012 LOC file is borderline under the 2000-LOC ceiling but factoring it recovers a shared `reachability` induction principle that several callers already duplicate by hand (~30 LOC of duplication recovered).
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

## 8. Phase AN5 — Scheduler / SchedContext + `eventuallyExits` closure

**Goal**: Address SCH-M01..M05 hygiene and SC-M01..M03 (CBS witness, PIP closure-form, import-cycle banner). Split the 3633-line `Scheduler/Operations/Preservation.lean` per Theme 4.7. **Substantively close DEF-AK2-K.4 `eventuallyExits` hypothesis for the canonical RPi5 deployment.**

**Effort**: 4–5 days (AN5-F adds ~2 days). **Blocks**: AN6. **Sub-tasks**: 7 (AN5-A..AN5-G).

### AN5-A — Scheduler `Preservation.lean` 3633-line split (SCH dispatch + Theme 4.7)

- **Audit IDs**: SCH-M01 (factor TCB cases dispatch), Theme 4.7
- **Files**:
  - `SeLe4n/Kernel/Scheduler/Operations/Preservation.lean` (3633 LOC)
  - Hub `Scheduler/Operations.lean` re-export
- **Total effort**: ~1.5 days. **Cascade**: 0 external sites; ~3500 lines moved into 6 child modules.

**Sub-sub-task breakdown** (8 commits, one per AN5-A.N):

- **AN5-A.1 — Seam inventory** (0.1 day)
  - Catalog `Preservation.lean` declarations into 6 target child modules. Spot-check total declaration count.
  - **Acceptance**: seam map committed (ephemeral).

- **AN5-A.2 — Factor SCH-M01 `tcbCasesPreservation` helper** (0.25 day)
  - Before splitting the file, factor the duplicated `cases obj` dispatch (identified by audit at lines 267-308 and 439-448) into a named helper:
    ```lean
    -- In (or extracted into) Preservation/RunQueueHelpers.lean
    private lemma tcbCasesPreservation (st : SystemState) (oid : ObjId)
        (P : KernelObject → Prop) (hTcb : ∀ tcb, st.lookupKernelObject oid = some (.tcb tcb) → P (.tcb tcb))
        (hOther : ∀ obj, (∀ tcb, obj ≠ .tcb tcb) → P obj) : ... := ...
    ```
  - Apply at all 4 operation sites (`schedule`/`handleYield`/`timerTick`/`switchDomain`). Recover ~80 LOC. Land as a single commit before the split so the audit-mentioned divergence risk is closed first.
  - **Acceptance**: 4 call sites now use the helper; no behavior change; module gate PASS.

- **AN5-A.3 — Extract `Preservation/Schedule.lean`** (0.15 day)
  - Move `schedule`-family theorems (~500-600 LOC).
  - **Acceptance**: child module builds; parent imports.

- **AN5-A.4 — Extract `Preservation/HandleYield.lean`** (0.15 day)
  - Move `handleYield`-family theorems (~400-500 LOC).
  - **Acceptance**: child module builds.

- **AN5-A.5 — Extract `Preservation/TimerTick.lean`** (0.15 day)
  - Move `timerTick`-family theorems (~700-800 LOC — includes budget-aware variants).
  - **Acceptance**: child module builds.

- **AN5-A.6 — Extract `Preservation/SwitchDomain.lean`** (0.15 day)
  - Move `switchDomain`-family theorems (~400-500 LOC).
  - **Acceptance**: child module builds.

- **AN5-A.7 — Extract `Preservation/RunQueueHelpers.lean` + `Preservation/ReplenishmentPipeline.lean`** (0.25 day)
  - RunQueueHelpers: `remove_preserves_nodup`, `insert_preserves_nodup`, the new `tcbCasesPreservation` (~300 LOC).
  - ReplenishmentPipeline: `popDueReplenishments_*`, `refillSchedContext_*`, `processReplenishmentsDue_*` (~500 LOC).
  - **Acceptance**: both child modules build; full gate PASS.

- **AN5-A.8 — Finalize as thin re-export hub** (0.1 day)
  - `Preservation.lean` reduces to 6 imports + its own cross-subsystem bridge witnesses (keeps the latter because they transitively consume all 6 child modules).
  - `wc -l` verification: each child ≤ 1000 LOC; parent ≤ 100 LOC.
  - Refresh `CLAUDE.md` "Known large files" list.
  - **Acceptance**: file sizes at target; full gate PASS.

- **Regression test (cumulative)**: `lake build SeLe4n.Kernel.Scheduler.Operations.Preservation` at every commit; full gate after AN5-A.2 (to verify SCH-M01 factoring doesn't break anything) and after AN5-A.8.
- **Cascade**: 0 external (re-export pattern); 80 LOC recovered via SCH-M01 factoring.

### AN5-B — Scheduler MEDIUM batch (SCH-M02..M05)

- **Audit IDs**: SCH-M02..M05
- **Plan**:
  - **SCH-M02**: prefix RunQueue implementation helpers with `_rq_internal_` OR add `private` where the proof chain allows. Spot-check `remove_preserves_nodup`, `insert_preserves_nodup`.
  - **SCH-M03**: introduce `replenishmentPipelineOrder : SystemState → Prop` capturing pop → refill → process; prove `timerTick_preserves_replenishmentPipelineOrder`.
  - **SCH-M04**: split `Scheduler/Operations/Core.lean:340-447` into pure `Operations.lean` and proof-harness `Wrappers.lean`. Mandatory — no stretch/deferrable framing. The split sharpens the boundary between pure operation definitions and their structure-preserving wrappers; doing it now means every subsequent commit honors the boundary. Budget: 0.25 day; single commit.
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

### AN5-F — `eventuallyExits` closure for RPi5 canonical deployment (DEF-AK2-K.4)

- **Audit ID**: DEF-AK2-K.4 (absorbed from `AUDIT_v0.29.0_DEFERRED.md`)
- **Files**:
  - `SeLe4n/Kernel/Scheduler/Liveness/WCRT.lean` — main WCRT theorem
  - `SeLe4n/Platform/RPi5/Board.lean` — canonical RPi5 deployment parameters (54 MHz timer, default CBS period, default priority bands)
  - `SeLe4n/Kernel/Scheduler/Liveness/RPi5CanonicalConfig.lean` (new) — deployment-schema witness module
  - `docs/spec/SELE4N_SPEC.md` §5.7 — update WCRT deployment obligation language
- **Total effort**: ~2 days. **Cascade**: 1 new module + ~5 WCRT-theorem call sites that can drop the externalised hypothesis.

**Rationale for closure (not deferral)**:

`eventuallyExits` is the audit's documented "by-design externalisation" — the general kernel cannot prove it unconditionally because it is a property of the deployment's scheduling discipline (CBS bandwidth admission, priority-band configuration, timer ticks bounded per period). WS-AN's directive is to close all deferred items before v1.0.0; this closure discharges the hypothesis for the **canonical RPi5 deployment configuration** (the only deployment targeted by v1.0.0) while leaving the general theorem parameterised for future platforms.

**Sub-sub-task breakdown** (6 commits):

- **AN5-F.1 — Define deployment-config schema** (0.25 day)
  - In new `SeLe4n/Kernel/Scheduler/Liveness/RPi5CanonicalConfig.lean`:
    ```lean
    structure DeploymentSchedulingConfig where
      timerFrequencyHz : Nat      -- 54_000_000 on RPi5
      cbsPeriodTicks : Nat        -- default 10_000 ticks = ~185 µs at 54 MHz
      maxPriorityBands : Nat      -- 256 per seL4 MCS
      maxDomains : Nat            -- 16
      configDefaultTimeSlice : Nat -- default time slice per domain
      admissibleUtilisation : Nat  -- sum of ⌈budget/period⌉ across bound SCs, ≤ 1000 per-mille
    ```
  - Add decidable predicate `DeploymentSchedulingConfig.wellFormed` requiring positive frequency, positive period, utilisation ≤ 1000.
  - **Acceptance**: module compiles; schema in place.

- **AN5-F.2 — Canonical RPi5 instance** (0.25 day)
  - `def rpi5CanonicalConfig : DeploymentSchedulingConfig := { timerFrequencyHz := 54_000_000, cbsPeriodTicks := 10_000, maxPriorityBands := 256, maxDomains := 16, configDefaultTimeSlice := 1000, admissibleUtilisation := 750 }` (leaves 25% safety margin).
  - `theorem rpi5CanonicalConfig_wellFormed : rpi5CanonicalConfig.wellFormed := by decide`.
  - **Acceptance**: instance present; wellformedness proven.

- **AN5-F.3 — `eventuallyExits` canonical witness** (0.75 day)
  - Prove `theorem rpi5_canonicalConfig_eventuallyExits : ∀ st : SystemState, wellFormedSchedulerState st → bandProgressWitnessedBy rpi5CanonicalConfig st → eventuallyExits st`.
  - Proof sketch: under `admissibleUtilisation ≤ 750‰` and `wellFormedSchedulerState`, the scheduler's band-progress witness guarantees finite-step exit via the existing WCRT step bound combined with the canonical-config utilisation bound.
  - Key lemmas composed: `cbs_bandwidth_bounded_tight` (AK6-I), `wcrt_bound_unfold` (AF-02), `bandExhaustion_bounded` (Liveness/BandExhaustion).
  - **Acceptance**: theorem proven; no `sorry`/`axiom`; module gate PASS.

- **AN5-F.4 — WCRT theorem specialisation for RPi5** (0.25 day)
  - Add specialised theorem `wcrt_bound_rpi5 : ∀ tid, wcrt tid ≤ 256 * L_max + N * (B + P) (specialised for rpi5CanonicalConfig)` that drops the externalised `eventuallyExits` hypothesis because AN5-F.3 discharges it.
  - The general `wcrt_bound` theorem retains the parameterised form for non-RPi5 deployments.
  - **Acceptance**: specialised theorem proven; general theorem unchanged.

- **AN5-F.5 — Runtime witness at boot** (0.25 day)
  - Extend `bootFromPlatformChecked` on the RPi5 path to emit the canonical-config witness at boot time: the checked boot path validates the platform config matches `rpi5CanonicalConfig` (or records a diagnostic that the deployment is not canonical, retaining the parameterised WCRT semantics).
  - **Acceptance**: boot bridge emits witness; 2 new runtime tests (canonical-config PASS + non-canonical diagnostic emission).

- **AN5-F.6 — SPEC §5.7 update + DEF-AK2-K.4 closure** (0.25 day)
  - Update `docs/spec/SELE4N_SPEC.md` §5.7 to document the two-tier WCRT semantics: (i) general parameterised theorem with `eventuallyExits` hypothesis; (ii) RPi5-canonical specialisation with the hypothesis discharged. Cross-reference to `Scheduler/Liveness/RPi5CanonicalConfig.lean`.
  - DEF-AK2-K.4 is marked RESOLVED (not deferred) in the `AUDIT_v0.29.0_DEFERRED.md` update landing in AN12-G.
  - **Acceptance**: SPEC section present; DEF-AK2-K.4 closure noted in commit message.

- **Regression test**: full gate; `lake exe liveness_suite`.
- **Cascade**: 1 new module + ~5 WCRT call-site updates.

### AN5-G — AN5 closure

- **Files**: `CHANGELOG.md`; `CLAUDE.md` large-files-list refresh
- **Acceptance**: PR merged; full gate + rust gate PASS; DEF-AK2-K.4 explicitly noted as RESOLVED

---

## 9. Phase AN6 — Architecture / InformationFlow / CrossSubsystem

**Goal**: Address H-07 (template substantive discharge of one closure-form projection theorem), H-08 (assumption consumption index), H-09 (untypedRegionsDisjoint scope clarification or transitive strengthening). Batch ARCH/IF/CX MEDIUMs. Split the 3768-line `InformationFlow/Invariant/Operations.lean`.

**Effort**: 7–9 days. **Blocks**: AN9 (via `VSpaceBackend` wiring) + AN12.

### AN6-A — Substantive discharge of ALL SIX `*_preserves_projection` theorems (H-07; closes E-5 residual entirely)

- **Audit ID**: H-07 (HIGH); Theme 4.1 anchor; closes E-5 NI-H02 residual **in full** (not via template only)
- **Files**:
  - `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean` — all SIX closure-form theorems: `schedContextConfigure_preserves_projection`, `schedContextBind_preserves_projection`, `schedContextUnbind_preserves_projection`, `lifecycleRetype_preserves_projection`, `tcbSuspend_preserves_projection`, `tcbResume_preserves_projection`
  - `SeLe4n/Kernel/API.lean:2114-2153` — every arm of `dispatchCapabilityOnly_preserves_projection` drops its `hArmProj` closure once the corresponding per-op theorem is substantively proven
- **Total effort**: ~6–9 days. **Toolchain risk**: HIGH — Lean 4.28.0's `split` and `split_ifs` on `Except.ok`-wrapped deeply-nested match conditions is the documented blocker per AK6F.20b. **No partial discharge permitted.** If any one arm cannot close under the primary proof strategy, invoke the escalation ladder in §2.4 risk register (manual rcases → Classical.byContradiction+decide → hand-unfolded structural).

**Rationale**: the prior plan's "discharge one as a template, defer the other five as `DEF-H-07.partial`" approach is rejected. WS-AN's directive is to close every finding substantively; the 5-of-6 residual gap is precisely the form of deferral the maintainer has forbidden. The six arms are symmetric enough that the proof-engineering cost per arm drops after the first one ships (cascading from ~1.5 days for arm #1 to ~0.75 days for arm #6 as the recipe stabilises).

**Sub-sub-task breakdown** (8 commits, AN6-A.1..AN6-A.8):

- **AN6-A.1 — Target ordering + shared proof-sketch** (0.25 day)
  - Rank the six arms by expected difficulty (easiest first):
    1. `serviceQuery_preserves_projection` — per CLAUDE.md AK6F.11, already substantively proven; AN6-A copies the structure as the reference template (no proof change; just re-organise the file header to make the pattern discoverable).
    2. `schedContextConfigure_preserves_projection` — best ratio of named frames to closure depth.
    3. `tcbResume_preserves_projection` — uses AK6-F's `resumeThread_frame_insert` and `resumeThread_frame_ensureRunnable` directly.
    4. `schedContextBind_preserves_projection`
    5. `schedContextUnbind_preserves_projection`
    6. `tcbSuspend_preserves_projection`
    7. `lifecycleRetype_preserves_projection` — highest complexity (cross-subsystem retype path).
  - Capture the proof-sketch template in a non-ephemeral comment block inside `InformationFlow/Invariant/Operations.lean` (survives past AN12 so future auditors see the pattern).
  - **Acceptance**: ordering documented; template comment committed.

- **AN6-A.2 — Discharge arm #2 `schedContextConfigure_preserves_projection`** (1.5 day, the longest arm; establishes the recipe)
  - Primary strategy: `split_ifs` on the `Except.ok`-wrapped match condition, each arm invoking a named frame lemma.
  - Escalation ladder (if primary fails, take next step; budget up to 1.5 days per arm on the toolchain workaround):
    1. Manual `rcases hConfig : … <;> …` with `Except.ok_eq_iff_get?` rewrites.
    2. `Classical.byContradiction` + `decide` on the boolean skeleton + `exact absurd …`.
    3. Hand-unfolded structural proof using explicit `Except.bind_eq_ok` rewrites.
  - **Acceptance**: theorem body fully substantive (no `hArmProj` closure); `lake build SeLe4n.Kernel.InformationFlow.Invariant.Operations` PASS.

- **AN6-A.3 — Discharge arm #3 `tcbResume_preserves_projection`** (1 day)
  - Apply the recipe established in AN6-A.2. Lower expected effort because AK6-F's frame lemmas compose directly.
  - **Acceptance**: theorem substantively proven.

- **AN6-A.4 — Discharge arm #4 `schedContextBind_preserves_projection`** (1 day)
  - Same recipe. Uses AK6-F's `schedContextBind_frame_runQueue_rebucket` frame lemma.
  - **Acceptance**: theorem substantively proven.

- **AN6-A.5 — Discharge arm #5 `schedContextUnbind_preserves_projection`** (0.75 day)
  - Recipe stabilised by now; uses `schedContextUnbind_frame_*` lemmas.
  - **Acceptance**: theorem substantively proven.

- **AN6-A.6 — Discharge arm #6 `tcbSuspend_preserves_projection`** (0.75 day)
  - Uses `suspendThread_frame_remove` family of frame lemmas.
  - **Acceptance**: theorem substantively proven.

- **AN6-A.7 — Discharge arm #7 `lifecycleRetype_preserves_projection` (highest complexity)** (2 days)
  - Most complex: cross-subsystem retype touches objects, CDT, lifecycle, capabilityRefs, and optionally Scheduler (if retyping a TCB). Compose ~12 frame lemmas (vs. ~6 for the other arms). Extra budget accordingly.
  - If the toolchain genuinely cannot close this arm via any of the escalation steps: invoke AN6-A.ESCALATE (add a dedicated `_lifecycleRetype_preserves_projection_helpers.lean` file containing the ~300 LOC hand-unfolded proof). Budget: up to 3 days for AN6-A.7 total.
  - **Acceptance**: theorem substantively proven.

- **AN6-A.8 — Tighten `dispatchCapabilityOnly_preserves_projection` for all 6 arms + doc recipe** (0.5 day)
  - In `SeLe4n/Kernel/API.lean:2114-2153`, drop the `hArmProj` parameter for all six arms; `dispatchCapabilityOnly_preserves_projection` becomes a closed-form composition theorem with no caller-supplied closures.
  - Cascade: downstream NI theorems in `InformationFlow/Invariant/Composition.lean` drop their closures too. ~15–20 call-site updates.
  - Update CLAUDE.md's AK6F.20b tracking entry to "CLOSED at AN6-A (v1.0.0 release-hardened)".
  - Update `docs/audits/AUDIT_v0.29.0_ERRATA.md` E-5 closure note.
  - Add a multi-paragraph recipe block at the top of `InformationFlow/Invariant/Operations.lean` documenting the shared proof pattern.
  - **Acceptance**: dispatch theorem has no `hArmProj` parameter; all six arms have named substantive proofs; E-5 CLOSED; full gate PASS.

- **Regression test**: full gate; `lake exe information_flow_suite` PASS at every AN6-A.N commit.
- **Cascade**: ~15–20 proof updates in API.lean / Composition.lean (cumulative across all six arms).
- **Risk mitigation**: the escalation ladder (primary `split_ifs` → manual `rcases` → `Classical.byContradiction` + `decide` → hand-unfolded structural) is exhaustive; one of them closes every arm. No partial-discharge fallback exists in WS-AN.

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

### AN6-C — `untypedRegionsDisjoint` transitive strengthening (H-09) — Track B MANDATORY

- **Audit ID**: H-09 (HIGH)
- **Files**:
  - `SeLe4n/Model/Object/Types.lean` — `UntypedObject` structure gains `parent : Option ObjId` field
  - `SeLe4n/Kernel/CrossSubsystem.lean:476-485` — predicate definition + preservation
  - `SeLe4n/Kernel/Lifecycle/Operations.lean` — `retypeFromUntyped` sets the parent field on allocated children
  - `docs/spec/SELE4N_SPEC.md` §5 — updated to document transitive disjointness (NOT the weaker direct-parent-child-excluded scope)
- **Total effort**: ~4 days (Track B substantively proven + the 50+ site renaming Track A originally had). **Cascade**: ~130 sites (50 rename + 80 preservation cascades).

**Rationale**: the prior plan's two-track approach with Track B as "stretch" is rejected per maintainer directive. WS-AN closes H-09 substantively by introducing transitive ancestor disjointness and preserving it through every retype; the weaker direct-parent-child scope is unacceptable for v1.0.0.

**Sub-sub-task breakdown** (10 commits):

- **AN6-C.1 — Add `UntypedObject.parent : Option ObjId` field** (0.25 day)
  - Extend `UntypedObject` in `SeLe4n/Model/Object/Types.lean` with a `parent : Option ObjId` field. `none` for top-level (boot-allocated) untypeds; `some parentId` for retype-allocated children.
  - Bump default ctor + serialisation. Verify FrozenOps/Core and RobinHood bridges keep building.
  - **Acceptance**: field present; `lake build SeLe4n.Model.Object.Types` PASS.

- **AN6-C.2 — Wire parent-setting into `retypeFromUntyped`** (0.25 day)
  - In `Lifecycle/Operations.lean`, `retypeFromUntyped` now writes `parent := some parentId` when the newly-allocated child is itself a `.untyped` object; for non-untyped children, no parent field to set.
  - Update `retypeFromUntyped_childId_fresh` (AK8-A) to also record the parent-set fact as a post-condition.
  - **Acceptance**: retype path sets parent correctly; lifecycle module builds; new test `untyped_retype_sets_parent` passes.

- **AN6-C.3 — Define parent-chain walker with fuel bound** (0.25 day)
  - In `CrossSubsystem.lean`:
    ```lean
    def untypedAncestorChain (st : SystemState) (oid : ObjId) : Nat → List ObjId
      | 0 => []
      | n+1 => match st.getUntyped? oid with
              | some ut => match ut.parent with
                           | none => [oid]
                           | some pid => oid :: untypedAncestorChain st pid n
              | none => []
    def maxRetypeDepth : Nat := 256
    ```
  - Prove `untypedAncestorChain_bounded : (untypedAncestorChain st oid fuel).length ≤ fuel`.
  - **Acceptance**: walker defined; bounded; compiles.

- **AN6-C.4 — Define `untypedAncestorRegionsDisjoint` predicate** (0.5 day)
  - ```lean
    def untypedAncestorRegionsDisjoint (st : SystemState) : Prop :=
      ∀ ut₁ ut₂ : UntypedObject,
        ut₁ ∈ st.allUntypedObjects →
        ut₂ ∈ st.allUntypedObjects →
        ut₁.objId ≠ ut₂.objId →
        ut₂.objId ∉ untypedAncestorChain st ut₁.objId maxRetypeDepth →
        ut₁.objId ∉ untypedAncestorChain st ut₂.objId maxRetypeDepth →
        regionsDisjoint ut₁.region ut₂.region
    ```
  - Prove `default_untypedAncestorRegionsDisjoint` (vacuous over empty state).
  - **Acceptance**: predicate compiles; default witness proven.

- **AN6-C.5 — Prove preservation through `retypeFromUntyped`** (1 day)
  - Main preservation theorem: `retypeFromUntyped_preserves_untypedAncestorRegionsDisjoint`.
  - Proof sketch: the new child's region is strictly contained in parent's region via `allocate_child_fits_parent` (AK8-A); for any existing untyped `ut₁` not in the new child's ancestor chain, `ut₁.region` is disjoint from parent's region (by pre-state invariant), hence disjoint from child's region (by strict containment + transitivity).
  - Two key lemmas: (i) `region_strictly_contained_implies_disjoint_of_not_ancestor`; (ii) `allUntypedObjects_after_retype_extends_by_one_child`.
  - **Acceptance**: preservation theorem proven; module gate PASS.

- **AN6-C.6 — Retype to `.untyped` children: ancestor-chain extends by one** (0.5 day)
  - When retype target is `.untyped` (i.e., allocating a child untyped region inside a parent), the new child joins the parent's ancestor chain one level deeper.
  - Prove `retype_to_untyped_extends_ancestor_chain`: for the new child `c`, `untypedAncestorChain st' c.objId ⊇ untypedAncestorChain st parent.objId ++ [c.objId]`.
  - Update AN6-C.5's main theorem to handle the retype-to-untyped case separately (the new child is trivially in its own ancestor chain; disjointness with the ancestor set must exclude the chain).
  - **Acceptance**: retype-to-untyped case proven; module gate PASS.

- **AN6-C.7 — Add as 13th conjunct of `crossSubsystemInvariant`** (1 day, cascade-heavy)
  - Follow AN2-D playbook: 13-conjunct extension; extend `crossSubsystemInvariant` from 12 (after AN2-D's typedIdDisjointness) to 13 conjuncts; add `crossSubsystemInvariant_to_untypedAncestorRegionsDisjoint` projection.
  - Extend all 5 core bridges (`_objects_change_bridge`, `_retype_bridge`, `_objects_frame`, `_services_change`, `_composition_gap_documented`) with a new `hAncestorDisj : untypedAncestorRegionsDisjoint st'` hypothesis.
  - `_retype_bridge` discharges the new witness internally from AN6-C.5/C.6.
  - Cascade through 34 per-operation bridge lemmas (uniform call-pattern edit).
  - **Acceptance**: 13-conjunct invariant bundle builds; cascade complete; full gate PASS.

- **AN6-C.8 — Rename predicate + retire legacy `untypedRegionsDisjoint_directParentChildExcluded` form** (1 day, batched)
  - The new predicate subsumes the old direct-parent-child-excluded form (Track A in the prior plan). Remove the old form entirely; all 50+ call sites migrate to `untypedAncestorRegionsDisjoint`.
  - Batches by subsystem: CrossSubsystem default/frame (~10), Architecture/Invariant retype bridges (~8), Capability/Invariant (~8), Lifecycle (~10), Platform/Boot + tests (~14).
  - **Acceptance**: `grep -rn "untypedRegionsDisjoint\|untypedRegionsDisjoint_directParentChildExcluded" SeLe4n/` returns only the primary definition + its transitive variant; deprecation warnings at zero.

- **AN6-C.9 — Field-set catalog + runtime checks + tests** (0.5 day)
  - Bump `crossSubsystemFieldSets` count 12 → 13; `untypedAncestorRegionsDisjoint_fields := [.objects]`.
  - Extend `crossSubsystem_pairwise_coverage_complete` from C(12,2)=66 to C(13,2)=78.
  - Update `SeLe4n/Testing/InvariantChecks.lean` runtime check from 12 → 13 predicates; `checkUntypedAncestorRegionsDisjoint` decidable runtime predicate.
  - Add 4 regression tests in `tests/Ak7RegressionSuite.lean`: default PASS, 2-level retype chain PASS, 3-level retype chain PASS, deliberate aliased-region rejection FAIL.
  - **Acceptance**: full gate; `lake exe ak7_regression_suite` PASS.

- **AN6-C.10 — SPEC §5 update + H-09 closure note** (0.15 day)
  - `docs/spec/SELE4N_SPEC.md` §5 updated to document transitive ancestor disjointness (not the weaker scope). Cross-reference from the invariant definition docstring.
  - Commit message notes H-09 CLOSED substantively; audit ERRATA would normally document scope clarifications but H-09 now matches its original audit-text scope, so no ERRATA update is required.
  - **Acceptance**: SPEC updated; H-09 closed.

- **Regression test (cumulative)**: full gate after every AN6-C.N commit; `lake exe ak7_regression_suite` PASS at AN6-C.9.
- **Cascade**: ~130 sites explicitly counted above (50 rename + 80 preservation cascade).

### AN6-D — Architecture MEDIUM batch (ARCH-M01..M03) — VSpaceBackend production-wired

- **Audit IDs**: ARCH-M01..M03
- **Files**:
  - `SeLe4n/Kernel/Architecture/VSpaceBackend.lean:52-61` (typeclass)
  - `SeLe4n/Kernel/Architecture/VSpace.lean` (current concrete implementation)
  - `SeLe4n/Kernel/Architecture/VSpaceARMv8.lean` (backend instance from AG6-C/D)
  - `SeLe4n/Kernel/Architecture/PageTable.lean` (walk)
  - `SeLe4n/Kernel/API.lean` + `Kernel/Lifecycle/Operations.lean` (VSpace consumers)
- **Total effort**: ~2 days (ARCH-M01 is non-trivial because it changes production dispatch).

**Sub-sub-task breakdown** (5 commits):

- **AN6-D.1 — ARCH-M01 wire `VSpaceBackend` as the production indirection** (1 day, cascade-heavy)
  - Refactor `VSpace.lean` to operate on `VSpaceBackend`-indirected primitives (`backend.mapPage`, `backend.unmapPage`, `backend.lookupPage`) instead of concrete `VSpaceRoot` operations. The `VSpaceARMv8` instance (AG6-C/D) becomes the default production backend via a `[backend : VSpaceBackend] := ARMv8VSpaceBackend` section binding in `VSpace.lean`.
  - Production kernel entry points (vspaceMap, vspaceUnmap) continue to work unchanged because `ARMv8VSpaceBackend` implements the same operations the concrete form used.
  - Simulation / test platforms can substitute their own `VSpaceBackend` instance (e.g., `SimVSpaceBackend`) by overriding the section binding.
  - Cascade: ~15-20 call sites in `VSpace.lean` + consumers; each receives the backend argument either explicitly or via instance resolution.
  - **Acceptance**: `VSpaceBackend` typeclass is now production-load-bearing; `lake build` PASS; no `-- STATUS: deferred` comment remains on the typeclass module.

- **AN6-D.2 — ARCH-M01 delete dead-code `#[allow(unused)]`-style tags** (0.1 day)
  - Remove any "staged for H3" or "deferred" module-level comments from `VSpaceBackend.lean` since the module is now production.
  - **Acceptance**: `grep -n "STATUS: deferred\|staged for H3" SeLe4n/Kernel/Architecture/VSpaceBackend.lean` returns empty.

- **AN6-D.3 — ARCH-M02 `pageTableWalk_depth_bound` theorem** (0.25 day)
  - In `PageTable.lean`, add:
    ```lean
    theorem pageTableWalk_depth_bound (root : PageTableLevel) (vaddr : VAddr) :
        (pageTableWalk root vaddr).depth ≤ 4 := by
      induction root with | ... ;
      simp [pageTableWalk]
    ```
  - The bound is provable by structural recursion on the 4-level ARMv8 page table. Any runtime implementation consuming `pageTableWalk` can invoke this theorem as a witness.
  - **Acceptance**: theorem proven; module gate PASS.

- **AN6-D.4 — ARCH-M03 `KernelError.invalidMessageInfoDetailed` debug variant** (0.3 day)
  - Add `KernelError.invalidMessageInfoDetailed (_ : IpcBufferReadError) : KernelError` variant (discriminant assigned as 51 if next available).
  - Gate emission behind `set_option sele4n.debug.detailedErrors true` at the decode site — production builds (option off) collapse to the single `KernelError.invalidMessageInfo` variant per ABI convention; debug builds preserve the internal `IpcBufferReadError` tag for diagnostics.
  - Rust-side ABI sync: add matching variant to `rust/sele4n-types/src/error.rs` (InvalidMessageInfoDetailed=51); update conformance tests.
  - **Acceptance**: variant defined both sides; Rust gate PASS; full gate PASS.

- **AN6-D.5 — Integration tests for production VSpaceBackend** (0.35 day)
  - Add 3 regression tests in a new `tests/VSpaceBackendSuite.lean`:
    - `vspace_backend_arm_v8_default_instance` — default production path uses ARMv8 backend
    - `vspace_backend_sim_override` — simulation platform can swap in a SimVSpaceBackend
    - `vspace_backend_wxCompliant_transfers` — W^X compliance transfers through the indirection
  - Wire into `test_tier2_negative.sh`.
  - **Acceptance**: 3 tests PASS; full gate PASS.

- **Regression test**: full gate; `lake exe vspace_backend_suite`.
- **Cascade**: ARCH-M01 ~15-20 sites; ARCH-M02 ~1; ARCH-M03 ~3 + Rust ABI sync.

### AN6-E — InformationFlow MEDIUM batch (IF-M01..M03)

- **Audit IDs**: IF-M01..M03
- **Total effort**: ~1 day (IF-M03 split dominates).

**Sub-sub-task breakdown** (3 IF-M items; IF-M03 expanded into AN3-C-style playbook):

- **AN6-E.1 — IF-M01 `serviceObservable` covert-channel scope doc** (0.1 day)
  - Add `SELE4N_SPEC.md` §7 subsection "§7.X — Non-interference scope and exclusions":
    > "§7.X: `serviceObservable` covers boolean service presence only, not internal state. Cross-service covert channels — for example, one service observing another's restart cadence via service-presence sampling — are NOT covered by the NI property. These are accepted covert channels; see `AUDIT_v0.30.6_COMPREHENSIVE.md` §2.5 IF-M01."
  - Cross-reference from the `serviceObservable` definition's docstring.
  - **Acceptance**: SPEC + docstring updated.

- **AN6-E.2 — IF-M02 NI-L3 negative-case regression test** (0.15 day)
  - Add 4 negative-case tests in `tests/InformationFlowSuite.lean` (one per NI-L3-accepted covert channel):
    - build two states differing only in the channel's observable (e.g., scheduler PIP boost, scheduler timing, domain schedule, service restart cadence);
    - project both via `projectKernelObject`;
    - assert the projections DIFFER (i.e., the channel remains observable today).
  - These guard against an accidental future "fix" that silently closes the channel and invalidates the acceptance documentation.
  - **Acceptance**: 4 tests committed; `lake exe information_flow_suite` PASS with the 4 new assertions.

- **AN6-E.3 — IF-M03 Operations.lean 3768-line split (4 child files)** (0.75 day)
  - Follow AN3-C playbook for 4 children (~940 LOC each):
    - `Operations/IPC.lean` (per-op preservation for IPC-family ops: send, receive, call, reply, notification signal/wait)
    - `Operations/Capability.lean` (per-op preservation for cap ops: copy, move, mutate, mint, delete, revoke)
    - `Operations/SchedContext.lean` (per-op preservation for SC ops: configure, bind, unbind, yieldTo, priority ops)
    - `Operations/Architecture.lean` (per-op preservation for arch ops: vspaceMap/Unmap, exception dispatch, interrupt, service query/revoke/register, lifecycle retype, suspend/resume)
  - 5 commits: seam inventory + 4 extractions.
  - **Acceptance**: each child ≤ 1000 LOC; hub ≤ 50 LOC; full gate after each commit.

- **Regression test**: full gate; `lake exe information_flow_suite` PASS.
- **Cascade**: IF-M01 ~0, IF-M02 ~1 test, IF-M03 ~0 external.

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
- **Total effort**: ~1.25 days. **Cascade**: PLT-M07 wires 6 modules into the build graph.

**Sub-sub-task breakdown** (7 commits):

- **AN7-D.1 — PLT-M01 deprecate `bootFromPlatformUnchecked` alias** (0.1 day)
  - Add `@[deprecated "use bootFromPlatformChecked; see PLT-M01"]` annotation.
  - Also move into a `SeLe4n.Testing.Deprecated` namespace in the same commit (mandatory — production adopters must not accidentally import the unchecked form; the Testing.Deprecated namespace makes the intent-tag explicit).
  - **Acceptance**: deprecation warning fires on legacy call sites; test-path consumers audited.

- **AN7-D.2 — PLT-M02 / PLT-M03 full RPi5/VSpaceBoot shim + non-empty config bridge** (2.5 days, mandatory)
  - Create new `SeLe4n/Platform/RPi5/VSpaceBoot.lean` module that establishes the boot VSpaceRoot with a full invariant witness for the canonical RPi5 kernel image layout.
  - Module contents:
    - `def rpi5BootVSpaceRoot : VSpaceRoot` — the boot page-table (identity-mapped + kernel text at 0x80000 + kernel data + MMIO regions, consistent with `rust/sele4n-hal/src/mmu.rs::BOOT_L1_TABLE` descriptors).
    - `theorem rpi5BootVSpaceRoot_wellFormed : VSpaceRoot.wellFormed rpi5BootVSpaceRoot` — validates permission bits, ASID assignment, alignment.
    - `theorem rpi5BootVSpaceRoot_wxCompliant : rpi5BootVSpaceRoot.wxCompliant` — W^X (AK3-B four-layer defense) discharged at boot.
    - `theorem rpi5BootVSpaceRoot_bootSafe : bootSafeObject (.vspaceRoot rpi5BootVSpaceRoot)` — bridge into the `bootFromPlatformChecked` per-object check.
  - Refine `bootFromPlatformChecked` in `SeLe4n/Platform/Boot.lean` to include VSpaceRoot in its `bootSafeObject` sweep (previously excluded per AK9-B). Two paths:
    - If `config.vspaceRoot = some rpi5BootVSpaceRoot`: the `bootSafe` check is discharged by `rpi5BootVSpaceRoot_bootSafe`.
    - If `config.vspaceRoot = none`: the boot path fails closed with `.invalidConfiguration`.
  - Extend `bootFromPlatform_crossSubsystemInvariant_bridge` from empty-config-only to full-config case: the new theorem `bootFromPlatformChecked_crossSubsystemInvariant_rpi5canonical` proves the 13-conjunct `crossSubsystemInvariant` holds for the non-empty RPi5 boot state.
  - Cascade: 5 frame lemmas + the main bridge theorem + 1 AK9-B update.
  - 3 new regression tests in `tests/Ak9PlatformSuite.lean`: (a) rpi5BootVSpaceRoot wellFormed, (b) non-empty config boot bridge PASS, (c) missing-vspaceRoot config rejection.
  - DEF-P-L9 is simultaneously closed by this sub-task (the VSpaceRoot boot exclusion is eliminated — VSpaceRoot is now included in `bootSafeObject`).
  - **No fallback to DEF-PLT-M02**: WS-AN closes the non-empty-config bridge substantively; the prior `DEF-PLT-M02` tracking entry is marked RESOLVED in AN12-G.
  - **Acceptance**: new module builds; `bootFromPlatformChecked` includes VSpaceRoot in its check; 3 new tests pass; full gate PASS; DEF-P-L9 noted RESOLVED in commit message.

- **AN7-D.3 — PLT-M04 (already covered by AN7-A)** — no additional work; record as "closed by AN7-A" in the commit message.

- **AN7-D.4 — PLT-M05 `parseFdtNodes` size-derived fuel migration** (0.15 day)
  - Walk all callers; replace fixed `2000` fuel with `hdr.sizeDtStruct / 4` (matching the `findMemoryRegPropertyChecked` default from AK9-F).
  - **Acceptance**: all callers migrated; `lake exe ak9_platform_suite` PASS.

- **AN7-D.5 — PLT-M06 `extractPeripherals` arbitrary-depth lift** (0.5 day)
  - Refactor `extractPeripherals` to perform a fuel-bounded recursive walk of the DTB tree (default fuel `dtb.header.sizeDtStruct / 16`, which bounds the node count). Replace the hardcoded depth-2 traversal with a proper recursive descent so any platform with deeper DTB nesting is supported.
  - Correctness theorem: `extractPeripherals_terminates_under_fuel : ∀ fuel, extractPeripherals dtb fuel` terminates; `extractPeripherals_fuel_sufficient_for_BCM2712 : dtb.header.sizeDtStruct / 16 ≥ bcm2712_max_node_count := by decide` ensures default fuel is sufficient for the target platform.
  - Bonus: the new recursive form also composes cleanly with the `DeviceTreeParseError.fuelExhausted` variant (AJ3-A) for explicit error reporting when a pathological DTB exhausts the fuel budget.
  - **No deferral**: the prior "TODO(post-1.0)" is superseded; WS-AN closes PLT-M06 before v1.0.0.
  - **Acceptance**: recursive walk implemented; termination proof present; fuel-sufficiency theorem proven; `lake exe ak9_platform_suite` PASS with a new depth-3+ DTB fixture test.
  - Cross-reference in `SELE4N_SPEC.md` §6.
  - **Acceptance**: docstring + SPEC entry.

- **AN7-D.6 — PLT-M07 staged-modules wiring (6 modules)** (0.75 day)
  - Create new meta-module `SeLe4n/Platform/Staged.lean`:
    ```lean
    /-! PLT-M07: Staged modules wired into the build graph so refactors
        in their dependencies break loudly. Each module is tagged
        "STATUS: staged for H3 hardware binding" in its own header. -/
    import SeLe4n.Platform.Sim.Contract
    import SeLe4n.Platform.FFI
    import SeLe4n.Platform.RPi5.Contract
    import SeLe4n.Kernel.Architecture.CacheModel
    import SeLe4n.Kernel.Architecture.ExceptionModel
    import SeLe4n.Kernel.Architecture.TimerModel
    ```
  - Add `Staged.lean` to the test-harness build target (via `Main.lean`'s test entry or a new `lake exe staged_probe` that no-ops but forces the import graph).
  - For each of the 6 child modules: add `-- STATUS: staged for H3 hardware binding` header comment + cross-reference to `SELE4N_SPEC.md` §8.15 activation roadmap.
  - Also wire `SeLe4n/Kernel/Concurrency/Assumptions.lean` (created in AN12-B) into `Staged.lean` per AN12-B.4. Note: after AN9-J's SMP bring-up lands, most entries in this module transition from "SMP-latent" to "SMP-implemented, runtime-gated by `smp_enabled=false` at v1.0.0" — the module remains present as a confirmation inventory rather than a pending-work surface.
  - **Acceptance**: `lake build SeLe4n.Platform.Staged` PASS; each child module gets per-commit build verification via `lake build <Module.Path>`.

- **AN7-D.7 — Staged-modules build-graph CI check** (0.1 day)
  - Extend `scripts/test_tier1_build.sh` (or an equivalent build-verification step) to assert `lake build SeLe4n.Platform.Staged` succeeds. This forces the 6 staged modules to compile on every PR even though they're not in `Main.lean`'s chain.
  - **Acceptance**: CI check active; synthetic breakage of a staged module produces CI failure.

- **Regression test**: full gate; `lake exe ak9_platform_suite` PASS.
- **Cascade**: ~6 staged modules come under CI build.

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
- **Total effort**: ~0.5 day.

**Sub-sub-task breakdown** (4 commits):

- **AN8-A.1 — Define `UartGuard<'a>` + `with_guard()` method** (0.15 day)
  - Add:
    ```rust
    pub struct UartGuard<'a> {
        inner: &'a mut Uart,
        lock: &'a UartLock,
    }
    impl Drop for UartGuard<'_> {
        fn drop(&mut self) {
            self.lock.release();  // release the CAS-acquired spin lock
        }
    }
    impl UartLock {
        pub fn with_guard(&self) -> UartGuard<'_> {
            self.acquire();
            UartGuard {
                inner: unsafe { &mut *BOOT_UART_INNER.0.get() },
                lock: self,
            }
        }
    }
    ```
  - The `'a` lifetime on `UartGuard` pins the mutable-borrow lifetime to the guard's own lifetime; dropping the guard first drops the mutable borrow, then runs the release via `Drop`.
  - **Acceptance**: `UartGuard` struct + `with_guard()` compile; SAFETY comments pin the mutable-borrow lifetime explicitly.

- **AN8-A.2 — Thin-wrapper `with()` delegating to `with_guard()`** (0.1 day)
  - Rewrite the existing `with()`:
    ```rust
    pub fn with<F, R>(&self, f: F) -> R where F: FnOnce(&mut Uart) -> R {
        let mut guard = self.with_guard();
        f(guard.inner)
    }
    ```
  - The `unsafe { f(&mut *BOOT_UART_INNER.0.get()) }` block is eliminated; all `unsafe` is now localized to `with_guard()`'s single pointer dereference.
  - **Acceptance**: `with()` compiles as thin wrapper; cargo gate PASS.

- **AN8-A.3 — Add runtime test for guard semantics** (0.15 day)
  - New cargo test asserting Drop runs on scope exit:
    ```rust
    #[test]
    fn uart_guard_drops_lock_on_scope_exit() {
        let lock = UartLock::new();
        let before = lock.is_held();
        {
            let _g = lock.with_guard();
            assert!(lock.is_held(), "lock held while guard alive");
        }
        assert!(!lock.is_held(), "lock released after guard drops");
        assert_eq!(before, lock.is_held());
    }
    ```
  - Plus a `#[should_panic]` test verifying double-release does not deadlock (if relevant to the spin primitive).
  - **Acceptance**: both tests pass.

- **AN8-A.4 — `kprint!` macro consumer audit** (0.1 day)
  - Walk every `kprint!` call site and verify it continues to go through `with(...)` — no call-site changes expected because `with()` is a thin wrapper around `with_guard()`.
  - Spot-check panic-path behavior: under `panic = "abort"`, `Drop` does not run; the release therefore does not fire on panic. That is correct for the fatal-invariant-abort design per gic.rs:299-308 rationale (H-19 context). Document in `UartGuard`'s docstring.
  - **Acceptance**: all `kprint!` sites unchanged; panic-behavior doc present.

- **Regression test**: rust gate; new cargo tests pass.
- **Cascade**: 0 external call-site changes.

### AN8-B — MPIDR_CORE_ID_MASK shared symbol (H-18) — Option A MANDATORY + belt-and-suspenders Option B

- **Audit ID**: H-18 (HIGH)
- **Files**: `rust/sele4n-hal/src/cpu.rs`, `rust/sele4n-hal/src/boot.S:39`, `rust/sele4n-hal/build.rs` (new or extended)
- **Total effort**: ~1 day. **No fallback ladder** — both Option A (shared symbol) and Option B (build-time assertion) ship together for defense-in-depth. Option A is the primary mechanism; Option B catches any accidental drift introduced in future refactors (e.g., someone replacing the `adrp+ldr` with the old `mov+movk` literals).

**Sub-sub-task breakdown** (5 commits, A.1..A.3 + B.1..B.2, no decision gate):

- **AN8-B.1 — Expose `MPIDR_CORE_ID_MASK_SYM` as `.rodata` symbol** (0.15 day)
  - In `cpu.rs`:
    ```rust
    pub const MPIDR_CORE_ID_MASK: u64 = 0x00FFFFFF;
    #[no_mangle]
    pub static MPIDR_CORE_ID_MASK_SYM: u64 = MPIDR_CORE_ID_MASK;
    ```
  - Verify the symbol resolves via `nm target/aarch64-unknown-none/release/sele4n-hal.a | grep MPIDR_CORE_ID_MASK_SYM` shows a `D` or `R` (data / rodata) entry.
  - **Acceptance**: symbol present in compiled binary.

- **AN8-B.2 — Update `boot.S` to load via `adrp` + `ldr`** (0.25 day)
  - Replace:
    ```
    mov x2, #0xFFFF
    movk x2, #0xFF, lsl #16
    ```
    with:
    ```
    adrp x2, MPIDR_CORE_ID_MASK_SYM
    ldr x2, [x2, :lo12:MPIDR_CORE_ID_MASK_SYM]
    ```
  - Verify the linker script (`link.ld`) places `.rodata` within `adrp`+`lo12` reach of `boot.S` (typically within a 4 GiB window; for a small kernel this is always satisfied). If linker layout requires adjustment, update `link.ld` in the same commit.
  - **Acceptance**: `cargo build` PASS; `objdump -d` shows the new instruction sequence; QEMU boot still reaches core-0 wake-up.

- **AN8-B.3 — QEMU-side verification** (0.2 day)
  - Run `scripts/test_qemu.sh` to confirm the boot-core gate still works — a core-0 boot and a simulated secondary-core boot with MPIDR Aff0=1 Aff1=0 Aff2=0 both behave correctly under the shared mask.
  - **Acceptance**: QEMU boot successful; no regression.

- **AN8-B.4 — Belt-and-suspenders: `const _: () = assert!(...)` in `cpu.rs`** (0.1 day)
  - Add:
    ```rust
    const _: () = assert!(MPIDR_CORE_ID_MASK == 0x00FFFFFF);
    ```
  - Redundant with Option A (since the symbol is derived from the constant), but catches future developers who might replace `MPIDR_CORE_ID_MASK_SYM` with a literal `0xFFFFFF` (typo) or similar.
  - **Acceptance**: build fails if the constant is accidentally modified.

- **AN8-B.5 — `build.rs` scan-and-match for assembly literal regression** (0.3 day)
  - In `rust/sele4n-hal/build.rs`, add a scan that fails the build if the legacy `mov x2, #0xFFFF` + `movk x2, #0xFF, lsl #16` pattern reappears anywhere in `src/boot.S` (catches "someone reverts to the literals" regression):
    ```rust
    fn main() {
        println!("cargo:rerun-if-changed=src/boot.S");
        let boot_s = std::fs::read_to_string("src/boot.S").unwrap();
        let legacy_pattern = regex::Regex::new(r"mov\s+x2,\s*#0xFFFF\s*\n\s*movk\s+x2,\s*#0xFF,\s*lsl\s*#16").unwrap();
        assert!(!legacy_pattern.is_match(&boot_s),
            "boot.S contains the legacy MPIDR_CORE_ID_MASK literal pattern; use adrp+ldr via MPIDR_CORE_ID_MASK_SYM per AN8-B (H-18)");
    }
    ```
  - Pin `regex` to `[build-dependencies]` in `rust/sele4n-hal/Cargo.toml`.
  - **Acceptance**: build.rs rejects the legacy pattern; synthetic regression (restore old pattern) fails CI with explicit message.

- **Regression test**: rust gate; `scripts/test_qemu.sh` PASS (or skip-with-log in CI-without-emulator).
- **Cascade**: 3 files (cpu.rs + boot.S + build.rs + Cargo.toml). **No DEF-* fallback**; both mechanisms ship.

### AN8-C — `dispatch_irq` EOI-before-handler refactor (H-19, audit Option b MANDATORY)

- **Audit ID**: H-19 (HIGH) — both audit Option a (doc + clippy lint) AND Option b (EOI emission reordering) now land together
- **Files**: `rust/sele4n-hal/src/gic.rs:362-386`, `rust/sele4n-hal/src/lib.rs` (IRQ handler function attributes)
- **Total effort**: ~1 day.

**Rationale for taking Option b**: the prior plan's "defer Option b to post-1.0 hardware-binding workstream" is rejected. WS-AN closes H-19 substantively by reordering the `ack → handle → EOI` sequence to `ack → EOI → handle` (permitted by GIC-400 for level-sensitive and edge-reconfigured interrupts per §3.1 of the GIC-400 TRM, provided the handler does not re-enter the ISR line). This eliminates the "EOI lost on handler panic" class entirely because EOI has already fired before the handler body runs.

**Sub-sub-task breakdown** (5 commits):

- **AN8-C.1 — Refactor `dispatch_irq` to emit EOI before handler invocation** (0.4 day)
  - Rewrite the ack/EOI sequencing:
    ```rust
    pub fn dispatch_irq<F: FnOnce(IntId)>(handler: F) -> AckResult {
        let ack = acknowledge_irq();
        match ack {
            AckResult::Handled(intid) => {
                end_of_interrupt(intid);  // EOI BEFORE handler body
                handler(intid);           // Handler runs with INTID already cleared
                AckResult::Handled(intid)
            }
            AckResult::OutOfRange(raw) => {
                end_of_interrupt_raw(raw); // Still EOI out-of-range to prevent GIC lockup
                AckResult::OutOfRange(raw)
            }
            AckResult::Spurious => AckResult::Spurious, // No EOI for spurious per GIC-400 §3.1
        }
    }
    ```
  - The `EoiGuard` from AK5-B is no longer needed for the Handled / OutOfRange paths (EOI already fires before handler). Retain the Spurious path unchanged.
  - **Acceptance**: `dispatch_irq` no longer relies on Drop for EOI in the normal path; handler panic no longer leaves INTID active on the GIC.

- **AN8-C.2 — Update Lean-side `InterruptDispatch.lean` model to reflect new ordering** (0.2 day)
  - In `SeLe4n/Kernel/Architecture/InterruptDispatch.lean`, refactor `interruptDispatchSequence` to emit `endOfInterrupt` before the handler invocation (mirror Rust semantics).
  - Update proof `interruptDispatchSequence_always_ok` (AI2-A) to reflect the new ordering; the theorem still holds — EOI still fires on every path.
  - Add new theorem `interruptDispatchSequence_eoi_before_handler` witnessing the ordering property.
  - **Acceptance**: Lean model matches Rust reality; proof updates; module gate PASS.

- **AN8-C.3 — Clippy lint guard at IRQ-handler-function level** (0.1 day)
  - Tag each registered IRQ handler (in `rust/sele4n-hal/src/lib.rs` or wherever handlers are declared) with `#[deny(clippy::panic)]` so direct `panic!()` inside handler bodies becomes a compile error. Defense-in-depth even though AN8-C.1 eliminates the panic-loses-EOI class structurally.
  - **Acceptance**: clippy lint active; synthetic panic inside a handler fails `cargo clippy`.

- **AN8-C.4 — Handler re-entrancy soundness check** (0.2 day)
  - GIC-400 permits EOI-before-handler ONLY for interrupts that do not re-enter their INTID during the handler body. Validate each registered handler: if any handler could plausibly re-trigger its own INTID (e.g., a timer handler that rewrites CNTP_CVAL_EL0 before handler exit), verify it runs with the GIC's priority-mask high enough to prevent re-entry, OR document explicit re-entry handling.
  - Add an audit comment in `dispatch_irq` enumerating every registered handler and its re-entrancy category. Document the invariant: "handlers MUST NOT re-trigger their own INTID before the handler returns; GIC-400 priority masking enforces this under the current PMR configuration."
  - For timer handlers (the obvious re-entry candidate), verify the PMR configuration holds the priority above timer's during the handler; document the interlock.
  - **Acceptance**: re-entrancy analysis present; PMR-interlock documented per handler.

- **AN8-C.5 — Regression tests + doc block** (0.1 day)
  - Add a cargo test that verifies the EOI-before-handler ordering by instrumenting a test handler that records the order of events via a `&AtomicUsize` counter.
  - Add a multi-paragraph doc block at the top of `dispatch_irq` explaining the ordering decision, GIC-400 §3.1 reference, and re-entrancy invariant.
  - **Acceptance**: test passes; doc block present; rust gate PASS.

- **Regression test**: rust gate; `cargo test --workspace`; `cargo clippy --workspace -- -D warnings` PASS
- **Cascade**: 2 files in Rust (`gic.rs`, `lib.rs`) + 1 Lean file (`InterruptDispatch.lean`). **No deferral**; audit's Option b lands.

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

## 12. Phase AN9 — Hardware-binding closure (NEW)

**Goal**: substantively close every hardware-binding item previously carried in `AUDIT_v0.29.0_DEFERRED.md` plus the four hardware-binding items surfaced by AN1-C (DEF-R-HAL-L17..L20). This phase pairs Lean-side correctness proofs with Rust HAL implementation so each deferred item has a proof-linked implementation at v1.0.0 ship.

**Scope**: 10 sub-tasks (AN9-A through AN9-J) covering TLB+Cache composition (DEF-A-M04), `tlbBarrierComplete` substantive binding (DEF-A-M06), MMU/Device BarrierKind composition (DEF-A-M08/M09), `suspendThread` atomicity via HAL bracket (DEF-C-M04), VSpaceRoot boot-bridge closure cross-check (DEF-P-L9 — already discharged in AN7-D.2; AN9-E records the cross-reference), SVC FFI wiring (DEF-R-HAL-L14), bounded WFE (DEF-R-HAL-L17), parameterized barriers (DEF-R-HAL-L18), OSH widening (DEF-R-HAL-L19), and secondary-core bring-up / SMP enablement (DEF-R-HAL-L20).

**Effort**: 18–22 dev-days. **Blocks**: AN11, AN12. **Depends on**: AN6 (invariant layer ready for composition) + AN8 (Rust HAL barriers refactored; EOI-before-handler landed).

### AN9-A — DEF-A-M04: TLB+Cache composition full closure

- **Audit ID**: DEF-A-M04 (absorbed from `AUDIT_v0.29.0_DEFERRED.md`, Category A hardware-binding)
- **Files**:
  - `SeLe4n/Kernel/Architecture/CacheModel.lean` (currently `CacheBarrierKind` + `cacheCoherentForExecutable`)
  - `SeLe4n/Kernel/Architecture/TlbModel.lean` (currently `tlbBarrierComplete` stub)
  - `SeLe4n/Kernel/Architecture/PageTable.lean` (page-table update entry points)
  - `rust/sele4n-hal/src/cache.rs` (`clean_pagetable_range`, `ic_iallu`, new FFI-visible barrier witnesses)
  - `rust/sele4n-hal/src/tlb.rs` (TLB invalidation emission + new FFI witnesses)
  - New `SeLe4n/Kernel/Architecture/TlbCacheComposition.lean` — composition theorem file
- **Total effort**: ~2.5 days.

**Rationale for closure (not deferral)**: AK3-G landed `CacheBarrierKind` + `cacheCoherentForExecutable` + `pageTableUpdate_icache_coherent_under_sequence` as a PARTIAL remediation. The composition theorem assumed an externalised sequence hypothesis that only real-hardware emission can discharge. AN9-A wires the HAL's actual emission sites through a FFI layer into Lean so the composition theorem becomes unconditional.

**Sub-sub-task breakdown** (6 commits):

- **AN9-A.1 — Add `@[extern]` FFI layer for cache+TLB sequence witnesses** (0.4 day)
  - In `SeLe4n/Kernel/Architecture/CacheModel.lean`, add:
    ```lean
    @[extern "sele4n_hal_cache_clean_pagetable_range_witness"]
    opaque cacheCleanPagetableRangeWitness : ∀ (addr len : Nat), IO CacheBarrierKind
    @[extern "sele4n_hal_ic_iallu_witness"]
    opaque icIalluWitness : IO CacheBarrierKind
    ```
  - Rust side emits `cache::clean_pagetable_range(...)` + `cache::ic_iallu()` and returns a Lean-compatible `CacheBarrierKind` variant tag.
  - **Acceptance**: FFI symbols declared both sides; Lean imports compile; Rust crate exports symbols; `cargo test --workspace` links.

- **AN9-A.2 — Extend `CacheBarrierKind` with sequence-composition constructor** (0.3 day)
  - Add `CacheBarrierKind.sequenced (pre : CacheBarrierKind) (post : CacheBarrierKind) : CacheBarrierKind` + associativity lemma.
  - Update `cacheCoherentForExecutable` to accept the sequenced form and prove composition preserves coherency.
  - **Acceptance**: constructor present; composition lemma proven.

- **AN9-A.3 — Substantive `pageTableUpdate_icache_coherent` theorem** (0.7 day)
  - Replace the AK3-G externalised-sequence version with a theorem that takes no externalised hypothesis. Proof composes `cacheCleanPagetableRangeWitness` + `icIalluWitness` + the sequenced composition lemma.
  - **Acceptance**: theorem holds unconditionally; old externalised form marked `@[deprecated]`.

- **AN9-A.4 — Page-table update entry points emit the witness** (0.4 day)
  - Every kernel operation that writes a page-table entry (via `VSpaceBackend.mapPage` / `unmapPage` under AN6-D) threads the witness emission through the HAL FFI.
  - **Acceptance**: write paths validated; full gate PASS.

- **AN9-A.5 — QEMU validation harness** (0.4 day)
  - New `scripts/test_qemu_tlb_cache_coherence.sh`: boots kernel in QEMU `virt` machine, exercises a page-table update followed by an executable-page flush, verifies no stale-I-cache fetch.
  - Wired into Tier-2 CI (skip-with-log if no QEMU).
  - **Acceptance**: harness passes in QEMU.

- **AN9-A.6 — Close DEF-A-M04 in `AUDIT_v0.29.0_DEFERRED.md`** (0.1 day)
  - Mark DEF-A-M04 RESOLVED with AN9-A commit SHA; update the disposition table.
  - **Acceptance**: tracking entry shows RESOLVED.

- **Regression test**: full gate + rust gate + QEMU harness.
- **Cascade**: ~6 Lean files touched + 3 Rust files + 1 new script.

### AN9-B — DEF-A-M06 / DEF-AK3-I: `tlbBarrierComplete` substantive binding

- **Audit ID**: DEF-A-M06 / DEF-AK3-I (absorbed, Category A)
- **Files**:
  - `SeLe4n/Kernel/Architecture/Invariant.lean` (current TPI-DOC-AK3I annotation)
  - `SeLe4n/Kernel/Architecture/TlbModel.lean`
  - `rust/sele4n-hal/src/tlb.rs` (call-graph static analysis source)
  - New `rust/sele4n-hal/build.rs` scan helper (extends AN8-B.5's scanner)
- **Total effort**: ~2 days.

**Sub-sub-task breakdown** (5 commits):

- **AN9-B.1 — Static-analysis pass of HAL TLB call graph** (0.5 day)
  - Extend `rust/sele4n-hal/build.rs` to scan `tlb.rs` and verify every `tlbi` instruction is bracketed by `dsb ish` before and `isb` after. Fail the build on any violation.
  - Record the analysis output as machine-readable metadata (`target/tlb_barrier_bracketed.json`) that Lean-side can ingest via the FFI layer from AN9-A.1.
  - **Acceptance**: build.rs scanner present; current tlb.rs passes; synthetic violation test fails build.

- **AN9-B.2 — FFI witness for barrier-bracketed invalidation** (0.4 day)
  - Add `@[extern "sele4n_hal_tlb_invalidate_barrier_bracketed_witness"]` that returns a proof-carrying token `TlbInvalidationWitness` each time the HAL emits a TLB invalidation with proper bracketing.
  - **Acceptance**: FFI bridge present both sides.

- **AN9-B.3 — Refine `tlbBarrierComplete` to consume the witness** (0.5 day)
  - The invariant now requires a `TlbInvalidationWitness` at every TLB-invalidation kernel entry point instead of being a stub `True` predicate.
  - Preservation theorems for every kernel operation that invalidates TLB entries (VSpaceBackend.unmapPage, ASID reuse, retype-from-VSpaceRoot) thread the witness.
  - **Acceptance**: `tlbBarrierComplete` is substantively enforced; preservation chain complete.

- **AN9-B.4 — Cascade through existing AK3-I TPI-DOC annotations** (0.4 day)
  - Remove the TPI-DOC-AK3I annotation from `Architecture/Invariant.lean`; replace with cross-reference to the new substantive theorem `tlbBarrierComplete_bridge_via_hal_witness`.
  - **Acceptance**: no TPI-DOC-AK3I annotations remain; `grep -rn "TPI-DOC-AK3I" SeLe4n/` returns empty.

- **AN9-B.5 — Close DEF-A-M06 / DEF-AK3-I in v0.29.0 DEFERRED file** (0.1 day)
  - Mark RESOLVED with commit SHA.
  - **Acceptance**: tracking entry shows RESOLVED.

- **Regression test**: full gate + rust gate + synthetic unbracketed-tlbi regression test.
- **Cascade**: ~8 preservation theorems updated.

### AN9-C — DEF-A-M08 / DEF-A-M09 / DEF-AK3-K: MMU / Device BarrierKind composition

- **Audit IDs**: DEF-A-M08, DEF-A-M09, DEF-AK3-K (absorbed, Category A)
- **Files**:
  - `SeLe4n/Kernel/Architecture/VSpaceARMv8.lean` (currently carries TPI-DOC doc block)
  - New `SeLe4n/Kernel/Architecture/BarrierComposition.lean`
  - `rust/sele4n-hal/src/mmio.rs` (MMIO write barrier emission)
  - `rust/sele4n-hal/src/mmu.rs` (MMU update barrier emission)
- **Total effort**: ~2 days.

**Sub-sub-task breakdown** (5 commits):

- **AN9-C.1 — Define `BarrierKind` composition algebra** (0.3 day)
  - In new `BarrierComposition.lean`:
    ```lean
    inductive BarrierKind where
      | none
      | dsbIshst        -- write-ordering before MMU update
      | dcCvacDsbIsh    -- D-cache clean + D-side sync (page-table pages)
      | isb             -- instruction-side serialization
      | sequenced (pre : BarrierKind) (post : BarrierKind)
    ```
  - Prove associativity + `BarrierKind.subsumes` partial order.
  - **Acceptance**: algebra present; laws proven.

- **AN9-C.2 — MMU update composition theorem (A-M08)** (0.5 day)
  - Prove `pageTableUpdate_observes_armv8_ordering : BarrierKind.sequenced dsbIshst (BarrierKind.sequenced dcCvacDsbIsh isb)` subsumes the ARMv8 page-table update ordering requirement (per ARM ARM D8.11).
  - **Acceptance**: theorem proven; composition complete.

- **AN9-C.3 — MMIO write composition theorem (A-M09)** (0.4 day)
  - Prove `mmioWrite_observes_dsbIshst_before_sideEffect : MMIO writes sequence with DSB ISHST before any externally-observable side effect`.
  - Wire FFI witness from `mmio.rs` so every MMIO write returns a `BarrierKind` witness Lean can consume.
  - **Acceptance**: theorem proven; FFI witness in place.

- **AN9-C.4 — Cascade + remove TPI-DOC annotations** (0.7 day)
  - Replace TPI-DOC-AK3K doc block at top of `VSpaceARMv8.lean` with cross-reference to the new substantive theorems.
  - Every page-table update and MMIO write call site in the kernel threads the corresponding `BarrierKind` witness.
  - **Acceptance**: TPI-DOC-AK3K removed; ~12 call sites updated; full gate PASS.

- **AN9-C.5 — Close DEF-A-M08/M09/AK3-K in v0.29.0 DEFERRED file** (0.1 day)
  - Mark three entries RESOLVED with commit SHA.
  - **Acceptance**: tracking entries RESOLVED.

- **Regression test**: full gate + rust gate.
- **Cascade**: ~12 sites + 1 new module + 3 updated theorems.

### AN9-D — DEF-C-M04: `suspendThread` atomicity via HAL interrupt-disable bracket

- **Audit ID**: DEF-C-M04 (absorbed, Category A)
- **Files**:
  - `SeLe4n/Kernel/Lifecycle/Suspend.lean` (currently carries H3-ATOMICITY annotation)
  - `rust/sele4n-hal/src/ffi.rs` (suspendThread FFI wrapper — new file or extension)
  - `rust/sele4n-hal/src/interrupts.rs` (existing `with_interrupts_disabled`)
- **Total effort**: ~1.25 days.

**Sub-sub-task breakdown** (4 commits):

- **AN9-D.1 — FFI wrapper brackets suspendThread with interrupts-disabled** (0.4 day)
  - In `rust/sele4n-hal/src/ffi.rs`, add:
    ```rust
    #[no_mangle]
    pub extern "C" fn sele4n_suspend_thread(tid: u64) -> u32 {
        crate::interrupts::with_interrupts_disabled(|| {
            unsafe { sele4n_suspend_thread_inner(tid) }
        })
    }
    extern "C" {
        fn sele4n_suspend_thread_inner(tid: u64) -> u32; // Lean-provided
    }
    ```
  - The inner function is the existing Lean-level `suspendThread` dispatch entry; the outer wrapper guarantees that the transient inconsistency window (remove from run queue → clear `pendingMessage`) is atomic wrt interrupts.
  - **Acceptance**: FFI wrapper present; cargo builds.

- **AN9-D.2 — Clippy lint enforces bracket discipline** (0.2 day)
  - Add `#[must_use = "call sele4n_suspend_thread, not sele4n_suspend_thread_inner, to preserve atomicity"]` on the inner function, plus a clippy lint that flags direct calls to `_inner` outside the `ffi.rs` module.
  - **Acceptance**: clippy warns on direct `_inner` use; synthetic-violation test fails `cargo clippy -- -D warnings`.

- **AN9-D.3 — Lean-side atomicity theorem** (0.5 day)
  - In `SeLe4n/Kernel/Lifecycle/Suspend.lean`, replace the H3-ATOMICITY annotation with:
    ```lean
    theorem suspendThread_atomicity_under_ffi_bracket :
        ∀ (st : SystemState) (tid : ThreadId),
        st.machine.interruptsEnabled = false →
        ∃ st', suspendThread st tid = .ok st' ∧
               suspendThread_transientWindowInvariant st' := by
      -- proof composes existing suspend-preservation lemmas with the
      -- interrupts-enabled = false precondition established by the FFI wrapper
    ```
  - The precondition is discharged at kernel entry by the FFI wrapper's `with_interrupts_disabled` call.
  - **Acceptance**: theorem proven; module gate PASS.

- **AN9-D.4 — Close DEF-C-M04 in v0.29.0 DEFERRED file** (0.15 day)
  - Mark DEF-C-M04 RESOLVED with commit SHA.
  - **Acceptance**: tracking entry RESOLVED.

- **Regression test**: full gate + rust gate + `lake exe suspend_resume_suite`.
- **Cascade**: 2 new/modified Rust files + 1 new theorem + 1 annotation removal.

### AN9-E — DEF-P-L9: VSpaceRoot boot exclusion — closed by AN7-D.2 cross-reference

- **Audit ID**: DEF-P-L9 (absorbed; closure work landed in AN7-D.2)
- **Effort**: 0.1 day (cross-reference only; the substantive work is in AN7-D.2's `RPi5/VSpaceBoot.lean` module).
- **Plan**:
  - Add annotation in `SeLe4n/Platform/Boot.lean` at the former boot-exclusion site: `-- DEF-P-L9 RESOLVED by AN7-D.2: VSpaceRoot now included in bootSafeObject via RPi5/VSpaceBoot.lean`.
  - Mark DEF-P-L9 RESOLVED in `AUDIT_v0.29.0_DEFERRED.md` with reference to AN7-D.2's commit SHA.
- **Acceptance**: annotation present; tracking entry RESOLVED.
- **Regression test**: inherits from AN7-D.2.

### AN9-F — DEF-R-HAL-L14: SVC FFI wiring to `sele4n_syscall_dispatch`

- **Audit ID**: DEF-R-HAL-L14 (absorbed, Category A)
- **Files**:
  - `rust/sele4n-hal/src/trap.rs:186` (current `handle_svc` stub returning `NOT_IMPLEMENTED = 17`)
  - `rust/sele4n-hal/src/lib.rs:89` (ffi export)
  - New `rust/sele4n-hal/src/svc_dispatch.rs` — typed argument marshalling
  - `SeLe4n/Kernel/API.lean` (Lean-side syscall entry, currently `syscallEntryChecked`)
- **Total effort**: ~3 days.

**Sub-sub-task breakdown** (7 commits):

- **AN9-F.1 — Design typed argument marshalling layer** (0.5 day)
  - New `rust/sele4n-hal/src/svc_dispatch.rs` exports `pub fn dispatch_svc(syscall_id: u32, args: &SyscallArgs) -> Result<u64, KernelError>`.
  - `SyscallArgs` mirrors the Lean `SyscallArgs` union type (MessageInfo + msgRegs + IPC buffer reference); per-syscall decoding uses the existing AK4 ABI types.
  - **Acceptance**: `svc_dispatch.rs` compiles; type shapes match Lean.

- **AN9-F.2 — Lean-side `@[extern]` dispatcher** (0.4 day)
  - In `SeLe4n/Kernel/API.lean`, expose `@[extern "sele4n_syscall_dispatch"] opaque syscallDispatchFromAbi : SyscallId → SyscallArgs → IO (Except KernelError UInt64)`.
  - Wrap existing `syscallEntryChecked` so the FFI route matches.
  - **Acceptance**: FFI symbol declared; wrapper compiles.

- **AN9-F.3 — `handle_svc` routes through the typed dispatcher** (0.5 day)
  - Replace the `NOT_IMPLEMENTED = 17` stub in `trap.rs:186` with:
    ```rust
    pub fn handle_svc(trap_frame: &TrapFrame) -> u64 {
        let syscall_id = trap_frame.x0 as u32;
        let args = SyscallArgs::from_trap_frame(trap_frame);
        match unsafe { svc_dispatch::dispatch_svc(syscall_id, &args) } {
            Ok(ret) => ret,
            Err(e) => e.to_u32() as u64, // ABI convention
        }
    }
    ```
  - **Acceptance**: handle_svc returns non-stub values; `cargo build` PASS.

- **AN9-F.4 — End-to-end FFI integration test** (0.6 day)
  - Add cargo integration test `tests/svc_dispatch_roundtrip.rs` that constructs a synthetic TrapFrame, calls `handle_svc`, and asserts the correct kernel error variant is returned.
  - Extend `scripts/test_qemu.sh` to exercise a real SVC instruction trap end-to-end (`svc #0` from a userspace stub).
  - **Acceptance**: cargo integration test PASS; QEMU SVC round-trip PASS.

- **AN9-F.5 — Rust-side proof-of-typedness audit** (0.3 day)
  - Every typed argument decoded in `svc_dispatch.rs` must match a corresponding AK4-D decoder on the Lean side. Validate with a new `scripts/check_abi_parity.sh` that greps both sides and reports mismatches.
  - **Acceptance**: parity script PASS; no mismatches.

- **AN9-F.6 — Update source TODOs** (0.15 day)
  - Replace the AN1-C-placed `TODO(AN9-F)` markers with annotations `// CLOSED at AN9-F: see commit SHA`.
  - **Acceptance**: no remaining `TODO(AN9-F)` in source.

- **AN9-F.7 — Close DEF-R-HAL-L14 in v0.29.0 DEFERRED file** (0.1 day)
  - Mark RESOLVED with commit SHA.
  - **Acceptance**: tracking entry RESOLVED.

- **Regression test**: full gate + rust gate + QEMU SVC round-trip.
- **Cascade**: 1 new Rust module + 2 modified trap.rs/lib.rs + Lean-side FFI layer + integration test.

### AN9-G — DEF-R-HAL-L17: Bounded WFE timeout guard

- **Audit ID**: DEF-R-HAL-L17 (new, surfaced by AN1-C)
- **Files**: `rust/sele4n-hal/src/lib.rs:62` (current `wfe()` call), `rust/sele4n-hal/src/cpu.rs`
- **Total effort**: ~0.75 day.

**Rationale**: unconditional `wfe()` in the idle loop can hang if no wake event ever arrives (e.g., mis-configured timer). A bounded timeout guard breaks the sleep periodically, sanity-checks the scheduler's tick counter, and re-arms timer interrupts if required. Closes the "interrupt-wait optimisation" item.

**Sub-sub-task breakdown** (4 commits):

- **AN9-G.1 — Define `wfe_bounded(max_ticks: u64)` helper** (0.2 day)
  - In `rust/sele4n-hal/src/cpu.rs`, add a bounded wrapper that reads CNTPCT_EL0, issues `wfe()`, and falls through after `max_ticks` have elapsed regardless of event state.
  - **Acceptance**: helper compiles; a unit test on non-aarch64 exercises the fall-through path.

- **AN9-G.2 — Replace `lib.rs:62` wfe() with wfe_bounded(10 ms at 54 MHz)** (0.15 day)
  - Default timeout: 10 ms × 54_000_000 / 1000 = 540000 ticks.
  - On fall-through, re-check the scheduler's `nextWakeUp` and re-arm the timer if it has drifted.
  - **Acceptance**: boot loop no longer hangs on missing wake event; QEMU verifies.

- **AN9-G.3 — Update source TODOs** (0.1 day)
  - Replace `TODO(AN9-G)` marker with `// CLOSED at AN9-G: bounded WFE with 10ms fall-through`.
  - **Acceptance**: no remaining TODO.

- **AN9-G.4 — Close DEF-R-HAL-L17 in v0.29.0 DEFERRED file** (0.1 day)
  - Mark RESOLVED with commit SHA.
  - **Acceptance**: tracking entry RESOLVED.

- **Regression test**: rust gate + QEMU idle-loop smoke.
- **Cascade**: 2 files.

### AN9-H — DEF-R-HAL-L18: Parameterized barriers (accept `BarrierKind` argument)

- **Audit ID**: DEF-R-HAL-L18 (new, surfaced by AN1-C)
- **Files**: `rust/sele4n-hal/src/barriers.rs`, `rust/sele4n-hal/src/lib.rs:69`
- **Total effort**: ~1 day.

**Rationale**: current barrier helpers (`dsb_ish()`, `dsb_ishst()`, `isb()`) are separate functions. Consuming code selects one; there's no way for generic code to accept "whichever barrier is appropriate for the caller's situation" as an argument. Parameterisation lets the AN9-C `BarrierKind` composition algebra translate directly to HAL emission.

**Sub-sub-task breakdown** (4 commits):

- **AN9-H.1 — Define `BarrierKind` enum in `barriers.rs`** (0.2 day)
  - Mirror AN9-C.1's Lean-side `BarrierKind` inductive as a Rust enum with `emit(self)` method dispatching to the appropriate `dsb/isb` call.
  - **Acceptance**: enum + emit method compile.

- **AN9-H.2 — Migrate existing single-purpose barrier call sites to `BarrierKind`** (0.5 day)
  - Walk `mmu.rs`, `tlb.rs`, `cache.rs`, `mmio.rs` and replace direct `dsb_ish()` / `dsb_ishst()` / `isb()` calls with `BarrierKind::DsbIsh.emit()` / `BarrierKind::DsbIshst.emit()` / `BarrierKind::Isb.emit()`.
  - **Acceptance**: ~15 call sites migrated; cargo test PASS; no behavioural change.

- **AN9-H.3 — Update source TODOs** (0.1 day)
  - Replace `TODO(AN9-H)` marker with `// CLOSED at AN9-H: BarrierKind parameterisation`.
  - **Acceptance**: no remaining TODO.

- **AN9-H.4 — Close DEF-R-HAL-L18 in v0.29.0 DEFERRED file** (0.1 day)
  - Mark RESOLVED with commit SHA.
  - **Acceptance**: tracking entry RESOLVED.

- **Regression test**: rust gate + QEMU.
- **Cascade**: ~15 call sites migrated.

### AN9-I — DEF-R-HAL-L19: OSH widening for multi-core

- **Audit ID**: DEF-R-HAL-L19 (new, surfaced by AN1-C)
- **Files**: `rust/sele4n-hal/src/barriers.rs` (extend with OSH variants), `rust/sele4n-hal/src/lib.rs:84`
- **Total effort**: ~0.75 day.

**Rationale**: ARM `dsb ish` synchronises only within the Inner Shareable domain (typically cluster-local). For multi-core systems spanning clusters and for device-coherent ordering guarantees, `dsb osh` (Outer Shareable) is required. AN9-I adds the OSH-width barriers as first-class members of `BarrierKind` (AN9-H) and migrates the small set of call sites that require outer-shareable ordering (MMIO device writes that cross cluster boundaries, PSCI secondary-core wake-ups).

**Sub-sub-task breakdown** (4 commits):

- **AN9-I.1 — Add `BarrierKind::DsbOsh` + `BarrierKind::DsbOshst` variants** (0.2 day)
  - Extend AN9-H's enum; `emit()` dispatches to `dsb osh` / `dsb oshst` respectively.
  - **Acceptance**: variants compile; aarch64 test path exercises them.

- **AN9-I.2 — Migrate cross-cluster call sites** (0.3 day)
  - MMIO writes that target device registers visible to other clusters use `DsbOshst`.
  - PSCI CPU_ON calls (prep for AN9-J) use `DsbOsh` before emitting the PSCI SMC.
  - Document each migrated site: `-- AN9-I: widened from DsbIshst to DsbOshst for cross-cluster visibility`.
  - **Acceptance**: ~5 call sites migrated; `cargo test` PASS.

- **AN9-I.3 — Update source TODOs** (0.1 day)
  - Replace `TODO(AN9-I)` marker with `// CLOSED at AN9-I: OSH-width barriers added`.
  - **Acceptance**: no remaining TODO.

- **AN9-I.4 — Close DEF-R-HAL-L19 in v0.29.0 DEFERRED file** (0.15 day)
  - Mark RESOLVED with commit SHA.
  - **Acceptance**: tracking entry RESOLVED.

- **Regression test**: rust gate + QEMU multi-core smoke (inherits AN9-J).
- **Cascade**: ~5 sites.

### AN9-J — DEF-R-HAL-L20: Secondary-core bring-up (SMP enablement, merged off by default at v1.0.0)

- **Audit ID**: DEF-R-HAL-L20 (new, surfaced by AN1-C). **This is the largest and highest-risk sub-task in AN9.**
- **Files**:
  - `rust/sele4n-hal/src/boot.S` (PSCI CPU_ON call + secondary entry point)
  - New `rust/sele4n-hal/src/smp.rs` — SMP bring-up logic, per-core init paths
  - New `rust/sele4n-hal/src/psci.rs` — PSCI HVC/SMC wrapper
  - `rust/sele4n-hal/src/trap.rs` (per-core trap frame storage via TPIDR_EL1)
  - `SeLe4n/Kernel/Concurrency/Assumptions.lean` (AN12-B SMP inventory) — update post-SMP-bring-up to reflect which assumptions ARE still load-bearing
  - `rust/sele4n-hal/src/boot.rs` (boot-flag `smp_enabled` plumbed from kernel command-line)
- **Total effort**: ~7 days. Largest AN9 sub-task; staged across 8 commits so each is independently reviewable.

**Rationale for pre-1.0 closure + "disabled-by-default" stance**: maintainer directive requires absorption of DEF-R-HAL-L20 into pre-1.0 work. However, SMP ships **as a compile-and-test-included feature gated off at runtime** at v1.0.0 — the kernel-command-line `smp_enabled` flag is `false` by default, so single-core semantics preserve. The SMP code path is code-reviewed, QEMU-tested with `-smp 4`, and present in the v1.0.0 image, but activation is a deployment-time decision. This satisfies the "complete all deferred work before v1.0.0" directive (SMP is implemented + tested + merged) while preserving single-core as the default-safe configuration.

**Sub-sub-task breakdown** (8 commits):

- **AN9-J.1 — PSCI wrapper module** (0.5 day)
  - New `rust/sele4n-hal/src/psci.rs`: exports `pub fn cpu_on(target_mpidr: u64, entry_point: usize, context_id: u64) -> PsciResult`. Emits `hvc #0` (or `smc #0` if configured) with PSCI function ID `0x8400_0003` (CPU_ON) per ARM DEN0022.
  - **Acceptance**: PSCI wrapper compiles; unit test on non-aarch64 stubs the HVC.

- **AN9-J.2 — Per-core TPIDR_EL1 scratch + trap frame storage** (0.75 day)
  - Reserve per-core TPIDR_EL1 storage pointing at a `PerCoreData` structure (trap frame buffer + scheduler state + interrupt mask). On `boot.S` entry for secondary cores, write TPIDR_EL1 before any trap-capable code runs.
  - **Acceptance**: per-core data layout defined; secondary core preserves its own TPIDR across a synthetic trap in QEMU.

- **AN9-J.3 — Secondary-core entry assembly** (0.75 day)
  - In `boot.S`, add a `secondary_entry` label that primary core passes as `entry_point` to PSCI. Secondary entry: set up SP, TPIDR_EL1, call `rust_secondary_main`.
  - **Acceptance**: secondary entry assembly present; QEMU `-smp 4` boots up to 4 cores.

- **AN9-J.4 — `rust_secondary_main` performs per-core MMU + GIC CPU interface init** (1 day)
  - Each secondary core: loads TTBR from the shared primary-set boot L1 table, enables its SCTLR with the same bitmap as primary (AK5-C), initialises its GIC CPU interface (secondary GICC_CTLR + GICC_PMR from GIC-400 TRM).
  - Waits on a per-core ready flag set by the primary once the kernel image is fully set up.
  - **Acceptance**: all cores reach the post-MMU state; `printk` from each core shows up in UART log.

- **AN9-J.5 — `smp_enabled` runtime flag gates primary → secondary CPU_ON calls** (0.5 day)
  - Boot primary parses kernel command line for `smp_enabled=true|false`; if `false` (default), skips PSCI CPU_ON entirely. If `true`, issues CPU_ON for each MPIDR read from the platform's cpus list.
  - **Acceptance**: default boot is single-core (SMP code not activated); `smp_enabled=true` boots 4 cores.

- **AN9-J.6 — Integrate with `InterruptDispatch.lean` + SPI routing** (1 day)
  - Lean-side interrupt dispatch accommodates a `target_cpu : Fin numCpus` parameter; per-core GIC CPU interfaces register separately. Per-core timer IRQ (PPI 30) routed to the respective core.
  - Update `interruptDispatchSequence_always_ok` (AI2-A) to account for `target_cpu`.
  - **Acceptance**: Lean model composes; each core services its own timer IRQ.

- **AN9-J.7 — QEMU `-smp 4` boot test + regression** (1 day)
  - Extend `scripts/test_qemu.sh` with an `--smp 4` path that boots the kernel with `smp_enabled=true` and verifies all 4 cores reach a steady state.
  - Add `scripts/test_smp_smoke.sh` — new tier-2 test.
  - **Acceptance**: SMP smoke passes in QEMU; single-core default path unchanged.

- **AN9-J.8 — Update source TODOs, SMP inventory, close DEF-R-HAL-L20** (0.5 day)
  - Replace `TODO(AN9-J)` with `// CLOSED at AN9-J: PSCI CPU_ON + per-core init; smp_enabled flag gates activation`.
  - Update `SeLe4n/Kernel/Concurrency/Assumptions.lean` (AN12-B inventory) — items that were SMP-latent now have their SMP-side implementation landed; single-core is a runtime default, not a proof-layer constraint.
  - Mark DEF-R-HAL-L20 RESOLVED in `AUDIT_v0.29.0_DEFERRED.md`.
  - **Acceptance**: all TODOs retargeted; inventory updated; tracking entry RESOLVED.

- **Regression test**: rust gate + QEMU `-smp 4` smoke + single-core default path smoke (both must pass).
- **Cascade**: 4 new/modified Rust files + 1 Lean interrupt-dispatch update + 1 new script + 1 inventory update.

### AN9-K — AN9 closure

- **Files**: `CHANGELOG.md` entry consolidating AN9-A..J; `CLAUDE.md` large-files-list refresh (new modules)
- **Acceptance**: PR merged; full gate + rust gate + QEMU smoke (single-core + SMP) PASS; all 10 DEF-* entries closed under AN9 (A-M04, A-M06, A-M08, A-M09, C-M04, P-L9 cross-ref, R-HAL-L14, L17, L18, L19, L20) are marked RESOLVED in `docs/audits/AUDIT_v0.29.0_DEFERRED.md` with AN9-* commit SHAs.

---

## 13. Phase AN10 — AK7 cascade completion (NEW)

**Goal**: substantively close DEF-AK7-E.cascade and DEF-AK7-F.cascade (reader + writer sides) from `AUDIT_v0.29.0_DEFERRED.md`. This phase is mechanical but voluminous: ~600+ call sites across 5 kernel subsystems migrate from raw identifier / raw-match patterns to the AL2-A typed helpers and `Valid*` subtypes introduced in the AL workstream. Each migration step is guarded by the AK7 cascade monotonicity metrics already wired into `scripts/ak7_cascade_check_monotonic.sh` so progress is machine-visible.

**Scope**: 4 sub-tasks (AN10-A through AN10-D) covering handler-signature tightening (DEF-AK7-E, ~240 sites), reader-side typed-helper adoption (DEF-AK7-F reader, ~304+ sites), writer-side `storeObjectKindChecked` adoption (DEF-AK7-F writer, ~50 sites), and final metric floors / monotonicity-gate hardening.

**Effort**: 8–10 dev-days. **Blocks**: AN11. **Depends on**: AN9 (SMP-safe predicates land in Valid*-typed handler signatures).

### AN10-A — DEF-AK7-E.cascade: Handler signatures ObjId/ThreadId/SchedContextId → Valid* subtypes

- **Audit ID**: DEF-AK7-E (absorbed, Category B proof-hygiene — elevated to pre-1.0 per maintainer directive)
- **Files**: Lifecycle / SchedContext / IpcBufferValidation / Scheduler handler dispatch arms + per-op preservation theorems
- **Total effort**: ~4 days. **Cascade**: ~240 call sites. **Monotonicity metric**: `SENTINEL_CHECK_DISPATCH` (should grow to a post-AN10 floor).

**Sub-sub-task breakdown** (6 commits; batched by subsystem cluster):

- **AN10-A.1 — Migrate Lifecycle handlers (~50 sites)** (0.75 day)
  - Handler signatures: `suspendThread : ThreadId → …` → `suspendThread : ValidThreadId → …`; same for `resumeThread`, `lifecycleRetype` (takes `ValidObjId` for target), and their preservation theorems.
  - `validateThreadIdArg` already wired at dispatch boundary (AL1b/AL8); this step pushes `ValidThreadId` through the handler body instead of unwrapping.
  - **Acceptance**: Lifecycle handlers + preservation theorems carry `Valid*` types; `lake build SeLe4n.Kernel.Lifecycle.Operations` PASS.

- **AN10-A.2 — Migrate SchedContext handlers (~40 sites)** (0.6 day)
  - `schedContextConfigure/Bind/Unbind/yieldTo` signatures take `ValidSchedContextId` / `ValidObjId`.
  - **Acceptance**: SC handlers migrated; module gate PASS.

- **AN10-A.3 — Migrate Scheduler handlers (~50 sites)** (0.75 day)
  - `setPriorityOp`, `setMCPriorityOp`, priority-management handlers take `ValidThreadId`.
  - **Acceptance**: Scheduler handler surface migrated; module gate PASS.

- **AN10-A.4 — Migrate IpcBufferValidation + Capability handlers (~50 sites)** (0.75 day)
  - `setIPCBufferOp`, plus any remaining Capability handlers not already migrated in AL workstream.
  - **Acceptance**: IPC-buffer + Cap surface migrated.

- **AN10-A.5 — Migrate Scheduler liveness + WCRT proof sites (~50 sites)** (0.65 day)
  - WCRT / liveness theorems that destructure `ThreadId` to `ObjId` now thread `ValidThreadId` through; downstream preservation closures compose automatically.
  - **Acceptance**: Liveness proofs build; `lake exe liveness_suite` PASS.

- **AN10-A.6 — Metric floor bump + DEF-AK7-E closure** (0.25 day)
  - `scripts/ak7_cascade_baseline.sh`: `SENTINEL_CHECK_DISPATCH` floor raised from current value (15 at v0.30.0) to target post-AN10 value.
  - Mark DEF-AK7-E.cascade RESOLVED in `AUDIT_v0.29.0_DEFERRED.md`.
  - **Acceptance**: metric advanced; tracking entry RESOLVED; `ak7_cascade_check_monotonic.sh` PASS.

- **Regression test**: full gate + rust gate + `lake exe ak7_regression_suite` PASS after each batch.
- **Cascade**: ~240 sites, bounded by the batching above.

### AN10-B — DEF-AK7-F.cascade reader side: raw-match → AL2-A typed helpers (~304+ sites)

- **Audit ID**: DEF-AK7-F.reader.hygiene (absorbed)
- **Files**: Scheduler (151), IPC (104), Architecture/InformationFlow/Lifecycle/FrozenOps/SchedContext/Platform (~49) consumer modules
- **Total effort**: ~3 days. **Cascade**: ~304+ call sites. **Monotonicity metric**: `RAW_MATCH_TCB`, `RAW_MATCH_ENDPOINT`, `RAW_MATCH_NOTIFICATION`, `RAW_MATCH_UNTYPED`, `RAW_LOOKUP_TID`, `GETTCB_ADOPTION`, `GETSCHEDCTX_ADOPTION` (should drop / grow respectively).

**Sub-sub-task breakdown** (5 commits; batched by subsystem):

- **AN10-B.1 — Scheduler reader migration (~151 sites)** (1 day)
  - Replace `match st.objects[tid]? with | some (.tcb tcb) => …` with `match st.getTcb? tid with | some tcb => …` and similar for schedContext.
  - **Acceptance**: `RAW_MATCH_TCB` drops by ~120+; `GETTCB_ADOPTION` rises by ~120+; module gate PASS.

- **AN10-B.2 — IPC reader migration (~104 sites)** (0.75 day)
  - Same pattern; endpoint / notification raw-match sites migrate to `getEndpoint?` / `getNotification?`.
  - **Acceptance**: `RAW_MATCH_ENDPOINT` + `RAW_MATCH_NOTIFICATION` drop; adoption metrics rise.

- **AN10-B.3 — Cross-subsystem reader migration (~49 sites)** (0.5 day)
  - Architecture / InformationFlow / Lifecycle / FrozenOps / SchedContext / Platform.
  - **Acceptance**: remaining raw-match sites in production surface drop to ≤ 20 (ceiling set by the helper-definition file itself, which retains the patterns by design).

- **AN10-B.4 — Metric floors + monotonicity tightening** (0.5 day)
  - Set new post-AN10 floors on all 7 reader-side metrics. `RAW_MATCH_TCB` target floor ≤ 100 (from 600 at v0.30.0), `GETTCB_ADOPTION` target floor ≥ 300 (from 49).
  - **Acceptance**: `ak7_cascade_check_monotonic.sh` PASS against new baseline.

- **AN10-B.5 — Close DEF-AK7-F.reader.hygiene in v0.29.0 DEFERRED file** (0.25 day)
  - Mark RESOLVED with commit SHA.
  - **Acceptance**: tracking entry RESOLVED.

- **Regression test**: full gate + `lake exe ak7_regression_suite` after each batch.
- **Cascade**: ~304+ sites.

### AN10-C — DEF-AK7-F.cascade writer side: storeObject → storeObjectKindChecked (~50 sites)

- **Audit ID**: DEF-AK7-F.writer.hygiene (absorbed)
- **Files**: ~50 in-place `storeObject` call sites across kernel subsystems
- **Total effort**: ~1.5 days. **Cascade**: ~50 sites. **Monotonicity metric**: `STOREOBJECTCHECKED_ADOPTION` (should grow to post-AN10 floor).

**Sub-sub-task breakdown** (3 commits):

- **AN10-C.1 — Migrate IPC + Scheduler writer sites (~25 sites)** (0.6 day)
  - Replace `storeObject oid (.tcb tcb)` with `storeObjectKindChecked oid (.tcb tcb)` throughout these subsystems. Each migration is transparent because `storeObjectKindChecked_sameKind_eq_storeObject` discharges the equivalence at same-kind writes (fresh allocations discharged via `storeObjectKindChecked_fresh_eq_storeObject`).
  - **Acceptance**: ~25 sites migrated; preservation proofs build with no new obligations.

- **AN10-C.2 — Migrate Capability / Lifecycle / Service / SchedContext / Platform writer sites (~25 sites)** (0.6 day)
  - Same pattern.
  - **Acceptance**: remaining 25 sites migrated.

- **AN10-C.3 — Metric floor + DEF-AK7-F.writer closure** (0.3 day)
  - `STOREOBJECTCHECKED_ADOPTION` floor: 9 (at v0.30.0) → ~55 post-AN10.
  - Mark DEF-AK7-F.writer.hygiene RESOLVED in `AUDIT_v0.29.0_DEFERRED.md`.
  - **Acceptance**: metric advanced; tracking entry RESOLVED.

- **Regression test**: full gate + `lake exe ak7_regression_suite`.
- **Cascade**: ~50 sites.

### AN10-D — AN10 closure + metric-floor hardening

- **Files**: `CHANGELOG.md` entry; `CLAUDE.md` WS-AN entry refresh; `scripts/ak7_cascade_baseline.sh` final-floor update
- **Plan**:
  - Consolidate metric floors into baseline: every AK7 metric that grew during AN10-A/B/C receives its new floor; monotonicity gate rejects regressions against the post-AN10 baseline.
  - Three `DEF-AK7-*` entries (E, F.reader, F.writer) all marked RESOLVED.
  - AN10-A/B/C commit SHAs cross-referenced from the tracking entries.
- **Acceptance**: PR merged; full gate + rust gate PASS; all 3 AK7-cascade tracking entries RESOLVED; monotonicity-check baseline updated.

---

## 14. Phase AN11 — Tests / CI / Scripts

**Goal**: close the four HIGH test findings (H-20 KernelError matrix, H-21 lake-exe timeout, H-22 small-fixture sha256, H-23 named AK6 tests), batch TST-M01..M13, and address Test LOWs. This phase exercises everything the prior phases shipped (including AN9 hardware-binding and AN10 cascade work) and gates AN12's closure.

**Effort**: 4–5 days. **Blocks**: AN12.

### AN11-A — KernelError variant cross-syscall coverage matrix (H-20)

- **Audit ID**: H-20 (HIGH)
- **Files**:
  - `tests/KernelErrorMatrixSuite.lean` (new) — dedicated suite for the rejection matrix
  - `scripts/test_tier2_negative.sh` — wire the new suite
  - `SeLe4n/Model/State.lean:34-97` — verify the 51-variant `KernelError` enumeration is the source-of-truth
- **Total effort**: ~2.5 days. **Cascade**: ~45 new scenarios in ONE new suite file.

**Sub-sub-task breakdown** (7 commits, AN9-A.1..A.7):

- **AN9-A.1 — Matrix schema + source-of-truth verification** (0.25 day)
  - Define `KernelErrorRejection` structure:
    ```lean
    structure KernelErrorRejection where
      syscall : SyscallId
      expectedError : KernelError
      scenarioTag : String
      scenarioDesc : String
    deriving Repr
    ```
  - Enumerate all 51 `KernelError` variants in `SeLe4n/Model/State.lean`; confirm the count matches the audit's claim. If AN3..AN8 introduce new variants (AN6-E `partialResolution`, AN7-E `partialResolution`, etc.), include them.
  - **Acceptance**: schema committed; variant-count assertion matches source.

- **AN9-A.2 — Baseline coverage layer (already-tested variants)** (0.25 day)
  - Rows for the 14 variants the audit confirms are already exercised somewhere in tests. Even though they have coverage elsewhere, land formal matrix entries so the new suite is the canonical source.
  - Variants: `.addressOutOfBounds`, `.declassificationDenied`, `.flowDenied`, `.illegalState`, `.invalidArgument`, `.invalidCapability`, `.invalidMessageInfo`, `.invalidObjectType`, `.ipcMessageTooLarge`, `.ipcMessageTooManyCaps`, `.mmioUnaligned`, `.nullCapability`, `.objectNotFound`, `.policyDenied`.
  - **Acceptance**: 14 rows present and passing; matrix table-driven test harness runs.

- **AN9-A.3 — Security-priority variants (audit-named)** (0.5 day)
  - Rows for the 9 variants the audit explicitly flags as security-critical coverage gaps:
    - `.revocationRequired` — CDT revocation path
    - `.asidNotBound` — VSpace ASID path
    - `.schedulerInvariantViolation` — scheduler domain-split contradiction
    - `.alignmentError` — MMIO / page-table alignment
    - `.vmFault` — page-table walk fault
    - `.targetSlotOccupied` — CSpace insert to occupied slot
    - `.cyclicDependency` — service-registry cycle detection
    - `.dependencyViolation` — service-registry unmet dependency
    - `.replyCapInvalid` — IPC reply without valid reply cap
  - For each, construct a deliberately-failing input and assert the dispatcher returns the expected variant.
  - **Acceptance**: 9 rows present and passing.

- **AN9-A.4 — IPC / SchedContext / Lifecycle error path variants** (0.5 day)
  - Rows for remaining IPC-adjacent variants (e.g., `.endpointQueueEmpty`, `.notificationQueueEmpty`, `.sendBlocked`), SchedContext-specific variants (`.schedContextInvariantViolation`, `.replenishmentError`), and Lifecycle/retype variants (`.retypeBadChildType`, `.untypedOutOfRange`, `.untypedWatermarkMismatch`).
  - **Acceptance**: ~8 rows present and passing.

- **AN9-A.5 — Architecture / Capability / Service residual variants** (0.5 day)
  - Remaining architecture variants (`.pageTableFault`, `.vspaceLookupFailure`, `.interruptSpurious`), capability variants (`.cnodeIndexOverflow`, `.cnodeRadixMismatch`, `.mintAttenuationInvalid`), service variants.
  - Target count so the **≥35 total** target is met.
  - **Acceptance**: total matrix rows ≥ 35; `errorMatrix_covers_at_least_35 : errorMatrix.length ≥ 35 := by decide` witness theorem.

- **AN9-A.6 — Coverage-witness theorems + per-syscall marker** (0.25 day)
  - `errorMatrix_covers_at_least_35 : errorMatrix.length ≥ 35 := by decide`
  - Optional stretch: `errorMatrix_covers_security_critical : ∀ v ∈ [.revocationRequired, .asidNotBound, ...], ∃ row ∈ errorMatrix, row.expectedError = v := by decide`
  - `errorMatrix_distinctSyscalls : ∀ sid : SyscallId, (∃ row ∈ errorMatrix, row.syscall = sid)` — every syscall has at least one rejection row (optional extension depending on coverage).
  - **Acceptance**: theorems decidable; suite's `main` reports coverage count and critical-variant coverage boolean.

- **AN9-A.7 — CI wiring + coverage monotonicity metric** (0.25 day)
  - Wire `lake exe kernel_error_matrix_suite` into `scripts/test_tier2_negative.sh`.
  - Extend `scripts/ak7_cascade_baseline.sh` with `KERRORMATRIX_ROWS` monotonicity metric (floor = matrix-row-count-at-this-commit; should grow over time).
  - **Acceptance**: CI runs the suite; monotonicity metric added to baseline.

- **Regression test**: full gate; `lake exe kernel_error_matrix_suite` PASS.
- **Cascade**: ~35+ new test scenarios across 7 commits.

### AN11-B — `lake exe …` timeout wrapper (H-21)

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

### AN11-C — Small-fixture sha256 companions (H-22 — downgraded LOW, addressed here)

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

### AN11-D — Named test functions for AK6 sub-tests (H-23, TST-M11)

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

### AN11-E — Test MEDIUM batch (TST-M01..M13)

- **Audit IDs**: TST-M01..M13 (subset; some already covered by AN9-C / AN9-D)
- **Total effort**: ~1 day (mostly script edits).

**Sub-sub-task breakdown** (11 items; TST-M10 + TST-M11 already covered):

- **AN9-E.1 — TST-M01 AK8 sub-item test coverage** (0.2 day)
  - Extend the AK8-B atomicity + success-path pattern to AK8-C/D/E/F/G/H/I/J/K sub-items that lack tests. Add test groups in `tests/NegativeStateSuite.lean` (or a new `Ak8CoverageSuite.lean`).
  - Each AK8 sub-item gets: 1 success-path test + 1 failure-path test.
  - **Acceptance**: ~18 new test cases (9 AK8 sub-items × 2); `test_tier2_negative.sh` PASS.

- **AN9-E.2 — TST-M02 `assertCrossSubsystemInvariants` bundle** (0.1 day)
  - In `SeLe4n/Testing/InvariantChecks.lean`, add bundled assertion function `assertCrossSubsystemInvariants : SystemState → IO Bool` running all 12 (post-AN2-D) cross-subsystem invariants in sequence with a single composite failure report.
  - **Acceptance**: bundled assertion present; invoked from `MainTraceHarness` as a trace-end validation.

- **AN9-E.3 — TST-M03 `_common.sh` creation** (0.1 day)
  - Create `scripts/_common.sh` with shared helpers used across tier scripts (`log_info`, `log_error`, timing measurement, temp-file cleanup).
  - Update `scripts/test_abi_roundtrip.sh:14` to `source "$(dirname "$0")/_common.sh"` (drop the `|| true` swallow).
  - Audit other tier scripts for similar swallowed-source patterns; migrate each.
  - **Acceptance**: `_common.sh` present; no more silent-failure `source` lines.

- **AN9-E.4 — TST-M04 `github.token` standardization** (0.1 day)
  - `grep -rn "secrets\.GITHUB_TOKEN" .github/workflows/*.yml` to identify sites; replace with `github.token` (the automatic per-action token; more scoped).
  - Leave `secrets.GITHUB_TOKEN` only where a documented reason exists (e.g., a cross-repo action).
  - **Acceptance**: standardized; workflows green.

- **AN9-E.5 — TST-M05 GitBook drift hard failure** (0.05 day)
  - In `scripts/test_docs_sync.sh:36-56`, change warning exit to `exit 1` on drift.
  - **Acceptance**: GitBook drift now fails CI.

- **AN9-E.6 — TST-M06 tier-3 description verification** (0.05 day)
  - Verify `scripts/test_tier3_invariant_surface.sh`'s header comment matches CLAUDE.md's "invariant-surface anchors" phrasing (doesn't claim behavioral coverage).
  - **Acceptance**: comment consistent.

- **AN9-E.7 — TST-M07 `setup_lean_env.sh` idempotency guard** (0.1 day)
  - Add sentinel file check `~/.elan/.sele4n-bootstrap-marker`; if present, skip re-bootstrap (but still re-install hooks via AN1-B.2's idempotent installer).
  - **Acceptance**: second-invocation is a no-op for elan/lake but still refreshes the hook.

- **AN9-E.8 — TST-M08 `apt-get` retry with backoff** (0.1 day)
  - In `.github/workflows/lean_action_ci.yml:45-50`, wrap the `apt-get install` call in a 3-attempt retry loop with exponential backoff (2s, 4s, 8s).
  - **Acceptance**: CI workflow includes retry; synthetic-flake test verifies retry fires.

- **AN9-E.9 — TST-M09 `expectCond`/`expectError` empty-tag rejection** (0.1 day)
  - In `SeLe4n/Testing/Helpers.lean:23-44`, add runtime assertion `tag.length > 0` at function entry; same for `label`. Reject empty strings with a clear error message.
  - **Acceptance**: helper validates input; existing call sites with non-empty strings unchanged.

- **AN9-E.10 — TST-M12 `audit_testing_framework.sh` integration** (0.1 day)
  - Audit what the script does; if useful, wire into `scripts/test_tier4_nightly_candidates.sh`; otherwise remove.
  - Audit recommendation: integrate.
  - **Acceptance**: script wired OR removed; documented in `CLAUDE.md`.

- **AN9-E.11 — TST-M13 `TraceSequenceProbe` tier decision** (0.05 day)
  - Either promote `TraceSequenceProbe` from Tier 4 → Tier 2 (if runtime budget allows per TST-M13), OR document in CLAUDE.md why it's Tier-4-only.
  - Default: document (simpler; no perf risk).
  - **Acceptance**: doc updated.

- **Regression test**: full gate; `scripts/test_tier0_hygiene.sh` PASS.
- **Cascade**: ~10-15 script/test edits.

### AN11-F — Test LOW batch

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

### AN11-G — AN11 closure

- **Files**: `CHANGELOG.md`; `scripts/test_lib.sh` final review
- **Acceptance**: PR merged; full gate + rust gate PASS; new suites registered in CI

---

## 15. Phase AN12 — Documentation, themes, closure

**Goal**: synthesise the AN1..AN11 deltas, deliver the cross-cutting Theme 4.1 (discharge index) and Theme 4.4 (SMP inventory — confirming AN9 work landed), batch DOC-M01..M08 + DOC LOWs, **mark all 11 absorbed DEF-* items RESOLVED in the existing `docs/audits/AUDIT_v0.29.0_DEFERRED.md` file (no new DEFERRED file created)**, update `WORKSTREAM_HISTORY.md`, refresh `CLAUDE.md`, bump version, and close WS-AN.

**Effort**: 3 days. **Blocks**: workstream closure (final gate). **Branch**: same WS-AN branch.

### AN12-A — Theme 4.1 deliverable: closure-form discharge index

- **Audit reference**: §4.1 Cross-cutting theme
- **Files**:
  - `docs/audits/AUDIT_v0.30.6_DISCHARGE_INDEX.md` (new) — the discharge artifact
  - `SeLe4n/Kernel/CrossSubsystem.lean` — references the index from inline cross-references
- **Total effort**: ~1 day. **Cascade**: ~17 theorem-docstring updates across 3 themes.

**Sub-sub-task breakdown** (5 commits):

- **AN12-A.1 — Scaffold file + methodology section** (0.1 day)
  - Create `docs/audits/AUDIT_v0.30.6_DISCHARGE_INDEX.md` with:
    - Header: Plan ID, workstream, source audit, baseline, author, date
    - §1 "Methodology" — explains the row format (Theorem name | File:Line | Hypothesis names | Discharge site | Reachability check)
    - §2 "Theme index" — table of contents for the three theme sections
  - **Acceptance**: file scaffold committed; §1 §2 visible.

- **AN12-A.2 — Theme A: CDT post-state witnesses (6 entries)** (0.25 day)
  - Section "§3.A — CDT post-state discharge (H-04 / AN4-C)"
  - Rows (one per CDT-modifying operation): `cspaceCopy`, `cspaceMove`, `cspaceMutate`, `cspaceMint`, `cspaceDelete`, `cspaceRevoke`.
  - For each row: theorem name, file:line, `hCdtCompleteness` + `hCdtAcyclicity` hypothesis witness-threading pattern, canonical discharge site in `CrossSubsystem.lean`, a `#check` expression demonstrating reachability on one representative state.
  - **Acceptance**: 6 CDT rows committed; each row has all 5 fields filled.

- **AN12-A.3 — Theme B: Projection closures (6 entries)** (0.3 day)
  - Section "§3.B — Projection closures (H-07 / AN6-A / AK6F.20b)"
  - Rows (one per cap-only dispatch arm): `schedContextConfigure`, `schedContextBind`, `schedContextUnbind`, `lifecycleRetype`, `tcbSuspend`, `tcbResume`.
  - For the substantively-discharged target from AN6-A.2/A.3/A.4: "DISCHARGED at AN6-A.2 (or .3/.4)" + commit SHA.
  - For the remaining 5: discharge recipe described in prose (which frame lemmas, in what order); cross-reference the `AN6-A.6` template recipe.
  - **Acceptance**: 6 projection-closure rows committed; discharged row has commit SHA; remaining rows have named recipes.

- **AN12-A.4 — Theme C: Schedule closures (5 entries)** (0.2 day)
  - Section "§3.C — Schedule closures (SC-M02 / AN5-D)"
  - Rows: `setPriorityOp`, `setMCPriorityOp`, `schedContextBind` (schedule-projection arm), `schedContextConfigure` (schedule-projection arm), `serviceRevoke` (schedule-projection arm).
  - For each: `hSchedProj` closure threading pattern, discharge site.
  - **Acceptance**: 5 schedule-closure rows committed.

- **AN12-A.5 — Inline cross-references + closure witness** (0.15 day)
  - At each of the 17 theorem's docstrings, insert:
    ```
    -- Discharge: see docs/audits/AUDIT_v0.30.6_DISCHARGE_INDEX.md §3.{A,B,C}-<entry>
    ```
  - Add a marker theorem in `CrossSubsystem.lean`:
    ```lean
    theorem closureForm_discharge_index_documented : True := trivial
    -- Cross-reference: docs/audits/AUDIT_v0.30.6_DISCHARGE_INDEX.md
    ```
  - Add to `scripts/website_link_manifest.txt`.
  - **Acceptance**: 17 docstrings updated; marker theorem present; website-links PASS.

- **Regression test**: smoke gate; `check_website_links.sh` PASS at AN12-A.5.

### AN12-B — Theme 4.4 deliverable: SMP-inventory confirmation (AN9 absorbed the SMP work)

- **Audit reference**: §4.4 Cross-cutting theme
- **Files**:
  - `SeLe4n/Kernel/Concurrency/Assumptions.lean` (new) — single-core inventory module
  - `docs/spec/SELE4N_SPEC.md` §6 — cross-reference
- **Total effort**: ~0.75 day. **Cascade**: 1 new module + 1 SPEC cross-reference.

**Sub-sub-task breakdown** (4 commits):

- **AN12-B.1 — Scaffold module + inventory entry schema** (0.15 day)
  - New `SeLe4n/Kernel/Concurrency/Assumptions.lean` with structure:
    ```lean
    structure SmpLatentAssumption where
      identifier : Lean.Name
      singleCoreWitness : String  -- what holds today
      smpDischarge : String       -- what must hold under concurrency
      sourceTheorem : Lean.Name
      auditReference : String
    ```
  - Plus a `def smpLatentInventory : List SmpLatentAssumption := [ ... ]` aggregator.
  - Module-level tag: `-- This module is post-1.0 SMP refactor surface. See SELE4N_SPEC.md §6.`
  - **Acceptance**: module compiles; schema in place.

- **AN12-B.2 — Inventory entries — capability / lifecycle / scheduler** (0.25 day)
  - Add 5 entries, one `def` per site, each with filled-in fields:
    1. `cspaceLookupMultiLevel_smpLatent` (H-05 / AN4-D) — resolved CNode validity across calls
    2. `cspaceCopyMoveMutate_smpLatent` — CDT post-state composition assumes no concurrent mutation
    3. `lifecyclePreRetypeCleanup_smpLatent` — sequential cleanup ordering
    4. `serviceHasPathTo_smpLatent` (SVC-M01 / AN4-H) — graph traversal is non-atomic
    5. `timerTickReplenishmentPipeline_smpLatent` — timer + replenishment pipeline atomicity
  - **Acceptance**: 5 entries present; each has all 5 fields; module builds.

- **AN12-B.3 — Inventory entries — foundation / architecture** (0.2 day)
  - Add 3 more entries:
    6. `typedIdDisjointness_smpLatent` (H-10 / AN2-D) — AN2-D's invariant holds structurally; SMP invariant still holds but needs atomicity on `storeObject`
    7. `architecture_singleCoreOnly_smpLatent` — already explicit in `Architecture/Assumptions.lean`; this entry cross-links it
    8. `bootFromPlatform_currentCore_is_zero_smpLatent` (CX-M03 / AN6-F) — boot bridge currently-core-zero
  - Post-AN2-C, `RegisterFile.BEq` (H-11) drops out of inventory because the `Fin 32` refactor makes concurrency a non-issue for register-file equality.
  - **Acceptance**: inventory now has 8 entries; total aggregator list `smpLatentInventory.length = 8`.

- **AN12-B.4 — SPEC §6 cross-reference + module hygiene** (0.15 day)
  - Add `docs/spec/SELE4N_SPEC.md` §6 new subsection "§6.X — SMP-Latent Single-Core Assumptions" listing the 8 inventory entries in tabular form with cross-references back to the Lean module.
  - Mark the module as a "staged-for-hardware-binding" module per PLT-M07 convention; ensure it's wired into the `Platform.Staged` meta-module (AN7-D PLT-M07).
  - Register in `scripts/website_link_manifest.txt`.
  - **Acceptance**: SPEC section visible; `check_website_links.sh` PASS; module builds.

- **Regression test**: smoke gate; module gate `lake build SeLe4n.Kernel.Concurrency.Assumptions`.
- **Cascade**: 1 new module; SPEC update.

### AN12-C — Documentation MEDIUM batch (DOC-M01..M08)

- **Audit IDs**: DOC-M01..M08
- **Plan**:
  - **DOC-M01**: covered by AN1-A (i18n READMEs included).
  - **DOC-M02**: covered by AN7-D (PLT-M07 staged-modules wiring).
  - **DOC-M03**: add per-file SPDX headers `// SPDX-License-Identifier: GPL-3.0-or-later` to all Rust files (`rust/**/*.rs`); add `-- SPDX-License-Identifier: GPL-3.0-or-later` to all Lean files missing it. Mechanical pass; ~150 files.
  - **DOC-M04**: covered by AN0-A baseline + per-phase CLAUDE.md large-files-list refresh; AN12 final refresh consolidates.
  - **DOC-M05**: regenerate `docs/codebase_map.json` post AN1..AN9 via `scripts/generate_codebase_map.py`; verify README metric table matches via `scripts/sync_readme_from_codebase_map.sh --check`.
  - **DOC-M06**: covered by AN1-A (all 10 i18n READMEs verified).
  - **DOC-M07**: add new `WORKSTREAM_HISTORY.md` entry "WS-AN post-audit-remediation" enumerating C-01..C-03, H-01..H-24 finding IDs and their disposition.
  - **DOC-M08**: create `CONTRIBUTING.md` covering contributor expectations, branch policy, test gates, and the C-03 hook installation. Also document the `pull_request_target` non-use as a security decision.
- **Acceptance**: each DOC-M addressed
- **Regression test**: smoke gate; `check_website_links.sh` PASS; `check_version_sync.sh` PASS
- **Cascade**: DOC-M03 ~150 file headers (mechanical, low-risk)

### AN12-D — Documentation LOW batch

- **Audit IDs**: 5 LOW per audit §2.10
- **Plan**:
  - Annotate or remove `docs/dev_history/audits/audit_findings_provided_by_me.md`
  - Establish CLAUDE.md "Active workstream context" archive convention: keep last 3 releases inline, archive older to `docs/CLAUDE_HISTORY.md`
  - "One active audit at a time" convention documented in `docs/audits/README.md` (new short doc explaining the audit-doc lifecycle: COMPREHENSIVE → ERRATA → DEFERRED → archive into `docs/dev_history/audits/`)
  - `.gitignore` verified adequate (no change)
  - Test harness file naming discipline verified (no change)
- **Acceptance**: each LOW addressed
- **Regression test**: smoke gate

### AN12-E — Theme 4.5 / 4.6 inline-marker hygiene pass

- **Audit references**: §4.5 (workstream IDs in comments) and §4.6 (stale forward references)
- **Files**: codebase-wide comment grep
- **Total effort**: ~1 day. **Cascade**: ~2000+ comment edits across ~200 files (trivially low-risk per commit).

**Sub-sub-task breakdown** (6 commits, selective-scope approach per §20 question 6):

- **AN12-E.1 — Inventory + classification pass** (0.2 day)
  - `grep -rn "WS-[A-Z]\|\bAK[0-9]\|\bAJ[0-9]\|\bAI[0-9]\|\bAH[0-9]\|\bAG[0-9]\|\bAF[0-9]\|\bAE[0-9]\|\bAD[0-9]\|\bAC[0-9]\|\bAB[0-9]\|\bAA[0-9]" SeLe4n/ rust/ tests/ scripts/ --include="*.lean" --include="*.rs" --include="*.sh"` into a temporary inventory file.
  - Classify each marker into one of three buckets (tag with `[HIST]`, `[DEFER]`, `[ROT]` prefixes):
    - **[HIST]** — historical completed-work reference (legitimate; leave alone)
    - **[DEFER]** — deferred-work pointer; retarget to canonical `DEF-*` ID per AN1-C pattern
    - **[ROT]** — workstream-cadence rot; convert to `// see WORKSTREAM_HISTORY:<id>` short cross-reference
  - Estimated counts after classification: ~3000 [HIST] (leave as-is), ~20 [DEFER] (retarget), ~2000 [ROT] (shorten). The bulk of work is [ROT].
  - **Acceptance**: classified inventory committed (ephemeral; deleted at AN12-E.6).

- **AN12-E.2 — [DEFER] retargets (≤30 sites; high-priority)** (0.15 day)
  - These are the actually-incorrect forward references that AN1-C missed. Each gets retargeted to a live WS-AN sub-task ID (AN9-*, AN10-*, etc.) per the §16 absorption map. No retarget points to a DEF-* entry unless that entry is in `AUDIT_v0.29.0_DEFERRED.md` AND the source-side TODO is tracking a RESOLVED row (in which case the TODO gets removed entirely — there is no live deferred work to point at).
  - **Acceptance**: all [DEFER]-tagged markers retargeted; grep for deferred-work pointers to closed workstreams returns 0 non-historical matches.

- **AN12-E.3 — [ROT] batch 1: IPC + Scheduler subsystems (~500 markers)** (0.2 day)
  - Bulk convert inline workstream markers in `SeLe4n/Kernel/IPC/` and `SeLe4n/Kernel/Scheduler/` to short `// see WH:<id>` form.
  - Commit as a single atomic rewrite; reviewer verifies via diff that only comment content changed.
  - **Acceptance**: batch commit lands; smoke gate PASS.

- **AN12-E.4 — [ROT] batch 2: Capability + Lifecycle + Service + SchedContext (~400 markers)** (0.15 day)
  - Same pattern.
  - **Acceptance**: smoke gate PASS.

- **AN12-E.5 — [ROT] batch 3: Architecture + IF + CrossSubsystem + Foundation + Model (~600 markers)** (0.15 day)
  - Same pattern.
  - **Acceptance**: smoke gate PASS.

- **AN12-E.6 — [ROT] batch 4: Platform + API + Rust + tests + scripts (~500 markers) + inventory cleanup + metric** (0.15 day)
  - Same pattern; plus delete the ephemeral inventory from AN12-E.1.
  - Extend `scripts/ak7_cascade_baseline.sh` with `INLINE_WORKSTREAM_MARKERS` metric (floor = post-sweep count; should NOT grow in future PRs).
  - **Acceptance**: total inline-marker count dropped by ~40% (estimated 5000 → 3000); monotonicity metric committed to baseline; `check_website_links.sh` PASS.

- **Regression test (cumulative)**: smoke gate after each batch commit; `check_website_links.sh` PASS at AN12-E.6.
- **Cascade**: ~2000+ mechanical comment edits across 6 commits.

### AN12-F — Theme 4.7 file-split completion pass

- **Audit reference**: §4.7
- **Files**: any kernel `.lean` file ≥ 2000 LOC after AN3-C/D, AN4-F (CAP-M03), AN5-A, AN6-E
- **Plan**:
  1. Re-scan with `wc -l` after AN3..AN6 splits land. Verify the original 5 monolithic files are below the 2000-LOC ceiling.
  2. If any file remains above ceiling (e.g., `Capability/Operations.lean` at 1651 LOC is borderline; `Model/Object/Structures.lean` at 2769 LOC may still need a split), schedule a mini-split commit here.
  3. Update `CLAUDE.md` "Known large files" list to reflect the post-AN12 sizes.
  4. Document the 2000-LOC ceiling convention in `CONTRIBUTING.md` (links to AN12-C / DOC-M08).
- **Acceptance**: no production `.lean` file > 2000 LOC except `CHANGELOG.md` and other documentation/historical content per audit's own exception
- **Regression test**: full gate
- **Cascade**: 0–2 additional file splits depending on residual sizes

### AN12-G — Close `AUDIT_v0.29.0_DEFERRED.md` entries in-place (no new DEFERRED file created)

- **Files**: `docs/audits/AUDIT_v0.29.0_DEFERRED.md` (edit in-place; no new file)
- **Plan**: per the maintainer directive, WS-AN does NOT create a `AUDIT_v0.30.6_DEFERRED.md` sibling. Instead, every row in the existing `AUDIT_v0.29.0_DEFERRED.md` is annotated RESOLVED with the closing WS-AN sub-task ID and commit SHA. Per the §16 absorption map, all 11 rows close:
  - DEF-A-M04 — **RESOLVED in AN9-A** (commit SHA)
  - DEF-A-M06 / DEF-AK3-I — **RESOLVED in AN9-B**
  - DEF-A-M08 — **RESOLVED in AN9-C**
  - DEF-A-M09 / DEF-AK3-K — **RESOLVED in AN9-C**
  - DEF-C-M04 — **RESOLVED in AN9-D**
  - DEF-P-L9 — **RESOLVED in AN7-D.2** (primary); AN9-E records cross-reference
  - DEF-R-HAL-L14 — **RESOLVED in AN9-F**
  - DEF-F-L9 — **RESOLVED in AN2-G**
  - DEF-AK2-K.4 — **RESOLVED in AN5-F** (RPi5-canonical-config witness; general theorem retains parameterised form)
  - DEF-AK7-E.cascade — **RESOLVED in AN10-A**
  - DEF-AK7-F.cascade — **RESOLVED in AN10-B (reader) + AN10-C (writer)**
- Add a closure summary at the top of `AUDIT_v0.29.0_DEFERRED.md` stating "All 11 items closed under WS-AN (v0.30.7). Zero items carried past v1.0.0."
- No new `AUDIT_v0.30.6_DEFERRED.md` sibling file is created because WS-AN produces zero deferred items (§15.1 rule enforced at gate).
- **Acceptance**: every row in `AUDIT_v0.29.0_DEFERRED.md` annotated RESOLVED with commit SHAs; closure summary at top; `grep -c "^### DEF-" docs/audits/AUDIT_v0.29.0_DEFERRED.md` matches `grep -c "RESOLVED in AN" docs/audits/AUDIT_v0.29.0_DEFERRED.md` (every row resolved).
- **Regression test**: smoke gate; `check_website_links.sh` PASS
- **Cascade**: 1 file edited in-place (~11 row annotations + 1 summary paragraph).

### AN12-H — `WORKSTREAM_HISTORY.md` WS-AN entry

- **Files**: `docs/WORKSTREAM_HISTORY.md`
- **Plan**: append the canonical WS-AN closure entry following the WS-AK/WS-AM precedent:
  - WS-AN identity: `v0.30.6 → v1.0.0` (or v0.30.7+ maintainer-selected patch-only sequence)
  - 13-phase breakdown (AN0..AN12) with gate-state table
  - Cross-reference to:
    - `docs/audits/AUDIT_v0.30.6_COMPREHENSIVE.md`
    - `docs/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md` (this doc)
    - `docs/audits/AUDIT_v0.29.0_DEFERRED.md` (in-place RESOLVED annotations landed in AN12-G)
    - `docs/audits/AUDIT_v0.30.6_DISCHARGE_INDEX.md` (AN12-A)
  - Finding-count arithmetic: 196 audit findings closed (2 actionable CRITICAL + 23 HIGH + 71 MEDIUM + 58 LOW + 40 INFO) + **11 absorbed DEF-* items all RESOLVED** + 4 new AN9 sub-tasks (DEF-R-HAL-L17..L20) all closed in-phase
  - Deferred-items count: **zero past v1.0.0**
- **Acceptance**: entry committed; gate-state table filled
- **Regression test**: smoke gate

### AN12-I — `CLAUDE.md` Active-workstream-context refresh

- **Files**: `CLAUDE.md`
- **Plan**:
  1. Replace the top "Active workstream context" paragraph with a WS-AN summary (parallel to the current WS-AK AK10 paragraph).
  2. Per AN12-D LOW item: archive pre-WS-AK paragraphs to `docs/CLAUDE_HISTORY.md` so the active file returns under the 500-line-chunked-read threshold.
  3. Update "Known large files" list — `CHANGELOG.md` grows, `Structural.lean`/`Preservation.lean`/`IF Operations.lean` shrink, new DISCHARGE_INDEX file is small and doesn't qualify; several new AN9-created modules (`VSpaceBoot.lean`, `BarrierComposition.lean`, `smp.rs`, `psci.rs`, etc.) added to the layout.
  4. Update "Next workstream" line: since WS-AN closed every deferred item, set to "**v1.0.0 release-ready; no hardware-binding or cascade backlog**" with cross-reference to the RESOLVED rows in `docs/audits/AUDIT_v0.29.0_DEFERRED.md`.
- **Acceptance**: CLAUDE.md active section reflects WS-AN closure; archive file created; large-files list refreshed
- **Regression test**: smoke gate

### AN12-J — Version bump and release trajectory

- **Files**: 15 version-bearing files (per `scripts/check_version_sync.sh` canonical list)
- **Plan**:
  1. Per AK10-C precedent, **do NOT tag v1.0.0 programmatically** — the v1.0.0 tag is a maintainer manual action.
  2. Instead, bump patch version `0.30.6 → 0.30.7` (or whatever sequence the maintainer selects) for the WS-AN release cut.
  3. `scripts/check_version_sync.sh` PASS at the new version across all 15 files (`lakefile.toml`, `rust/Cargo.toml`, `README.md` + 10 i18n READMEs, `docs/spec/SELE4N_SPEC.md`, `CLAUDE.md`, and any CHANGELOG header).
  4. If the maintainer chooses `v1.0.0` as the WS-AN cut, perform the tag in a separate commit after the plan lands.
- **Acceptance**: `check_version_sync.sh` PASS at the new version
- **Regression test**: full gate + rust gate + `check_version_sync.sh`

### AN12-K — CHANGELOG entry consolidation

- **Files**: `CHANGELOG.md`
- **Plan**: consolidate AN1..AN11 per-phase entries under a single `## [0.30.7] — 2026-MM-DD (WS-AN closure)` (or equivalent version) heading, structured as:
  ```
  ### Addressed (AUDIT_v0.30.6_COMPREHENSIVE.md)
   - Critical: C-01, C-03 (C-02 resolved in prior commit)
   - High: H-01..H-24 (23 closed substantively in AN1..AN11; H-22 addressed post-downgrade in AN11-C)
   - Medium: 71/71 closed across AN3..AN11
   - Low: 58/58 closed in batch commits
  ### Absorbed from AUDIT_v0.29.0_DEFERRED.md (all 11 RESOLVED)
   - Hardware-binding (AN9): DEF-A-M04/M06/M08/M09, DEF-C-M04, DEF-P-L9, DEF-R-HAL-L14
   - Cascade (AN10): DEF-AK7-E, DEF-AK7-F.reader, DEF-AK7-F.writer
   - Proof-hygiene / semantic: DEF-F-L9 (AN2-G), DEF-AK2-K.4 (AN5-F)
  ### New AN9 items (all closed in-phase)
   - DEF-R-HAL-L17/L18/L19/L20 (bounded WFE / parameterized barriers / OSH / SMP)
  ### Deferred past v1.0.0
   - **NONE** — zero items carry past this release per WS-AN directive.
  ### Thanks
   - ...
  ```
- **Acceptance**: single coherent entry; no "deferred past v1.0.0" items beyond the explicit NONE line; cross-references to `AUDIT_v0.29.0_DEFERRED.md` RESOLVED rows present
- **Regression test**: smoke gate; `check_website_links.sh` PASS

### AN12-L — Final release gate

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

### AN12-M — Archive plan files

- **Files**:
  - `docs/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md` (this doc) → `docs/dev_history/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md`
  - `docs/audits/AUDIT_v0.29.0_COMPREHENSIVE.md` → `docs/dev_history/audits/AUDIT_v0.29.0_COMPREHENSIVE.md`
  - `docs/audits/AUDIT_v0.29.0_DEFERRED.md` → `docs/dev_history/audits/AUDIT_v0.29.0_DEFERRED.md`
  - `docs/audits/AUDIT_v0.29.0_ERRATA.md` → `docs/dev_history/audits/AUDIT_v0.29.0_ERRATA.md`
- **Plan**: per audit §2.10 "one active audit at a time" convention (new in AN12-D). When WS-AN closes, archive this plan + the v0.29.0 parent audit alongside it. The v0.30.6 COMPREHENSIVE stays in `docs/audits/` until the next audit cuts, then it archives too.
- **Acceptance**: files moved; every reference (CLAUDE.md, WORKSTREAM_HISTORY, README) updated to the archived paths; `check_website_links.sh` updated manifest; `scripts/website_link_manifest.txt` refreshed
- **Regression test**: smoke gate + `check_website_links.sh` PASS

### AN12-N — WS-AN closure

- **Files**: a final summary commit referencing the full WS-AN disposition
- **Acceptance**:
  - Every sub-task AN0-A..AN12-M accounted for
  - WORKSTREAM_HISTORY.md records closure with gate-state table
  - `docs/audits/` contains only the v0.30.6 comprehensive + the post-audit DISCHARGE_INDEX + the new DEFERRED
  - The plan itself is archived under `docs/dev_history/audits/`
- **Regression test**: the AN12-L final release gate

---

## 14. Cross-cutting theme handling — detailed placement rationale

This section explains why the seven cross-cutting themes identified in
`AUDIT_v0.30.6_COMPREHENSIVE.md` §4 are folded into the per-subsystem
phases rather than each given its own dedicated phase, plus how they
interact.

### 14.1 Theme 4.1 — Closure-form proof obligations

**Where addressed**: AN4-C (CDT bridges), AN6-A (all 6 projection theorems substantively discharged), AN12-A (index artifact aggregating AN4-C + AN6-A + SC-M02 closures).

**Rationale**: the three sub-patterns (CDT post-state, `hProjEq`, `hSchedProj`) live in different subsystems and their discharges are
already different shapes. Addressing each in the phase that owns its
subsystem keeps the cascade bounded. The index artifact in AN12-A
aggregates all three into a single auditable deliverable without
forcing a monolithic phase.

**Interaction**: AN4-C's CDT bridge template informs AN6-A's choice of
which projection theorem to substantively discharge first (the CDT
pattern generalises to the projection-closure pattern). AN12-A then
indexes both as a single artifact. With AN6-A discharging ALL SIX arms
substantively, AN12-A's §3.B Projection Closures section contains six
DISCHARGED rows with commit SHAs — no residual closure-form entries.

### 14.2 Theme 4.2 — Tuple-projection brittleness → named structures

**Where addressed**: AN2-G (`allTablesInvExtK` — foundation anchor), AN3-B (`ipcInvariantFull`), AN4-F (CAP-M05 `capabilityInvariantBundle`), plus incidental at AN6-E (other bundles surfaced during IF split).

**Rationale**: named-structure refactor touches every consumer. Doing
it per-subsystem in the subsystem's own phase means each cascade runs
once against a stable set of imports. Doing it as a monolithic phase
would require all subsystem phases to pause while the refactor lands —
worse throughput.

**Interaction**: AN2-G establishes the convention (how to write the
bridge theorem, how to migrate destructures). AN3-B, AN4-F follow the
convention mechanically. AN12 does NOT need to re-run any
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

**Where addressed**: AN4-D (H-05 first inventory entry), AN6-F / CX-M03 (`bootFromPlatform_currentCore_is_zero_witness`), **AN9-J (SMP bring-up lands substantively — code+test merged, runtime-gated by `smp_enabled=false` default)**, AN12-B (post-AN9-J confirmation inventory — module records which items transitioned from "SMP-latent" to "SMP-implemented, runtime-gated").

**Rationale**: the inventory is a docs/pre-SMP-checklist artifact, not
a behavior change. Per-subsystem entries land as the subsystem gets
touched; AN9-J absorbs the real SMP bring-up (PSCI, per-core init, QEMU `-smp 4` smoke); AN12-B then aggregates the inventory into a single module that documents which entries transitioned from "SMP-latent single-core assumption" to "SMP-implemented runtime-gated" at v1.0.0.

**Interaction**: AN12-B's module imports no kernel modules — it is
docs-only. AN4-D / CX-M03 / AN9-J are the proof-level + implementation
witnesses that AN12-B indexes.

### 14.5 Theme 4.5 — Workstream IDs in comments

**Where addressed**: AN12-E.

**Rationale**: a mechanical inline-marker hygiene pass. Late-phase
because every prior phase introduces new AN-* markers; doing it once
at AN12 is more efficient than pausing to re-run it after each phase.

**Interaction**: AN12-E's grep baseline is captured in AN0-A and
AN12-E's input is the AN1..AN11 cumulative inline-marker count.

### 14.6 Theme 4.6 — Stale forward references

**Where addressed**: AN1-C (source-side retarget of WS-V/AG10 TODOs to live AN9-F/G/H/I/J sub-task IDs), AN12-E (codebase-wide hygiene pass).

**Rationale**: the urgent retargets land in AN1 (closes H-24 CRITICAL-ish
gate item); the broader cleanup aggregates in AN12.

**Interaction**: AN1-C targets the 6 flagged sites; AN12-E catches the
remainder and, after AN9 lands, removes TODO markers that are now tracking RESOLVED work (nothing to track any more).

### 14.7 Theme 4.7 — Monolithic file splits

**Where addressed**: AN3-C (Structural.lean), AN3-D (NotificationPreservation + CallReplyRecv), AN4-F / CAP-M03 (Preservation.lean), AN4-G / LIF-M05 (Lifecycle/Operations.lean), AN5-A (Scheduler/Preservation.lean), AN6-E / IF-M03 (IF/Operations.lean), AN12-F (residual sweep).

**Rationale**: each split is subsystem-local; doing each in its own
phase preserves reviewability (smaller diffs, single reviewer domain).
AN12-F sweeps any remaining ≥ 2000 LOC files after AN3..AN6 land.

**Interaction**: AN12-F depends on all prior splits having landed.

---

## 15. Closure criteria & v1.0.0 release readiness checklist

This section is the **single canonical gate** for declaring WS-AN
complete. Every item below must be verifiable.

### 15.1 Audit finding disposition (mandatory — zero deferrals permitted)

| Severity | Audit count | WS-AN target | Verification |
|----------|------------:|--------------|--------------|
| CRITICAL | 3 (1 resolved pre-WS-AN) | 2/2 closed in AN1 | C-01 (AN1-A), C-03 (AN1-B); C-02 already resolved |
| HIGH | 24 | **23/23 closed** in AN1..AN11 (H-22 downgraded LOW per audit, addressed AN11-C) | each has a sub-task ID; per-PR evidence |
| MEDIUM | 71 | **71/71 closed** across AN3..AN11 | per-PR evidence |
| LOW | 58 | **58/58 closed** in batch commits | per-PR evidence |
| INFO | 40 | n/a — verifications, not work | (informational) |
| DEF-* (v0.29.0 DEFERRED) | 11 | **11/11 absorbed + RESOLVED** (7 hardware-binding in AN9, 2 AK7 cascades in AN10, 1 eventuallyExits in AN5-F, 1 allTablesInvExtK structure refactor in AN2-G) | per-PR evidence + AUDIT_v0.29.0_DEFERRED.md RESOLVED-with-commit-SHA entries |

**Rule (strengthened)**: **No finding may be deferred past v1.0.0.** Every CRITICAL, HIGH, MEDIUM, LOW finding from `AUDIT_v0.30.6_COMPREHENSIVE.md` has a live sub-task ID in §3..§15 that must close substantively before WS-AN ships. Every DEF-* entry in the pre-existing `AUDIT_v0.29.0_DEFERRED.md` has a live sub-task ID that closes it substantively and updates the tracking row to RESOLVED. **WS-AN does NOT create a new `AUDIT_v0.30.6_DEFERRED.md` file**; the `AUDIT_v0.29.0_DEFERRED.md` file is updated in-place with per-row RESOLVED annotations + commit SHAs in AN12-G.

**Consequence**: if any sub-task is blocked by a toolchain or hardware constraint the plan cannot reasonably close, the workstream itself pauses and is escalated to the maintainer before any defer decision is made. Deferral is NOT an automatic fallback; it requires explicit maintainer approval that would amend this plan.

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
- [ ] `docs/audits/AUDIT_v0.29.0_DEFERRED.md` edited in-place with all 11 rows annotated RESOLVED + commit SHAs (zero deferred past v1.0.0; **no new `AUDIT_v0.30.6_DEFERRED.md` file created**)
- [ ] `docs/audits/AUDIT_v0.30.6_DISCHARGE_INDEX.md` committed
- [ ] `CONTRIBUTING.md` committed (DOC-M08)
- [ ] All Rust + Lean files have SPDX headers (DOC-M03)
- [ ] `docs/spec/SELE4N_SPEC.md` updated with §5/§6/§7 deltas referenced in AN3..AN6

### 15.5 Hardware-fidelity gate (MANDATORY — AN9 absorbs hardware-binding into pre-1.0)

- [ ] BCM2712 hardware constants cross-checked (existing `scripts/test_hw_crosscheck.sh` PASS)
- [ ] QEMU boot if emulator available (`scripts/test_qemu.sh` PASS or skip-with-log)
- [ ] QEMU `-smp 4` boot smoke (`scripts/test_smp_smoke.sh` PASS; exercises AN9-J)
- [ ] No regression in `docs/hardware_validation/*.md` reports
- [ ] New QEMU validation harnesses from AN9 all PASS (TLB+cache AN9-A, SVC round-trip AN9-F, SMP AN9-J)

### 15.6 Fixture & determinism gate (mandatory)

- [ ] All 3 fixtures have sha256 companions and `test_tier2_trace.sh` enforces all 3
- [ ] `lake exe sele4n` byte-identical to `tests/fixtures/main_trace_smoke.expected`
- [ ] `nightly_determinism.yml` cross-commit drift check confirmed passing
- [ ] `tests/fixtures/README.md` documents regeneration (TST-M10)

### 15.7 Maintainer-decision items (NOT gated by WS-AN automation)

- Final v1.0.0 tag — manual maintainer action per AK10-C precedent
- Whether DOC-M03 SPDX header pass lands as a single mechanical PR or batched per-subsystem
- Whether AN9-J's `smp_enabled` flag flips to default-true at v1.0.0 or ships default-false with a patch-release flip after real-hardware SMP validation

---

## 16. Absorption map — every `AUDIT_v0.29.0_DEFERRED.md` entry maps to a live WS-AN sub-task

**Directive**: per the maintainer, WS-AN does NOT create a new `AUDIT_v0.30.6_DEFERRED.md` file. Every one of the 11 entries in `AUDIT_v0.29.0_DEFERRED.md` is absorbed into pre-1.0 work via a named AN sub-task; at AN12-G each row is annotated RESOLVED with the closing commit SHA. No new deferred items are created during WS-AN execution.

This section is the **absorption map**: given any DEF-* ID, find the WS-AN sub-task that closes it.

### 16.1 Hardware-binding category (all absorbed in AN9 + AN7-D.2)

| Deferred ID | Audit Finding | WS-AN sub-task (substantive closure) | Phase | Expected commit target |
|-------------|---------------|--------------------------------------|-------|------------------------|
| DEF-A-M04 | A-M04 (TLB+cache composition) | **AN9-A** (TLB+cache composition full closure via FFI witness layer) | AN9 | PR-12, AN9-A.1..A.6 |
| DEF-A-M06 / DEF-AK3-I | A-M06 (`tlbBarrierComplete`) | **AN9-B** (build-time scanner + FFI witness + substantive preservation) | AN9 | PR-12, AN9-B.1..B.5 |
| DEF-A-M08 | A-M08 (MMU BarrierKind) | **AN9-C** (BarrierKind composition algebra; MMU update theorem) | AN9 | PR-12, AN9-C.1..C.5 |
| DEF-A-M09 / DEF-AK3-K | A-M09 (Device BarrierKind) | **AN9-C** (same sub-task; MMIO write ordering theorem) | AN9 | PR-12, AN9-C.1..C.5 |
| DEF-C-M04 | C-M04 (`suspendThread` atomicity) | **AN9-D** (HAL interrupt-disable bracket + clippy discipline) | AN9 | PR-12, AN9-D.1..D.4 |
| DEF-P-L9 | P-L9 (VSpaceRoot boot exclusion) | **AN7-D.2** (full `RPi5/VSpaceBoot.lean` shim closes non-empty-config boot bridge); AN9-E cross-reference | AN7 (primary) + AN9 (cross-ref) | PR-10 (primary), PR-12 (cross-ref) |
| DEF-R-HAL-L14 | R-HAL-L14 (SVC FFI wiring) | **AN9-F** (typed-argument marshalling + `sele4n_syscall_dispatch` bridge + QEMU SVC round-trip) | AN9 | PR-12, AN9-F.1..F.7 |

### 16.2 Proof-hygiene / semantic-refactor category (all absorbed in AN2 / AN5 / AN10)

| Deferred ID | Audit Finding | WS-AN sub-task (substantive closure) | Phase | Expected commit target |
|-------------|---------------|--------------------------------------|-------|------------------------|
| DEF-F-L9 | F-L9 (17-deep tuple refactor) | **AN2-G** (`allTablesInvExtK` tuple→structure refactor; deletes tuple form) | AN2 | PR-5, AN2-G.1..G.7 |
| DEF-AK2-K.4 | AK2-K.4 (`eventuallyExits` previously by-design) | **AN5-F** (RPi5-canonical-config substantive witness; general theorem retains parameterised form) | AN5 | PR-9, AN5-F.1..F.6 |
| DEF-AK7-E.cascade | F-M03 (ValidObjId/ValidThreadId rollout) | **AN10-A** (~240 handler-signature migrations across Lifecycle/SchedContext/Scheduler/IpcBuffer/Capability) | AN10 | PR-13, AN10-A.1..A.6 |
| DEF-AK7-F.cascade | F-M04 (reader + writer hygiene) | **AN10-B** (reader: ~304+ raw-match migrations) + **AN10-C** (writer: ~50 storeObjectKindChecked migrations) | AN10 | PR-13, AN10-B.1..B.5 + AN10-C.1..C.3 |

### 16.3 New hardware-binding sub-tasks surfaced by AN1-C (all absorbed in AN9)

These items are NEW in WS-AN (not in `AUDIT_v0.29.0_DEFERRED.md`) but are TODO markers in the Rust HAL that were pointing at the closed `WS-V`/`AG10` workstreams. AN1-C retargets the source-side TODOs to live AN9 sub-task IDs; AN9 closes each substantively.

| New ID | Source | WS-AN sub-task | Expected commit target |
|--------|--------|----------------|------------------------|
| DEF-R-HAL-L17 (bounded WFE) | AN1-C / `lib.rs:62` | **AN9-G** | PR-12, AN9-G.1..G.4 |
| DEF-R-HAL-L18 (parameterized barriers) | AN1-C / `lib.rs:69` | **AN9-H** | PR-12, AN9-H.1..H.4 |
| DEF-R-HAL-L19 (OSH widening) | AN1-C / `lib.rs:84` | **AN9-I** | PR-12, AN9-I.1..I.4 |
| DEF-R-HAL-L20 (secondary-core bring-up / SMP) | AN1-C / `lib.rs:91` | **AN9-J** (largest AN9 sub-task; ships SMP merged but gated off-by-default at runtime via `smp_enabled=false`) | PR-12, AN9-J.1..J.8 |

### 16.4 Closure-form / H-09 / VSpaceBackend items — no new DEF-* entries created

The maintainer directive specifically rejects the prior plan's "defer on toolchain block" / "defer Track B" / "defer VSpaceBackend" escape hatches. These items close substantively in-phase:

- **H-07** (6 closure-form projection theorems): all 6 discharged in **AN6-A** (no `DEF-H-07.partial`). Escalation ladder in §2.4 risk register guarantees at least one proof strategy closes each arm.
- **H-09** (untypedRegionsDisjoint transitive): Track B mandatory in **AN6-C** (no `DEF-H-09.transitive`). `UntypedObject.parent` field added in AN6-C.1; transitive disjointness is the 13th conjunct of `crossSubsystemInvariant`.
- **ARCH-M01** (VSpaceBackend typeclass): wired as production indirection in **AN6-D** (no "forward-looking H3 infrastructure" tag). ARMv8 instance becomes the default production backend.
- **PLT-M02 / PLT-M03** (VSpaceRoot non-empty-config boot bridge): substantive closure in **AN7-D.2** + cross-reference in AN9-E (no `DEF-PLT-M02`).
- **H-18** (MPIDR_CORE_ID_MASK drift): both shared linker symbol (Option A) and build-time assertion (Option B) ship together in **AN8-B** (no `DEF-H-18.linker`).
- **H-19** (EOI loss on handler panic): audit's Option b (EOI before handler invocation per GIC-400) lands in **AN8-C** (no "defer to post-1.0" annotation).
- **FND-M05** (DS-L5 heartbeat fragility): full decomposition to ≤ 200,000 heartbeats in **AN2-F.5** (no `DEF-FND-M05.partial`).

### 16.5 `AUDIT_v0.29.0_DEFERRED.md` final-state expectation (at WS-AN close)

After AN12-G lands, `docs/audits/AUDIT_v0.29.0_DEFERRED.md` has every row annotated:

```
### DEF-A-M04 — TLB+Cache Composition Full Closure
- **RESOLVED in WS-AN**: AN9-A (commit <SHA>)
- **Prior disposition**: AK3-G PARTIAL+DOC → now substantively closed
- [ ... original acceptance criteria retained for audit-trail ... ]
```

The file is preserved in `docs/audits/` (not archived) as the canonical historical record of items that were once deferred; the RESOLVED annotations make clear none carry past v1.0.0. **No sibling `AUDIT_v0.30.6_DEFERRED.md` file is created** because WS-AN produces zero deferred items.

### 16.6 Errata acknowledgement (AUDIT_v0.29.0_ERRATA.md)

All six errata are informational closures under v0.30.6. WS-AN does NOT modify the errata file except E-5 which gets a closure addendum confirming the residual (6 closure-form theorems) is now fully discharged in AN6-A.

| Errata | WS-AN action |
|--------|--------------|
| E-1 (S-H03 verification) | None |
| E-2 (R-HAL-M12 dead-code) | None |
| E-3 (A-H01 three-layer extent) | None |
| E-4 (R-HAL-H02 partial) | None |
| E-5 (NI-H02 composition) | **Addendum in AN6-A.8**: all 6 arms substantively discharged; E-5 residual fully closed |
| E-6 (finding-count arithmetic) | None |

---

## 17. PR mapping & commit ordering

This section sequences the AN0..AN12 sub-tasks into PR batches so a
project lead can plan reviews and contributors know which PRs depend
on which.

### 17.1 Recommended PR sequence

| PR | Phase | Sub-tasks | Title (suggested) | Depends on |
|----|-------|-----------|-------------------|------------|
| PR-1 | AN0 | AN0-A, AN0-B, AN0-C | `WS-AN AN0: workstream plan + baseline` | (none) |
| PR-2 | AN1 | AN1-A, AN1-B, AN1-C, AN1-D | `WS-AN AN1: critical-path blockers (C-01, C-03, H-24)` | PR-1 |
| PR-3 | AN2 (1/3) | AN2-A, AN2-B | `WS-AN AN2.1: Badge + wrapper-type private-mk discipline (H-13, Theme 4.3)` | PR-1 |
| PR-4 | AN2 (2/3) | AN2-C, AN2-D | `WS-AN AN2.2: RegisterFile Fin 32 + typedIdDisjointness (H-10, H-11)` | PR-3 |
| PR-5 | AN2 (3/3) | AN2-E, AN2-F, AN2-G, AN2-H | `WS-AN AN2.3: Foundation MEDIUM batch + 17-tuple refactor (FND-M01..M08, DEF-F-L9 ABSORBED)` | PR-4 |
| PR-6 | AN8 (parallel) | AN8-A..F | `WS-AN AN8: Rust HAL hardening incl. EOI-before-handler (H-17, H-18, H-19 Option b, RUST-M01..M08)` | PR-1 (independent of Lean phases) |
| PR-7 | AN3 | AN3-A..G | `WS-AN AN3: IPC subsystem (H-01 Option A, IPC-M01..M09, Theme 4.7 split)` | PR-5 |
| PR-8 | AN4 | AN4-A..J | `WS-AN AN4: Capability/Lifecycle/Service (H-02..H-06)` | PR-5 |
| PR-9 | AN5 | AN5-A..G | `WS-AN AN5: Scheduler/SchedContext + eventuallyExits closure (SCH/SC MEDIUMs, DEF-AK2-K.4 ABSORBED)` | PR-5 |
| PR-10 | AN7 | AN7-A..G | `WS-AN AN7: Platform/API + full RPi5/VSpaceBoot shim (H-14..H-16, PLT-M02/M03, DEF-P-L9 ABSORBED)` | PR-5 |
| PR-11 | AN6 | AN6-A..H | `WS-AN AN6: Arch/IF/CX (H-07 all-6-arms, H-08, H-09 Track B, ARCH-M01 VSpaceBackend wired)` | PR-7, PR-8, PR-9, PR-10 |
| PR-12 | AN9 (split across 3 sub-PRs if reviewer bandwidth tight) | AN9-A..K | `WS-AN AN9: Hardware-binding closure (TLB+cache, barriers, SVC FFI, SMP)` | PR-6, PR-11 |
| PR-13 | AN10 | AN10-A..D | `WS-AN AN10: AK7 cascade completion (DEF-AK7-E/F ABSORBED, ~600 sites)` | PR-12 |
| PR-14 | AN11 | AN11-A..G | `WS-AN AN11: Tests/CI/Scripts (H-20..H-23)` | PR-13 |
| PR-15 | AN12 (1/2) | AN12-A..F | `WS-AN AN12.1: discharge index, SMP inventory confirmation, doc batch` | PR-14 |
| PR-16 | AN12 (2/2) | AN12-G..N | `WS-AN AN12.2: closure (DEFERRED.md in-place RESOLVED, HISTORY, version, gate)` | PR-15 |

**Parallelism opportunity**: PR-6 (Rust HAL) is independent of all Lean
phases; can land any time after PR-1 and must land before PR-12 (AN9).
PR-7..PR-10 (AN3, AN4, AN5, AN7) are independent of each other and can
land in any order or in parallel once PR-5 (foundation hardening)
merges.

**PR-12 (AN9) sub-split for parallel review**: AN9 is by far the
largest PR at ~2500 LOC delta. Where reviewer bandwidth permits, split
into:
- PR-12a: AN9-A/B/C (TLB+cache+barriers; ~700 LOC)
- PR-12b: AN9-D/E/F (atomicity + VSpaceBoot cross-ref + SVC FFI; ~800 LOC)
- PR-12c: AN9-G/H/I/J/K (bounded WFE + parameterized barriers + OSH + SMP + closure; ~1000 LOC)

PR-14 (AN11) and PR-15/16 (AN12) cannot start until upstream phases land because tests depend on the final kernel surface (including AN9 hardware-binding and AN10 cascade migrations).

### 17.2 Hot-path early landing

If reviewer bandwidth is constrained, prioritise:

1. PR-2 (AN1) — unblocks public-facing CRITICAL items
2. PR-6 (AN8) — independent, can land in background; unblocks PR-12
3. PR-5 (AN2) — foundation; unblocks PR-7..PR-10
4. PR-12 (AN9) — largest phase; start review early even while upstream PRs are still in flight

### 17.3 Per-PR review scope guidance

| PR | Approx LOC delta | Files touched | Reviewer focus |
|----|----:|----:|----------------|
| PR-1 | ~2500 | 1 (this plan) | Plan completeness, audit cross-refs, §16 absorption-map accuracy |
| PR-2 | ~80 | ~15 | Stale-pointer correctness, hook idempotency, live AN9-F..J TODO retargets |
| PR-3 | ~150 | ~10 | Subtype gate cascades, BadgeOverflowSuite extension |
| PR-4 | ~200 | ~25 | Fin 32 refactor cascade, typedIdDisjointness preservation cascade (cascade-heavy) |
| PR-5 | ~600 | ~80 | Heartbeat profile (FND-M05 full decomposition, no partial), 17-tuple → structure migration |
| PR-6 | ~500 | ~12 (rust/) | RAII refactor correctness, MPIDR symbol drift gate (A+B), EOI-before-handler re-entrancy review |
| PR-7 | ~700 | ~15 | Structural.lean split correctness (Theme 4.7), named projections, mandatory Option A primitives extraction |
| PR-8 | ~900 | ~20 | lifecycleRetypeObject visibility cascade, CDT discharge index, mintDerivedCap return type tightening |
| PR-9 | ~500 | ~12 | Scheduler split, blockingGraphAcyclic rename cascade, eventuallyExits RPi5-canonical witness proof |
| PR-10 | ~600 | ~12 | DTB deprecation, Check predicate fail-closed, full RPi5/VSpaceBoot shim + non-empty-config boot bridge |
| PR-11 | ~1100 | ~30 | ALL 6 arms substantively discharged (closure-form template), untypedAncestorRegionsDisjoint Track B, VSpaceBackend wired production-live |
| PR-12 | ~2500 | ~25 (mix Lean+rust) | Hardware-binding FFI witnesses, SVC FFI round-trip, SMP bring-up + `smp_enabled` gating |
| PR-13 | ~1200 | ~80+ | AK7 cascade mechanical migrations; verify monotonicity metrics advance; no silent test regressions |
| PR-14 | ~1500 | ~10 (tests/scripts) | KernelError matrix coverage (≥35 variants), timeout wrapper, named AK6 tests |
| PR-15 | ~600 | ~30 | Discharge index correctness, SMP inventory confirmation (AN9 work landed; items now single-core default but SMP code reviewed + merged) |
| PR-16 | ~300 | ~25 | Version sync, archive moves, CHANGELOG consolidation, DEFERRED.md in-place RESOLVED annotations |

### 17.4 PR-merge gate sequence (each PR's CI must pass)

For each PR:
1. `lake build` PASS
2. `cargo test --workspace` PASS
3. `cargo clippy --workspace -- -D warnings` 0 warnings
4. `./scripts/test_smoke.sh` PASS (smoke gate)
5. For PRs that touch theorems / invariants: `./scripts/test_full.sh` PASS (full gate)
6. For PRs that touch fixtures: `sha256sum -c` on companion files PASS
7. `./scripts/check_version_sync.sh` PASS at the prevailing version (no version bump until AN12-J)
8. `./scripts/check_website_links.sh` PASS
9. For PR-12 (AN9): `scripts/test_qemu.sh` PASS (or skip-with-log); `scripts/test_smp_smoke.sh` PASS on QEMU `-smp 4`
10. For PR-13 (AN10): `scripts/ak7_cascade_check_monotonic.sh` PASS against the AN10-advanced baseline

The AN12-L final release gate is the master verification; per-PR CI
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
| H-20 | AN11 | AN11-A |
| H-21 | AN11 | AN11-B |
| H-22 (LOW post-downgrade) | AN11 | AN11-C |
| H-23 | AN11 | AN11-D |
| H-24 | AN1 | AN1-C |

### 18.3 MEDIUM audit IDs (grouped by subsystem)

**IPC (M01..M09)** — all in **AN3-B..F** (M01 in AN3-B; M02..M04 in AN3-C/D; M05..M09 in AN3-E)
**Scheduler (SCH-M01..M05)** — all in **AN5-A, AN5-B**
**Capability (CAP-M01..M05)** — all in **AN4-F**
**Lifecycle (LIF-M01..M06)** — all in **AN4-G**
**Service (SVC-M01..M04)** — all in **AN4-H**
**SchedContext (SC-M01..M03)** — **AN5-D** (SC-M02 cross-references AN6-A)
**Architecture (ARCH-M01..M03)** — **AN6-D** (ARCH-M01 VSpaceBackend wired production-live, not tagged-deferred)
**InformationFlow (IF-M01..M03)** — **AN6-E**
**CrossSubsystem (CX-M01..M05)** — **AN6-F**
**Foundation (FND-M01..M08)** — **AN2-F** (with M03 also touching AN2-B)
**Platform (PLT-M01..M07)** — **AN7-D** (PLT-M02/M03 closed substantively in AN7-D.2 with RPi5/VSpaceBoot shim; PLT-M06 full recursion in AN7-D.5)
**API (API-M01..M02)** — **AN7-E**
**Rust (RUST-M01..M08)** — **AN8-D** (with M06 covered by AN1-C)
**Tests (TST-M01..M13)** — **AN11-E** (with M10/M11 covered by AN11-C/D)
**Documentation (DOC-M01..M08)** — **AN12-C** (with M01/M06 covered by AN1-A; M02 by AN7-D; M04 by AN12 final refresh)

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
| Tests/CI | AN11-F |
| Documentation | AN12-D |

### 18.5 Cross-cutting themes

| Theme | Phase(s) | Sub-task(s) |
|-------|----------|-------------|
| 4.1 Closure-form proofs | AN4, AN6, AN12 | AN4-C, AN6-A (ALL 6 arms), AN12-A |
| 4.2 Tuple → structure | AN2, AN3, AN4 | AN2-G (DEF-F-L9 absorbed), AN3-B, AN4-F (CAP-M05) |
| 4.3 Subtype gates | AN2, AN4, AN10 | AN2-A, AN2-B, AN2-F (FND-M03), AN4-F (CAP-M04), **AN10-A (DEF-AK7-E ValidObjId rollout)** |
| 4.4 SMP-latent assumptions | AN4, AN6, AN9, AN12 | AN4-D, AN6-F (CX-M03), **AN9-J (SMP bring-up absorbed)**, AN12-B (SMP inventory confirmation post-AN9) |
| 4.5 Workstream IDs in comments | AN12 | AN12-E |
| 4.6 Stale forward references | AN1, AN12 | AN1-C, AN12-E |
| 4.7 Monolithic file splits | AN3, AN4, AN5, AN6, AN12 | AN3-C/D, AN4-F (CAP-M03)/AN4-G (LIF-M05), AN5-A, AN6-E (IF-M03), AN12-F |

### 18.6 Absorbed deferred IDs (from `AUDIT_v0.29.0_DEFERRED.md`)

All 11 rows are absorbed as live pre-1.0 work per the §16 absorption map. Each row in `AUDIT_v0.29.0_DEFERRED.md` is annotated RESOLVED at AN12-G with the closing commit SHA.

| Source | Disposition | Closing sub-task |
|--------|-------------|------------------|
| DEF-A-M04 | **ABSORBED → RESOLVED** | AN9-A |
| DEF-A-M06 / DEF-AK3-I | **ABSORBED → RESOLVED** | AN9-B |
| DEF-A-M08 | **ABSORBED → RESOLVED** | AN9-C |
| DEF-A-M09 / DEF-AK3-K | **ABSORBED → RESOLVED** | AN9-C |
| DEF-C-M04 | **ABSORBED → RESOLVED** | AN9-D |
| DEF-P-L9 | **ABSORBED → RESOLVED** (primary in AN7-D.2, cross-ref in AN9-E) | AN7-D.2 |
| DEF-R-HAL-L14 | **ABSORBED → RESOLVED** | AN9-F |
| DEF-F-L9 | **ABSORBED → RESOLVED** | AN2-G |
| DEF-AK2-K.4 | **ABSORBED → RESOLVED** (RPi5-canonical witness) | AN5-F |
| DEF-AK7-E.cascade | **ABSORBED → RESOLVED** | AN10-A |
| DEF-AK7-F.cascade | **ABSORBED → RESOLVED** (reader AN10-B, writer AN10-C) | AN10-B + AN10-C |

### 18.7 New AN9 sub-tasks surfaced by AN1-C (all absorbed in-phase — no new DEF entries)

| New sub-task ID | Source | Category | Closing sub-task |
|-----------------|--------|----------|------------------|
| DEF-R-HAL-L17 (bounded WFE) | AN1-C / `lib.rs:62` | Hardware / interrupt-wait | **AN9-G** |
| DEF-R-HAL-L18 (parameterized barriers) | AN1-C / `lib.rs:69` | Hardware / barriers | **AN9-H** |
| DEF-R-HAL-L19 (OSH widening) | AN1-C / `lib.rs:84` | SMP / barriers | **AN9-I** |
| DEF-R-HAL-L20 (secondary-core bring-up / SMP) | AN1-C / `lib.rs:91` | SMP / multi-core | **AN9-J** |

**Result at WS-AN close**: **zero deferred items** past v1.0.0. Every row in `AUDIT_v0.29.0_DEFERRED.md` is RESOLVED. No `AUDIT_v0.30.6_DEFERRED.md` file exists.

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
- `AN{phase}-{letter}.{digit}` — e.g., `AN3-B.4` is "sub-sub-task 4 inside AN3-B"; each sub-sub-task corresponds to one atomic commit
- `AN{phase}-{letter}.{digit}.{digit}` — rare third-level decomposition for pathologically large units (e.g., `AN4-F.5.4` is "sub-sub-sub-task inside CAP-M05 named-projection refactor")
- Sub-tasks are sequential within a phase; letter ordering reflects dependency
- "AN12-G" is "Phase AN12, sub-task G" — the in-place closure annotations for `AUDIT_v0.29.0_DEFERRED.md` (no new DEFERRED file created)
- Audit-ID cross-reference is recorded in the sub-task heading for forward and reverse traversal
- For sub-sub-tasks, the commit message convention is `WS-AN {SubSubId}: <one-line> (<audit-IDs>)` — e.g., `WS-AN AN2-D.3: retype preservation for typedIdDisjointness (H-10)`

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

3. **AN6-C (H-09 transitive disjointness)** — removed from open questions. Per maintainer directive, Track B (transitive `untypedAncestorRegionsDisjoint`) is mandatory; the prior stretch-goal framing is superseded. No decision remains.

4. **PR-6 (AN8) parallel landing** — is there a separate Rust-focused
   contributor available? Default: assume same contributor; PR-6
   serializes after PR-1. Note: AN9 significantly increases Rust workload, so a dedicated Rust/HAL contributor is strongly recommended for the v1.0.0 timeline.

5. **DOC-M03 SPDX header pass** — single mechanical PR (~150 file
   header changes, easy review) or batched per-subsystem (more PRs,
   smaller diffs)? Default: single PR for review efficiency.

6. **AN12-E inline-marker hygiene scope** — full sweep or selective
   (only retarget closed-workstream pointers, leave per-feature
   markers)? Default: selective per audit guidance "after each
   portfolio closes, replace inline workstream markers" — ie selective.

7. **AN9-J SMP default enablement** — AN9-J lands SMP bring-up code reviewed + merged + QEMU-tested, but gated behind a runtime `smp_enabled` flag defaulted to `false` at v1.0.0 boot. Does the maintainer want to flip the default to `true` for v1.0.0 (risk: single-core is the validated hardware configuration; SMP is QEMU-tested only), or stay default-off (AN9-J's proposal)? Default: stay default-off at v1.0.0; flip to default-on in a patch release after real-hardware SMP validation lands.

8. **Deferral escalation protocol** — if any sub-task genuinely cannot close under the plan's escalation ladders (e.g., a Lean 4.28.0 toolchain bug that blocks AN6-A.7's `lifecycleRetype_preserves_projection`, or a QEMU limitation that prevents AN9-J SMP smoke), does the maintainer approve pausing the workstream and escalating, or can the item be the one exception that ships with a narrow DEF-* annotation? Default (per §15.1 rule): pause and escalate; no silent deferrals.

---

## 21. Closure note

This plan is **single-source-of-truth** for WS-AN. Any AN-* sub-task
that is renamed, dropped, or split during execution must be
reflected by a same-PR edit to this file. The plan archives to
`docs/dev_history/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md` only after
AN12-N (the workstream closure) ships and `docs/WORKSTREAM_HISTORY.md`
records the WS-AN entry.

**Zero-deferral rule**: per maintainer directive, no sub-task may be
silently deferred. Every CRITICAL, HIGH, MEDIUM, LOW finding in
`AUDIT_v0.30.6_COMPREHENSIVE.md` and every row in
`AUDIT_v0.29.0_DEFERRED.md` has a live AN sub-task ID in §3..§15 that
must close substantively before WS-AN ships. If the plan encounters a
genuinely un-closable obstacle (toolchain bug, hardware limitation that
cannot be worked around), the workstream pauses and is escalated per
§20 question 8 — deferral is NOT an automatic fallback.

This document is GPL-3.0+ licensed (see `LICENSE`) per the project's
standard.

---

## 22. Sub-sub-task decomposition principles

This section documents the **criteria** that were used to decide which
sub-tasks get broken down into `.N` sub-sub-tasks versus kept as
single units. Future workstreams (WS-AO, etc.) should apply the same
criteria.

### 22.1 Triggers for decomposition

A sub-task MUST be decomposed into sub-sub-tasks if any one of the
following applies:

1. **Cascade ≥ 10 sites** — a refactor touching 10 or more production
   call sites should batch into a series of commits, one batch per
   subsystem cluster, so review diffs stay scoped.
2. **Effort ≥ 0.75 days** — a sub-task estimated at more than ~6 hours
   of focused work is better expressed as multiple smaller commits
   that can be interrupted and resumed.
3. **Multi-option decision** — if a sub-task has "Option A / Option B"
   decision points (e.g., linker-layout fallback in AN8-B), each
   option gets its own sub-sub-task sequence with an explicit decision
   gate.
4. **Toolchain risk** — if a sub-task depends on a Lean or Rust
   toolchain feature that may not work uniformly (e.g., AN6-A's
   `split_ifs` on `Except.ok`-wrapped match), break into an attempt
   ladder with fallbacks.
5. **Mixed concerns** — if a single sub-task addresses multiple
   independent findings (e.g., AN4-F's 5 CAP-M IDs), decompose into
   per-finding sub-sub-tasks even if each individual finding is
   small.
6. **File split (Theme 4.7)** — every monolithic-file split decomposes
   into seam-inventory + per-child-extraction + hub-finalization
   commits. Minimum 2-3 commits per split.
7. **Structure refactor (Theme 4.2)** — every tuple→structure
   refactor follows the 6-step AN3-B playbook: structure + bridge,
   projection abbrevs, swap primary, migrate subsystem consumers,
   migrate cross-subsystem consumers, delete deprecated form +
   monotonicity metric.
8. **Invariant extension (AM4 playbook)** — every `crossSubsystemInvariant`
   extension follows the AN2-D playbook: predicate + default, frame
   lemmas, preservation through retype, conjunct addition, 5 core
   bridges, 34 per-op bridges, field-set catalog.

### 22.2 Granularity anti-patterns (avoid)

- **Over-decomposition**: if a sub-sub-task has ≤ 15 minutes of
  engineer work and isn't a review/audit boundary, fold it into a
  parent sub-task. Example of over-decomposition: splitting a docstring
  rewrite into 4 commits (one per paragraph).
- **Cascade-free decomposition**: if a sub-task has 0 cascade and ≤
  100 LOC delta, it's one commit. Don't invent sub-sub-tasks for the
  sake of structure.
- **Ordering coupling**: if sub-sub-tasks MUST land in a specific
  order AND cannot be reviewed independently, they're one logical unit;
  combine them. The `.N` numbering is for independently-reviewable
  commits, not for narratively-ordered steps inside a single commit.

### 22.3 Review-scope guidance per sub-sub-task

Every sub-sub-task commit should:

1. **Stand alone**: a reviewer reading only the sub-sub-task's diff
   should understand what changed and why.
2. **Pass CI by itself**: each commit should not require a subsequent
   commit to restore green CI. Use temporary shims or bidirectional
   bridges (AN2-G.1's `allTablesInvExtKTuple` kept callable) to
   maintain build-greenness mid-migration.
3. **Reference its parent**: the commit message includes both the
   sub-sub-task ID (`AN2-D.3`) and the audit finding IDs it addresses
   (`H-10`).
4. **Document cascade**: if the commit touches N files, the commit
   message records N in the summary so the aggregate cascade can be
   reconstructed from the git log post-closure.

### 22.4 Emergency reversion protocol

If a sub-sub-task commit breaks the full gate in a way that cannot be
fixed forward within 1 hour, revert it and open a `DEF-*` tracking
entry for a post-workstream revisit. This is preferable to blocking
the rest of the workstream on a single stubborn cascade. Examples
where this may apply:

- AN2-C.3 LawfulBEq derivation fails due to Lean toolchain limitation
  → revert; open `DEF-AN2-C.3-lawfulbeq`; proceed with AN2-C.4/.5
- AN6-A.2/A.3/A.4 all fail → ship partial discharge (AN6-A.4)
  preserves the sub-task's value
- AN2-G.4 consumer migration breaks a non-obvious subsystem → revert
  just that batch; re-plan with a smaller granularity

**End of plan.**









