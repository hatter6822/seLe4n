# SM9 — Documentation, Tests, Version Closure (WS-SM Phase 9)

> **Phase**: SM9 of WS-SM
> **Parent overview**: [`SMP_MULTICORE_COMPLETION_PLAN.md`](SMP_MULTICORE_COMPLETION_PLAN.md)
> **Audited cut**: `v0.31.2`
> **Target releases**: v0.98.0 → **v1.0.0**
> **Calendar estimate**: 4-6 weeks
> **Sub-task count**: 25-35 across ~10-15 PRs

## 1. Phase goal

SM9 is the v1.0.0 release-cut phase. All substantive SMP work
is complete; SM9 synchronizes documentation, completes the test
suites, bumps the version, and records WS-SM closure.

**Concrete deliverables**:

1. **Specification update** (SM9.A.1): spec §6.4 rewritten for
   SMP with 5 new subsections.
2. **GitBook chapters** (SM9.A.2, .A.3): new chapter 16 (SMP
   architecture), chapter 17 (verified lock primitives).
3. **README sync** (SM9.A.4): metrics, capability claim, 10
   i18n.
4. **DEVELOPMENT.md + CLAIM_EVIDENCE_INDEX.md** (SM9.A.5, .A.6).
5. **WORKSTREAM_HISTORY.md** WS-SM closure (SM9.A.7).
6. **codebase_map.json regeneration** (SM9.A.8).
7. **website manifest** (SM9.A.9).
8. **Full SMP test suites** (SM9.B): 6 new test files,
   fixtures, tier-4 + tier-5 scripts.
9. **Version bump to v1.0.0** (SM9.C.1): ~25 files synchronized.
10. **CHANGELOG closure** (SM9.C.2).
11. **Archive WS-RC artefacts** (SM9.C.3, .C.4).
12. **Tag v1.0.0** (SM9.C.5).

## 2. Dependencies

- All of SM0..SM8 complete.
- Acceptance gates for SM0..SM8 green.
- Tier 0..5 tests green at HEAD.

## 3. Sub-tasks

### SM9.A — Documentation sync (3-4 PRs, 9 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM9.A.1 | Spec §6.4 rewrite (5 subsections) | `docs/spec/SELE4N_SPEC.md` | L |
| SM9.A.2 | New GitBook chapter 16 (SMP architecture, ~300 LoC) | `docs/gitbook/16-smp-architecture.md` | L |
| SM9.A.3 | New GitBook chapter 17 (verified lock primitives) | `docs/gitbook/17-verified-lock-primitives.md` | L |
| SM9.A.4 | README metrics + capability claim; 10 i18n | (11 files) | M |
| SM9.A.5 | DEVELOPMENT.md updates | (1 file) | S |
| SM9.A.6 | CLAIM_EVIDENCE_INDEX.md entries | (1 file) | M |
| SM9.A.7 | WORKSTREAM_HISTORY.md WS-SM closure summary | (1 file) | L |
| SM9.A.8 | Regenerate codebase_map.json | (1 file) | T |
| SM9.A.9 | Update website_link_manifest.txt | (1 file) | S |

### SM9.B — Test suite completion (2-4 PRs, 13 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM9.B.1 | `tests/SmpSchedulerSuite.lean` (~600 LoC) | (1 file) | XL |
| SM9.B.2 | `tests/SmpIpcSuite.lean` (~500 LoC) | (1 file) | XL |
| SM9.B.3 | `tests/SmpCapabilitySuite.lean` (~400 LoC) | (1 file) | L |
| SM9.B.4 | `tests/SmpTlbShootdownSuite.lean` (~400 LoC) | (1 file) | L |
| SM9.B.5 | `tests/SmpInformationFlowSuite.lean` (~400 LoC) | (1 file) | L |
| SM9.B.6 | `tests/SmpFoundationsSuite.lean` (~250 LoC; from SM0.S) | (1 file) | M |
| SM9.B.7 | `tests/fixtures/smp_4core_boot.expected` | (1 file) | M |
| SM9.B.8 | `tests/fixtures/smp_ipc_4core.expected` | (1 file) | M |
| SM9.B.9 | `tests/fixtures/smp_tlb_shootdown.expected` | (1 file) | M |
| SM9.B.10 | `scripts/test_tier4_smp.sh` (replaces stub) | (1 file) | M |
| SM9.B.11 | `scripts/test_tier5_lock_correspondence.sh` (new tier) | (1 file) | M |
| SM9.B.12 | Wire all tier-4/5 into `test_nightly.sh` | (1 file) | S |
| SM9.B.13 | Verify all 210 SM theorems land at HEAD | tier-5 manifest | M |

### SM9.C — Version bump + closure (1-2 PRs, 5 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM9.C.1 | Version bump to v1.0.0 (~25 files synchronized) | M |
| SM9.C.2 | CHANGELOG v1.0.0 closure entry | `CHANGELOG.md` | M |
| SM9.C.3 | Move WS-RC artefacts to dev_history/audits/ | (file moves) | S |
| SM9.C.4 | Move WS-SM plan + per-phase docs to dev_history/planning/ | (11 file moves) | T |
| SM9.C.5 | Tag v1.0.0 (maintainer-cut) | git tag | T |

### SM9.D — AN12-B inventory closure (1 PR, 3 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM9.D.1 | Each `smpLatentInventory` entry's `smpDischarge` updated to "SMP-implemented in WS-SM" | `Concurrency/Assumptions.lean` | M |
| SM9.D.2 | Rename `smpLatentInventory` to `smpDischargedInventory` (or retire entirely) | (refactor) | M |
| SM9.D.3 | 8-entry size witness retained | Theorem | T |

### SM9.E — Final QEMU validation (1 PR, 3 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM9.E.1 | Full QEMU `-smp 4` boot + workload run | `scripts/test_v1_0_0_release_validation.sh` | L |
| SM9.E.2 | All 5 tiers green on the release candidate | (verification) | M |
| SM9.E.3 | Release-candidate trace fixture commit | (1 file) | S |

## 4. Version-bump file list

The 25 files synchronized in SM9.C.1:

```
lakefile.toml              :: version = "1.0.0"
README.md                  :: header + metrics
docs/i18n/<lang>/README.md :: 10 files
CHANGELOG.md               :: ## [1.0.0] heading
CLAUDE.md                  :: version reference + active workstream → CLOSED
AGENTS.md                  :: byte-mirror of CLAUDE.md
docs/spec/SELE4N_SPEC.md   :: header
rust/Cargo.toml            :: workspace version
rust/sele4n-hal/src/boot.rs :: KERNEL_VERSION = "1.0.0"
rust/sele4n-hal/Cargo.toml :: version
rust/sele4n-abi/Cargo.toml :: version
rust/sele4n-sys/Cargo.toml :: version
rust/sele4n-types/Cargo.toml :: version
rust/Cargo.lock            :: regenerated
docs/codebase_map.json     :: version + metrics
docs/DEVELOPMENT.md        :: version reference
docs/CLAIM_EVIDENCE_INDEX.md :: closure entries
scripts/check_version_sync.sh :: regenerates / verifies
```

## 5. CHANGELOG v1.0.0 closure entry skeleton

```markdown
## [1.0.0] - YYYY-MM-DD — Bootable verified SMP microkernel

WS-SM PORTFOLIO COMPLETE.  v1.0.0 ships seLe4n as a bootable
verified SMP microkernel on Raspberry Pi 5 (BCM2712).  All 4
cores brought up; per-core scheduler with cross-core wake via
SGI; per-object reader-writer fine locks with hierarchical
acquire order; verified TicketLock + RwLock primitives modeled
in Lean against an abstract ARMv8.1-A LSE memory model and
proven correct; cross-core IPC; explicit-ack TLB shootdown
protocol; per-core noninterference under SMP.

Closures (from the WS-SM audit):
- SMP-C1: bring_up_secondaries wired via Phase 5 + DTB cmdline.
- SMP-C2: rust_secondary_main full init (MMU/VBAR/GIC/timer).
- SMP-C3: kernelStateRef safety under per-object fine locks +
  serializability (Cor 2.1.11).
- SMP-C4: IS-variant TLB instructions + explicit-ack shootdown
  protocol (Thm 3.3.1 in SMP_TLB_SHOOTDOWN_PLAN).
- SMP-H1: SGI primitive (gic::send_sgi + dispatch).
- SMP-H2: ArchAssumption.singleCoreOperation constructor added,
  then retired post-SM4 (path-a Vector replacement).
- SMP-H3: AN12-B inventory build-anchored via Concurrency/Anchors.
- SMP-H4: verified TicketLock + RwLock primitives.
- 7 MEDIUM + 5 LOW findings closed.

New theorem count: ~210 substantive theorems across SM2..SM8.
Zero Lean axioms.  Zero sorry/native_decide.  Tier 0..5 all
green.

WS-RC R0..R5 LANDED at v0.31.2 (preserved); R6..R14 absorbed
into SM-phases per SM0.Q.  Single unified workstream.

Plan: docs/dev_history/planning/SMP_MULTICORE_COMPLETION_PLAN.md
       (overview)
       docs/dev_history/planning/SMP_FOUNDATIONS_PLAN.md (SM0)
       docs/dev_history/planning/SMP_RUST_HAL_PLAN.md (SM1)
       docs/dev_history/planning/SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md (SM2)
       docs/dev_history/planning/SMP_PER_OBJECT_LOCKS_PLAN.md (SM3)
       docs/dev_history/planning/SMP_PER_CORE_STATE_PLAN.md (SM4)
       docs/dev_history/planning/SMP_PER_CORE_SCHEDULER_PLAN.md (SM5)
       docs/dev_history/planning/SMP_CROSS_CORE_IPC_PLAN.md (SM6)
       docs/dev_history/planning/SMP_TLB_SHOOTDOWN_PLAN.md (SM7)
       docs/dev_history/planning/SMP_INFORMATION_FLOW_PLAN.md (SM8)
       docs/dev_history/planning/SMP_RELEASE_CLOSURE_PLAN.md (SM9)
```

## 6. Verification strategy

### 6.1 What SM9 proves

5 marker theorems:
- `smpRetiredInventory_complete` (all 8 entries discharged)
- `wsm_phase_count = 10`
- `wsm_acceptance_gate_count` (count of acceptance items met)
- `wsm_theorem_count` (~210 substantive theorems)
- `v1_0_0_release_witness`

### 6.2 What SM9 validates

- Tier 0..5 green at HEAD.
- All v1.0.0 acceptance-gate items checked.
- QEMU `-smp 4` release validation.

## 7. Risk inventory

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Documentation drift between phase plans and live tree | MED | LOW | SM9.A audits each cross-reference |
| Version bump misses a file | LOW | MED | `scripts/check_version_sync.sh` gate |
| CHANGELOG entry incomplete | LOW | LOW | Template above lists all SM-phase closures |
| Archive move breaks website manifest | LOW | LOW | SM9.A.9 updates manifest in same PR |
| QEMU release-validation script fails | MED | HIGH | Iterate on test infrastructure as needed |
| Tier-5 (lock correspondence) misses a divergence | LOW | HIGH | Cross-language stress test catches |
| Maintainer signs off on release without all gates green | LOW | CRIT | Explicit acceptance-gate checklist |

## 8. Acceptance gate

- [ ] Spec §6.4 rewritten for SMP.
- [ ] GitBook chapters 16 + 17 published.
- [ ] README + 10 i18n synced.
- [ ] DEVELOPMENT.md + CLAIM_EVIDENCE_INDEX.md + WORKSTREAM_HISTORY.md updated.
- [ ] codebase_map.json regenerated.
- [ ] All 6 SMP test suites land + run.
- [ ] tier-4 + tier-5 scripts in test_nightly.sh.
- [ ] Version bumped to 1.0.0 across all 25 files.
- [ ] CHANGELOG v1.0.0 entry.
- [ ] WS-RC + WS-SM artefacts archived.
- [ ] AN12-B inventory discharged.
- [ ] QEMU release-validation green.
- [ ] Tier 0..5 green at HEAD.
- [ ] **v1.0.0 tag cut by maintainer.**

## 9. Cross-references

- **Previous**: [`SMP_TLB_SHOOTDOWN_PLAN.md`](SMP_TLB_SHOOTDOWN_PLAN.md), [`SMP_INFORMATION_FLOW_PLAN.md`](SMP_INFORMATION_FLOW_PLAN.md)
- **None next** — SM9 is the closure phase; v1.0.0 ships.

## 10. Theorem catalogue for SM9

5 marker theorems (§6.1).

## Appendix A — Verification commands

```bash
source ~/.elan/env

# Tier 0..5:
./scripts/test_tier0_hygiene.sh
./scripts/test_fast.sh
./scripts/test_smoke.sh
./scripts/test_full.sh
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh
./scripts/test_tier5_lock_correspondence.sh

# Version sync:
./scripts/check_version_sync.sh

# Release validation:
./scripts/test_v1_0_0_release_validation.sh

# Final QEMU SMP boot:
./scripts/test_qemu_smp_bringup.sh
```

---

*SM9 is the v1.0.0 ribbon-cutting. All substantive SMP work
landed in SM0..SM8; SM9 ensures the documentation, tests, and
metadata reflect the new reality. The v1.0.0 tag closes
WS-SM and ships the bootable verified SMP microkernel.*
