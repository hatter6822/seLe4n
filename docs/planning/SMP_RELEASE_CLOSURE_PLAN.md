# SM10 — Boot Path, Documentation, Tests, Version Closure (WS-SM Phase 10)

> **Status**: **PLANNED — BLOCKED on WS-RR.**  SM10 must not open until
> RR8 closes.  Re-baselined against the pre-SM10 completeness audit at
> `v0.34.3`; §1 states what the phase actually owns, which is a boot path
> as well as a release cut.

> **Phase**: SM10 of WS-SM
> **Parent overview**: [`SMP_MULTICORE_COMPLETION_PLAN.md`](SMP_MULTICORE_COMPLETION_PLAN.md)
> **Audited cut**: `v0.31.2`; **re-baselined against** the pre-SM10
> completeness audit at `v0.34.3`
> ([`UNFINISHED_SMP_WORK.md`](UNFINISHED_SMP_WORK.md) §2.2)
> **Blocked on**: **WS-RR** ([`SMP_RELEASE_READINESS_PLAN.md`](SMP_RELEASE_READINESS_PLAN.md)) —
> SM10 must not open until RR8 closes
> **Target releases**: v0.98.0 → **v1.0.0**
> **Calendar estimate**: the original 4–6 weeks covered documentation only and
> is superseded; the replacement is derived from the measured aarch64 surface
> by **RR1.11** and lands here in the same cut
> **Sub-task count**: 25-35 across ~10-15 PRs, **plus SM10.1** — sized by
> RR1.11, not by this line

## 1. Phase goal

SM10 ships v1.0.0.  Two distinct kinds of work sit under that heading, and
conflating them is what the pre-SM10 audit filed as a finding against this
plan's own §1:

1. **SM10.1 — the boot path.**  A bare-metal Lean runtime port: an aarch64
   image target, Lean cross-compilation, runtime hosting on the metal, the
   `@[export] lean_kernel_main` entry, the install-ordering resolution
   `rust/sele4n-hal/src/kernel_entry.rs` demands, and the context-restore seam.
   This is kernel implementation, not release bookkeeping.
2. **SM10.2–SM10.6 — the release cut.**  Documentation sync, test-suite
   completion, the version bump, the AN12-B inventory closure, and the tag.

**The phase goal this section carried until `v0.34.26` was false.**  It read
"All substantive SMP work is complete; SM10 synchronizes documentation,
completes the test suites, bumps the version, and records WS-SM closure", at a
4–6 week estimate.  Measured against the tree at `v0.34.3` the boot path did
not exist in any form (register §2.2):

| Required | State at the audited cut |
|----------|--------------------------|
| A bootable binary target | `rust/` has **no `[[bin]]`** — the only binary is `rust/sele4n-hal/src/bin/rw_lock_oracle.rs`, a host test oracle |
| Lean → aarch64 object code | `lakefile.toml` declares one **host** `[[lean_lib]]` and 70 **host** `[[lean_exe]]`s; no `precompileModules`, no `moreLinkArgs`, no cross-compilation rule |
| `libsele4n.a` for aarch64 | Nothing in the tree produces it, though `rust/sele4n-hal/src/boot.rs` asserts it is linked |
| Bare-metal Lean runtime hosting | Zero hits for `lean_initialize_runtime_module` / `lean_io_mark_end_initialization` anywhere |
| `@[export] lean_kernel_main` | **Absent.**  `boot.rs` declares it `extern "C"`; the only exported kernel entry is `lean_secondary_kernel_main`, and that module is *staged*, outside the production closure |
| aarch64 compile coverage | **None** in tree or CI: 67 cfg-gated blocks, 60 `asm!` sites and all three `.S` files are never compiled |

So SM10 is **not** a ribbon-cutting over finished work.  It is the phase that
makes the kernel boot, and then cuts the release.  Judging it on the release
checklist alone is the conflation that let the tier-4 gates certify phases
nothing had run.

**What is genuinely complete** is SM0..SM9's *model and proof* surface — the
per-core scheduler, cross-core IPC, the TLB shootdown protocol, per-core
non-interference and the declassification closure are substantively real, and
the audit cleared them (register §8).  What is not complete is everything
between that surface and a running image, plus the remediation WS-RR owns.

**Concrete deliverables**:

1. **The boot path** (SM10.1): aarch64 image target, Lean cross-compile,
   bare-metal runtime hosting, `@[export] lean_kernel_main`, the install
   ordering, the context-restore seam and the two WS-RA obligations §2 names.
   Sequenced and sized by RR1.11 from the measured aarch64 surface.
2. **Specification update** (SM10.2.1): spec §6.4 rewritten for
   SMP with 5 new subsections.
3. **GitBook chapters** (SM10.2.2, .A.3): new chapter 16 (SMP
   architecture), chapter 17 (verified lock primitives).
4. **README sync** (SM10.2.4): metrics, capability claim, 11
   i18n locales.
5. **DEVELOPMENT.md + CLAIM_EVIDENCE_INDEX.md** (SM10.2.5, .A.6).
6. **WORKSTREAM_HISTORY.md** WS-SM closure (SM10.2.7).
7. **codebase_map.json regeneration** (SM10.2.8).
8. **website manifest** (SM10.2.9).
9. **SMP test-suite completion** (SM10.3) over the suites and fixtures that
   already exist — see §3 SM10.3 for what is new and what is extension.
10. **Version bump to v1.0.0** (SM10.6.1), synchronized across every site
    `scripts/version_locations.sh` registers.
11. **CHANGELOG closure** (SM10.6.2).
12. **Archive WS-RC + WS-SM artefacts** (SM10.6.3, .C.4).
13. **Tag v1.0.0** (SM10.6.5).

## 2. Dependencies

- All of SM0..SM9 complete.
- Acceptance gates for SM0..SM9 green.
- **WS-RA complete** ([`SYSCALL_RETURN_ABI_PLAN.md`](SYSCALL_RETURN_ABI_PLAN.md)).
  SM10.1 ships a bootable image, and a kernel whose every successful syscall
  returns the caller's own capability pointer — which userspace decodes as a
  `KernelError` — is not bootable in any useful sense.  WS-RA was sequenced
  **before SM9** and its core landed at v0.33.37 (the immediate-return
  convention is live end to end), but it is listed here because SM10.1 is the
  gate that would otherwise have exposed it.  **SM10.1 inherits two named
  obligations from WS-RA**: (1) **frame delivery** — RA.B.5b's staging half
  landed at v0.33.38 (the unblocking arms stage the woken waiter's frame;
  `blockedReturn_staged_in_waiter_frame`), so what remains is exactly
  **SM10.1's context restore delivering the staged frame** (WS-RA §3.5); the
  wait-before-signal badge ordering is staged end to end and completes when
  the restore seam goes live.  (2) The cancellation/timeout error-frame
  staging (WS-RA §9 registered debt): before `contextRestoreSeamLive` flips,
  `cancelIpcBlocking` and `timeoutThread` must stage an error frame, or a
  cancelled waiter resumes reading its stale staged arguments as a return
  value.
- **WS-DT complete** — the IPC `ipcInvariantFull` de-threading workstream
  ([`IPC_INVARIANT_DETHREADING_PLAN.md`](IPC_INVARIANT_DETHREADING_PLAN.md),
  registered in [`../WORKSTREAM_HISTORY.md`](../WORKSTREAM_HISTORY.md) as
  **WS-DT**).  Slices D1, D6 and D8 are open at `v0.34.25`: two of the twenty
  `ipcInvariantFull` conjuncts —
  `blockedThreadsPendingMessageConsistent` and `replyCallerLinkageReciprocal`,
  which the audit put at 33 and 31 of the 35 bundles — are still assumed as
  **post-state hypotheses**, so `ipcInvariantFull` is not today an end-to-end
  machine-checked property of the live kernel, and neither
  `dispatchWithCap_preserves_ipcInvariantFull` nor
  `syscallDispatch_preserves_ipcInvariantFull` exists.  SM10.2.4 (README
  capability claim) and SM10.2.6 (`CLAIM_EVIDENCE_INDEX.md` entries) are the
  sub-tasks that would otherwise write v1.0.0 verification claims over this
  surface.  **Closed by WS-RR phase RR3**, which absorbs all three slices and
  retires the plan at RR3.17.
- Tier 0..5 tests green at HEAD.

## 3. Sub-tasks

> **The sub-phases are numbered, and the numbers are execution order.**
> Until `v0.34.36` they were lettered A–E and the letters were *not* the
> order: **SM10.3.7** (the 4-core boot fixture) and **SM10.3.10** (running the
> Tier-4 gate green) both consume the bootable image, and the version bump and
> tag ran before the image existed at all.  A reader following the letters
> reached fixture generation, release closure and the tag before there was
> anything to boot.  A prose note said so and asked the reader to compensate,
> which CLAUDE.md rejects outright: "*Phase number is execution order… A
> 'sequencing note' that contradicts the numbering means the numbering is
> wrong, not that the note is helpful.*"  The numbering was wrong, so it was
> re-sequenced rather than annotated.
>
> **Old letter → new number.**  The labels are *numbers* rather than
> re-assigned letters on purpose: `SM10.E` is cited in `CHANGELOG.md` entries
> and closed audit plans, which the project's rules never renumber, so reusing
> a letter would silently repurpose those citations.  Nothing is ambiguous —
> an old letter always means what it meant.
>
> | Was | Is | Why it moved |
> |-----|----|--------------|
> | `SM10.E` (boot path, `SM10.E.D1` image build) | **SM10.1** (`SM10.1.1`) | Everything downstream consumes the image; it is the prerequisite, so it is first |
> | `SM10.A` | **SM10.2** | Unchanged in order |
> | `SM10.B` | **SM10.3** | Now follows the image its fixture and Tier-4 rows need |
> | `SM10.D` | **SM10.4** | Unchanged in order |
> | `SM10.E.1`–`.3` (final QEMU validation) | **SM10.5** | Split out of the boot-path phase: it runs *on* the image, against completed suites |
> | `SM10.C` (version bump + tag) | **SM10.6** | The tag is the last act, not the third |
>
> The one sub-phase that split is the old `SM10.E`, which carried both the
> image build and the validation that consumes it — a phase that was its own
> prerequisite.  Historical prose (`CHANGELOG.md`, `docs/dev_history/`,
> `docs/audits/`) keeps the old letters by design.

### SM10.1 — Bootable image and boot path (1 sub-task + the runtime port)

The bare-metal Lean runtime port: an aarch64 image target, Lean
cross-compilation, runtime hosting on the metal, the `@[export]
lean_kernel_main` entry, the install-ordering resolution below, and the
context-restore seam.  **Everything downstream consumes this**, which is why
it is first: `SM10.3.7`'s 4-core boot fixture cannot be generated without an
image, `SM10.3.10`'s Tier-4 gate reports NOT RUN until one exists, and
`SM10.5` boots the artefact this phase produces.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM10.1.1 | Bootable image target — `kernel8.img` + `config.txt` packaging, and the `sele4n-hal` bootable binary it packages | `scripts/build_rpi5_image.sh` | XL |

**Registered obligation — `lean_kernel_main` install ordering.**  When
SM10.1.1 defines the primary's boot seam (`lean_kernel_main`, the
symbol the image target resolves), its `initialiseKernelState` install
is a kernel-state **write** that today would run *outside* the
kernel-entry lock and *after* Phase 5 has released the secondaries —
whose bracketed timer ticks and `.reschedule` receivers are already
committing against the same `IO.Ref`.  An unbracketed install racing a
bracketed commit can be overwritten by a post-state derived from the
pre-install default state (the lost-commit shape
`kernel_entry.rs`'s module docs describe).  SM10.1 MUST close this by
one of:

1. **Order** — perform the Lean kernel-state install *before*
   `apply_cmdline_and_start_smp` releases any secondary (splitting the
   install from the primary's run loop if `lean_kernel_main` combines
   them), so no concurrent committer exists during the install; or
2. **Bracket** — run the install inside
   `kernel_entry::with_kernel_entry`, joining the five already-bracketed
   committing entries.

Option 1 is preferred (it also lets the secondaries' bring-up
reschedule observe the real boot state — with per-core idle threads
installed — instead of the empty default).  Cross-references:
`SeLe4n/Platform/FFI.lean` (`modifyGetKernelState` docstring) and
`rust/sele4n-hal/src/kernel_entry.rs` (module docs) both name this
obligation.

### SM10.2 — Documentation sync (9 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM10.2.1 | Spec §6.4 rewrite (5 subsections) | `docs/spec/SELE4N_SPEC.md` | L |
| SM10.2.2 | New GitBook chapter 16 (SMP architecture, ~300 LoC) | `docs/gitbook/16-smp-architecture.md` | L |
| SM10.2.3 | New GitBook chapter 17 (verified lock primitives) | `docs/gitbook/17-verified-lock-primitives.md` | L |
| SM10.2.4 | README metrics + capability claim; 11 i18n locales | (12 files) | M |
| SM10.2.5 | DEVELOPMENT.md updates | (1 file) | S |
| SM10.2.6 | CLAIM_EVIDENCE_INDEX.md entries | (1 file) | M |
| SM10.2.7 | WORKSTREAM_HISTORY.md WS-SM closure summary | (1 file) | L |
| SM10.2.8 | Regenerate codebase_map.json | (1 file) | T |
| SM10.2.9 | Update website_link_manifest.txt | (1 file) | S |

**SM10.2's documentation work-list** is not "re-audit the docs".  WS-RR
RR0.11 triaged the pre-SM10 audit's 99 low-severity findings by remedy and
routed **37** of them here, enumerated as destination 5 in
[`UNFINISHED_SMP_WORK.md`](UNFINISHED_SMP_WORK.md) §7.1 with a per-row cite.
The other 62 went elsewhere on purpose: 20 were closed by the RR0 cut, 9 by
registering them in the debt register, 18 belong to a phase already reworking
the same artefact, and **15 needed code, a proof, a test or a wiring change
and became RR7 rows (RR7.27–RR7.31)** — handing those to a documentation
sweep would have closed the release over unwired proven structures and a live
docstring citing a theorem that does not exist.  Four of the 37 (register rows
41, 52, 62, 70) are **source comments**, not documents; read the code beside
each before editing it.

### SM10.3 — Test suite completion (13 sub-tasks)

**Refreshed against the tree by RR0.8 at `v0.34.26`.**  This table was written
at `v0.31.2` and described as *new files* five suites, two fixtures and two
tier scripts that the SM5..SM9 phases had since landed — one of them 11,756
lines — while naming the two tier scripts under names nothing in the tree
carries.  A closure phase whose test table asks for work already done is a
phase that will either redo it or tick it unexamined; the rows below say what
each sub-task still owes.

`tests/` carries **22** `Smp*` suites today, not six.  The six named here are
the ones this table originally scoped; the other sixteen (per-core selection,
switch, wake, timer, idle, PIP, domain, CBS, WCRT, invariant, cross-core
call/notification/reply, cancellation, cache maintenance, surface anchors)
landed with their own phases and are wired in Tier 2.

| Sub | Description | State at `v0.34.26` | Est |
|-----|-------------|---------------------|-----|
| SM10.3.1 | `tests/SmpSchedulerSuite.lean` | **exists** (441 lines, `smp_scheduler_suite`, Tier-2 wired, golden `smp_4core_scheduler.expected` from SM5.K.4).  Owed: extension only, if SM10.1's boot path exposes an uncovered path | S |
| SM10.3.2 | `tests/SmpIpcSuite.lean` | **exists** (1,373 lines, Tier-2 wired, golden `smp_ipc_4core.expected` from SM6.F.4).  Owed: extension only | S |
| SM10.3.3 | `tests/SmpCapabilitySuite.lean` | **absent** — the one suite of the six that was never written.  Cross-core capability coverage today is incidental, inside the IPC and cross-core suites | L |
| SM10.3.4 | `tests/SmpTlbShootdownSuite.lean` | **exists** (3,354 lines, Tier-2 wired, golden `smp_tlb_shootdown.expected`).  Owed: extension only | S |
| SM10.3.5 | `tests/SmpInformationFlowSuite.lean` | **exists** (11,756 lines, Tier-2 wired, golden `smp_information_flow.expected`).  Owed: nothing; do not rewrite | T |
| SM10.3.6 | `tests/SmpFoundationsSuite.lean` | **exists** (965 lines, `smp_foundations_suite`, Tier-2 wired).  Owed: nothing | T |
| SM10.3.7 | `tests/fixtures/smp_4core_boot.expected` | **absent**, and correctly so: a boot trace fixture cannot be produced before SM10.1.1 builds the image.  Sequence it **after** the image, not before | M |
| SM10.3.8 | `tests/fixtures/smp_ipc_4core.expected` | **exists**, with its `.sha256` and Tier-3 anchors | T |
| SM10.3.9 | `tests/fixtures/smp_tlb_shootdown.expected` | **exists**, with its `.sha256` and Tier-3 anchors | T |
| SM10.3.10 | Tier-4 SMP script | **exists** as `scripts/test_tier4_smp_bootcheck.sh` — populated, not a stub; it is the gate that reports NOT RUN until SM10.1.1's image exists.  There is no `scripts/test_tier4_smp.sh` and none is needed.  Owed: run it green once the image lands | M |
| SM10.3.11 | Tier-5 cross-language script | **exists** as `scripts/test_tier5_cross_language.sh`.  There is no `scripts/test_tier5_lock_correspondence.sh`.  Owed: RR6.2–RR6.3 make the oracle drive the real locks; SM10 runs it | M |
| SM10.3.12 | Wire tier-4/5 into `test_nightly.sh` | **done** — `test_tier4_nightly_candidates.sh` (via `run_gate_check`) and `test_tier5_cross_language.sh` are both invoked there | T |
| SM10.3.13 | Verify the SM theorem manifest lands at HEAD | **mechanism landed** (RR0.6): `docs/smp_theorem_manifest.json` is generated from the tree and cross-checked in Tier 0, so "210 theorems" is no longer the criterion — the criterion is that the manifest agrees with the tree and every phase has an entry.  Owed: build the missing per-phase inventories (SM1, SM6..SM10), which contribute zero today | M |

**Registered debt — hardware-validation scripts** (from the v0.34.0
documentation audit; each is a runnable procedure `docs/HARDWARE_TESTING.md`
documents whose script does not exist yet, with today's partial coverage
noted there per section). Closure target: this phase (SM10.3 for the QEMU
scripts, SM10.1 for the image build):

| Debt | Script owed | HARDWARE_TESTING.md § |
|------|-------------|------------------------|
| SM10.3.D1 | `scripts/test_qemu_tlb_barrier_audit.sh` (TLBI bracket audit over `-d in_asm`) | §4.2 |
| SM10.3.D2 | `scripts/test_qemu_suspend_atomicity.sh` (suspend stress under 1 kHz tick) | §4.3 |
| SM10.3.D3 | `scripts/test_qemu_svc_roundtrip.sh` (userspace `svc #0` per `SyscallId`) | §4.4 |
| SM10.3.D4 | `scripts/test_qemu_wfe_bounded.sh` (bounded-WFE fall-through wallclock) | §4.5 |
| SM10.3.D5 | `scripts/test_barrier_kind_emission.sh` (objdump emission check) | §4.6 |
| SM10.3.D6 | `scripts/test_rpi5_osh_widening.sh` (on-board OSH latency probe) | §4.7 |
| SM10.1.1 | `scripts/build_rpi5_image.sh` (kernel8.img + config.txt packaging; also the `sele4n-hal` bootable binary target it packages) | §3.3 |
| SM10.3.D7 | Wire `scripts/test_qemu_tlb_cache_coherence.sh` — the script exists but is a self-skipping stub until SM10.1.1's image lands | §4.1 |

### SM10.4 — AN12-B inventory closure (3 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM10.4.1 | Each `smpLatentInventory` entry's `smpDischarge` updated to "SMP-implemented in WS-SM" | `Concurrency/Assumptions.lean` | M |
| SM10.4.2 | Rename `smpLatentInventory` to `smpDischargedInventory` (or retire entirely) | (refactor) | M |
| SM10.4.3 | 8-entry size witness retained | Theorem | T |

### SM10.5 — Final release validation (3 sub-tasks)

Runs on the image `SM10.1` produced, against the suites `SM10.3` completed —
which is why it sits here and not beside the image build.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM10.5.1 | Full QEMU `-smp 4` boot + workload run | `scripts/test_v1_0_0_release_validation.sh` | L |
| SM10.5.2 | All 5 tiers green on the release candidate | (verification) | M |
| SM10.5.3 | Release-candidate trace fixture commit | (1 file) | S |

### SM10.6 — Version bump + closure (5 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM10.6.1 | Version bump to v1.0.0 via `./scripts/bump_version.sh` (every site in `scripts/version_locations.sh`; §4) | M |
| SM10.6.2 | CHANGELOG v1.0.0 closure entry | `CHANGELOG.md` | M |
| SM10.6.3 | Move WS-RC artefacts to dev_history/audits/, plus `docs/planning/WS_RC_R4_TYPE_LEVEL_PROMOTION_PLAN.md` (a WS-RC artefact that sits under `docs/planning/`) | (file moves) | S |
| SM10.6.4 | Move WS-SM plan + per-phase docs to dev_history/planning/ — **19 file moves**, enumerated below | (19 file moves) | T |
| SM10.6.5 | Tag v1.0.0 (maintainer-cut) | git tag | T |

**SM10.6.4 archive list.**  The plan carried "11 file moves" against a list
that omitted SM9's own phase plan and every other WS-SM-adjacent planning
document — so the sub-task that retires the workstream's paper trail would
have left a third of it in `docs/planning/`, where a later reader would take
it for live work.  The list is enumerated here rather than left to the mover:

| # | File | Why it archives with WS-SM |
|---|------|-----------------------------|
| 1 | `SMP_MULTICORE_COMPLETION_PLAN.md` | the overview |
| 2 | `SMP_FOUNDATIONS_PLAN.md` | SM0 |
| 3 | `SMP_RUST_HAL_PLAN.md` | SM1 |
| 4 | `SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md` | SM2 |
| 5 | `SMP_PER_OBJECT_LOCKS_PLAN.md` | SM3 |
| 6 | `SMP_PER_CORE_STATE_PLAN.md` | SM4 |
| 7 | `SMP_PER_CORE_SCHEDULER_PLAN.md` | SM5 |
| 8 | `SMP_CROSS_CORE_IPC_PLAN.md` | SM6 |
| 9 | `SMP_TLB_SHOOTDOWN_PLAN.md` | SM7 |
| 10 | `SMP_INFORMATION_FLOW_PLAN.md` | SM8 |
| 11 | `SMP_DECLASSIFICATION_COMPLETION_PLAN.md` | **SM9 — the omission that produced this correction** |
| 12 | `SMP_RELEASE_CLOSURE_PLAN.md` | SM10 (this file) |
| 13 | `SMP_RELEASE_READINESS_PLAN.md` | WS-RR, the phase that gates this one |
| 14 | `UNFINISHED_SMP_WORK.md` | the register WS-RR closes; its own footer says it moves with them |
| 15 | `SMP_FINE_LOCK_MIGRATION_PLAN.md` | SM3.C.9's migration, closed by RR7.7 and SM10.1 |
| 16 | `SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md` | SM2.C-defer, absorbed by RR6 |
| 17 | `SMP_PANIC_HANG_REMEDIATION_PLAN.md` | the SM2.E remediation |
| 18 | `SYSCALL_RETURN_ABI_PLAN.md` | WS-RA, whose remaining obligations SM10.1 discharges |
| 19 | `REPLY_OBJECTS_COMPLETION_PLAN.md` | the SM6.C/SM6.D reply-object companion |

**Not moved by this sub-task**, and each for a stated reason — an archive list
is only correct if the exclusions are as deliberate as the inclusions:

- `IPC_INVARIANT_DETHREADING_PLAN.md` — already archived by **RR3.17**, which
  retires it on closing WS-DT.  Moving it twice is not possible; finding it
  still in `docs/planning/` when SM10 opens means RR3 did not close.
- `HARDWARE_PARTITION_ISOLATION_PLAN.md` — post-v1.0.0 and explicitly out of
  scope for the WS-SM audit.  It stays live.
- `WS_RC_R4_TYPE_LEVEL_PROMOTION_PLAN.md` — a WS-RC artefact; **SM10.6.3**
  moves it with the rest of WS-RC.

No path in this list appears in `scripts/website_link_manifest.txt`, so the
moves cannot 404 the website; `scripts/check_markdown_links.py` still has to
pass, so in-repo links to the moved paths are updated in the same PR.

## 4. Version-bump file list

**Do not maintain a list here.**  The authoritative registry is
[`scripts/version_locations.sh`](../../scripts/version_locations.sh); the
bumper and the Tier 0 verifier both read it, so a copy in this plan is a
second source of truth that can only drift out of agreement with the gate
that actually runs.  This section carried such a copy until `v0.34.29` and
it had drifted in both directions at once — it said 10 i18n locales where
the registry carries 11 (each contributing *two* sites, a badge and a
`Version` table row), omitted all three GitBook sites entirely, listed the
four per-crate `Cargo.toml`s which hold `version.workspace = true` and no
literal version at all, and listed `CHANGELOG.md`, `docs/DEVELOPMENT.md`,
`docs/CLAIM_EVIDENCE_INDEX.md` and `check_version_sync.sh` itself, none of
which are version sites.  Following it literally would have failed
`check_version_sync.sh`.

SM10.6.1 runs the bump in one step:

```bash
./scripts/bump_version.sh 1.0.0      # rewrites every registered site, then self-verifies
./scripts/check_version_sync.sh      # the Tier 0 gate, run again standalone
```

To see the live registry and its site count without running a bump:

```bash
./scripts/check_version_sync.sh | grep Checked   # "Checked <N> version sites."
```

At `v0.34.29` that reads **36 sites** across 13 path patterns.  Quote the
command, not the number: the count is a fact about the registry on the day
you run it, which is exactly why it is not written down here.

**What the bumper does not do** — the genuinely manual half of SM10.6.1,
and the only part that belongs in a plan:

| Manual step | Why the bumper cannot do it |
|-------------|------------------------------|
| `CHANGELOG.md` — the `## v1.0.0 — <summary>` entry | Prose. Deliberately not a version site (see CLAUDE.md, *Not version sites*); the bumper only reminds you |
| `CLAUDE.md` + `AGENTS.md` — active workstream WS-SM → **CLOSED** | A status transition, not a version string. The two files must stay byte-identical |
| `docs/CLAIM_EVIDENCE_INDEX.md` — v1.0.0 closure entries | New claims with new evidence cites |
| `docs/codebase_map.json` — metrics beyond the version field | Regenerated by `./scripts/sync_documentation_metrics.sh`, not by the bumper |

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

Theorem count: take it from docs/smp_theorem_manifest.json,
regenerated in this cut — 902 theorems registered in a
machine-checked inventory across SM0..SM10, of which SM2
contributes 22, SM3 276 and SM5 604.  The same inventories hold
1111 entries; the other 209 are defs, not proofs.  Quote the
902.  Do NOT restate a per-phase sum here; see the note below.
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
       docs/dev_history/planning/SMP_DECLASSIFICATION_COMPLETION_PLAN.md
       (SM9)
       docs/dev_history/planning/SMP_RELEASE_CLOSURE_PLAN.md (SM10)
       docs/dev_history/planning/SMP_RELEASE_READINESS_PLAN.md (WS-RR)
       plus the five WS-SM-adjacent plans and the register that
       SM10.6.4 enumerates -- nineteen files in total.
```

**Why the tally is not written out here.**  Until `v0.34.26` this section
carried the count as a hand-summed literal:

> 16 SM0 + 1 SM1 + 22 SM2 + 28 SM3 + ~50 SM4 + 30 SM5 + 25 SM6 + 14 SM7
> + 18 SM8 + 5 SM10 = 209 ≈ 210

That sum runs SM8 → SM10 with **no SM9 term**, though SM9 closed at
v0.33.100 — so this template, the `wsm_theorem_count` marker theorem and
SM10.3.13's "verify all 210 SM theorems land at HEAD" would each have
certified a number computed as if a landed phase never happened.  Nothing
would have broken when it did; that is what a hand-sum cannot do.

WS-RR RR0.5 and RR0.6 replaced it with a measurement.
`SeLe4n/Kernel/Concurrency/PhaseTheoremManifest.lean` registers one entry per
phase SM0..SM10 — **SM9 included** — and derives
`smpInventoriedTheoremCount` as the sum over those entries, with each entry's
count proved equal to the real inventory lengths.
`scripts/generate_smp_theorem_manifest.py` regenerates
`docs/smp_theorem_manifest.json` from the tree and fails Tier 0 when the
manifest, the Lean total, or the JSON disagree.  Read the number; do not
re-derive it.

**What the number counts, and what it does not.**  902 is the number of
**theorems** registered in a machine-checked inventory: named, resolving at
elaboration, duplicate-free, and — verified by the propositionality census —
of a type that is a `Prop`.

That last clause is not decoration.  The inventories register a phase's whole
surface, so 209 of their 1111 entries are `def`s: `wakeThreadLockSet` and
`determineTargetCore` in SM5.C's, `replenishOnCore` and
`migrateSchedContextReplenishment` in SM5.H's, the per-core invariant
*predicates* in SM5.I's, the WCRT cost functions in SM5.J's.  Every
inventory's construction macro proves its identifier resolves; none checks the
type.  A `List.length` therefore measures registrations, and quoting it as a
theorem count is the mistake this plan made at `v0.34.26` and corrected at
`v0.34.27` after review.  **`entryTotal` is 1111; `theoremTotal` is 902; quote
the second.**

Neither figure is the earlier "~210 substantive theorems", which was an
estimate of headline theorems per phase catalogue and is not recoverable from
the tree.  Six phases — SM1 and SM6..SM10 — have **no** theorem inventory and
are registered as contributing zero rather than given a plausible figure, so
902 *understates* what those phases prove.  Building the missing inventories is
registered debt with closure target **SM10.3.13**
(`docs/WORKSTREAM_HISTORY.md`); until they exist, the release note must say
"registered in a machine-checked inventory" rather than "proved", because
those are different claims.

## 6. Verification strategy

### 6.1 What SM10 proves

5 marker theorems.  Two landed early, under **corrected names**: the
originals spelled the workstream ID into the identifier (`wsm_` is `WS-SM`),
which CLAUDE.md's internal-first naming rule forbids and
`scripts/check_identifier_naming.py` would reject for any new code.  SM10
authors the remaining three under names that describe what they assert.

| Marker | State | Note |
|--------|-------|------|
| `smpRetiredInventory_complete` | SM10.4.3 | all 8 entries discharged |
| `SmpCompletionPhase.all_length = 11` | **landed** (RR0.6) | replaces `wsm_phase_count = 10`, which was both workstream-coded and wrong: SM0..SM10 is **eleven** phases, and SM0 is a phase whose theorems the manifest counts |
| acceptance-gate count | SM10 | replaces `wsm_acceptance_gate_count`; name it for what it counts (e.g. `smpAcceptanceGate_count`) |
| `smp_inventoried_theorem_count` | **landed** (RR0.6) | replaces `wsm_theorem_count`; a sum over `smpPhaseTheoremManifest`, not a literal — see §5 |
| release witness | SM10.6.5 | replaces `v1_0_0_release_witness`, whose `v1_0_0` component the naming gate reads as a version stamped into an identifier; spell the version without the `v` prefix (e.g. `release_witness_1_0_0`) |

The two landed markers live in
`SeLe4n/Kernel/Concurrency/PhaseTheoremManifest.lean` and are exercised by the
Tier-0 gate `scripts/generate_smp_theorem_manifest.py --check`.

### 6.2 What SM10 validates

- Tier 0..5 green at HEAD.
- All v1.0.0 acceptance-gate items checked.
- QEMU `-smp 4` release validation.

## 7. Risk inventory

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Documentation drift between phase plans and live tree | MED | LOW | SM10.2 audits each cross-reference |
| Version bump misses a file | LOW | MED | `scripts/check_version_sync.sh` gate |
| CHANGELOG entry incomplete | LOW | LOW | Template above lists all SM-phase closures |
| Archive move breaks website manifest | LOW | LOW | SM10.2.9 updates manifest in same PR |
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
- [ ] Version bumped to 1.0.0 across every registered site (`./scripts/check_version_sync.sh` passes).
- [ ] CHANGELOG v1.0.0 entry.
- [ ] WS-RC + WS-SM artefacts archived.
- [ ] AN12-B inventory discharged.
- [ ] QEMU release-validation green.
- [ ] Tier 0..5 green at HEAD.
- [ ] **v1.0.0 tag cut by maintainer.**

## 9. Cross-references

- **Previous**: [`SMP_TLB_SHOOTDOWN_PLAN.md`](SMP_TLB_SHOOTDOWN_PLAN.md), [`SMP_INFORMATION_FLOW_PLAN.md`](SMP_INFORMATION_FLOW_PLAN.md)
- **None next** — SM10 is the closure phase; v1.0.0 ships.

## 10. Theorem catalogue for SM10

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
# Tier 5 — the cross-language lock-correspondence oracle.  Delivered under
# this name, not the `test_tier5_lock_correspondence.sh` this block used to
# print, which never existed.
./scripts/test_tier5_cross_language.sh

# The SMP theorem manifest (RR0.6) — a hand-summed total cannot detect its
# own staleness, so the count is measured and cross-checked here.
python3 ./scripts/generate_smp_theorem_manifest.py --check

# Version sync:
./scripts/check_version_sync.sh

# Final QEMU SMP boot:
./scripts/test_qemu_smp_bringup.sh
```

`scripts/test_v1_0_0_release_validation.sh` — named by SM10.5.1 — **does not
exist yet**; it is SM10.1's to write, and it cannot run before SM10.1.1
produces the image.  It is listed as a deliverable rather than a command
here, because a verification block that prints a command nothing can run
teaches a reader the block is decorative.

---

*SM10 is the v1.0.0 ribbon-cutting. All substantive SMP work
landed in SM0..SM9; SM10 ensures the documentation, tests, and
metadata reflect the new reality. The v1.0.0 tag closes
WS-SM and ships the bootable verified SMP microkernel.*
